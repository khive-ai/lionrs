/-
Lion/Refinement/Authorization.lean
==================================

Authorization invariant and Authorized witness construction.

This module proves that when authorization checks pass under AuthInv,
there exists a valid Lean `Authorized` witness.

APPROACH (informed by deep analysis):
- The original axioms (is_valid_axiom, policy_permit_axiom, held_caps_axiom,
  liveness_axiom) are NOT provable from definitions alone
- They require system invariants about state consistency
- We use AuthInv from Lion.Contracts.Auth, then derive theorems from it

THEOREM CHAIN (no axioms required):
- authInv_preserved: AuthInv is preserved by Lean Step transitions
- host_call_preserves_authInv: Host calls preserve AuthInv
- plugin_internal_preserves_authInv: Plugin-internal steps preserve AuthInv
- kernel_internal_preserves_authInv: Kernel-internal steps preserve AuthInv

NOTE: This is NOT a Rust refinement file. It proves Lean invariant preservation.
Rust refinement axioms are in RuntimeCorrespondence (Lion.Contracts.RuntimeCorrespondence).

STATUS: COMPLETE - 0 sorries, 0 axioms. Fully proven.
-/

import Mathlib.Tactic
import Lion.Core.Rights
import Lion.Core.Policy
import Lion.Core.Crypto
import Lion.State.State
import Lion.State.Kernel
import Lion.Step.Authorization
import Lion.Step.Step
import Lion.Step.PluginInternal
import Lion.Step.KernelOp
import Lion.Step.HostCall
import Lion.Contracts.AuthContract
import Lion.Refinement.Correspondence

namespace Lion.Refinement.Authorization

open Lion
open Lion.Contracts.Auth

/-!
## Pending-cap invariants used by `cap_accept`

`cap_accept` flips a capability from `valid = false` to `valid = true`.
But two `AuthInv` fields (`pol_complete` and `temporal_safe`) only talk about
caps with `valid = true`. So, in the accepted-cap branch of those proofs, we
need facts about the *pending* cap in the pre-state.

**RESOLVED**: The `KernelExecHost` cap_accept spec now requires two preconditions:
1. Policy completeness: `∀ act ctx, cap.holder = act.subject → cap.target = act.target →
   act.rights ⊆ cap.rights → policy_check s.kernel.policy act ctx = .permit`
2. Temporal safety: `MetaState.is_live s.ghost cap.target`

These preconditions are enforced at accept-time, eliminating the need for axioms.
The proofs use `h_pol_pending` and `h_live_pending` from the destructured `hexec`.
-/

/-! ## AuthInv Preservation

ALL STEP TYPES NOW PROVABLE:
- plugin_internal: PROVEN (kernel, heldCaps, ghost unchanged)
- kernel_internal: PROVEN (kernel, plugins, ghost unchanged)
- host_call: PROVEN (via constructive KernelExecHost definition)
-/

/--
**THEOREM: Host Call Preserves AuthInv**

Fully proven from constructive KernelExecHost definition.

For most cases (cap_invoke, ipc_*, resource_*, workflow_*): s' = s or kernel unchanged.
For mem_alloc/free: Only ghost state changes.
For cap_delegate: Inserts new cap with valid=false, so valid-cap invariants hold.
For cap_revoke: Sets valid := false, invalidating descendants transitively.

STATUS: COMPLETE - 0 sorries.
-/
theorem host_call_preserves_authInv :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      AuthInv s →
      AuthInv s' := by
  intro hc a auth hr s s' hexec hinv
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec

  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- cap_delegate: inserts new cap with valid=false
  -- Since newCap.valid=false, all AuthInv conditions that require valid=true are preserved
  · obtain ⟨parentId, _, parent, delegatee, newRights, newId, h_parent_get, h_valid, h_fresh, h_lt, h_eq, _⟩ := hexec
    rw [h_eq]
    -- The new cap has valid=false by construction
    have h_new_invalid : (create_delegated_cap s parent delegatee newRights newId).valid = false := rfl
    -- Key fact: parent.id = parentId (by keys_match on original lookup)
    have h_parent_id_eq : parent.id = parentId := hinv.caps_wf.keys_match h_parent_get
    constructor
    -- 1. caps_wf: CapTable.WellFormed preserved by insert with freshness + ordering
    · constructor
      · -- keys_match: new cap has id = newId, old caps unchanged
        intro k c h_get
        simp only at h_get
        unfold RevocationState.insert create_delegated_cap at h_get
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
        split at h_get
        · rename_i h_beq; cases h_get; simp only; exact eq_of_beq h_beq
        · exact hinv.caps_wf.keys_match h_get
      · -- parent_lt: new cap has parent.id < newId (h_lt), old caps unchanged
        intro k c p h_get h_parent
        simp only at h_get
        unfold RevocationState.insert create_delegated_cap at h_get
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
        split at h_get
        · rename_i h_beq; cases h_get; simp only at h_parent; cases h_parent
          -- p = parent.id, need to show parent.id < k = newId
          -- h_beq tells us k = newId
          have h_k_eq : k = newId := (eq_of_beq h_beq).symm
          rw [h_parent_id_eq, h_k_eq]; exact h_lt
        · exact hinv.caps_wf.parent_lt h_get h_parent
      · -- parent_valid: new cap has valid=false (vacuous), old valid caps have parents in new table
        intro k c p h_get h_cap_valid h_parent
        simp only at h_get
        unfold RevocationState.insert create_delegated_cap at h_get
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
        split at h_get
        · rename_i h_beq; cases h_get; cases h_cap_valid  -- valid=false contradicts h_cap_valid
        · -- Old cap: parent exists in old table, show it's in new table
          obtain ⟨pcap, h_pcap_get, h_pcap_valid⟩ := hinv.caps_wf.parent_valid h_get h_cap_valid h_parent
          -- p is in old table, so if newId == p, freshness would be violated
          have h_p_ne_newId : p ≠ newId := by
            intro h_eq
            rw [h_eq] at h_pcap_get
            rw [Std.HashMap.get?_eq_getElem?] at h_pcap_get h_fresh
            rw [h_fresh] at h_pcap_get
            cases h_pcap_get
          refine ⟨pcap, ?_, h_pcap_valid⟩
          simp only
          unfold RevocationState.insert create_delegated_cap
          have h_ne : (newId == p) = false := by rw [beq_eq_false_iff_ne]; exact Ne.symm h_p_ne_newId
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne, ite_false]
          exact h_pcap_get
    -- 2. pol_complete: for caps in new table with valid=true
    -- Key: new cap has valid=false, so only old caps with valid=true apply
    · intro cap act ctx h_get h_cap_valid hh ht hrsub
      unfold RevocationState.insert create_delegated_cap at h_get
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
      split at h_get
      · rename_i h_beq; cases h_get
        -- new cap has valid=false, contradicts h_cap_valid : true = true
        -- After substitution, h_cap_valid becomes false = true
        cases h_cap_valid
      · exact hinv.pol_complete cap act ctx h_get h_cap_valid hh ht hrsub
    -- 3. held_consistent: plugins unchanged, new cap not held yet
    · intro pid capId h_in
      -- plugins unchanged, so h_in applies to old state
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in
      -- cap exists in old table; show it exists in new table
      by_cases h_eq_id : capId = newId
      · -- capId = newId: but newId is fresh (not in table), contradiction
        subst h_eq_id
        rw [Std.HashMap.get?_eq_getElem?] at h_get h_fresh
        rw [h_fresh] at h_get
        cases h_get
      · -- capId ≠ newId: cap preserved under insert
        refine ⟨cap, ?_⟩
        unfold RevocationState.insert create_delegated_cap
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        have h_ne : (newId == capId) = false := beq_eq_false_iff_ne.mpr (Ne.symm h_eq_id)
        simp only [h_ne, ite_false]; exact h_get
    -- 4. valid_caps_held: plugins unchanged, new cap has valid=false
    · intro capId cap h_get h_is_valid
      -- For new cap (newId): is_valid would be false since valid=false
      -- For old caps: use hinv.valid_caps_held after showing they're unchanged
      by_cases h_eq_new : capId = newId
      · -- capId = newId: contradiction - new cap has valid=false, so is_valid = false
        subst h_eq_new
        simp only [RevocationState.is_valid, RevocationState.insert, create_delegated_cap,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true,
          ↓reduceIte, Option.some_bind, Option.some_orElse, Bool.false_eq_true] at h_is_valid
      · -- capId ≠ newId: old cap, use invariant
        have h_ne : (newId == capId) = false := beq_eq_false_iff_ne.mpr (Ne.symm h_eq_new)
        have h_get_old : s.kernel.revocation.caps.get? capId = some cap := by
          simp only [RevocationState.insert, create_delegated_cap,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne, ite_false] at h_get
          exact h_get
        have h_is_valid_old : s.kernel.revocation.is_valid capId = true := by
          simp only [RevocationState.is_valid, RevocationState.insert, create_delegated_cap,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne, ite_false] at h_is_valid ⊢
          exact h_is_valid
        exact hinv.valid_caps_held capId cap h_get_old h_is_valid_old
    -- 5. temporal_safe: ghost unchanged, only old valid caps apply
    · intro cap_id cap h_get h_cap_valid
      unfold RevocationState.insert create_delegated_cap at h_get
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
      split at h_get
      · rename_i h_beq; cases h_get; cases h_cap_valid
      · exact hinv.temporal_safe cap_id cap h_get h_cap_valid

  -- cap_accept: only changes valid field of pending cap and adds to holder's heldCaps
  -- This completes two-phase delegation: pending cap becomes valid
  · obtain ⟨acceptId, acceptCap, h_get, h_invalid, h_holder, h_parent_valid, h_pol_pending, h_live_pending, h_eq, _⟩ := hexec
    rw [h_eq]
    -- Key equality: acceptCap.id = acceptId
    have h_id_eq : acceptCap.id = acceptId := hinv.caps_wf.keys_match h_get
    have h_get' : s.kernel.revocation.caps.get? acceptCap.id = some acceptCap := by
      rw [h_id_eq]; exact h_get
    -- Define the accepted cap for convenience
    let acceptedCap := { acceptCap with valid := true }
    constructor
    -- 1. caps_wf: preserved by insert with same key
    · constructor
      · -- keys_match
        intro k c h_get_new
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
        split at h_get_new
        · rename_i h_beq; cases h_get_new
          simp only
          have h_k_eq : acceptId = k := eq_of_beq h_beq
          rw [h_id_eq, h_k_eq]
        · exact hinv.caps_wf.keys_match h_get_new
      · -- parent_lt
        intro k c pid h_get_new h_parent
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
        split at h_get_new
        · rename_i h_beq; cases h_get_new
          -- Goal: pid < k, where k = acceptId (from h_beq)
          have h_k_eq : k = acceptId := (eq_of_beq h_beq).symm
          rw [h_k_eq, ← h_id_eq]
          -- { acceptCap with valid := true }.parent = acceptCap.parent definitionally
          have h_parent' : acceptCap.parent = some pid := h_parent
          exact hinv.caps_wf.parent_lt h_get' h_parent'
        · exact hinv.caps_wf.parent_lt h_get_new h_parent
      · -- parent_valid: complex case with parent insert
        intro k c pid h_get_new h_valid h_parent
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
        split at h_get_new
        · -- Accepted cap case: need to show parent exists in new table and is valid
          rename_i h_beq; cases h_get_new
          -- h_parent : { acceptCap with valid := true }.parent = some pid
          have h_parent' : acceptCap.parent = some pid := h_parent
          -- From cap_accept precondition: parent must be valid (IsValid caps pid)
          simp only [h_parent'] at h_parent_valid
          -- h_parent_valid : IsValid s.kernel.revocation.caps pid
          -- Use IsValid.get_cap to extract capability information
          obtain ⟨pcap, h_pcap_get, h_pcap_valid⟩ := IsValid.get_cap h_parent_valid
          -- Show parent is in new table (pid ≠ acceptId by parent_lt)
          have h_plt : pid < acceptCap.id := hinv.caps_wf.parent_lt h_get' h_parent'
          have h_pid_ne : pid ≠ acceptId := by
            intro h_eq; rw [h_id_eq] at h_plt; rw [h_eq] at h_plt; exact Nat.lt_irrefl _ h_plt
          refine ⟨pcap, ?_, h_pcap_valid⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_ne : (acceptId == pid) = false := beq_eq_false_iff_ne.mpr h_pid_ne.symm
          simp only [h_ne, ite_false]
          exact h_pcap_get
        · -- Other cap case: parent exists in new table
          -- Need to convert h_get_new from indexing notation to get? form
          have h_get_conv : s.kernel.revocation.caps.get? c.id = some c := by
            have h_km := hinv.caps_wf.keys_match h_get_new
            simp only [Std.HashMap.get?_eq_getElem?, h_km]; exact h_get_new
          obtain ⟨pcap, h_pcap_get, h_pcap_valid⟩ := hinv.caps_wf.parent_valid h_get_conv h_valid h_parent
          -- Parent is in new table (pid ≠ acceptId by different reasoning)
          have h_plt : pid < c.id := hinv.caps_wf.parent_lt h_get_conv h_parent
          -- pid ≠ acceptId: if they were equal, acceptCap would be the parent of c
          -- But acceptCap.valid = false and parent_valid requires parent to be valid
          -- Since h_pcap_valid says the parent is valid, and acceptCap is not valid, pid ≠ acceptId
          have h_pid_ne : pid ≠ acceptId := by
            intro h_eq
            -- If pid = acceptId, then pcap should be at acceptId
            -- But h_pcap_get says caps.get? pid = some pcap with pcap.valid = true
            -- And h_get says caps.get? acceptId = some acceptCap with acceptCap.valid = false
            rw [h_eq, ← h_id_eq] at h_pcap_get
            -- Now h_pcap_get : caps.get? acceptCap.id = some pcap
            -- And h_get' : caps.get? acceptCap.id = some acceptCap
            rw [h_pcap_get] at h_get'
            -- h_get' : some pcap = some acceptCap, so pcap = acceptCap
            injection h_get' with h_eq_cap
            -- h_eq_cap : pcap = acceptCap
            rw [h_eq_cap] at h_pcap_valid
            -- h_pcap_valid : acceptCap.valid = true, but h_invalid : acceptCap.valid = false
            rw [h_pcap_valid] at h_invalid
            cases h_invalid
          refine ⟨pcap, ?_, h_pcap_valid⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_ne : (acceptId == pid) = false := beq_eq_false_iff_ne.mpr h_pid_ne.symm
          simp only [h_ne, ite_false]
          exact h_pcap_get
    -- 2. pol_complete
    · intro cap act ctx h_cap_get h_cap_valid hh ht hrsub
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_cap_get
      split at h_cap_get
      · rename_i h_beq; cases h_cap_get
        -- accepted-cap branch: use h_pol_pending from cap_accept precondition
        have hh' : acceptCap.holder = act.subject := by simpa [acceptedCap] using hh
        have ht' : acceptCap.target = act.target := by simpa [acceptedCap] using ht
        have hrsub' : act.rights ⊆ acceptCap.rights := by simpa [acceptedCap] using hrsub
        exact h_pol_pending act ctx hh' ht' hrsub'
      · exact hinv.pol_complete cap act ctx h_cap_get h_cap_valid hh ht hrsub
    -- 3. held_consistent: capId ∈ heldCaps → ∃ cap, table.get? capId = some cap
    · intro pid capId h_in
      -- s'.plugins = Function.update s.plugins hc.caller (grant_cap acceptId)
      -- s'.kernel.revocation.caps = s.kernel.revocation.caps.insert acceptId acceptedCap
      by_cases hpid : pid = hc.caller
      · -- pid = caller: heldCaps gains acceptId
        subst hpid
        simp only [Function.update_self] at h_in
        -- h_in : capId ∈ (s.plugins hc.caller).grant_cap acceptId
        -- grant_cap adds acceptId to heldCaps
        unfold PluginState.grant_cap at h_in
        simp only [Finset.mem_insert] at h_in
        rcases h_in with h_capId_eq | h_old
        · -- capId = acceptId: use acceptedCap in new table
          rw [h_capId_eq]
          refine ⟨acceptedCap, ?_⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
          rfl
        · -- capId was already held: use invariant and insert preservation
          obtain ⟨cap, h_get'⟩ := hinv.held_consistent hc.caller capId h_old
          by_cases h_eq_id : capId = acceptId
          · subst h_eq_id; exact ⟨acceptedCap, Lion.HashMapLemmas.get?_insert_self _ _ _⟩
          · refine ⟨cap, ?_⟩
            simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
            have h_ne : (acceptId == capId) = false := beq_eq_false_iff_ne.mpr (Ne.symm h_eq_id)
            simp only [h_ne, ite_false]; exact h_get'
      · -- pid ≠ caller: plugin unchanged
        have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
          simp only [Function.update, hpid, ↓reduceIte] at h_in; exact h_in
        obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in_old
        by_cases h_eq_id : capId = acceptId
        · subst h_eq_id; exact ⟨acceptedCap, Lion.HashMapLemmas.get?_insert_self _ _ _⟩
        · refine ⟨cap, ?_⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_ne : (acceptId == capId) = false := beq_eq_false_iff_ne.mpr (Ne.symm h_eq_id)
          simp only [h_ne, ite_false]; exact h_get
    -- 4. valid_caps_held: THE KEY CASE
    -- cap_accept sets valid=true AND adds capId to holder's heldCaps
    · intro capId cap h_get_new h_is_valid
      by_cases h_eq_accept : capId = acceptId
      · -- capId = acceptId: the accepted cap
        -- cap.holder = acceptCap.holder = hc.caller
        have h_cap_holder : cap.holder = hc.caller := by
          rw [h_eq_accept] at h_get_new
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_self_eq_true, ↓reduceIte] at h_get_new
          cases h_get_new; exact h_holder
        -- s'.plugins = Function.update s.plugins hc.caller (grant_cap acceptId)
        -- Need: capId ∈ (s'.plugins cap.holder).heldCaps = (grant_cap acceptId).heldCaps
        rw [h_cap_holder, h_eq_accept]
        simp only [Function.update_self, PluginState.grant_cap, Finset.mem_insert, true_or]
      · -- capId ≠ acceptId: old cap
        have h_ne : (acceptId == capId) = false := beq_eq_false_iff_ne.mpr (Ne.symm h_eq_accept)
        have h_get_old : s.kernel.revocation.caps.get? capId = some cap := by
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            h_ne, ite_false] at h_get_new
          exact h_get_new
        have h_is_valid_old : s.kernel.revocation.is_valid capId = true := by
          simp only [RevocationState.is_valid, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, h_ne, ite_false] at h_is_valid ⊢
          exact h_is_valid
        have h_in_old : capId ∈ (s.plugins cap.holder).heldCaps :=
          hinv.valid_caps_held capId cap h_get_old h_is_valid_old
        -- cap.holder might equal hc.caller - handle both cases
        by_cases h_holder_eq : cap.holder = hc.caller
        · -- cap.holder = caller: heldCaps = grant_cap, which includes old caps
          rw [h_holder_eq]
          simp only [Function.update_self, PluginState.grant_cap, Finset.mem_insert]
          right; rw [← h_holder_eq]; exact h_in_old
        · -- cap.holder ≠ caller: plugins unchanged
          simp only [Function.update, h_holder_eq, ↓reduceIte]
          exact h_in_old
    -- 5. temporal_safe
    · intro cap_id cap h_get_new h_cap_valid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
      split at h_get_new
      · rename_i h_beq; cases h_get_new
        -- accepted-cap branch: use h_live_pending from cap_accept precondition
        have h_live : MetaState.is_live s.ghost acceptCap.target := h_live_pending
        simpa [acceptedCap] using h_live
      · exact hinv.temporal_safe cap_id cap h_get_new h_cap_valid

  -- cap_revoke: uses revoke_transitive which preserves AuthInv
  -- Key insight: revoke_transitive only INVALIDATES caps, never validates them
  -- So valid caps in new table were valid in old table, and properties transfer
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    rw [h_eq]
    -- s' only differs in s'.kernel.revocation = s.kernel.revocation.revoke_transitive revokeId
    -- plugins unchanged, policy unchanged
    constructor
    -- 1. caps_wf: CapTable.WellFormed - preserved by revoke_transitive lemmas
    · constructor
      · exact RevocationState.revoke_transitive_preserves_keys_match
          s.kernel.revocation revokeId hinv.caps_wf.keys_match
      · exact RevocationState.revoke_transitive_preserves_parent_lt
          s.kernel.revocation revokeId hinv.caps_wf.parent_lt
      · exact RevocationState.revoke_transitive_preserves_parent_valid
          s.kernel.revocation revokeId hinv.caps_wf.parent_lt hinv.caps_wf.parent_valid
    -- 2. pol_complete: valid caps were valid before, policy permits unchanged
    -- Key insight: revoke_transitive_get?_of_valid_true shows valid caps are UNCHANGED
    · intro cap act ctx hcap_get hcap_valid hh ht hrsub
      -- Pull the same cap back into the old table (unchanged because valid=true)
      have hcap_get_old : s.kernel.revocation.caps.get? cap.id = some cap :=
        RevocationState.revoke_transitive_get?_of_valid_true
          s.kernel.revocation revokeId cap.id cap hcap_get hcap_valid
      -- Apply old completeness (policy unchanged by revoke)
      exact hinv.pol_complete cap act ctx hcap_get_old hcap_valid hh ht hrsub
    -- 3. held_consistent: plugins unchanged
    -- revoke_transitive preserves existence (only changes valid flag via map)
    · intro pid capId h_in
      -- plugins unchanged by revoke
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in
      -- Cap exists in old table, show it exists in new table after revoke_transitive
      -- revoke_transitive is a map operation, preserving all keys
      unfold RevocationState.revoke_transitive
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]
      rw [Std.HashMap.get?_eq_getElem?] at h_get
      simp only [h_get, Option.map_some']
      split <;> exact ⟨_, rfl⟩
    -- 4. valid_caps_held: plugins unchanged, valid caps unchanged by revoke_transitive
    · intro capId cap h_get h_is_valid
      -- Valid caps are unchanged by revoke_transitive (only invalidates, never validates)
      -- First extract cap.valid = true from is_valid check
      have h_cap_valid : cap.valid = true :=
        Contracts.Auth.valid_flag_of_is_valid _ h_get h_is_valid
      have h_get_old : s.kernel.revocation.caps.get? capId = some cap :=
        RevocationState.revoke_transitive_get?_of_valid_true
          s.kernel.revocation revokeId capId cap h_get h_cap_valid
      have h_is_valid_old : s.kernel.revocation.is_valid capId = true := by
        simp only [RevocationState.is_valid]
        simp only [h_get_old, Option.some_bind, Option.some_orElse, h_cap_valid]
      -- plugins unchanged by revoke
      exact hinv.valid_caps_held capId cap h_get_old h_is_valid_old
    -- 5. temporal_safe: ghost unchanged, valid caps were valid before
    -- Key insight: revoke_transitive_get?_of_valid_true shows valid caps are UNCHANGED
    · intro cap_id cap h_get h_valid
      have h_get_old : s.kernel.revocation.caps.get? cap_id = some cap :=
        RevocationState.revoke_transitive_get?_of_valid_true
          s.kernel.revocation revokeId cap_id cap h_get h_valid
      -- ghost unchanged by revoke; so reuse hinv.temporal_safe
      exact hinv.temporal_safe cap_id cap h_get_old h_valid

  -- mem_alloc: only ghost state changes
  -- Uses alloc_preserves_is_live for temporal_safe
  · obtain ⟨size, h_eq, _⟩ := hexec
    rw [h_eq]
    -- s' = s.apply_alloc hc.caller size, only ghost changes
    constructor
    · -- caps_wf: kernel unchanged
      exact hinv.caps_wf
    · -- pol_complete: kernel unchanged
      exact hinv.pol_complete
    · -- held_consistent: kernel and plugins unchanged
      exact hinv.held_consistent
    · -- valid_caps_held: kernel and plugins unchanged
      exact hinv.valid_caps_held
    · -- temporal_safe: ghost changes but alloc_preserves_is_live
      intro cap_id cap h_get h_valid
      have h_live_old : MetaState.is_live s.ghost cap.target :=
        hinv.temporal_safe cap_id cap h_get h_valid
      -- s'.ghost = s.ghost.alloc (s.ghost.resources.size) hc.caller
      unfold State.apply_alloc
      exact MetaState.alloc_preserves_is_live s.ghost (s.ghost.resources.size) hc.caller cap.target h_live_old

  -- mem_free: only ghost state changes
  -- Uses precondition: no valid cap targets the freed address
  · obtain ⟨addr, h_live, h_no_valid_cap, h_eq, _⟩ := hexec
    rw [h_eq]
    constructor
    · -- caps_wf: kernel unchanged
      exact hinv.caps_wf
    · -- pol_complete: kernel unchanged
      exact hinv.pol_complete
    · -- held_consistent: kernel/plugins unchanged
      exact hinv.held_consistent
    · -- valid_caps_held: kernel and plugins unchanged
      exact hinv.valid_caps_held
    · -- temporal_safe: valid caps don't target freed addr, so liveness preserved
      intro cap_id cap h_get h_valid
      have h_live_old : MetaState.is_live s.ghost cap.target :=
        hinv.temporal_safe cap_id cap h_get h_valid
      -- cap.target ≠ addr by precondition h_no_valid_cap
      have h_ne : cap.target ≠ addr := h_no_valid_cap cap_id cap h_get h_valid
      unfold State.apply_free
      exact MetaState.free_preserves_is_live s.ghost addr cap.target h_ne h_live_old

  -- ipc_send: s' = s (message returned in hr)
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- ipc_receive: modifies actors only
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      rw [h_eq]
      constructor <;> [exact hinv.caps_wf; exact hinv.pol_complete;
                       exact hinv.held_consistent; exact hinv.valid_caps_held;
                       exact hinv.temporal_safe]
    · obtain ⟨h_eq, _⟩ := hexec
      rw [h_eq]
      constructor <;> [exact hinv.caps_wf; exact hinv.pol_complete;
                       exact hinv.held_consistent; exact hinv.valid_caps_held;
                       exact hinv.temporal_safe]

  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq; exact hinv

  -- declassify: modifies plugins level only, kernel unchanged
  -- heldCaps preserved but need to show through Function.update
  · obtain ⟨newLevel, h_le, h_eq, _⟩ := hexec
    rw [h_eq]
    -- s' only changes s.plugins via Function.update, kernel/ghost unchanged
    constructor
    · -- caps_wf: kernel unchanged by declassify
      exact hinv.caps_wf
    · -- pol_complete: policy + caps unchanged
      exact hinv.pol_complete
    · -- held_consistent: only plugins level updated, heldCaps unchanged
      intro pid capId h_in
      -- s'.plugins = Function.update s.plugins hc.caller { ... with level := newLevel }
      -- heldCaps is unchanged in the update
      by_cases hpid : pid = hc.caller
      · -- pid = hc.caller: updated plugin
        subst hpid
        simp only [Function.update_self] at h_in
        -- h_in is about the updated plugin, but heldCaps field is unchanged
        -- goal: ∃ cap, s.kernel.revocation.caps.get? capId = some cap
        -- kernel unchanged, so use hinv.held_consistent
        exact hinv.held_consistent hc.caller capId h_in
      · -- pid ≠ hc.caller: plugin untouched
        simp only [Function.update, hpid, ↓reduceIte] at h_in
        exact hinv.held_consistent pid capId h_in
    · -- valid_caps_held: kernel unchanged, plugins level changed but heldCaps unchanged
      intro capId cap h_get h_is_valid
      have h_in_old := hinv.valid_caps_held capId cap h_get h_is_valid
      -- s'.plugins cap.holder has same heldCaps as s.plugins cap.holder
      by_cases hpid : cap.holder = hc.caller
      · rw [hpid] at h_in_old ⊢; simp only [Function.update_self]; exact h_in_old
      · simp only [Function.update, hpid, ↓reduceIte]; exact h_in_old
    · -- temporal_safe: ghost unchanged
      exact hinv.temporal_safe

/--
**THEOREM: Plugin Internal Preserves AuthInv**

PROOF: Plugin internal execution does NOT modify:
- kernel (plugin_internal_kernel_unchanged)
- heldCaps (plugin_internal_caps_preserved)
- ghost state (plugin_internal_ghost_unchanged)

Therefore all AuthInv fields are preserved.
-/
theorem plugin_internal_preserves_authInv (pid : PluginId) (pi : PluginInternal)
    (s s' : State) (hexec : PluginExecInternal pid pi s s') (hinv : AuthInv s) :
    AuthInv s' := by
  have h_kernel := plugin_internal_kernel_unchanged pid pi s s' hexec
  have h_ghost := plugin_internal_ghost_unchanged pid pi s s' hexec
  have h_frame := plugin_internal_frame pid pi s s' hexec
  constructor
  · -- caps_wf: kernel unchanged (h_kernel : s'.kernel = s.kernel)
    rw [h_kernel]; exact hinv.caps_wf
  · -- pol_complete: kernel unchanged
    rw [h_kernel]; exact hinv.pol_complete
  · -- held_consistent: kernel unchanged, plugins unchanged or heldCaps preserved
    intro pid' capId h_in
    -- Get heldCaps preservation for the executing plugin
    have h_pid_caps := plugin_internal_caps_preserved pid pi s s' hexec
    -- Show heldCaps is unchanged for all plugins
    have h_heldCaps_all : ∀ p, (s'.plugins p).heldCaps = (s.plugins p).heldCaps := by
      intro p
      by_cases hp : p = pid
      · rw [hp]; exact h_pid_caps
      · have hplug : s'.plugins p = s.plugins p := h_frame p hp; simp only [hplug]
    -- Transport membership from s' to s
    have h_in_s : capId ∈ (s.plugins pid').heldCaps := by rw [← h_heldCaps_all pid']; exact h_in
    -- Use invariant on old state, then rewrite kernel
    obtain ⟨cap, h_get⟩ := hinv.held_consistent pid' capId h_in_s
    refine ⟨cap, ?_⟩
    rw [h_kernel]; exact h_get
  · -- valid_caps_held: kernel unchanged, heldCaps preserved for all plugins
    intro capId cap h_get h_is_valid
    -- Transport from s' to s
    rw [h_kernel] at h_get h_is_valid
    have h_in_s := hinv.valid_caps_held capId cap h_get h_is_valid
    -- Transport back to s' (heldCaps preserved)
    have h_pid_caps := plugin_internal_caps_preserved pid pi s s' hexec
    have h_heldCaps_all : ∀ p, (s'.plugins p).heldCaps = (s.plugins p).heldCaps := by
      intro p
      by_cases hp : p = pid
      · rw [hp]; exact h_pid_caps
      · have hplug : s'.plugins p = s.plugins p := h_frame p hp; simp only [hplug]
    rw [h_heldCaps_all]; exact h_in_s
  · -- temporal_safe: kernel and ghost unchanged
    -- TemporalSafetyInvariant s' = ∀ cap_id cap, s'.kernel.caps.get? cap_id = some cap → cap.valid → is_live s'.ghost cap.target
    intro cap_id cap h_cap h_valid
    rw [h_kernel] at h_cap
    have h_live := hinv.temporal_safe cap_id cap h_cap h_valid
    rw [h_ghost]
    exact h_live

/--
**THEOREM: Kernel Internal Preserves AuthInv**

PROOF: All kernel ops do NOT modify:
- kernel (time_tick/route_one/workflow_tick/unblock_send all preserve kernel)
- plugins (all kernel ops preserve plugins)
- ghost state (all kernel ops preserve ghost)

Therefore all AuthInv fields are preserved.
-/
theorem kernel_internal_preserves_authInv (op : KernelOp) (s s' : State)
    (hexec : KernelExecInternal op s s') (hinv : AuthInv s) :
    AuthInv s' := by
  cases op with
  | time_tick =>
    have frame := time_tick_comprehensive_frame s s' hexec
    constructor
    · rw [frame.1]; exact hinv.caps_wf
    · rw [frame.1]; exact hinv.pol_complete
    · -- held_consistent: plugins unchanged, kernel unchanged
      intro pid capId h_in
      have h_in_s : capId ∈ (s.plugins pid).heldCaps := by rw [← frame.2.1]; exact h_in
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in_s
      refine ⟨cap, ?_⟩; rw [frame.1]; exact h_get
    · -- valid_caps_held: kernel and plugins unchanged
      intro capId cap h_get h_is_valid
      rw [frame.1] at h_get h_is_valid
      have h_in_s := hinv.valid_caps_held capId cap h_get h_is_valid
      rw [frame.2.1]; exact h_in_s
    · -- temporal_safe: kernel and ghost unchanged
      intro cap_id cap h_cap h_valid
      rw [frame.1] at h_cap  -- s'.kernel → s.kernel
      have h_live := hinv.temporal_safe cap_id cap h_cap h_valid
      rw [frame.2.2.2.2.2.1]  -- s'.ghost → s.ghost
      exact h_live
  | route_one dst =>
    have frame := route_one_comprehensive_frame dst s s' hexec
    constructor
    · rw [frame.1]; exact hinv.caps_wf
    · rw [frame.1]; exact hinv.pol_complete
    · -- held_consistent: plugins unchanged, kernel unchanged
      intro pid capId h_in
      have h_in_s : capId ∈ (s.plugins pid).heldCaps := by rw [← frame.2.1]; exact h_in
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in_s
      refine ⟨cap, ?_⟩; rw [frame.1]; exact h_get
    · -- valid_caps_held: kernel and plugins unchanged
      intro capId cap h_get h_is_valid
      rw [frame.1] at h_get h_is_valid
      have h_in_s := hinv.valid_caps_held capId cap h_get h_is_valid
      rw [frame.2.1]; exact h_in_s
    · -- temporal_safe: kernel and ghost unchanged
      intro cap_id cap h_cap h_valid
      rw [frame.1] at h_cap  -- s'.kernel → s.kernel
      have h_live := hinv.temporal_safe cap_id cap h_cap h_valid
      rw [frame.2.2.2.2.2.1]  -- s'.ghost → s.ghost
      exact h_live
  | workflow_tick wid =>
    have frame := workflow_tick_comprehensive_frame wid s s' hexec
    constructor
    · rw [frame.1]; exact hinv.caps_wf
    · rw [frame.1]; exact hinv.pol_complete
    · -- held_consistent: plugins unchanged, kernel unchanged
      intro pid capId h_in
      have h_in_s : capId ∈ (s.plugins pid).heldCaps := by rw [← frame.2.1]; exact h_in
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in_s
      refine ⟨cap, ?_⟩; rw [frame.1]; exact h_get
    · -- valid_caps_held: kernel and plugins unchanged
      intro capId cap h_get h_is_valid
      rw [frame.1] at h_get h_is_valid
      have h_in_s := hinv.valid_caps_held capId cap h_get h_is_valid
      rw [frame.2.1]; exact h_in_s
    · -- temporal_safe: kernel and ghost unchanged
      intro cap_id cap h_cap h_valid
      rw [frame.1] at h_cap  -- s'.kernel → s.kernel
      have h_live := hinv.temporal_safe cap_id cap h_cap h_valid
      rw [frame.2.2.2.2.2.1]  -- s'.ghost → s.ghost
      exact h_live
  | unblock_send dst =>
    have frame := unblock_send_comprehensive_frame dst s s' hexec
    constructor
    · rw [frame.1]; exact hinv.caps_wf
    · rw [frame.1]; exact hinv.pol_complete
    · -- held_consistent: plugins unchanged, kernel unchanged
      intro pid capId h_in
      have h_in_s : capId ∈ (s.plugins pid).heldCaps := by rw [← frame.2.1]; exact h_in
      obtain ⟨cap, h_get⟩ := hinv.held_consistent pid capId h_in_s
      refine ⟨cap, ?_⟩; rw [frame.1]; exact h_get
    · -- valid_caps_held: kernel and plugins unchanged
      intro capId cap h_get h_is_valid
      rw [frame.1] at h_get h_is_valid
      have h_in_s := hinv.valid_caps_held capId cap h_get h_is_valid
      rw [frame.2.1]; exact h_in_s
    · -- temporal_safe: kernel and ghost unchanged (unblock_send has different frame structure)
      intro cap_id cap h_cap h_valid
      rw [frame.1] at h_cap  -- s'.kernel → s.kernel
      have h_live := hinv.temporal_safe cap_id cap h_cap h_valid
      rw [frame.2.2.2.2.2.2.1]  -- s'.ghost → s.ghost (unblock_send: one more level)
      exact h_live

/--
**THEOREM: AuthInv Preserved by All Steps**

Combines the proven cases (plugin_internal, kernel_internal) with the
host_call axiom to give the full preservation theorem.
-/
theorem authInv_preserved (s s' : State) (hinv : AuthInv s) (hstep : Step s s') :
    AuthInv s' := by
  cases hstep with
  | plugin_internal pid pi hpre hexec =>
    exact plugin_internal_preserves_authInv pid pi s s' hexec hinv
  | host_call hc a auth hr hparse hpre hexec =>
    exact host_call_preserves_authInv hc a auth hr s s' hexec hinv
  | kernel_internal op hexec =>
    exact kernel_internal_preserves_authInv op s s' hexec hinv

/-! ## Theorems Replacing Old Axioms -/

/-- THEOREM (replaces is_valid_axiom): Valid flag implies IsValid under AuthInv.

Uses strong induction on cap_id with ParentLt for termination.
-/
theorem isValid_of_valid_flag
    (s : State) (cap_id : CapId)
    (h_inv : AuthInv s) :
    (∃ cap, s.kernel.revocation.caps.get? cap_id = some cap ∧ cap.valid = true) →
    IsValid s.kernel.revocation.caps cap_id := by
  intro h_exists
  -- Strong induction on cap_id (parent ids are strictly smaller)
  induction cap_id using Nat.strongRecOn with
  | ind n ih =>
    rcases h_exists with ⟨c, hget, hvalid⟩
    -- Key matches id
    have hcid : c.id = n := h_inv.caps_wf.keys_match hget
    have hget_id : s.kernel.revocation.caps.get? c.id = some c := by
      simp only [hcid]; exact hget
    -- Case split on parent
    cases hparent : c.parent with
    | none =>
        -- Root case: no parent
        have h : IsValid s.kernel.revocation.caps c.id :=
          IsValid.root (caps := s.kernel.revocation.caps) (c := c) hget_id hvalid hparent
        simp only [hcid] at h
        exact h
    | some p =>
        -- Child case: parent must exist and be valid
        have hp_lt : p < n := h_inv.caps_wf.parent_lt hget hparent
        have hex_p : ∃ pc, s.kernel.revocation.caps.get? p = some pc ∧ pc.valid = true :=
          h_inv.caps_wf.parent_valid hget hvalid hparent
        -- Apply induction hypothesis on parent
        have hvalid_p : IsValid s.kernel.revocation.caps p := ih p hp_lt hex_p
        -- Build child validity
        have h : IsValid s.kernel.revocation.caps c.id :=
          IsValid.child (caps := s.kernel.revocation.caps) (c := c)
            (p_id := p) hget_id hvalid hparent hvalid_p
        simp only [hcid] at h
        exact h

/-- THEOREM (replaces policy_permit_axiom): Policy permits under AuthInv. -/
theorem policy_permit_of_authInv
    (s : State) (a : Action) (cap : Capability) (ctx : PolicyContext)
    (h_inv : AuthInv s)
    (h_in_table : s.kernel.revocation.caps.get? cap.id = some cap)
    (h_holder : cap.holder = a.subject)
    (h_target : cap.target = a.target)
    (h_rights : a.rights ⊆ cap.rights)
    (h_valid : s.kernel.revocation.is_valid cap.id = true) :
    policy_check s.kernel.policy a ctx = PolicyDecision.permit := by
  have h_cap_valid : cap.valid = true := valid_flag_of_is_valid _ h_in_table h_valid
  exact h_inv.pol_complete cap a ctx h_in_table h_cap_valid h_holder h_target h_rights

/-- THEOREM (replaces held_caps_axiom): Held caps under AuthInv.

NOTE: With Handle/State Separation, this theorem's TYPE has changed.
Old: cap ∈ (s.plugins cap.holder).heldCaps (Capability in Finset Capability)
New: cap.id ∈ (s.plugins cap.holder).heldCaps (CapId in Finset CapId)

Uses the ValidCapsHeld field of AuthInv directly.
-/
theorem held_caps_of_authInv
    (s : State) (cap : Capability)
    (h_inv : AuthInv s)
    (h_in_table : s.kernel.revocation.caps.get? cap.id = some cap)
    (h_valid : s.kernel.revocation.is_valid cap.id = true) :
    cap.id ∈ (s.plugins cap.holder).heldCaps :=
  h_inv.valid_caps_held cap.id cap h_in_table h_valid

/-- THEOREM (replaces liveness_axiom): Liveness under AuthInv. -/
theorem liveness_of_authInv
    (s : State) (cap : Capability) (r : ℕ)
    (h_inv : AuthInv s)
    (h_in_table : s.kernel.revocation.caps.get? cap.id = some cap)
    (h_valid : s.kernel.revocation.is_valid cap.id = true)
    (h_target : cap.target = r) :
    MetaState.is_live s.ghost r := by
  have h_cap_valid : cap.valid = true := valid_flag_of_is_valid _ h_in_table h_valid
  have h_live : MetaState.is_live s.ghost cap.target :=
    h_inv.temporal_safe cap.id cap h_in_table h_cap_valid
  simp only [h_target] at h_live
  exact h_live

/-! ## Main Refinement Theorem -/

/-- Build capability_check from individual checks

NOTE: With Handle/State Separation, h_held is now about CapId not Capability.
-/
theorem build_capability_check
    (s : State) (a : Action) (cap : Capability)
    (h_holder : cap.holder = a.subject)
    (h_target : cap.target = a.target)
    (h_rights : a.rights ⊆ cap.rights)
    (h_seal : Capability.verify_seal s.kernel.hmacKey cap)
    (h_revoc : s.kernel.revocation.is_valid cap.id = true)
    (h_held : cap.id ∈ (s.plugins a.subject).heldCaps) :
    capability_check s a cap := by
  unfold capability_check cap_isValid
  exact ⟨h_holder, h_target, h_rights, ⟨h_seal, h_revoc⟩, h_held⟩

/--
**Main Refinement Theorem**: Rust authorization refines Lean Authorized.

If the Rust `authorize_with_context` succeeds (all checks pass), then
there exists a valid Lean `Authorized` witness for the corresponding
state and action.

Now requires AuthInv assumption instead of 4 separate axioms.
-/
theorem rust_authorization_refines_lean
    (s : State)
    (a : Action)
    (cap : Capability)
    (ctx : PolicyContext)
    -- System invariant
    (h_inv : AuthInv s)
    -- Rust checks passed
    (h_holder : cap.holder = a.subject)
    (h_target : cap.target = a.target)
    (h_rights : a.rights ⊆ cap.rights)
    (h_seal : Capability.verify_seal s.kernel.hmacKey cap)
    (h_revoc : s.kernel.revocation.is_valid cap.id = true)
    (h_in_caps : s.kernel.revocation.caps.get? cap.id = some cap)
    -- Biba integrity check (Rust verifies for writes)
    (h_biba : biba_write_ok s a) :
    -- Conclusion: Lean Authorized exists
    ∃ (auth : Authorized s a), auth.cap = cap ∧ auth.ctx = ctx := by
  -- Get h_held from theorem (now about CapId, not Capability)
  have h_held : cap.id ∈ (s.plugins a.subject).heldCaps := by
    have h := held_caps_of_authInv s cap h_inv h_in_caps h_revoc
    rw [← h_holder]
    exact h
  -- Get h_pol from theorem
  have h_pol : policy_check s.kernel.policy a ctx = PolicyDecision.permit :=
    policy_permit_of_authInv s a cap ctx h_inv h_in_caps h_holder h_target h_rights h_revoc
  -- Get h_valid from theorem
  have h_valid : IsValid s.kernel.revocation.caps cap.id := by
    apply isValid_of_valid_flag s cap.id h_inv
    exact ⟨cap, h_in_caps, valid_flag_of_is_valid _ h_in_caps h_revoc⟩
  -- Get h_live from theorem
  have h_live : ∀ r, a.target = r → MetaState.is_live s.ghost r := by
    intro r hr
    rw [← hr, ← h_target]
    exact liveness_of_authInv s cap cap.target h_inv h_in_caps h_revoc rfl
  -- Build capability_check
  have h_cap : capability_check s a cap :=
    build_capability_check s a cap h_holder h_target h_rights h_seal h_revoc h_held
  -- Construct Authorized (now includes h_biba for Biba integrity)
  exact ⟨⟨cap, ctx, h_cap, h_pol, h_valid, h_live, h_rights, h_biba⟩, rfl, rfl⟩

/-! ## Corollaries -/

/-- Rust authorization implies complete mediation -/
theorem rust_auth_implies_mediated
    (s : State) (a : Action) (cap : Capability) (ctx : PolicyContext)
    (h_inv : AuthInv s)
    (h_holder : cap.holder = a.subject)
    (h_target : cap.target = a.target)
    (h_rights : a.rights ⊆ cap.rights)
    (h_seal : Capability.verify_seal s.kernel.hmacKey cap)
    (h_revoc : s.kernel.revocation.is_valid cap.id = true)
    (h_in_caps : s.kernel.revocation.caps.get? cap.id = some cap)
    (h_biba : biba_write_ok s a) :
    properly_mediated s a := by
  obtain ⟨auth, _, _⟩ := rust_authorization_refines_lean s a cap ctx h_inv
    h_holder h_target h_rights h_seal h_revoc h_in_caps h_biba
  exact ⟨auth, trivial⟩

/-- Rust authorization implies no ambient authority

NOTE: With Handle/State Separation, we prove capId is held and lookup the cap's rights.
The statement changes: instead of c ∈ heldCaps with c.rights, we have capId ∈ heldCaps
and a cap in the table with cap.rights.
-/
theorem rust_auth_no_ambient
    (s : State) (a : Action) (cap : Capability) (ctx : PolicyContext)
    (h_inv : AuthInv s)
    (h_holder : cap.holder = a.subject)
    (h_target : cap.target = a.target)
    (h_rights : a.rights ⊆ cap.rights)
    (h_seal : Capability.verify_seal s.kernel.hmacKey cap)
    (h_revoc : s.kernel.revocation.is_valid cap.id = true)
    (h_in_caps : s.kernel.revocation.caps.get? cap.id = some cap)
    (h_biba : biba_write_ok s a) :
    ∃ capId, capId ∈ (s.plugins a.subject).heldCaps ∧
      ∃ c, s.kernel.revocation.caps.get? capId = some c ∧ a.rights ⊆ c.rights := by
  obtain ⟨auth, h_cap_eq, _⟩ := rust_authorization_refines_lean s a cap ctx h_inv
    h_holder h_target h_rights h_seal h_revoc h_in_caps h_biba
  -- Use holder_has_cap theorem to get h_held
  have h_held := Authorized.holder_has_cap auth
  rw [h_cap_eq] at h_held
  refine ⟨cap.id, h_held, cap, h_in_caps, h_rights⟩

/-! ## Summary

This module proves:

1. **Main Refinement** (rust_authorization_refines_lean):
   AuthInv s → Rust authorize_with_context success → Lean Authorized exists

2. **Preservation Theorems** (fully proven, no axioms):
   - authInv_preserved: AuthInv is preserved by all state transitions
   - host_call_preserves_authInv: Host calls preserve AuthInv
   - plugin_internal_preserves_authInv: Plugin-internal steps preserve AuthInv
   - kernel_internal_preserves_authInv: Kernel-internal steps preserve AuthInv

3. **Derived Theorems** (from AuthInv):
   - isValid_of_valid_flag: Valid flag → IsValid (via strong induction)
   - policy_permit_of_authInv: Policy permits for matching caps
   - held_caps_of_authInv: Valid caps in heldCaps
   - liveness_of_authInv: Valid caps have live targets

4. **Corollaries**:
   - rust_auth_implies_mediated: Complete mediation holds
   - rust_auth_no_ambient: No ambient authority

Invariant definitions are in: Lion.Contracts.Auth

Total: ~800 lines, 0 sorries, 0 axioms. Fully proven.

The held_consistent proof for plugin_internal uses the key insight that heldCaps
is unchanged for all plugins: the executing plugin preserves heldCaps via
plugin_internal_caps_preserved, and other plugins are entirely unchanged via
plugin_internal_frame.
-/

end Lion.Refinement.Authorization
