/-
Lion/Composition/StructuralInvariants.lean
==========================================

Preservation proofs for structural invariants:
- HeldCapsOwnedCorrectly: If plugin holds cap, cap.holder = plugin id
- HeldCapsInTable: If plugin holds cap, cap exists in kernel table

Based on A9/A10 from deep compute synthesis.
-/

import Lion.Composition.StructuralDefs
import Lion.Core.HashMapLemmas
import Lion.Theorems.Confinement
import Lion.Step.Step
import Lion.Step.HostCall
import Lion.Step.PluginInternal
import Lion.Step.KernelOp

namespace Lion.Composition

open Std
open Lion  -- Bring HeldCapsOwnedCorrectly, HeldCapsInTableWeak into scope

/-! =========== HELPER LEMMAS =========== -/

/-- HashMap insert preserves existence at other keys. -/
lemma hashMap_preserve_exists_under_insert
    (m : HashMap CapId Capability) (k : CapId) (v : Capability) (cid : CapId) :
    (∃ cap', m.get? cid = some cap') →
    (∃ cap', (m.insert k v).get? cid = some cap') := by
  rintro ⟨cap', hget⟩
  by_cases h : cid = k
  · -- After subst h, cid replaces k everywhere
    subst h
    exact ⟨v, Lion.HashMapLemmas.get?_insert_self m cid v⟩
  · refine ⟨cap', ?_⟩
    rw [Lion.HashMapLemmas.get?_insert_of_ne m k v h]
    exact hget

/-- HashMap insert preserves get? at other keys (stronger than existence). -/
lemma hashMap_preserve_get_under_insert
    (m : HashMap CapId Capability) (k : CapId) (v : Capability) (cid : CapId) (cap : Capability)
    (h_get : m.get? cid = some cap) (h_ne : cid ≠ k := by decide) :
    (m.insert k v).get? cid = some cap := by
  rw [Lion.HashMapLemmas.get?_insert_of_ne m k v h_ne]
  exact h_get

/-- HashMap map preserves existence at all keys. -/
lemma hashMap_preserve_exists_under_map
    (m : HashMap CapId Capability) (f : CapId → Capability → Capability) (cid : CapId) :
    (∃ cap', m.get? cid = some cap') →
    (∃ cap', (m.map f).get? cid = some cap') := by
  rintro ⟨cap', hget⟩
  refine ⟨f cid cap', ?_⟩
  rw [HashMap.get?_eq_getElem?, HashMap.getElem?_map]
  have h_old : m[cid]? = some cap' := by
    simpa [HashMap.get?_eq_getElem?] using hget
  simp [h_old]

/-- revoke_transitive preserves holder field for all caps. -/
lemma revoke_transitive_preserves_holder
    (rs : RevocationState) (revokeId cid : CapId) (cap : Capability)
    (h_get : rs.caps.get? cid = some cap) :
    ∃ cap', (rs.revoke_transitive revokeId).caps.get? cid = some cap' ∧ cap'.holder = cap.holder := by
  simp only [RevocationState.revoke_transitive]
  rw [HashMap.get?_eq_getElem?, HashMap.getElem?_map]
  have h_old : rs.caps[cid]? = some cap := by
    simpa [HashMap.get?_eq_getElem?] using h_get
  simp only [h_old, Option.map_some']
  -- The mapped cap has same holder regardless of the condition
  refine ⟨_, rfl, ?_⟩
  split <;> rfl

/-- revoke_transitive (which uses map) preserves key existence. -/
lemma revocation_preserve_exists_under_revoke_transitive
    (rs : RevocationState) (root : CapId) (cid : CapId) :
    (∃ cap', rs.caps.get? cid = some cap') →
    (∃ cap', (rs.revoke_transitive root).caps.get? cid = some cap') := by
  intro h
  simp only [RevocationState.revoke_transitive]
  exact hashMap_preserve_exists_under_map rs.caps _ cid h

/-! =========== HELDCAPSOWNEDCORRECTLY PRESERVATION =========== -/

/-- Convenience: if every plugin's heldCaps is empty, HeldCapsOwnedCorrectly holds vacuously. -/
theorem heldCapsOwnedCorrectly_of_all_empty (s : State)
    (h_empty : ∀ pid, (s.plugins pid).heldCaps = ∅) :
    HeldCapsOwnedCorrectly s := by
  intro pid capId h_in
  have : capId ∈ (∅ : Finset CapId) := by simpa [h_empty pid] using h_in
  simp at this

/-- Plugin internal steps preserve HeldCapsOwnedCorrectly. -/
theorem plugin_internal_preserves_heldCapsOwnedCorrectly
    (execPid : PluginId) (pi : PluginInternal) (s s' : State)
    (hexec : PluginExecInternal execPid pi s s')
    (h_inv : HeldCapsOwnedCorrectly s) :
    HeldCapsOwnedCorrectly s' := by
  intro pid capId h_in
  -- plugin_internal preserves heldCaps and kernel
  have h_frame := plugin_internal_comprehensive_frame execPid pi s s' hexec
  have h_kernel : s'.kernel = s.kernel := h_frame.1
  by_cases hpid : pid = execPid
  · -- pid = execPid case: use frame property for the executing plugin
    rw [hpid]
    rw [hpid] at h_in
    have h_caps : (s'.plugins execPid).heldCaps = (s.plugins execPid).heldCaps := h_frame.2.2.2.2.2.2.2.2.1
    have h_in_old : capId ∈ (s.plugins execPid).heldCaps := by simpa [h_caps] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv execPid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩
  · have h_plug : s'.plugins pid = s.plugins pid := h_frame.2.1 pid hpid
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plug] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩

/-- Kernel internal ops preserve HeldCapsOwnedCorrectly (they don't touch plugins). -/
theorem kernel_internal_preserves_heldCapsOwnedCorrectly
    (op : KernelOp) (s s' : State)
    (hexec : KernelExecInternal op s s')
    (h_inv : HeldCapsOwnedCorrectly s) :
    HeldCapsOwnedCorrectly s' := by
  intro pid capId h_in
  cases op with
  | time_tick =>
    have h_frame := time_tick_comprehensive_frame s s' hexec
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩
  | route_one dst =>
    have h_frame := route_one_comprehensive_frame dst s s' hexec
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩
  | workflow_tick wid =>
    have h_frame := workflow_tick_comprehensive_frame wid s s' hexec
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩
  | unblock_send aid =>
    have h_frame := unblock_send_comprehensive_frame aid s s' hexec
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    exact ⟨cap, by rw [h_kernel]; exact h_get, h_holder⟩

/-! =========== HELDCAPSINTABLE PRESERVATION (EXISTENCE-BASED) =========== -/

-- HeldCapsInTableWeak is now defined in StructuralDefs.lean

/-- If all heldCaps are empty, HeldCapsInTableWeak holds vacuously. -/
theorem heldCapsInTableWeak_of_empty_heldCaps (s : State)
    (h_empty : ∀ pid, (s.plugins pid).heldCaps = ∅) :
    HeldCapsInTableWeak s := by
  intro pid capId h_in
  have : capId ∈ (∅ : Finset CapId) := by simpa [h_empty pid] using h_in
  simp at this

/-- Plugin internal steps preserve HeldCapsInTableWeak. -/
theorem plugin_internal_preserves_heldCapsInTableWeak
    (execPid : PluginId) (pi : PluginInternal) (s s' : State)
    (hexec : PluginExecInternal execPid pi s s')
    (h_inv : HeldCapsInTableWeak s) :
    HeldCapsInTableWeak s' := by
  intro pid capId h_in
  have h_frame := plugin_internal_comprehensive_frame execPid pi s s' hexec
  have h_kernel : s'.kernel = s.kernel := h_frame.1
  by_cases hpid : pid = execPid
  · -- pid = execPid case: rewrite h_in to use execPid
    rw [hpid] at h_in
    have h_caps : (s'.plugins execPid).heldCaps = (s.plugins execPid).heldCaps := h_frame.2.2.2.2.2.2.2.2.1
    have h_in_old : capId ∈ (s.plugins execPid).heldCaps := by simpa [h_caps] using h_in
    obtain ⟨cap', hget⟩ := h_inv execPid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩
  · have h_plug : s'.plugins pid = s.plugins pid := h_frame.2.1 pid hpid
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plug] using h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩

/-- Kernel internal ops preserve HeldCapsInTableWeak. -/
theorem kernel_internal_preserves_heldCapsInTableWeak
    (op : KernelOp) (s s' : State)
    (hexec : KernelExecInternal op s s')
    (h_inv : HeldCapsInTableWeak s) :
    HeldCapsInTableWeak s' := by
  intro pid capId h_in
  cases op with
  | time_tick =>
    have h_frame := time_tick_comprehensive_frame s s' hexec
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩
  | route_one dst =>
    have h_frame := route_one_comprehensive_frame dst s s' hexec
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩
  | workflow_tick wid =>
    have h_frame := workflow_tick_comprehensive_frame wid s s' hexec
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩
  | unblock_send aid =>
    have h_frame := unblock_send_comprehensive_frame aid s s' hexec
    have h_plugs : s'.plugins = s.plugins := h_frame.2.1
    have h_kernel : s'.kernel = s.kernel := h_frame.1
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by simpa [h_plugs] using h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    exact ⟨cap', by simpa [h_kernel] using hget⟩

/-! =========== HOST CALL PRESERVATION =========== -/

/-- Host calls preserve HeldCapsOwnedCorrectly.
    Key case: cap_accept adds capId to caller's heldCaps,
    and the precondition ensures acceptedCap.holder = caller. -/
theorem host_call_preserves_heldCapsOwnedCorrectly
    (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult)
    (s s' : State)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_inv : HeldCapsOwnedCorrectly s) :
    HeldCapsOwnedCorrectly s' := by
  intro pid capId h_in
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec

  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec
    subst h_eq; exact h_inv pid capId h_in

  -- cap_delegate: plugins unchanged, kernel changed but doesn't affect old caps
  · obtain ⟨_parentId, _, parent, delegatee, newRights, newId, _, _, h_fresh, _, h_eq, _⟩ := hexec
    -- Plugins unchanged in cap_delegate, so we can rewrite h_in
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    -- cap_delegate inserts a new cap but doesn't change existing ones
    rw [h_eq]
    refine ⟨cap, ?_, h_holder⟩
    -- The old cap is still in the new table at the same position
    simp only [RevocationState.insert]
    -- newId is fresh (greater than all existing keys), so capId ≠ newId
    -- h_fresh : ∀ k, table.contains k → k < newId
    -- h_get : table.get? capId = some cap, so capId is in table
    -- If capId = newId, then newId < newId - contradiction
    have h_ne : capId ≠ newId := by
      intro h_eq_cap
      rw [h_eq_cap] at h_get
      -- h_get : get? newId = some cap
      -- h_fresh : get? newId = none
      -- Contradiction: some cap ≠ none
      rw [h_fresh] at h_get
      cases h_get
    exact hashMap_preserve_get_under_insert s.kernel.revocation.caps newId
            (create_delegated_cap s parent delegatee newRights newId) capId cap h_get h_ne

  -- cap_accept: adds capId to caller's heldCaps
  · obtain ⟨acceptId, acceptCap, h_get_acceptCap, _h_invalid, h_holder_acceptCap, _h_parent_valid,
            _h_pol_pending, _h_live_pending, h_eq, _⟩ := hexec
    let acceptedCap := { acceptCap with valid := true }
    rw [h_eq]
    by_cases hpid : pid = hc.caller
    · -- pid = caller: capId is either acceptId or was already held
      subst hpid
      -- Extract h_in for the caller case
      have h_in_caller : capId ∈ (s'.plugins hc.caller).heldCaps := h_in
      simp only [h_eq, Function.update_self] at h_in_caller
      rw [PluginState.grant_cap, Finset.mem_insert] at h_in_caller
      cases h_in_caller with
      | inl h_eq_id =>
        -- capId = acceptId: show the accepted cap has holder = caller
        subst h_eq_id
        refine ⟨acceptedCap, ?_, h_holder_acceptCap⟩
        exact Lion.HashMapLemmas.get?_insert_self _ _ _
      | inr h_old =>
        -- capId was already held: check if it's the same as acceptId
        by_cases h_eq_id : capId = acceptId
        · -- capId = acceptId: use acceptedCap (insert overwrites)
          subst h_eq_id
          refine ⟨acceptedCap, ?_, h_holder_acceptCap⟩
          exact Lion.HashMapLemmas.get?_insert_self _ _ _
        · -- capId ≠ acceptId: use old cap from invariant
          obtain ⟨cap, h_get_old, h_holder_old⟩ := h_inv hc.caller capId h_old
          refine ⟨cap, ?_, h_holder_old⟩
          exact hashMap_preserve_get_under_insert s.kernel.revocation.caps acceptId
                  acceptedCap capId cap h_get_old h_eq_id
    · -- pid ≠ caller: plugin unchanged
      have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
        have h_plugins_same : (s'.plugins pid) = (s.plugins pid) := by
          simp only [h_eq, Function.update]
          rw [dif_neg hpid]
        rw [← h_plugins_same]; exact h_in
      by_cases h_eq_id : capId = acceptId
      · -- Case IMPOSSIBLE: if pid holds acceptId but pid ≠ caller,
        -- HeldCapsOwnedCorrectly(s) says holder = pid, but precondition says holder = caller.
        obtain ⟨cap, h_get_old, h_holder_old⟩ := h_inv pid capId h_in_old
        exfalso
        -- Functional property of HashMap: cap = acceptCap (same key, same value)
        rw [h_eq_id] at h_get_old
        have h_same : some cap = some acceptCap := by rw [← h_get_old, h_get_acceptCap]
        injection h_same with h_cap_eq
        -- Thus cap = acceptCap, so cap.holder = acceptCap.holder = hc.caller
        -- But h_holder_old says cap.holder = pid, so pid = caller - contradiction
        have h_holder_eq : cap.holder = acceptCap.holder := by rw [h_cap_eq]
        rw [h_holder_acceptCap] at h_holder_eq
        rw [h_holder_eq] at h_holder_old
        exact hpid h_holder_old.symm
      · obtain ⟨cap, h_get_old, h_holder_old⟩ := h_inv pid capId h_in_old
        refine ⟨cap, ?_, h_holder_old⟩
        exact hashMap_preserve_get_under_insert s.kernel.revocation.caps acceptId
                acceptedCap capId cap h_get_old h_eq_id

  -- cap_revoke: plugins unchanged, kernel changes but holder field preserved
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    -- Plugins unchanged, extract h_in for original state
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
    rw [h_eq]
    -- Use helper lemma: revoke_transitive preserves holder
    obtain ⟨cap', h_get', h_holder'⟩ := revoke_transitive_preserves_holder
        s.kernel.revocation revokeId capId cap h_get
    exact ⟨cap', h_get', by rw [h_holder']; exact h_holder⟩

  -- mem_alloc: plugins unchanged (only ghost changes)
  · obtain ⟨_, h_eq, _⟩ := hexec
    subst h_eq
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
      simp only [State.apply_alloc] at h_in
      exact h_in
    exact h_inv pid capId h_in_old

  -- mem_free: plugins unchanged (only ghost changes)
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    subst h_eq
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
      simp only [State.apply_free] at h_in
      exact h_in
    exact h_inv pid capId h_in_old

  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- ipc_receive: only actors change
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      subst h_eq
      exact h_inv pid capId h_in
    · obtain ⟨h_eq, _⟩ := hexec
      subst h_eq
      exact h_inv pid capId h_in

  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- declassify: only caller's level changes, not heldCaps or kernel
  · obtain ⟨_newLevel, _h_le, h_eq, _⟩ := hexec
    -- Kernel unchanged in declassify
    have h_kernel_eq : s'.kernel = s.kernel := by simp only [h_eq]
    -- Extract h_in for original state
    by_cases hpid : pid = hc.caller
    · subst hpid
      have h_in_old : capId ∈ (s.plugins hc.caller).heldCaps := by
        simp only [h_eq, Function.update_self] at h_in
        exact h_in
      obtain ⟨cap, h_get, h_holder⟩ := h_inv hc.caller capId h_in_old
      rw [h_eq]
      exact ⟨cap, h_get, h_holder⟩
    · have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
        simp only [h_eq, Function.update, hpid, ite_false] at h_in
        exact h_in
      obtain ⟨cap, h_get, h_holder⟩ := h_inv pid capId h_in_old
      rw [h_eq]
      exact ⟨cap, h_get, h_holder⟩

/-- Host calls preserve HeldCapsInTableWeak.
    Key cases: cap_delegate and cap_accept insert to table, cap_revoke maps table.
    All preserve existence at held cap IDs.
    With Handle/State Separation, heldCaps is Finset CapId (not Finset Capability). -/
theorem host_call_preserves_heldCapsInTableWeak
    (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult)
    (s s' : State)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_inv : HeldCapsInTableWeak s)
    (_h_wk : Confinement.well_keyed_table s.kernel.revocation.caps) :
    HeldCapsInTableWeak s' := by
  intro pid capId h_in
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec

  -- cap_invoke: s' = s (7 elements)
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec
    subst h_eq; exact h_inv pid capId h_in

  -- cap_delegate: inserts new cap, plugins unchanged (12 elements)
  · obtain ⟨_parentId, _, parent, delegatee, newRights, newId, _, _, _, _, h_eq, _⟩ := hexec
    -- Plugins unchanged, transform h_in
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    rw [h_eq]
    -- Table becomes insert newId newCap, use insert preservation
    simp only [RevocationState.insert]
    exact hashMap_preserve_exists_under_insert s.kernel.revocation.caps newId
            (create_delegated_cap s parent delegatee newRights newId) capId ⟨cap', hget⟩

  -- cap_accept: updates table at acceptId, may add to caller's heldCaps (10 elements)
  · obtain ⟨acceptId, acceptCap, _h_get, _h_invalid, _h_holder, _h_parent_valid,
            _h_pol_pending, _h_live_pending, h_eq, _⟩ := hexec
    rw [h_eq]
    by_cases hpid : pid = hc.caller
    · -- pid = caller
      subst hpid
      -- Transform h_in for caller's updated plugin
      have h_in_caller : capId ∈ (s'.plugins hc.caller).heldCaps := h_in
      simp only [h_eq, Function.update_self] at h_in_caller
      rw [PluginState.grant_cap, Finset.mem_insert] at h_in_caller
      cases h_in_caller with
      | inl h_eq_id =>
        -- capId = acceptId: show entry exists at acceptId
        subst h_eq_id
        refine ⟨{ acceptCap with valid := true }, ?_⟩
        exact Lion.HashMapLemmas.get?_insert_self _ _ _
      | inr h_old =>
        -- capId was already held: use invariant and insert preservation
        obtain ⟨cap', hget⟩ := h_inv hc.caller capId h_old
        exact hashMap_preserve_exists_under_insert s.kernel.revocation.caps acceptId
                { acceptCap with valid := true } capId ⟨cap', hget⟩
    · -- pid ≠ caller: plugin unchanged
      have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
        have h_plugins_same : (s'.plugins pid) = (s.plugins pid) := by
          simp only [h_eq, Function.update]
          rw [dif_neg hpid]
        rw [← h_plugins_same]; exact h_in
      obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
      exact hashMap_preserve_exists_under_insert s.kernel.revocation.caps acceptId
              { acceptCap with valid := true } capId ⟨cap', hget⟩

  -- cap_revoke: maps table (preserves keys), plugins unchanged
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    rw [h_eq]
    exact revocation_preserve_exists_under_revoke_transitive
            s.kernel.revocation revokeId capId ⟨cap', hget⟩

  -- mem_alloc: kernel unchanged (only ghost changes)
  · obtain ⟨_, h_eq, _⟩ := hexec
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq, State.apply_alloc]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    rw [h_eq]
    simp only [State.apply_alloc_kernel]
    exact ⟨cap', hget⟩

  -- mem_free: kernel unchanged (only ghost changes)
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    have h_plugins_eq : s'.plugins = s.plugins := by simp only [h_eq, State.apply_free]
    have h_in_old : capId ∈ (s.plugins pid).heldCaps := by rw [← h_plugins_eq]; exact h_in
    obtain ⟨cap', hget⟩ := h_inv pid capId h_in_old
    rw [h_eq]
    simp only [State.apply_free_kernel]
    exact ⟨cap', hget⟩

  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- ipc_receive: only actors change, kernel unchanged
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      subst h_eq
      exact h_inv pid capId h_in
    · obtain ⟨h_eq, _⟩ := hexec
      subst h_eq
      exact h_inv pid capId h_in

  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    subst h_eq
    exact h_inv pid capId h_in

  -- declassify: only caller's level changes, kernel unchanged
  · obtain ⟨newLevel, h_le, h_eq, _⟩ := hexec
    rw [h_eq]
    by_cases hpid : pid = hc.caller
    · subst hpid
      -- After h_eq, s'.plugins hc.caller = { s.plugins hc.caller with level := newLevel }
      -- so heldCaps is unchanged
      have h_in_old : capId ∈ (s.plugins hc.caller).heldCaps := by
        simp only [h_eq, Function.update_self] at h_in
        exact h_in
      exact h_inv hc.caller capId h_in_old
    · have h_in_old : capId ∈ (s.plugins pid).heldCaps := by
        simp only [h_eq] at h_in
        simp only [Function.update, hpid, ↓reduceIte] at h_in
        exact h_in
      exact h_inv pid capId h_in_old

/-! =========== FULL STEP PRESERVATION =========== -/

/-- Step preservation for HeldCapsOwnedCorrectly. -/
theorem step_preserves_heldCapsOwnedCorrectly
    (s s' : State) (st : Step s s')
    (h_inv : HeldCapsOwnedCorrectly s) :
    HeldCapsOwnedCorrectly s' := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
    exact plugin_internal_preserves_heldCapsOwnedCorrectly pid pi s s' hexec h_inv
  | host_call hc a auth hr hparse hpre hexec =>
    exact host_call_preserves_heldCapsOwnedCorrectly hc a auth hr s s' hexec h_inv
  | kernel_internal op hexec =>
    exact kernel_internal_preserves_heldCapsOwnedCorrectly op s s' hexec h_inv

/-- Step preservation for HeldCapsInTableWeak.
    Requires well_keyed_table for cap_accept case. -/
theorem step_preserves_heldCapsInTableWeak
    (s s' : State) (st : Step s s')
    (h_inv : HeldCapsInTableWeak s)
    (h_wk : Confinement.well_keyed_table s.kernel.revocation.caps) :
    HeldCapsInTableWeak s' := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
    exact plugin_internal_preserves_heldCapsInTableWeak pid pi s s' hexec h_inv
  | host_call hc a auth hr hparse hpre hexec =>
    exact host_call_preserves_heldCapsInTableWeak hc a auth hr s s' hexec h_inv h_wk
  | kernel_internal op hexec =>
    exact kernel_internal_preserves_heldCapsInTableWeak op s s' hexec h_inv

end Lion.Composition
