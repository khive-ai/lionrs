/-
Lion/Step/HostCall.lean
========================

Host function calls (trust boundary crossings).

REFACTORED: KernelExecHost is now CONSTRUCTIVE (def, not opaque).
This allows proving frame properties as theorems instead of axioms.

Axiom reduction: ~28 → 3 true axioms (seal, WASM bounds, Rust correspondence).
-/

import Lion.Core.Identifiers
import Lion.Core.HashMapLemmas
import Lion.State.Memory
import Lion.State.State
import Lion.Step.Authorization
import Lion.Theorems.Confinement
import Lion.Contracts.AuthContract

namespace Lion

/-! =========== HOST FUNCTIONS =========== -/

/-- All host functions that cross the trust boundary -/
inductive HostFunctionId where
  | cap_invoke      -- Use a capability
  | cap_delegate    -- Delegate capability to another plugin
  | cap_accept      -- Accept a delegated capability (completes two-phase delegation)
  | cap_revoke      -- Revoke a capability
  | mem_alloc       -- Allocate kernel-managed memory
  | mem_free        -- Free kernel-managed memory
  | ipc_send        -- Send message to another actor
  | ipc_receive     -- Receive message (blocking)
  | resource_create -- Create kernel resource
  | resource_access -- Access kernel resource
  | workflow_start  -- Start a workflow
  | workflow_step   -- Advance workflow state
  | declassify      -- Controlled information declassification
deriving DecidableEq, Repr, Hashable

/-! =========== HOST CALL STRUCTURE =========== -/

/-- Host call request from plugin -/
structure HostCall where
  caller   : PluginId
  function : HostFunctionId
  args     : List Nat  -- Simplified from WasmValue
  reads    : List (MemAddr × Size)   -- Memory regions to read
  writes   : List (MemAddr × Size)   -- Memory regions to write
deriving Repr

/-- Result of host call execution -/
structure HostResult where
  newCaps : List Capability  -- Capabilities created/delegated
  newMsgs : List Message     -- Messages queued

instance : Repr HostResult where
  reprPrec _ _ := "«HostResult»"

/-! =========== HOST CALL PARSING =========== -/

/-- Parse host call to action (opaque implementation) -/
opaque hostcall_action : HostCall → Option Action

/-- Precondition for host call -/
def host_call_pre (hc : HostCall) (s : State) : Prop :=
  -- Must parse to valid action
  (∃ a, hostcall_action hc = some a ∧ a.subject = hc.caller) ∧
  -- Read regions must be in bounds and valid
  (∀ r ∈ hc.reads,
    LinearMemory.addr_in_bounds (s.plugins hc.caller).memory r.1 r.2) ∧
  -- Write regions must be in bounds and valid
  (∀ w ∈ hc.writes,
    LinearMemory.addr_in_bounds (s.plugins hc.caller).memory w.1 w.2)

/-! =========== HOST CALL HELPERS =========== -/

/-- Create a delegated capability from parent.
    CRITICAL: Uses intersection to GUARANTEE confinement.
    IMPORTANT: valid := false until explicitly accepted via cap_accept.
    This ensures AuthInv.held_consistent is preserved across cap_delegate. -/
def create_delegated_cap (s : State) (parent : Capability) (holder : PluginId)
    (newRights : Rights) (newId : CapId) : Capability where
  id := newId
  holder := holder
  target := parent.target
  rights := newRights ∩ parent.rights  -- CONFINEMENT BY CONSTRUCTION
  parent := some parent.id
  epoch := s.kernel.revocation.epoch
  valid := false  -- Starts invalid until cap_accept (two-phase delegation)
  signature := seal_payload s.kernel.hmacKey {
    holder := holder
    target := parent.target
    rights := newRights ∩ parent.rights
    parent := some parent.id
    epoch := s.kernel.revocation.epoch
  }

/-! =========== CONSTRUCTIVE HOST CALL EXECUTION =========== -/

/--
**CONSTRUCTIVE KernelExecHost**

Defines exactly what each host function does to state.
This is a DEFINITION (def), not opaque, enabling theorem proofs.

Key insight: Each case explicitly specifies:
1. What state changes occur
2. What stays the same (frame)

From this definition, all frame properties become PROVABLE theorems.
-/
def KernelExecHost
    (hc : HostCall)
    (_a : Action)
    (_auth : Authorized s _a)
    (hr : HostResult)
    (s s' : State) : Prop :=
  match hc.function with
  -- CAPABILITY OPERATIONS (may modify kernel.revocation)
  | .cap_invoke =>
      -- Use a capability: validate and record usage
      -- Handle model: caller holds capId, we look up the cap in kernel table
      ∃ capId ∈ (s.plugins hc.caller).heldCaps,
      ∃ cap : Capability,
        s.kernel.revocation.caps.get? capId = some cap ∧
        IsValid s.kernel.revocation.caps capId ∧
        s' = s ∧  -- State unchanged (invoke just uses the cap)
        hr = { newCaps := [], newMsgs := [] }
  | .cap_delegate =>
      -- Delegate capability: create new cap with rights ⊆ parent
      -- The new cap is returned in hr.newCaps for delivery via IPC
      -- (NOT directly added to delegatee's heldCaps - that violates frame)
      -- PRECONDITIONS:
      --   1. parent cap exists in table and is valid
      --   2. caller holds the parent cap ID
      --   3. newId is fresh (not in table) - ensures well_keyed_table preserved
      --   4. parentId < newId - ensures ParentLt invariant preserved
      ∃ parentId ∈ (s.plugins hc.caller).heldCaps,
      ∃ parent : Capability,
      ∃ delegatee : PluginId,
      ∃ newRights : Rights,
      ∃ newId : CapId,
        s.kernel.revocation.caps.get? parentId = some parent ∧
        IsValid s.kernel.revocation.caps parentId ∧
        s.kernel.revocation.caps.get? newId = none ∧  -- Freshness
        parentId < newId ∧  -- ParentLt ordering
        let newCap := create_delegated_cap s parent delegatee newRights newId
        let newRevocation := s.kernel.revocation.insert newCap
        -- Only kernel.revocation is modified; plugins unchanged
        s' = { s with kernel := { s.kernel with revocation := newRevocation } } ∧
        hr = { newCaps := [newCap], newMsgs := [] }
  | .cap_accept =>
      -- Accept a delegated capability (two-phase delegation phase 2)
      -- PRECONDITIONS:
      --   1. cap exists in kernel table with valid = false
      --   2. cap.holder = hc.caller (only intended recipient can accept)
      --   3. cap.parent exists and is valid (parent wasn't revoked before accept)
      --   4. policy is complete for this cap (needed once it becomes valid)
      --   5. target is live (temporal safety, needed once it becomes valid)
      ∃ capId : CapId,
      ∃ cap : Capability,
        s.kernel.revocation.caps.get? capId = some cap ∧
        cap.valid = false ∧  -- Pending (not yet accepted)
        cap.holder = hc.caller ∧  -- Only holder can accept
        (match cap.parent with
          | none => True  -- Root cap, no parent check needed
          | some pid => IsValid s.kernel.revocation.caps pid) ∧  -- Parent must be valid
        -- Policy completeness: policy permits actions matching this cap
        (∀ act ctx,
          cap.holder = act.subject →
          cap.target = act.target →
          act.rights ⊆ cap.rights →
          policy_check s.kernel.policy act ctx = PolicyDecision.permit) ∧
        -- Temporal safety: target resource is live
        MetaState.is_live s.ghost cap.target ∧
        let acceptedCap := { cap with valid := true }
        let newRevocation := { s.kernel.revocation with
          caps := s.kernel.revocation.caps.insert capId acceptedCap }
        -- Handle model: add capId to heldCaps (not full cap)
        let newPlugin := (s.plugins hc.caller).grant_cap capId
        s' = { s with
          kernel := { s.kernel with revocation := newRevocation },
          plugins := Function.update s.plugins hc.caller newPlugin } ∧
        hr = { newCaps := [], newMsgs := [] }
  | .cap_revoke =>
      -- Revoke capability transitively: set valid=false on cap and all descendants
      -- Uses revoke_transitive to preserve ValidParentPresent invariant
      ∃ capId : CapId,
        s.kernel.revocation.caps.get? capId ≠ none ∧
        s' = { s with kernel := { s.kernel with
          revocation := s.kernel.revocation.revoke_transitive capId } } ∧
        hr = { newCaps := [], newMsgs := [] }
  -- MEMORY OPERATIONS (modify ghost state only)
  | .mem_alloc =>
      ∃ size : Nat,
        s' = s.apply_alloc hc.caller size ∧
        hr = { newCaps := [], newMsgs := [] }
  | .mem_free =>
      -- PRECONDITIONS:
      --   1. addr is live (allocated and not freed)
      --   2. No valid capabilities target this address (temporal safety)
      ∃ addr : MemAddr,
        MetaState.is_live s.ghost addr ∧
        (∀ k c, s.kernel.revocation.caps.get? k = some c → c.valid = true → c.target ≠ addr) ∧
        s' = s.apply_free addr ∧
        hr = { newCaps := [], newMsgs := [] }
  -- IPC OPERATIONS
  -- Note: Direct mailbox modification happens at kernel level, not here.
  -- Host call only validates and queues; kernel delivers asynchronously.
  | .ipc_send =>
      -- Validate message and return it via hr.newMsgs
      -- Actual delivery to dst.mailbox is kernel's job (preserves frame)
      ∃ msg : Message,
        msg.src = hc.caller ∧
        (s.actors msg.dst).mailbox.length < (s.actors msg.dst).capacity ∧
        s' = s ∧  -- No state change; message returned for kernel to deliver
        hr = { newCaps := [], newMsgs := [msg] }
  | .ipc_receive =>
      -- Modify only caller's actor state
      if (s.actors hc.caller).mailbox.isEmpty then
        let newActor := (s.actors hc.caller).set_blocked hc.caller
        s' = { s with actors := Function.update s.actors hc.caller newActor } ∧
        hr = { newCaps := [], newMsgs := [] }
      else
        let (newActor, _) := (s.actors hc.caller).consume
        s' = { s with actors := Function.update s.actors hc.caller newActor } ∧
        hr = { newCaps := [], newMsgs := [] }
  -- RESOURCE OPERATIONS
  | .resource_create => s' = s ∧ hr = { newCaps := [], newMsgs := [] }
  | .resource_access => s' = s ∧ hr = { newCaps := [], newMsgs := [] }
  -- WORKFLOW OPERATIONS
  | .workflow_start => s' = s ∧ hr = { newCaps := [], newMsgs := [] }
  | .workflow_step => s' = s ∧ hr = { newCaps := [], newMsgs := [] }
  -- DECLASSIFICATION (special: may modify security level)
  | .declassify =>
      ∃ newLevel : SecurityLevel,
        newLevel ≤ (s.plugins hc.caller).level ∧
        let oldPlugin := s.plugins hc.caller
        let newPlugin : PluginState := { oldPlugin with level := newLevel }
        s' = { s with plugins := Function.update s.plugins hc.caller newPlugin } ∧
        hr = { newCaps := [], newMsgs := [] }

/-! =========== EFFECTFUL CLASSIFICATION =========== -/

/-- All host calls are effectful (cross trust boundary) -/
def is_effectful_host_call : HostFunctionId → Bool := fun _ => true

/-- Declassify is special (affects security level) -/
def is_declassify (hf : HostFunctionId) : Bool :=
  hf = .declassify

/-! =========== HOST CALL FRAME STRUCTURE =========== -/

/--
**Host Call Frame Properties**

Named structure for host call frame properties. Using a structure instead of
nested tuples makes proofs more maintainable - field reordering won't break proofs.
-/
structure HostCallFrame (hc : HostCall) (s s' : State) : Prop where
  /-- Other plugins unchanged -/
  plugins_frame : ∀ other, other ≠ hc.caller → s'.plugins other = s.plugins other
  /-- Actors outside caller unchanged -/
  actors_frame : ∀ aid, aid ≠ hc.caller → s'.actors aid = s.actors aid
  /-- Workflows unchanged -/
  workflows_unchanged : s'.workflows = s.workflows
  /-- Resources unchanged -/
  resources_unchanged : s'.resources = s.resources
  /-- Caller's level preserved (except declassify) -/
  caller_level_preserved : hc.function ≠ .declassify → (s'.plugins hc.caller).level = (s.plugins hc.caller).level
  /-- Kernel hmacKey unchanged (security-critical, never modified by host calls) -/
  hmacKey_unchanged : s'.kernel.hmacKey = s.kernel.hmacKey
  /-- Kernel policy unchanged (configuration, not modified by host calls) -/
  policy_unchanged : s'.kernel.policy = s.kernel.policy
  /-- Time unchanged (only time_tick increments time) -/
  time_unchanged : s'.time = s.time

/-! =========== FRAME THEOREMS (NOW PROVABLE!) =========== -/

/--
**THEOREM (was AXIOM): Host Call Comprehensive Frame**

Now PROVABLE from the constructive definition of KernelExecHost.
Each case explicitly specifies state changes, making frame properties derivable.
-/
theorem host_call_comprehensive_frame :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' → HostCallFrame hc s s' := by
  intro hc a auth hr s s' hexec
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- Case: cap_invoke (s' = s)
  · obtain ⟨_, _, cap, _, _, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: cap_delegate (modifies kernel.revocation only)
  · obtain ⟨_, _, parent, delegatee, newRights, newId, _, _, _, _, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: cap_accept (modifies kernel.revocation and plugins caller)
  · obtain ⟨capId, cap, _, _, _, _, _, _, h_eq, _⟩ := hexec
    constructor
    · intro other h_ne; simp only [h_eq]; exact Function.update_of_ne h_ne _ _
    · intro aid _; simp [h_eq]
    · simp [h_eq]
    · simp [h_eq]
    · intro _; simp [h_eq]
    · simp [h_eq]
    · simp [h_eq]
    · simp [h_eq]
  -- Case: cap_revoke (modifies kernel.revocation only)
  · obtain ⟨_, _, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: mem_alloc (modifies ghost only)
  · obtain ⟨_, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq, State.apply_alloc]
  -- Case: mem_free (modifies ghost only)
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq, State.apply_free]
  -- Case: ipc_send (s' = s, message returned in hr)
  · obtain ⟨msg, _, _, h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: ipc_receive (modifies actors caller only)
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      constructor
      · intro other _; simp [h_eq]
      · intro aid h_ne; simp only [h_eq]; exact Function.update_of_ne h_ne _ _
      · simp [h_eq]
      · simp [h_eq]
      · intro _; simp [h_eq]
      · simp [h_eq]
      · simp [h_eq]
      · simp [h_eq]
    · obtain ⟨h_eq, _⟩ := hexec
      constructor
      · intro other _; simp [h_eq]
      · intro aid h_ne; simp only [h_eq]; exact Function.update_of_ne h_ne _ _
      · simp [h_eq]
      · simp [h_eq]
      · intro _; simp [h_eq]
      · simp [h_eq]
      · simp [h_eq]
      · simp [h_eq]
  -- Case: resource_create (s' = s)
  · obtain ⟨h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: resource_access (s' = s)
  · obtain ⟨h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: workflow_start (s' = s)
  · obtain ⟨h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: workflow_step (s' = s)
  · obtain ⟨h_eq, _⟩ := hexec
    constructor <;> simp [h_eq]
  -- Case: declassify (modifies plugins caller level)
  · obtain ⟨newLevel, _, h_eq, _⟩ := hexec
    constructor
    · intro other h_ne; simp only [h_eq]; exact Function.update_of_ne h_ne _ _
    · intro aid _; simp [h_eq]
    · simp [h_eq]
    · simp [h_eq]
    · intro h_not_decl; exact absurd hfn h_not_decl
    · simp [h_eq]
    · simp [h_eq]
    · simp [h_eq]

/--
**THEOREM (was AXIOM): Non-Capability Host Call Kernel Frame**

For host calls that are NOT capability operations, the full kernel state is unchanged.
-/
theorem host_call_non_cap_kernel_unchanged :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      hc.function ≠ .cap_invoke →
      hc.function ≠ .cap_delegate →
      hc.function ≠ .cap_accept →
      hc.function ≠ .cap_revoke →
      s'.kernel = s.kernel := by
  intro hc a auth hr s s' hexec h1 h2 h3 h4
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- cap_invoke: contradiction
  · simp [hfn] at h1
  -- cap_delegate: contradiction
  · simp [hfn] at h2
  -- cap_accept: contradiction
  · simp [hfn] at h3
  -- cap_revoke: contradiction
  · simp [hfn] at h4
  -- mem_alloc: ghost only
  · obtain ⟨_, h_eq, _⟩ := hexec; simp [h_eq, State.apply_alloc]
  -- mem_free: ghost only
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; simp [h_eq, State.apply_free]
  -- ipc_send: state unchanged
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; simp [h_eq]
  -- ipc_receive: actors only
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
    · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
  -- resource_create: state unchanged
  · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
  -- resource_access: state unchanged
  · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
  -- workflow_start: state unchanged
  · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
  -- workflow_step: state unchanged
  · obtain ⟨h_eq, _⟩ := hexec; simp [h_eq]
  -- declassify: plugins only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; simp [h_eq]

/--
**THEOREM (was AXIOM): Capability Integrity Preservation**

Host calls preserve capability integrity: all capabilities have valid seals.
-/
theorem host_call_preserves_cap_integrity :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      (∀ capId cap, s.kernel.revocation.caps.get? capId = some cap →
        Capability.verify_seal s.kernel.hmacKey cap) →
      (∀ capId cap, s'.kernel.revocation.caps.get? capId = some cap →
        Capability.verify_seal s'.kernel.hmacKey cap) := by
  intro hc a auth hr s s' hexec h_pre capId cap h_cap_in_s'
  -- hmacKey is preserved by all host calls (from frame)
  have h_key := (host_call_comprehensive_frame hc a auth hr s s' hexec).hmacKey_unchanged
  rw [h_key]
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec
    subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- cap_delegate: new cap inserted with valid seal
  · obtain ⟨_, _, parent, delegatee, newRights, newId, _, _, _, _, h_eq, _⟩ := hexec
    rw [h_eq] at h_cap_in_s'
    unfold RevocationState.insert at h_cap_in_s'
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_cap_in_s'
    let newCap := create_delegated_cap s parent delegatee newRights newId
    split at h_cap_in_s'
    · -- New cap case: capId matches inserted key
      rename_i h_beq
      cases h_cap_in_s'
      unfold Capability.verify_seal create_delegated_cap Capability.payload
      simp only
      exact seal_verify_roundtrip s.kernel.hmacKey _
    · -- Existing cap case: cap was in original table
      rename_i h_not_beq
      exact h_pre capId cap h_cap_in_s'
  -- cap_accept: modifies valid field but signature unchanged
  · obtain ⟨acceptId, acceptCap, h_get, _, _, _, _, _, h_eq, _⟩ := hexec
    rw [h_eq] at h_cap_in_s'
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_cap_in_s'
    split at h_cap_in_s'
    · -- Accepted cap case: same cap but valid=true
      rename_i h_beq
      cases h_cap_in_s'
      -- The accepted cap has same signature as original
      have h_pre_verify : Capability.verify_seal s.kernel.hmacKey acceptCap :=
        h_pre acceptId acceptCap h_get
      -- Build payload equality (valid not in payload)
      have h_payload : { acceptCap with valid := true }.payload = acceptCap.payload := rfl
      have h_sig : { acceptCap with valid := true }.signature = acceptCap.signature := rfl
      exact Capability.verify_seal_transfer s.kernel.hmacKey h_sig h_payload h_pre_verify
    · -- Other cap case: unchanged
      exact h_pre capId cap h_cap_in_s'
  -- cap_revoke: modifies valid field but signature unchanged
  -- revoke_transitive only sets valid=false, preserving signature
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    rw [h_eq] at h_cap_in_s'
    -- Use structure preservation to get old cap with same signature/payload fields
    obtain ⟨capOld, h_capOld_get, h_id, h_rights, h_target, h_parent, h_epoch, h_holder, h_sig⟩ :=
      RevocationState.revoke_transitive_preserves_structure
        s.kernel.revocation revokeId capId cap h_cap_in_s'
    -- Get seal validity for old cap from precondition
    have h_pre_verify : Capability.verify_seal s.kernel.hmacKey capOld :=
      h_pre capId capOld h_capOld_get
    -- Build payload equality from preserved fields (valid not in payload)
    have h_payload : cap.payload = capOld.payload :=
      Capability.payload_eq_of_fields_eq h_holder h_target h_rights h_parent h_epoch
    -- Transfer verify_seal from capOld to cap
    exact Capability.verify_seal_transfer s.kernel.hmacKey h_sig h_payload h_pre_verify
  -- mem_alloc: kernel unchanged
  · obtain ⟨_, h_eq, _⟩ := hexec
    rw [h_eq] at h_cap_in_s'; unfold State.apply_alloc at h_cap_in_s'
    exact h_pre capId cap h_cap_in_s'
  -- mem_free: kernel unchanged
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    rw [h_eq] at h_cap_in_s'; unfold State.apply_free at h_cap_in_s'
    exact h_pre capId cap h_cap_in_s'
  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- ipc_receive: actors only
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq] at h_cap_in_s'; exact h_pre capId cap h_cap_in_s'
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq] at h_cap_in_s'; exact h_pre capId cap h_cap_in_s'
  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_pre capId cap h_cap_in_s'
  -- declassify: plugins only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; rw [h_eq] at h_cap_in_s'; exact h_pre capId cap h_cap_in_s'

/--
**THEOREM: Capability Confinement Preservation (Strong Version)**

Host calls preserve capability confinement given full AuthInv.
Uses KeyMatchesId and held_consistent from AuthInv to complete the proof.
-/
theorem host_call_preserves_cap_confined_strong
    (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s' : State)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_auth : Contracts.Auth.AuthInv s)
    (h_wf : Confinement.well_formed_table s.kernel.revocation.caps) :
    Confinement.well_formed_table s'.kernel.revocation.caps := by
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- cap_delegate: new cap with rights ⊆ parent.rights (via intersection)
  -- Core insight: create_delegated_cap uses newRights ∩ parent.rights
  · obtain ⟨parentId, _, parent, _delegatee, newRights, newId, h_parent_in_kernel, _h_valid, h_fresh, h_lt, h_eq, _⟩ := hexec
    rw [h_eq]
    intro c pid h_get h_parent
    unfold RevocationState.insert at h_get
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
    let newCap := create_delegated_cap s parent _delegatee newRights newId
    -- KeyMatchesId: parent.id = parentId (since caps.get? parentId = some parent)
    have h_id_eq : parent.id = parentId := h_auth.caps_wf.keys_match h_parent_in_kernel
    split at h_get
    · -- New cap case: c = newCap
      rename_i h_beq
      cases h_get
      -- newCap.parent = some parent.id, so pid = parent.id
      unfold create_delegated_cap at h_parent
      simp only at h_parent
      cases h_parent
      -- Use parent directly since we have h_parent_in_kernel: caps.get? parent.id = some parent
      refine ⟨parent, ?_, ?_⟩
      · -- parent is at parent.id in new table (insert at newId ≠ parent.id)
        unfold RevocationState.insert create_delegated_cap
        have h_ne : (newId == parent.id) = false := by
          rw [beq_eq_false_iff_ne, h_id_eq]
          exact Nat.ne_of_gt h_lt
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne]
        rw [h_id_eq]; exact h_parent_in_kernel
      · -- valid_delegation: newCap.parent = some parent.id, rights ⊆ parent.rights
        unfold Confinement.valid_delegation create_delegated_cap
        exact ⟨rfl, Finset.inter_subset_right, rfl⟩
    · -- Existing cap case
      rename_i h_not_beq
      have h_get_old : s.kernel.revocation.caps.get? c.id = some c := h_get
      obtain ⟨p, h_p_get, h_vdel⟩ := h_wf c pid h_get_old h_parent
      refine ⟨p, ?_, h_vdel⟩
      unfold RevocationState.insert create_delegated_cap
      have h_ne : (newId == pid) = false := by
        rw [beq_eq_false_iff_ne]
        intro h_eq_pid
        rw [h_eq_pid] at h_fresh
        rw [h_fresh] at h_p_get
        cases h_p_get  -- some p = none is absurd
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne]
      exact h_p_get
  -- cap_accept: only changes valid field, parent/rights/target preserved
  · obtain ⟨acceptId, acceptCap, h_get, _, _, _, _, _, h_eq, _⟩ := hexec
    rw [h_eq]
    intro c pid h_get_new h_parent
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
    -- Get key equality: acceptCap.id = acceptId
    have h_id_eq : acceptCap.id = acceptId := h_auth.caps_wf.keys_match h_get
    -- Rewrite h_get to use acceptCap.id
    have h_get' : s.kernel.revocation.caps.get? acceptCap.id = some acceptCap := by
      rw [h_id_eq]; exact h_get
    split at h_get_new
    · -- Accepted cap case: valid changed but structure preserved
      rename_i h_beq
      cases h_get_new
      simp only at h_parent
      obtain ⟨p, h_p_get, h_vdel⟩ := h_wf acceptCap pid h_get' h_parent
      refine ⟨p, ?_, ?_⟩
      · -- Parent is in new table (parent was already there, and acceptId ≠ pid by ParentLt)
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        have h_ne : (acceptId == pid) = false := by
          rw [beq_eq_false_iff_ne]
          intro h_eq_pid
          have h_plt : pid < acceptCap.id := h_auth.caps_wf.parent_lt h_get' h_parent
          rw [h_id_eq] at h_plt
          rw [h_eq_pid] at h_plt
          exact Nat.lt_irrefl pid h_plt
        simp only [h_ne]
        exact h_p_get
      · exact h_vdel
    · -- Other cap case: c is from original table (not the accepted cap)
      obtain ⟨p, h_p_get, h_vdel⟩ := h_wf c pid h_get_new h_parent
      by_cases h_eq_pid : acceptId = pid
      · -- Parent is the accepted cap (pid = acceptId)
        -- In the new table, parent is {acceptCap with valid := true}
        have h_get_pid : s.kernel.revocation.caps.get? pid = some acceptCap := by
          rw [← h_eq_pid]; exact h_get
        rw [h_get_pid] at h_p_get
        cases h_p_get  -- p = acceptCap
        refine ⟨{ acceptCap with valid := true }, ?_, ?_⟩
        · -- Parent in new table at pid = acceptId
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_beq : (acceptId == pid) = true := beq_iff_eq.mpr h_eq_pid
          simp only [h_beq, ite_true]
        · -- valid_delegation preserved: rights and target unchanged
          exact h_vdel
      · -- Parent is NOT the accepted cap (pid ≠ acceptId)
        refine ⟨p, ?_, h_vdel⟩
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        have h_ne : (acceptId == pid) = false := beq_eq_false_iff_ne.mpr h_eq_pid
        simp only [h_ne]
        exact h_p_get
  -- cap_revoke: valid field changes, parent/rights/target preserved
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    rw [h_eq]
    exact Confinement.revoke_transitive_preserves_well_formed_table
      s.kernel.revocation revokeId h_wf
  -- mem_alloc: kernel unchanged
  · obtain ⟨_, h_eq, _⟩ := hexec
    rw [h_eq]; unfold State.apply_alloc; exact h_wf
  -- mem_free: kernel unchanged
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    rw [h_eq]; unfold State.apply_free; exact h_wf
  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- ipc_receive: actors only
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact h_wf
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact h_wf
  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact h_wf
  -- declassify: plugins only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; rw [h_eq]; exact h_wf

/--
**THEOREM (was AXIOM): Capability Confinement Preservation**

Host calls preserve capability confinement: delegated caps have rights ⊆ parent.
Uses table_invariant (well_keyed ∧ well_formed) for complete proof of cap_revoke.
-/
theorem host_call_preserves_cap_confined :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      Confinement.table_invariant s.kernel.revocation.caps →
      Confinement.table_invariant s'.kernel.revocation.caps := by
  intro hc a auth hr s s' hexec ⟨h_keyed, h_wf⟩
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- cap_delegate: uses freshness, consistency, and parent ordering preconditions
  · obtain ⟨parentId, _, parent, _delegatee, newRights, newId, h_parent_in_kernel, _h_valid, h_fresh, h_lt, h_eq, _⟩ := hexec
    rw [h_eq]
    -- KeyMatchesId: parent.id = parentId (from well_keyed_table precondition)
    have h_id_eq : parent.id = parentId := h_keyed parentId parent h_parent_in_kernel
    refine ⟨?_, ?_⟩
    · -- well_keyed_table
      intro k c h_get
      unfold RevocationState.insert at h_get
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
      split at h_get
      · -- New cap case: k = newId, c = newCap
        rename_i h_beq
        cases h_get
        -- h_beq : ((create_delegated_cap ...).id == k) = true
        -- Goal: (create_delegated_cap ...).id = k
        unfold create_delegated_cap at h_beq ⊢
        simp only at h_beq
        exact eq_of_beq h_beq
      · -- Existing cap case
        exact h_keyed k c h_get
    · -- well_formed_table
      intro c pid h_get h_parent
      unfold RevocationState.insert at h_get
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get
      let newCap := create_delegated_cap s parent _delegatee newRights newId
      split at h_get
      · -- New cap case
        rename_i h_beq
        cases h_get
        unfold create_delegated_cap at h_parent
        simp only at h_parent
        cases h_parent
        refine ⟨parent, ?_, ?_⟩
        · unfold RevocationState.insert create_delegated_cap
          have h_ne : (newId == parent.id) = false := by
            rw [beq_eq_false_iff_ne, h_id_eq]
            exact Nat.ne_of_gt h_lt
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne]
          rw [h_id_eq]; exact h_parent_in_kernel
        · unfold Confinement.valid_delegation create_delegated_cap
          exact ⟨rfl, Finset.inter_subset_right, rfl⟩
      · -- Existing cap case
        have h_get_old : s.kernel.revocation.caps.get? c.id = some c := h_get
        obtain ⟨p, h_p_get, h_vdel⟩ := h_wf c pid h_get_old h_parent
        refine ⟨p, ?_, h_vdel⟩
        unfold RevocationState.insert create_delegated_cap
        have h_ne : (newId == pid) = false := by
          rw [beq_eq_false_iff_ne]
          intro h_eq_pid
          rw [h_eq_pid] at h_fresh
          rw [h_fresh] at h_p_get
          cases h_p_get  -- some p = none is absurd
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h_ne]
        exact h_p_get
  -- cap_accept: insert with same key, only valid field changes
  · obtain ⟨acceptId, acceptCap, h_get, _, _, _, _, _, h_eq, _⟩ := hexec
    rw [h_eq]
    -- Key equality: acceptCap.id = acceptId
    have h_id_eq : acceptCap.id = acceptId := h_keyed acceptId acceptCap h_get
    have h_get' : s.kernel.revocation.caps.get? acceptCap.id = some acceptCap := by
      rw [h_id_eq]; exact h_get
    refine ⟨?_, ?_⟩
    · -- well_keyed_table preserved
      intro k c h_get_new
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
      split at h_get_new
      · -- Accepted cap case
        rename_i h_beq
        cases h_get_new
        -- The accepted cap has same id as original: need acceptCap.id = k
        -- h_beq : (acceptId == k) = true, and h_id_eq : acceptCap.id = acceptId
        have h_k_eq : acceptId = k := eq_of_beq h_beq
        simp only
        rw [h_id_eq, h_k_eq]
      · -- Other cap unchanged
        exact h_keyed k c h_get_new
    · -- well_formed_table preserved
      intro c pid h_get_new h_parent
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h_get_new
      split at h_get_new
      · -- Accepted cap case: c = {acceptCap with valid := true}
        rename_i h_beq
        cases h_get_new
        simp only at h_parent
        obtain ⟨p, h_p_get, h_vdel⟩ := h_wf acceptCap pid h_get' h_parent
        by_cases h_eq_pid : acceptId = pid
        · -- Parent is the accepted cap itself (self-referential or updated parent)
          have h_get_pid : s.kernel.revocation.caps.get? pid = some acceptCap := by
            rw [← h_eq_pid]; exact h_get
          rw [h_get_pid] at h_p_get
          cases h_p_get  -- p = acceptCap
          refine ⟨{ acceptCap with valid := true }, ?_, h_vdel⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_beq' : (acceptId == pid) = true := beq_iff_eq.mpr h_eq_pid
          simp only [h_beq', ite_true]
        · -- Parent is different from accepted cap
          refine ⟨p, ?_, h_vdel⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_ne : (acceptId == pid) = false := beq_eq_false_iff_ne.mpr h_eq_pid
          simp only [h_ne]
          exact h_p_get
      · -- Other cap unchanged
        obtain ⟨p, h_p_get, h_vdel⟩ := h_wf c pid h_get_new h_parent
        by_cases h_eq_pid : acceptId = pid
        · -- Parent is the accepted cap
          have h_get_pid : s.kernel.revocation.caps.get? pid = some acceptCap := by
            rw [← h_eq_pid]; exact h_get
          rw [h_get_pid] at h_p_get
          cases h_p_get  -- p = acceptCap
          refine ⟨{ acceptCap with valid := true }, ?_, h_vdel⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_beq' : (acceptId == pid) = true := beq_iff_eq.mpr h_eq_pid
          simp only [h_beq', ite_true]
        · -- Parent is different
          refine ⟨p, ?_, h_vdel⟩
          simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          have h_ne : (acceptId == pid) = false := beq_eq_false_iff_ne.mpr h_eq_pid
          simp only [h_ne]
          exact h_p_get
  -- cap_revoke: Uses revoke_transitive which preserves table_invariant
  · obtain ⟨revokeId, _, h_eq, _⟩ := hexec
    rw [h_eq]
    refine ⟨?_, ?_⟩
    · intro k c h_get
      exact RevocationState.revoke_transitive_preserves_keys_match
        s.kernel.revocation revokeId (fun h => h_keyed _ _ h) h_get
    · exact Confinement.revoke_transitive_preserves_well_formed_table
        s.kernel.revocation revokeId h_wf
  -- mem_alloc: kernel unchanged
  · obtain ⟨_, h_eq, _⟩ := hexec
    rw [h_eq]; unfold State.apply_alloc; exact ⟨h_keyed, h_wf⟩
  -- mem_free: kernel unchanged
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    rw [h_eq]; unfold State.apply_free; exact ⟨h_keyed, h_wf⟩
  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- ipc_receive: actors only
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_keyed, h_wf⟩
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_keyed, h_wf⟩
  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_keyed, h_wf⟩
  -- declassify: plugins only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_keyed, h_wf⟩

/-! =========== DERIVED HOST CALL THEOREMS =========== -/

/-- Host Call Plugin Frame -/
theorem host_call_plugin_frame (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    ∀ other, other ≠ hc.caller → s'.plugins other = s.plugins other :=
  (host_call_comprehensive_frame hc a auth hr s s' h).plugins_frame

/-- Host Call Actor Frame -/
theorem host_call_actor_frame (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    ∀ aid, aid ≠ hc.caller → s'.actors aid = s.actors aid :=
  (host_call_comprehensive_frame hc a auth hr s s' h).actors_frame

/-- Host Call Workflows Unchanged -/
theorem host_call_workflows_unchanged (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    s'.workflows = s.workflows :=
  (host_call_comprehensive_frame hc a auth hr s s' h).workflows_unchanged

/-- Host Call Resources Unchanged -/
theorem host_call_resources_unchanged (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    s'.resources = s.resources :=
  (host_call_comprehensive_frame hc a auth hr s s' h).resources_unchanged

/-- Host Call Resource Level Frame (derived from resources_unchanged) -/
theorem host_call_resource_level_frame (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    ∀ rid, (s.resources rid).level = (s'.resources rid).level := by
  intro rid
  have hres := (host_call_comprehensive_frame hc a auth hr s s' h).resources_unchanged
  simp [hres]

/-- Host Call Resource Content Frame (derived from resources_unchanged) -/
theorem host_call_resource_content_frame (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    ∀ rid, (s.resources rid).level < (s.plugins hc.caller).level →
      s'.resources rid = s.resources rid := by
  intro rid _
  have hres := (host_call_comprehensive_frame hc a auth hr s s' h).resources_unchanged
  simp [hres]

/-- Host Call Level Preserved -/
theorem host_call_caller_level_preserved (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h_not_declassify : hc.function ≠ .declassify)
    (h : KernelExecHost hc a auth hr s s') :
    (s'.plugins hc.caller).level = (s.plugins hc.caller).level :=
  (host_call_comprehensive_frame hc a auth hr s s' h).caller_level_preserved h_not_declassify

/-- Host Call hmacKey Unchanged -/
theorem host_call_hmacKey_unchanged (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    s'.kernel.hmacKey = s.kernel.hmacKey :=
  (host_call_comprehensive_frame hc a auth hr s s' h).hmacKey_unchanged

/-- Host Call Policy Unchanged -/
theorem host_call_policy_unchanged (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    s'.kernel.policy = s.kernel.policy :=
  (host_call_comprehensive_frame hc a auth hr s s' h).policy_unchanged

/-- Host Call Time Unchanged -/
theorem host_call_time_unchanged (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (s s' : State)
    (h : KernelExecHost hc a auth hr s s') :
    s'.time = s.time :=
  (host_call_comprehensive_frame hc a auth hr s s' h).time_unchanged

/-! =========== HOST CALL MEMORY BOUNDS PRESERVATION =========== -/

/--
**THEOREM (was AXIOM): Host Call Memory Bounds Preservation**

Host calls preserve the WASM memory bounds invariant.
If caller's memory was bounded before, it remains bounded after.
-/
theorem host_call_respects_memory_bounds :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      -- Precondition: memory bounded in s
      (∀ addr, (s.plugins hc.caller).memory.bytes.contains addr →
        addr < (s.plugins hc.caller).memory.bounds) →
      -- Postcondition 1: memory bounded in s'
      (∀ addr, (s'.plugins hc.caller).memory.bytes.contains addr →
        addr < (s'.plugins hc.caller).memory.bounds) ∧
      -- Postcondition 2: bounds unchanged
      (s'.plugins hc.caller).memory.bounds = (s.plugins hc.caller).memory.bounds := by
  intro hc a auth hr s s' hexec h_pre
  -- Host calls don't modify caller's plugin memory (that's plugin_internal's job)
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- For each case, plugins unchanged means memory unchanged
  -- cap_invoke
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- cap_delegate
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_pre, rfl⟩
  -- cap_accept: modifies plugins caller.heldCaps but memory unchanged
  · obtain ⟨_, _, _, _, _, _, _, _, h_eq, _⟩ := hexec
    rw [h_eq]
    constructor
    · simp only [Function.update_self]; exact h_pre
    · simp only [Function.update_self, PluginState.grant_cap_memory_bounds]
  -- cap_revoke
  · obtain ⟨_, _, h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_pre, rfl⟩
  -- mem_alloc
  · obtain ⟨_, h_eq, _⟩ := hexec
    rw [h_eq]
    unfold State.apply_alloc
    exact ⟨h_pre, rfl⟩
  -- mem_free
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    rw [h_eq]
    unfold State.apply_free
    exact ⟨h_pre, rfl⟩
  -- ipc_send
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- ipc_receive
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_pre, rfl⟩
    · obtain ⟨h_eq, _⟩ := hexec; rw [h_eq]; exact ⟨h_pre, rfl⟩
  -- resource_create
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- resource_access
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- workflow_start
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- workflow_step
  · obtain ⟨h_eq, _⟩ := hexec; subst h_eq; exact ⟨h_pre, rfl⟩
  -- declassify
  · obtain ⟨_, _, h_eq, _⟩ := hexec
    rw [h_eq]
    simp only [Function.update_self]
    -- After update_self, plugins hc.caller = { oldPlugin with level := newLevel }
    -- Memory is unchanged, so h_pre applies
    constructor
    · intro addr h_contains; exact h_pre addr h_contains
    · -- memory.bounds unchanged when only level changes
      simp only []

/-! =========== HOST CALL ACTOR MAILBOX CAPACITY =========== -/

/--
**THEOREM (was AXIOM): Host Call Mailbox Capacity Preservation**

Host calls (including ipc_send) respect actor mailbox capacity.
-/
theorem host_call_respects_mailbox_capacity :
    ∀ (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State),
      KernelExecHost hc a auth hr s s' →
      (∀ aid : ActorId,
        (s.actors aid).mailbox.length ≤ (s.actors aid).capacity →
        (s'.actors aid).mailbox.length ≤ (s'.actors aid).capacity) := by
  intro hc a auth hr s s' hexec aid h_cap
  unfold KernelExecHost at hexec
  cases hfn : hc.function <;> simp only [hfn] at hexec
  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- cap_delegate: kernel only
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- cap_accept: plugins modified but actors unchanged
  · obtain ⟨_, _, _, _, _, _, _, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- cap_revoke: kernel only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- mem_alloc: ghost only
  · obtain ⟨_, h_eq, _⟩ := hexec; simp only [h_eq, State.apply_alloc]; exact h_cap
  -- mem_free: ghost only
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; simp only [h_eq, State.apply_free]; exact h_cap
  -- ipc_send: s' = s (message in hr, not delivered)
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- ipc_receive: only modifies caller actor (blockedOn or consume)
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      simp only [h_eq]
      by_cases h_aid : aid = hc.caller
      · -- set_blocked only changes blockedOn, not mailbox
        subst h_aid
        simp only [Function.update_self]
        -- set_blocked preserves mailbox length and capacity
        have h_mb := ActorRuntime.set_blocked_preserves_mailbox (s.actors hc.caller) hc.caller
        have h_cap_eq := ActorRuntime.set_blocked_preserves_capacity (s.actors hc.caller) hc.caller
        simp only [h_mb, h_cap_eq]
        exact h_cap
      · simp only [Function.update_of_ne h_aid]; exact h_cap
    · obtain ⟨h_eq, _⟩ := hexec
      simp only [h_eq]
      by_cases h_aid : aid = hc.caller
      · -- consume removes from mailbox, decreasing length
        subst h_aid
        simp only [Function.update_self]
        -- consume preserves capacity and decreases/maintains mailbox length
        have h_cap_eq := ActorRuntime.consume_preserves_capacity (s.actors hc.caller)
        simp only [h_cap_eq]
        -- consume can only decrease mailbox length
        have h_decr_or_same : ((s.actors hc.caller).consume.1).mailbox.length ≤
                              (s.actors hc.caller).mailbox.length := by
          unfold ActorRuntime.consume
          cases hm : (s.actors hc.caller).mailbox with
          | nil => simp only [hm]; omega
          | cons _ rest => simp only [List.length_cons]; omega
        omega
      · simp only [Function.update_of_ne h_aid]; exact h_cap
  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap
  -- declassify: plugins only
  · obtain ⟨_, _, h_eq, _⟩ := hexec; simp only [h_eq]; exact h_cap

/-! =========== HOST CALL WORKFLOW PROGRESS PRESERVATION =========== -/

/--
**Theorem: Host Call Workflow Progress Preservation**

Host calls preserve workflow progress possibility.
Derived from workflows_unchanged and time_unchanged in HostCallFrame.
-/
theorem host_call_respects_workflow_progress
    (hc : HostCall) (a : Action) (auth : Authorized s a) (hr : HostResult) (s s' : State)
    (hexec : KernelExecHost hc a auth hr s s') :
    (∀ wid : WorkflowId,
      (s'.workflows wid).status = .running →
      ((s.workflows wid).status = .running →
        (s.time < (s.workflows wid).timeout_at ∨
         (s.workflows wid).pending_count > 0 ∨
         (s.workflows wid).active_count > 0)) →
      (s'.time < (s'.workflows wid).timeout_at ∨
       (s'.workflows wid).pending_count > 0 ∨
       (s'.workflows wid).active_count > 0)) := by
  intro wid h_running' h_progress
  -- workflows and time are unchanged by host calls
  have h_wf := host_call_workflows_unchanged hc a auth hr s s' hexec
  have h_time := host_call_time_unchanged hc a auth hr s s' hexec
  -- Convert h_running' from s' to s using workflow frame
  have h_running_s : (s.workflows wid).status = .running := by
    rw [← h_wf]; exact h_running'
  -- Apply h_progress to get result in terms of s
  have h_result := h_progress h_running_s
  -- Rewrite goal from s' to s using frames
  simp only [h_wf, h_time]
  exact h_result

end Lion
