/-
Lion/Contracts/AuthContract.lean
================================

Authorization System Invariants for Rust-Lean Refinement.

These invariants capture properties that must hold for authorization refinement
to succeed. They are bundled into AuthInv which is preserved by all transitions.

INVARIANTS:
1. CapTable.KeyMatchesId: HashMap keys match stored cap.id
2. CapTable.ParentLt: Parent IDs strictly less than child (termination)
3. CapTable.ValidParentPresent: Valid caps with parents have valid parents
4. policy_complete: Policy permits for matching valid caps
5. KernelPluginConsistency: Valid caps are in holder's heldCaps
6. TemporalSafetyInvariant: Valid caps have live targets
7. TimeCoherent: kernel.now = State.time (clock synchronization)

These were identified by deep analysis as the minimal set needed
to make the original authorization axioms provable as theorems.
-/

import Lion.State.State
import Lion.State.Kernel
import Lion.Core.Policy
import Lion.Step.Authorization

namespace Lion.Contracts.Auth

open Lion

/-! ## CapTable Invariants

These invariants ensure the capability table is well-formed and enables
proving IsValid from local validity.
-/

/-- HashMap well-formedness: the key equals the stored capability's id. -/
def CapTable.KeyMatchesId (caps : CapTable) : Prop :=
  ∀ {id : CapId} {cap : Capability},
    caps.get? id = some cap → cap.id = id

/-- Parent pointers strictly decrease by CapId (enables termination of parent chain traversal).

JUSTIFICATION: Capabilities are issued with monotonically increasing IDs.
A derived capability's parent was issued earlier, so parent.id < child.id.
-/
def CapTable.ParentLt (caps : CapTable) : Prop :=
  ∀ {id : CapId} {cap : Capability} {p : CapId},
    caps.get? id = some cap →
    cap.parent = some p →
    p < id

/-- If a capability is marked valid and has a parent, the parent exists and is also marked valid.

JUSTIFICATION: Revocation is transitive - revoking a parent revokes all children.
So if a cap is valid and has a parent, that parent must be valid too.
-/
def CapTable.ValidParentPresent (caps : CapTable) : Prop :=
  ∀ {id : CapId} {cap : Capability} {p : CapId},
    caps.get? id = some cap →
    cap.valid = true →
    cap.parent = some p →
    ∃ pcap : Capability, caps.get? p = some pcap ∧ pcap.valid = true

/-- Well-formedness bundle for cap tables. -/
structure CapTable.WellFormed (caps : CapTable) : Prop where
  keys_match : CapTable.KeyMatchesId caps
  parent_lt : CapTable.ParentLt caps
  parent_valid : CapTable.ValidParentPresent caps

/-! ## System Invariants

These invariants capture consistency between different parts of system state.
-/

/-- Policy completeness: policy permits actions for matching valid capabilities.

JUSTIFICATION: The kernel only issues capabilities for permitted actions.
If a valid capability matches an action, the policy must permit it.
-/
def policy_complete (ps : PolicyState) (caps : CapTable) : Prop :=
  ∀ cap a ctx,
    caps.get? cap.id = some cap →
    cap.valid = true →
    cap.holder = a.subject →
    cap.target = a.target →
    a.rights ⊆ cap.rights →
    policy_check ps a ctx = .permit

/-- Kernel-plugin consistency: held cap IDs exist in the kernel table.

JUSTIFICATION (Handle/State Separation Model):
- Plugins hold CapIds (handles), not full Capability copies
- This invariant ensures referential integrity: handles point to real entries
- The kernel maintains this on cap_accept (adds ID to heldCaps and cap to table)
- Revocation only flips valid=false; handles remain but grant no authority

This is the converse of the old model: we check heldCaps → table, not table → heldCaps.
Validity is checked at USE time, not possession time.
-/
def KernelPluginConsistency (s : State) : Prop :=
  ∀ pid capId,
    capId ∈ (s.plugins pid).heldCaps →
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap

/-- Temporal safety: valid capabilities target live resources.

JUSTIFICATION: When a resource is freed, all capabilities targeting it
are revoked (valid := false). So valid caps always have live targets.
-/
def TemporalSafetyInvariant (s : State) : Prop :=
  ∀ cap_id cap,
    s.kernel.revocation.caps.get? cap_id = some cap →
    cap.valid = true →
    MetaState.is_live s.ghost cap.target

/-- Valid caps are held: The reverse direction of KernelPluginConsistency.

If a capability is in the table AND is valid, then its ID is in the
holder's heldCaps. This follows from the cap lifecycle:
- Caps enter table via cap_delegate (invalid, holder = delegatee)
- Caps become valid only via cap_accept by the holder
- cap_accept adds the capId to the caller's heldCaps
- cap_accept only succeeds if cap.holder = caller

So valid caps are always in their holder's heldCaps.
-/
def ValidCapsHeld (s : State) : Prop :=
  ∀ capId cap,
    s.kernel.revocation.caps.get? capId = some cap →
    s.kernel.revocation.is_valid capId = true →
    capId ∈ (s.plugins cap.holder).heldCaps

/-! ## Authorization Invariant Bundle -/

/-- Complete authorization invariant for system states.

All theorems about authorization derive from this invariant being preserved
across transitions. This is the SINGLE axiom needed for refinement.
-/
structure AuthInv (s : State) : Prop where
  /-- Cap table is well-formed -/
  caps_wf : CapTable.WellFormed s.kernel.revocation.caps
  /-- Policy is complete wrt capabilities -/
  pol_complete : policy_complete s.kernel.policy s.kernel.revocation.caps
  /-- Kernel and plugin caps are consistent (heldCaps → table) -/
  held_consistent : KernelPluginConsistency s
  /-- Valid caps are in holder's heldCaps (table + valid → heldCaps) -/
  valid_caps_held : ValidCapsHeld s
  /-- Temporal safety holds -/
  temporal_safe : TemporalSafetyInvariant s

/-! ## Initial State Proofs -/

/-- Empty cap table is well-formed (vacuously true). -/
theorem empty_caps_wf : CapTable.WellFormed {} where
  keys_match := by intro _ _ h; simp at h
  parent_lt := by intro _ _ _ h _; simp at h
  parent_valid := by intro _ _ _ h _ _; simp at h

/-- Empty cap table satisfies policy_complete (vacuously true). -/
theorem empty_caps_policy_complete (ps : PolicyState) :
    policy_complete ps {} := by
  intro cap _ _ h _ _ _ _
  simp at h

/-- Initial state satisfies KernelPluginConsistency (vacuously if heldCaps empty). -/
theorem initial_kernel_plugin_consistency
    (s : State) (h_empty_held : ∀ pid, (s.plugins pid).heldCaps = ∅) :
    KernelPluginConsistency s := by
  intro pid capId h_in
  simp [h_empty_held pid] at h_in

/-- Initial state satisfies TemporalSafetyInvariant (if no caps). -/
theorem initial_temporal_safety
    (s : State) (h_empty : s.kernel.revocation.caps = {}) :
    TemporalSafetyInvariant s := by
  intro cap_id cap hget _
  simp [h_empty] at hget

/-- Initial state satisfies ValidCapsHeld (vacuously if no caps). -/
theorem initial_valid_caps_held
    (s : State) (h_empty : s.kernel.revocation.caps = {}) :
    ValidCapsHeld s := by
  intro capId cap hget _
  simp [h_empty] at hget

/-! ## Helper Lemmas -/

/-- Extract cap.valid from is_valid check when cap is in table -/
lemma valid_flag_of_is_valid
    (rs : RevocationState) {id : CapId} {cap : Capability}
    (hget : rs.caps.get? id = some cap)
    (hvalid : rs.is_valid id = true) :
    cap.valid = true := by
  unfold RevocationState.is_valid at hvalid
  simp only [hget] at hvalid
  exact hvalid

/-! ## Time Coherence Invariant

The system has two time representations that must be synchronized:
- `State.time`: Global time visible to proofs
- `kernel.now`: Kernel's time counter

These MUST be equal. This is the "clock redundancy" identified in refinement analysis.
-/

/-- Time coherence: kernel time matches global time.

    This invariant ensures the two time representations stay synchronized.
    Violated only by bugs in time_tick implementation.

    RATIONALE: The Lean spec has `State.time` for abstract reasoning and
    `kernel.now` for kernel-level operations. These must be equal.
-/
def TimeCoherent (s : State) : Prop :=
  s.kernel.now = s.time

/-- Initial state is time-coherent if both clocks start at 0 -/
theorem initial_time_coherent
    (s : State) (h_kernel : s.kernel.now = 0) (h_time : s.time = 0) :
    TimeCoherent s := by
  unfold TimeCoherent
  rw [h_kernel, h_time]

/-- Time tick preserves coherence if both clocks increment together -/
theorem time_tick_preserves_coherent
    (s s' : State)
    (h_coh : TimeCoherent s)
    (h_kernel_inc : s'.kernel.now = s.kernel.now + 1)
    (h_time_inc : s'.time = s.time + 1) :
    TimeCoherent s' := by
  unfold TimeCoherent at *
  rw [h_kernel_inc, h_time_inc, h_coh]

/-! ## Bounds Invariants (Overflow Safety)

These invariants ensure values stay within representable ranges for Rust types.
Without these, correspondence breaks when Lean values exceed Rust capacity.
-/

/-- Capability IDs stay within u128 range -/
def CapIdWithinU128 (caps : CapTable) : Prop :=
  ∀ cid cap, caps.get? cid = some cap → cid < 2^128

/-- Plugin IDs stay within u64 range (for active plugins) -/
def PluginIdWithinU64 (s : State) : Prop :=
  ∀ pid, (s.plugins pid).level ≠ .Public → pid < 2^64

/-- Time and epoch values stay within u64 range -/
def TimeWithinU64 (s : State) : Prop :=
  s.time < 2^64 ∧ s.kernel.revocation.epoch < 2^64 ∧ s.kernel.now < 2^64

/-- Complete bounds invariant bundle -/
structure BoundsInv (s : State) : Prop where
  /-- Cap IDs representable as u128 -/
  cap_ids : CapIdWithinU128 s.kernel.revocation.caps
  /-- Active plugin IDs representable as u64 -/
  plugin_ids : PluginIdWithinU64 s
  /-- Time values representable as u64 -/
  time_bounds : TimeWithinU64 s

/-- Initial state satisfies bounds (if starting from 0 with default plugins) -/
theorem initial_bounds_inv
    (s : State)
    (h_empty : s.kernel.revocation.caps = {})
    (h_time : s.time = 0)
    (h_epoch : s.kernel.revocation.epoch = 0)
    (h_now : s.kernel.now = 0)
    (h_plugins : s.plugins = fun _ => default) :  -- NEW: all plugins are default
    BoundsInv s where
  cap_ids := by
    intro cid cap h_get
    simp [h_empty] at h_get
  plugin_ids := by
    intro pid h_active
    -- Default plugin has level = .Public, so h_active is False
    simp only [h_plugins] at h_active
    exact absurd PluginState.default_level h_active
  time_bounds := by
    simp only [TimeWithinU64, h_time, h_epoch, h_now]
    decide

/-! ## System Invariant Bundle

Separates system-level invariants (bounds, time coherence) from
security invariants (AuthInv). Keeps proofs modular.
-/

/-- Complete system invariant bundle.

    These are orthogonal to AuthInv (security) and can be proven separately.
    Recommended: Thread SystemInv through step preservation alongside AuthInv.
-/
structure SystemInv (s : State) : Prop where
  /-- Kernel time = global time -/
  time_coherent : TimeCoherent s
  /-- All values within Rust representable bounds -/
  bounds_ok : BoundsInv s

/-- Initial state satisfies SystemInv -/
theorem initial_system_inv
    (s : State)
    (h_empty : s.kernel.revocation.caps = {})
    (h_time : s.time = 0)
    (h_epoch : s.kernel.revocation.epoch = 0)
    (h_now : s.kernel.now = 0)
    (h_plugins : s.plugins = fun _ => default) :
    SystemInv s where
  time_coherent := by
    unfold TimeCoherent
    rw [h_now, h_time]
  bounds_ok := initial_bounds_inv s h_empty h_time h_epoch h_now h_plugins

end Lion.Contracts.Auth
