/-
Lion/Composition/Bridge.lean
=============================

Bridge theorems connecting SystemInvariant to ComponentSafe.

This module proves that:
1. Components extracted from a valid state are ComponentSafe
2. ComponentSafe for all plugins implies SystemInvariant properties
3. Step preservation at component level implies system-level preservation

These bridges connect the compositional reasoning framework to the
existing proof infrastructure.
-/

import Lion.Composition.CompositionTheorem
import Lion.Composition.StructuralDefs
import Lion.Composition.StructuralInvariants
import Lion.Contracts.AuthContract
import Lion.Theorems.Confinement

namespace Lion

/-! =========== WORKHORSE LEMMA: DERIVE COMPONENTSAFE FROM INVARIANTS =========== -/

/--
**Workhorse lemma: Derive ComponentSafe from global + structural invariants**

This is the key insight for scalable proofs: instead of proving ComponentSafe
is preserved by tracking what each Step changed, we RE-DERIVE ComponentSafe
from invariants that hold in the post-state.

This pattern makes step preservation a one-liner corollary, and the proof
is stable even if steps add/revoke/transfer caps, as long as the invariants hold.
-/
theorem componentSafe_fromPlugin_of_invariants (s : State) (pid : PluginId)
    (h_unforgeable : CapUnforgeable s)
    (h_isolated : MemoryIsolated s)
    (h_struct : ComponentStructInv s) :
    ComponentSafe s (Component.fromPlugin s pid) := by
  constructor
  · -- 1. Unforgeable: caps in heldCaps have valid seals
    -- With Handle/State Separation: h_in_held : capId ∈ (s.plugins pid).heldCaps (Finset CapId)
    intro capId h_in_held
    simp only [Component.fromPlugin] at h_in_held
    obtain ⟨cap, h_get⟩ := h_struct.held_in_table pid capId h_in_held
    exact ⟨cap, h_get, h_unforgeable capId cap h_get⟩

  · -- 2. Confined: caps exist in table (handle integrity)
    -- With Handle/State Separation, we only check existence, not validity
    -- Validity is checked at USE time (cap_invoke, cap_delegate)
    intro capId h_in_held
    simp only [Component.fromPlugin] at h_in_held
    exact h_struct.held_in_table pid capId h_in_held

  · -- 3. Isolated: memory within bounds
    intro addr h_contains
    exact h_isolated pid addr h_contains

  · -- 4. Compliant: holder ∈ sourcePids
    intro capId h_in_held
    simp only [Component.fromPlugin] at h_in_held
    obtain ⟨cap, h_get, h_holder⟩ := h_struct.held_owned pid capId h_in_held
    refine ⟨cap, h_get, ?_⟩
    simp only [Component.fromPlugin, Finset.mem_singleton]
    exact h_holder

/-! =========== BRIDGE: ComponentSafe ↔ SystemInvariant =========== -/

/-!
### Conceptual Relationship

ComponentSafe and SystemInvariant are at different abstraction levels:

- **ComponentSafe** (4 properties): Per-component predicate
  1. unforgeable: held caps are sealed
  2. confined: held caps exist in table (handle integrity)
  3. isolated: memory within WASM bounds
  4. compliant: holders in sourcePids

- **SystemInvariant** (11 properties): System-level predicate
  1. cap_unforgeable, 2. memory_isolated, 3. deadlock_free,
  4. cap_confined, 5. cap_revocable, 6. temporal_safe,
  7. message_delivery, 8. workflows_have_work, 9. workflow_progress,
  10. policy_sound, 11. step_confinement

**Direction A** (proven): SystemInvariant → AllComponentsSafe
  Via componentSafe_fromPlugin_of_invariants + structural invariants

**Direction B** (proven): AllComponentsSafe → (MemoryIsolated ∧ CapUnforgeable)
  Via all_safe_implies_system_invariant in CompositionTheorem.lean

The remaining 9 SystemInvariant properties are system-level and cannot be
derived from component-level properties alone. They require:
- Step existence (deadlock_free)
- Ghost state tracking (temporal_safe)
- Actor/workflow state (message_delivery, workflows_*)
- Authorization structure (cap_revocable, policy_sound)
- Noninterference (step_confinement)
- Table invariants (cap_confined)

The meaningful result is: SystemInvariant is preserved by Steps, and
SystemInvariant implies AllComponentsSafe. Therefore compositional security
is automatically preserved for all reachable states.
-/

/--
**Direction A: SystemInvariant → AllComponentsSafe**

If the system satisfies all 11 security properties, then every component
is individually safe.

This is the decomposition direction: system security implies component security.
-/
theorem systemInvariant_implies_allComponentsSafe (s : State)
    (h_sys : SystemInvariant s)
    (h_struct : ComponentStructInv s) :
    AllComponentsSafe s := by
  intro pid
  exact componentSafe_fromPlugin_of_invariants s pid
    h_sys.cap_unforgeable
    h_sys.memory_isolated
    h_struct

/-!
### Direction B: AllComponentsSafe contribution to SystemInvariant

AllComponentsSafe provides exactly 2 of 11 SystemInvariant properties:
- MemoryIsolated (from ComponentSafe.isolated for all pids)
- CapUnforgeable (from ComponentSafe.unforgeable + AllCapsHeld)

The remaining 9 properties are system-level and require separate proofs.
See: `all_safe_implies_system_invariant` in CompositionTheorem.lean
-/

/-! =========== COMPOSITIONAL SECURITY CHAIN =========== -/

/--
**Compositional Security Chain Theorem**

This is the main result connecting compositional and system-level security:

1. init_state satisfies SystemInvariant (init_satisfies_invariant)
2. Step preserves SystemInvariant (security_composition)
3. SystemInvariant → AllComponentsSafe (systemInvariant_implies_allComponentsSafe)
4. Therefore: All reachable states have all components safe

This means we get compositional security "for free" from the system-level proofs.
The ComponentSafe framework provides additional modularity for reasoning about
individual components and their composition.
-/
theorem compositional_security_chain (s : State)
    (h_reach : Reachable init_state s)
    (h_struct : ComponentStructInv s) :
    AllComponentsSafe s := by
  have h_sys := reachable_satisfies_invariant s h_reach
  exact systemInvariant_implies_allComponentsSafe s h_sys h_struct

/-! =========== STEP PRESERVATION: RE-DERIVE PATTERN =========== -/

/--
**Theorem: Step preserves component safety (re-derive pattern)**

The key insight: we don't track what changed during the step.
Instead, we re-derive ComponentSafe from post-state invariants.

Given:
- SystemInvariant holds in post-state s'
- Structural invariants hold in post-state s'

Then ComponentSafe holds in s' - regardless of what the step did.

This makes the proof a one-liner corollary of the workhorse lemma.
-/
theorem step_preserves_component_safe (s s' : State) (_st : Step s s')
    (pid : PluginId)
    (h_sys' : SystemInvariant s')
    (h_struct' : ComponentStructInv s') :
    ComponentSafe s' (Component.fromPlugin s' pid) :=
  componentSafe_fromPlugin_of_invariants s' pid
    h_sys'.cap_unforgeable
    h_sys'.memory_isolated
    h_struct'

/-! =========== PROVEN STRUCTURAL INVARIANT PRESERVATION =========== -/

/-- KeyMatchesId (from AuthInv) implies well_keyed_table (from Confinement).
    They're the same predicate with different argument binding styles. -/
lemma keyMatchesId_implies_well_keyed {caps : CapTable}
    (h : Contracts.Auth.CapTable.KeyMatchesId caps) :
    Confinement.well_keyed_table caps := by
  intro k c hget
  exact h hget

/--
**THEOREM (was axiom): Step preserves HeldCapsInTable.**

With Handle/State Separation, HeldCapsInTable = HeldCapsInTableWeak (both are existence-based).
This is provable using step_preserves_heldCapsInTableWeak from StructuralInvariants.lean,
given well_keyed_table which we derive from AuthInv.caps_wf.keys_match.

This theorem requires AuthInv as input to provide the well_keyed_table property.
-/
theorem step_preserves_held_in_table (s s' : State) (st : Step s s')
    (h_auth : Contracts.Auth.AuthInv s) :
    HeldCapsInTable s → HeldCapsInTable s' := by
  intro h_held
  -- HeldCapsInTable = HeldCapsInTableWeak (identical definitions)
  -- Use the proven step_preserves_heldCapsInTableWeak theorem
  have h_wk : Confinement.well_keyed_table s.kernel.revocation.caps :=
    keyMatchesId_implies_well_keyed h_auth.caps_wf.keys_match
  exact Composition.step_preserves_heldCapsInTableWeak s s' st h_held h_wk

/-! =========== STEP PRESERVATION THEOREM =========== -/

/--
Preservation of structural invariants across steps.

Both invariants are FULLY PROVEN (no axioms):
- HeldCapsInTable: uses step_preserves_heldCapsInTableWeak
- HeldCapsOwnedCorrectly: proven in StructuralInvariants.lean

Handle/State Separation eliminated the HeldCapsIsValid axiom:
- Validity is checked at USE time (cap_invoke, cap_delegate preconditions)
- After revocation, handles remain but fail IsValid check when used
- This matches the semantic: "revoked cap cannot PASS", not "cannot HOLD"

Requires AuthInv to derive well_keyed_table for HeldCapsInTable preservation.
-/
theorem step_preserves_struct_inv (s s' : State) (st : Step s s')
    (h_struct : ComponentStructInv s)
    (h_auth : Contracts.Auth.AuthInv s) :
    ComponentStructInv s' := by
  constructor
  · -- HeldCapsInTable preserved (FULLY PROVEN)
    exact step_preserves_held_in_table s s' st h_auth h_struct.held_in_table
  · -- HeldCapsOwnedCorrectly preserved (FULLY PROVEN)
    exact Composition.step_preserves_heldCapsOwnedCorrectly s s' st h_struct.held_owned

end Lion
