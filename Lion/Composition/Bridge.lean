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

/-! =========== BRIDGE: ComponentSafe → SystemInvariant =========== -/

-- Note: all_components_safe_implies_memory_isolated is defined in CompositionTheorem.lean
-- We re-export it here for completeness of the bridge module.

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
theorem step_preserves_component_safe (s s' : State) (st : Step s s')
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
