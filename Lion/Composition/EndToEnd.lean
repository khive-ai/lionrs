/-
Lion/Composition/EndToEnd.lean
==============================

END-TO-END CORRECTNESS (v1 Chapter 5.3)

This file provides the capstone theorem for the Lion formal verification:
the complete end-to-end correctness guarantee matching v1 Theorem 5.3.

v1 Definition (§5.3.1):
  SystemInvariant(s) ≜ MemoryIsolation(s) ∧ DeadlockFreedom(s) ∧
                       CapabilityConfinement(s) ∧ PolicyCompliance(s) ∧
                       WorkflowTermination(s) ∧ ResourceBounds(s)

v1 Theorem 5.3 (§5.3.1):
  ∀s, σ: SystemInvariant(s) ⇒ SystemInvariant(execute(s, σ))

v1 Theorem 5.5 (§5.3.3):
  (∧_c SecureComponent(c)) ∧ CorrectInteractions ⇒ SecureSystem

This file proves these theorems by composing:
- SystemInvariant (11 properties)
- AllComponentsSafe (compositional security)
- AttackCoverage (defense completeness)
-/

import Lion.Composition.SystemInvariant
import Lion.Composition.ComponentSafe
import Lion.Composition.CompositionTheorem
import Lion.Composition.AttackCoverage
import Lion.Composition.Bridge
import Lion.Composition.StructuralInvariants
import Lion.Composition.PolicyWorkflowBridge

namespace Lion

/-! =========== END-TO-END CORRECTNESS STRUCTURE =========== -/

/--
**EndToEndCorrectness**: The complete security guarantee for Lion.

This structure captures v1's end-to-end correctness thesis (§5.3):
- System-level: All 11 invariant properties hold
- Component-level: Every component satisfies ComponentSafe
- Defense-level: All attack classes are mitigated

This is the MASTER predicate for Lion security verification.
-/
structure EndToEndCorrectness (s : State) : Prop where
  /-- v1 §5.3.1: System-wide invariant (11 properties) -/
  system_invariant : SystemInvariant s

  /-- v1 §5.3.3 Theorem 5.5: All components are individually secure -/
  all_components_safe : AllComponentsSafe s

  /-- v1 §5.3.3 Theorem 5.6: All attack classes have verified mitigations -/
  attack_coverage : ∀ attack : AttackClass, Mitigates attack s

/-! =========== INITIAL STATE CORRECTNESS =========== -/

/--
**Theorem: Initial state satisfies EndToEndCorrectness**

This establishes the BASE CASE for end-to-end correctness:
the initial system state is fully secure.

v1 Proof Strategy: Show each component of EndToEndCorrectness holds for init_state.
-/
theorem init_satisfies_end_to_end : EndToEndCorrectness init_state := by
  constructor
  -- system_invariant: from init_satisfies_invariant
  · exact init_satisfies_invariant
  -- all_components_safe: use componentSafe_fromPlugin_of_invariants with init structural inv
  · intro pid
    exact componentSafe_fromPlugin_of_invariants init_state pid
      init_satisfies_invariant.cap_unforgeable
      init_satisfies_invariant.memory_isolated
      init_state_has_struct_inv
  -- attack_coverage: from attack_coverage_of_systemInvariant
  · exact attack_coverage_of_systemInvariant init_state init_satisfies_invariant

/-! =========== STRUCTURAL INVARIANT PRESERVATION =========== -/

/--
**ComponentStructInv preservation under Step**

The structural invariant (held caps are in table and have correct holder)
is preserved by any valid step.

This bridges SystemInvariant preservation to ComponentSafe preservation.
-/
theorem structInv_preserved_by_step
    (s s' : State)
    (h_inv : SystemInvariant s)
    (h_struct : ComponentStructInv s)
    (h_step : Step s s') :
    ComponentStructInv s' := by
  -- Get well_keyed_table from cap_confined (which is table_invariant)
  have h_wk : Confinement.well_keyed_table s.kernel.revocation.caps :=
    h_inv.cap_confined.1
  constructor
  -- held_in_table: use step_preserves_heldCapsInTableWeak
  -- HeldCapsInTable and HeldCapsInTableWeak are definitionally equal
  · exact Composition.step_preserves_heldCapsInTableWeak s s' h_step h_struct.held_in_table h_wk
  -- held_owned: use step_preserves_heldCapsOwnedCorrectly
  · exact Composition.step_preserves_heldCapsOwnedCorrectly s s' h_step h_struct.held_owned

/-! =========== STEP PRESERVATION =========== -/

/--
**Theorem: Step preserves EndToEndCorrectness**

The INDUCTIVE STEP of v1 Theorem 5.3:
If the system satisfies EndToEndCorrectness and takes a valid step,
the resulting state also satisfies EndToEndCorrectness.
-/
theorem step_preserves_end_to_end
    (s s' : State)
    (h_e2e : EndToEndCorrectness s)
    (h_struct : ComponentStructInv s)
    (h_step : Step s s') :
    EndToEndCorrectness s' := by
  have h_inv' := security_composition s s' h_e2e.system_invariant h_step
  have h_struct' := structInv_preserved_by_step s s' h_e2e.system_invariant h_struct h_step
  constructor
  -- system_invariant: from security_composition
  · exact h_inv'
  -- all_components_safe: from componentSafe_fromPlugin_of_invariants
  · intro pid
    exact componentSafe_fromPlugin_of_invariants s' pid
      h_inv'.cap_unforgeable
      h_inv'.memory_isolated
      h_struct'
  -- attack_coverage: from the preserved SystemInvariant
  · exact attack_coverage_of_systemInvariant s' h_inv'

/--
**Theorem: Reachable states satisfy EndToEndCorrectness**

v1 Theorem 5.3 (full statement):
∀s, σ: SystemInvariant(s) ⇒ SystemInvariant(execute(s, σ))

Extended to the full EndToEndCorrectness predicate.

Note: Requires ComponentStructInv to be maintained along the path.
-/
theorem reachable_satisfies_end_to_end
    (s : State)
    (h_init : EndToEndCorrectness s)
    (h_struct : ComponentStructInv s)
    (s' : State)
    (h_reach : Reachable s s') :
    EndToEndCorrectness s' ∧ ComponentStructInv s' := by
  induction h_reach with
  | refl => exact ⟨h_init, h_struct⟩
  | step h_reach' h_step ih =>
      obtain ⟨h_e2e_mid, h_struct_mid⟩ := ih
      have h_e2e' := step_preserves_end_to_end _ _ h_e2e_mid h_struct_mid h_step
      have h_struct' := structInv_preserved_by_step _ _ h_e2e_mid.system_invariant h_struct_mid h_step
      exact ⟨h_e2e', h_struct'⟩

/--
**Corollary: Any state reachable from init_state satisfies EndToEndCorrectness**

This is the CAPSTONE THEOREM: starting from the initial state,
ANY reachable state satisfies the complete security guarantee.
-/
theorem any_reachable_from_init_is_secure
    (s : State)
    (h_reach : Reachable init_state s) :
    EndToEndCorrectness s :=
  (reachable_satisfies_end_to_end init_state
    init_satisfies_end_to_end
    init_state_has_struct_inv
    s h_reach).1

/-! =========== V1 EXPLICIT MAPPINGS =========== -/

/--
**v1 Theorem 5.3: System-Wide Invariant Preservation**

Explicit statement matching v1 §5.3.1.
-/
theorem v1_theorem_5_3_invariant_preservation :
    ∀ s s' : State,
      SystemInvariant s →
      Step s s' →
      SystemInvariant s' :=
  fun s s' h_inv h_step => security_composition s s' h_inv h_step

/--
**v1 Theorem 5.5: Security Composition**

(∧_c SecureComponent(c)) ∧ CorrectInteractions ⇒ SecureSystem

We have this via nary_composition_security + all_safe_implies_system_invariant.
-/
theorem v1_theorem_5_5_security_composition
    (s : State)
    (cs : List Component)
    (default : Component)
    (h_all_safe : ∀ c ∈ cs, ComponentSafe s c)
    (h_default_safe : ComponentSafe s default)
    (h_pairwise : PairwiseCompatible s cs)
    (h_default_compatible : ∀ c ∈ cs, Compatible s default c) :
    ComponentSafe s (Component.composeList cs default) :=
  nary_composition_security s cs default h_all_safe h_default_safe
    h_pairwise h_default_compatible

/--
**v1 Theorem 5.6: Attack Coverage**

Every attack class is mitigated by the system invariant.
-/
theorem v1_theorem_5_6_attack_coverage
    (s : State)
    (h_inv : SystemInvariant s) :
    ∀ attack : AttackClass, Mitigates attack s :=
  attack_coverage_of_systemInvariant s h_inv

/-! =========== SUMMARY =========== -/

/-
SUMMARY: End-to-End Correctness for Lion Microkernel

This file proves the capstone theorems from v1 Chapter 5.3:

1. **init_satisfies_end_to_end**:
   The initial state satisfies EndToEndCorrectness (base case) ✓

2. **step_preserves_end_to_end**:
   Every valid step preserves EndToEndCorrectness (inductive step)
   - Requires ComponentStructInv as additional invariant

3. **reachable_satisfies_end_to_end**:
   Any reachable state satisfies EndToEndCorrectness (v1 Thm 5.3)

4. **any_reachable_from_init_is_secure**:
   CAPSTONE: init_state → any reachable s → EndToEndCorrectness s

EXPLICIT V1 MAPPINGS:
- v1_theorem_5_3_invariant_preservation: SystemInvariant preservation ✓
- v1_theorem_5_5_security_composition: N-ary component composition ✓
- v1_theorem_5_6_attack_coverage: Defense completeness ✓

WHAT THIS PROVES:
- No unauthorized actions (capability + policy)
- No unauthorized information flows (isolation + capability)
- System remains responsive (deadlock freedom + termination)
- All attack classes mitigated (attack coverage)

DEPENDENCIES:
- SystemInvariant (11 properties)
- AllComponentsSafe (compositional security)
- AttackCoverage (defense mapping)
- security_composition (step preservation)
- componentSafe_fromPlugin_of_invariants (Bridge.lean)
- init_state_has_struct_inv (PolicyWorkflowBridge.lean)

PROOF STATUS: COMPLETE (0 sorries, 0 new axioms)

All lemmas proven using existing infrastructure:
- structInv_preserved_by_step: Uses step_preserves_heldCapsInTableWeak
  and step_preserves_heldCapsOwnedCorrectly from StructuralInvariants.lean
- reachable_satisfies_end_to_end: Induction with simultaneous E2E + StructInv tracking
-/

end Lion
