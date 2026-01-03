/-
Lion/Contracts/Interface.lean
==============================

Interface Contract structure for assume-guarantee composition.
Key insight: `affects` takes the Step witness, not just (s, s').
-/

import Lion.State.State
import Lion.Step.Step

namespace Lion

universe u v

/-! =========== STEP PREDICATE =========== -/

/--
A predicate over *witnessed* steps.
This is the right level to classify syscalls, plugin steps, kernel ops, etc.
Pattern matching on the Step constructor lets us distinguish cap_invoke from mem_alloc.
-/
abbrev StepPred (State : Type u) (Step : State → State → Type v) : Type (max u v) :=
  ∀ {s s' : State}, Step s s' → Prop

/-! =========== INTERFACE CONTRACT =========== -/

/--
Assume/guarantee-style interface contract for a component inside a global transition system.

Design principles:
1. `pre`: Assumptions about the environment (other components' invariants)
2. `inv`: The invariant this component guarantees
3. `affects`: Which steps are in this component's responsibility set
4. `preserve`: Proof that in-scope steps preserve the invariant (given preconditions)
5. `frame`: Proof that out-of-scope steps preserve the invariant (frame condition)

Key insight from a0.md: `affects` takes the Step witness (h : Step s s'),
not just the state pair (s, s'). This lets us pattern match on constructors.
-/
structure InterfaceContract (State : Type u) (Step : State → State → Type v) :
    Type (max (u+1) (v+1)) where
  /-- Assumptions about the environment / other components. -/
  pre : State → Prop

  /-- Invariant guaranteed by this component. -/
  inv : State → Prop

  /-- `affects h` means: this step is in the responsibility set of the component
      (or, more operationally, it may touch the footprint relevant to `inv`). -/
  affects : StepPred State Step

  /-- Preservation when the step is in-scope for this component. -/
  preserve :
    ∀ {s s'} (h : Step s s'),
      inv s → pre s → affects h → inv s'

  /-- Frame: preservation when the step is *not* in-scope for this component. -/
  frame :
    ∀ {s s'} (h : Step s s'),
      inv s → pre s → ¬ affects h → inv s'

namespace InterfaceContract

/-! =========== DERIVED LEMMAS =========== -/

/--
Key derived lemma: invariants are preserved for *any* step, by splitting on `affects`.
This is the workhorse for composition: just call `C.inv_step` for each contract.
-/
theorem inv_step
    {State : Type u} {Step : State → State → Type v}
    (C : InterfaceContract State Step)
    {s s' : State} (h : Step s s') :
    C.inv s → C.pre s → C.inv s' := by
  classical
  intro hinv hpre
  by_cases ha : C.affects h
  · exact C.preserve h hinv hpre ha
  · exact C.frame h hinv hpre ha

/--
Alternative: if you have a proof that affects is decidable, avoid classical.
-/
theorem inv_step_dec
    {State : Type u} {Step : State → State → Type v}
    (C : InterfaceContract State Step)
    {s s' : State} (h : Step s s')
    [Decidable (C.affects h)] :
    C.inv s → C.pre s → C.inv s' := by
  intro hinv hpre
  if ha : C.affects h then
    exact C.preserve h hinv hpre ha
  else
    exact C.frame h hinv hpre ha

/--
Binary relation view of step_rel (for tooling/debugging).
Existentially quantifies over the step witness.
-/
def stepRel
    {State : Type u} {Step : State → State → Type v}
    (C : InterfaceContract State Step) : State → State → Prop :=
  fun s s' => ∃ h : Step s s', C.affects h

/--
Composition of two contracts: both invariants are preserved if both preconditions hold.
-/
theorem compose_two
    {State : Type u} {Step : State → State → Type v}
    (C1 C2 : InterfaceContract State Step)
    {s s'} (h : Step s s') :
    C1.inv s → C1.pre s → C2.inv s → C2.pre s →
    C1.inv s' ∧ C2.inv s' := by
  intro h1inv h1pre h2inv h2pre
  exact ⟨C1.inv_step h h1inv h1pre, C2.inv_step h h2inv h2pre⟩

end InterfaceContract

/-! =========== CONTRACT COMPATIBILITY =========== -/

/--
Two contracts are compatible if C1's invariant implies C2's precondition.
This captures the assume-guarantee dependency relationship.
-/
def Contract.compatible
    {State : Type u} {Step : State → State → Type v}
    (C1 C2 : InterfaceContract State Step) : Prop :=
  ∀ s, C1.inv s → C2.pre s

/-- Transitivity of compatibility -/
theorem Contract.compatible_trans
    {State : Type u} {Step : State → State → Type v}
    (C1 C2 C3 : InterfaceContract State Step)
    (_h12 : Contract.compatible C1 C2)
    (h23 : Contract.compatible C2 C3) :
    ∀ s, C1.inv s → C2.inv s → C3.pre s := by
  intro s _h1 h2
  exact h23 s h2

end Lion
