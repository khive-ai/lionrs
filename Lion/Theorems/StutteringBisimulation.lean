/-
Lion/Theorems/StutteringBisimulation.lean
==========================================

Stuttering bisimulation infrastructure for TINI proofs.

Based on consultation A11-A12 recommendations:
- Star: Generic reflexive-transitive closure
- StepND: Steps without declassification
- LStutterSim: One-sided stuttering simulation
- Stuck-state lemma via role-swapping

This machinery enables proving TINI_noninterference as a theorem.

Mathematical Foundation:
- van Glabbeek (1993): The Linear Time - Branching Time Spectrum
- Mantel (2003): A Uniform Framework for the Formal Specification
  and Verification of Information Flow Security
- Murray et al. (2013): seL4 Information Flow Proofs
-/

import Lion.State.State
import Lion.Step.Step
import Lion.Theorems.NoninterferenceBase
import Lion.Theorems.RuntimeTrustBundle
import Mathlib.Logic.Relation

namespace Lion.Stuttering

open Lion Lion.Noninterference

/-! =========== PART 1: REFLEXIVE-TRANSITIVE CLOSURE (Mathlib) =========== -/

/--
Reflexive-transitive closure using Mathlib's ReflTransGen.
This replaces our custom Star definition with the standard Mathlib version.

Migration (2026-01-04, A9 Mathlib Integration):
- Star → Relation.ReflTransGen
- Star.refl → ReflTransGen.refl
- Star.tail → ReflTransGen.tail
- Star.trans → ReflTransGen.trans
- Star.single → ReflTransGen.single
- Star.cons → ReflTransGen.head
-/
abbrev Star {α : Type} (r : α → α → Prop) := Relation.ReflTransGen r

namespace Star

/-- Reflexivity of Star (delegate to ReflTransGen.refl) -/
theorem refl {α : Type} {r : α → α → Prop} (a : α) : Star r a a :=
  Relation.ReflTransGen.refl

/-- Tail constructor of Star (delegate to ReflTransGen.tail) -/
theorem tail {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : Star r a b) (hbc : r b c) : Star r a c :=
  Relation.ReflTransGen.tail hab hbc

/-- Transitivity of Star (delegate to ReflTransGen.trans) -/
theorem trans {α : Type} {r : α → α → Prop} {a b c : α} :
    Star r a b → Star r b c → Star r a c :=
  Relation.ReflTransGen.trans

/-- Single step implies Star (delegate to ReflTransGen.single) -/
theorem single {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  Relation.ReflTransGen.single h

/-- Prepend a step to Star (delegate to ReflTransGen.head) -/
theorem cons {α : Type} {r : α → α → Prop} {a b c : α}
    (h : r a b) (hbc : Star r b c) : Star r a c :=
  Relation.ReflTransGen.head h hbc

end Star

/-! =========== PART 2: NO-DECLASSIFICATION STEPS =========== -/

/--
A step together with a proof it is not a declassification step.
This bundles the no-declass condition into the relation itself,
eliminating the need for side-condition hypotheses.
-/
structure StepND (s s' : State) where
  step : Step s s'
  ndeclass : step.is_declassify = false

/-- Propositional wrapper: there exists a non-declassification step -/
def HasStepND (s s' : State) : Prop := Nonempty (StepND s s')

/-- Stuttering reachability: zero or more non-declassify steps -/
abbrev StutterReachND : State → State → Prop := Star HasStepND

/-- Convert a Trace.no_declassify to StutterReachND -/
theorem trace_to_stutter_reach {s s' : State} (t : Trace s s') (h : t.no_declassify) :
    StutterReachND s s' := by
  induction t with
  | nil => exact Star.refl _
  | cons st rest ih =>
    have ⟨h_nd, h_rest⟩ := h
    have h_rest_reach := ih h_rest
    exact Star.cons ⟨⟨st, h_nd⟩⟩ h_rest_reach

/-- ReachableNoDeclass implies StutterReachND -/
theorem reachable_no_declass_to_stutter {s s' : State}
    (h : ReachableNoDeclass s s') : StutterReachND s s' := by
  rcases h with ⟨t, h_nd⟩
  exact trace_to_stutter_reach t h_nd

/-! =========== PART 3: STUTTERING SIMULATION =========== -/

/--
One-sided stuttering simulation (sufficient for TINI).

If s1 ≈_L s2 and s1 takes a non-declass step to s1',
then s2 can reach some s2' (via zero or more non-declass steps)
such that s1' ≈_L s2'.

This is the key property that enables trace induction.
-/
def LStutterSim (L : SecurityLevel) : Prop :=
  ∀ {s1 s2 s1' : State},
    low_equivalent L s1 s2 →
    StepND s1 s1' →
    ∃ s2', StutterReachND s2 s2' ∧ low_equivalent L s1' s2'

/-! =========== PART 4: STUCK STATES =========== -/

/--
**Strengthened Step Consistent for Non-Declass Steps**

When matching a low non-declass step, the matching step is also non-declass.
This follows directly from the strengthened step_consistent which returns
the is_declassify property of the matching step.
-/
def step_consistent_nd (L : SecurityLevel) : Prop :=
  ∀ {s1 s2 s1' : State},
    low_equivalent L s1 s2 →
    ∀ (st1 : StepND s1 s1'),
      is_low_step L st1.step →
      ∃ s2', Nonempty (StepND s2 s2') ∧ low_equivalent L s1' s2'

/--
**Low Step Type Matching (THEOREM)**

For a low step, the matching step has the same is_declassify property AND is also low.

This is now a THEOREM, derived directly from the strengthened step_consistent
which returns is_low_step L st2, st2.is_declassify = st1.is_declassify, and equivalence.

Previously this was an axiom. Now it's a consequence of the stronger specification.
The return type includes `is_low_step L st2` which makes `low_step_match_level` unnecessary.
-/
theorem low_step_match_same_type (L : SecurityLevel)
    (h_step : step_consistent L) :
    ∀ {s1 s2 s1' : State},
      low_equivalent L s1 s2 →
      ∀ (st1 : Step s1 s1'),
        is_low_step L st1 →
        ∃ s2', ∃ (st2 : Step s2 s2'),
          is_low_step L st2 ∧
          st2.is_declassify = st1.is_declassify ∧
          low_equivalent L s1' s2' := by
  intro s1 s2 s1' heq st1 h_low
  obtain ⟨s2', st2, h_low2, h_same_declass, heq'⟩ := h_step s1 s2 s1' heq st1 h_low
  exact ⟨s2', st2, h_low2, h_same_declass, heq'⟩

/-!
**Low Step Determinism**

For low steps, the destination state is uniquely determined by the source state
and the step type. This captures that low-observable operations are deterministic:
- plugin_internal: WASM execution is deterministic
- host_call: Kernel response is deterministic given state
- kernel_internal: Scheduler is deterministic

Now derived from RuntimeTrustBundle. The theorem `low_step_deterministic` is
exported from `Lion.Theorems.RuntimeTrustBundle`.
-/

/-!
**Note on low_step_match_level**

This property is now SUBSUMED by the strengthened `low_step_match_same_type`.
The theorem `low_step_match_same_type` returns `is_low_step L st2` directly,
eliminating the need for a separate `low_step_match_level` lemma.

The old axiom/theorem has been removed; usages should destructure the
`is_low_step` from `low_step_match_same_type` directly.
-/

/--
**step_consistent implies step_consistent_nd (Theorem)**

The strengthened step_consistent now directly returns the matching step's
is_declassify property, making this derivation straightforward.

The key insight: step_consistent returns st2.is_declassify = st1.is_declassify,
so when st1 is non-declassify, st2 is automatically non-declassify.
-/
theorem step_consistent_implies_nd (L : SecurityLevel) :
    step_consistent L → step_consistent_nd L := by
  intro h_sc
  unfold step_consistent_nd
  intro s1 s2 s1' heq st_nd h_low
  -- Use the strengthened step_consistent directly
  have h_match := low_step_match_same_type L h_sc heq st_nd.step h_low
  obtain ⟨s2', st2, _h_low2, h_same_declass, heq'⟩ := h_match
  -- h_same_declass : st2.is_declassify = st_nd.step.is_declassify
  -- st_nd.ndeclass : st_nd.step.is_declassify = false
  -- Therefore: st2.is_declassify = false
  have h_nd2 : st2.is_declassify = false := by rw [h_same_declass, st_nd.ndeclass]
  exact ⟨s2', ⟨⟨st2, h_nd2⟩⟩, heq'⟩

/--
A state is stuck (w.r.t. non-declass steps) if no StepND is possible.
-/
def StuckND (s : State) : Prop := ∀ s', StepND s s' → False

/--
A state is low-stuck if all non-declassify steps are high.
Declassify steps are excluded because they represent intentional information release,
which is handled separately in TINI proofs (not a covert channel).
-/
def LowStuck (L : SecurityLevel) (s : State) : Prop :=
  ∀ s' (st : Step s s'), st.is_declassify = false → ¬ is_low_step L st

/-! =========== PART 5: STUCK-STATE LEMMA VIA ROLE-SWAPPING =========== -/

/--
**Key Lemma**: If s1 is stuck and s1 ≈_L s2, then s2 has no LOW steps.

This is proved by swapping the arguments to step_consistent:
- If s2 could take a low step to s2'
- Then by step_consistent (with roles swapped), s1 would have a matching step
- But s1 is stuck, contradiction

This is the crucial lemma that was blocking the TINI proof.
-/
lemma no_low_step_of_stuck_left (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    {s t t' : State}
    (heq : low_equivalent L s t)
    (h_stuck : StuckND s)
    (st : StepND t t')
    (h_low : is_low_step L st.step) :
    False := by
  -- Use strengthened step_consistent_nd which preserves non-declass property
  have h_sc_nd : step_consistent_nd L := step_consistent_implies_nd L h_step_consistent
  -- Apply with roles swapped
  have heq_symm : low_equivalent L t s := low_equivalent_symm heq
  obtain ⟨s', ⟨h_step_nd⟩, _⟩ := h_sc_nd heq_symm st h_low
  exact h_stuck s' h_step_nd

/--
**Corollary**: If left is stuck, every step from right is high.
-/
lemma stuck_forces_high_steps (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    {s t t' : State}
    (heq : low_equivalent L s t)
    (h_stuck : StuckND s)
    (st : StepND t t') :
    is_high_step L st.step := by
  by_contra h_not_high
  have h_low : is_low_step L st.step := by
    simp only [is_high_step, is_low_step] at *
    exact le_of_not_gt h_not_high
  exact no_low_step_of_stuck_left L h_step_consistent heq h_stuck st h_low

/--
**Corollary**: If left is stuck, right is low-stuck.
-/
lemma stuck_implies_low_stuck (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    {s t : State}
    (heq : low_equivalent L s t)
    (h_stuck : StuckND s) :
    LowStuck L t := by
  intro t' st h_ndeclass h_low
  -- st is non-declassify by hypothesis, so we can construct StepND
  let h_nd : StepND t t' := ⟨st, by simp [h_ndeclass]⟩
  exact no_low_step_of_stuck_left L h_step_consistent heq h_stuck h_nd h_low

/-! =========== PART 6: TRACE LIFTING =========== -/

/--
**Trace Lifting Lemma**: Stuttering simulation lifts to traces.

If we have stuttering simulation, and s1 reaches sf1 via non-declass steps,
and s1 ≈_L s2, then s2 can reach some sf2 such that sf1 ≈_L sf2.
-/
theorem trace_stutter_lift (L : SecurityLevel)
    (h_sim : LStutterSim L)
    {s1 sf1 s2 : State}
    (heq : low_equivalent L s1 s2)
    (hreach1 : StutterReachND s1 sf1) :
    ∃ s2f, StutterReachND s2 s2f ∧ low_equivalent L sf1 s2f := by
  induction hreach1 with
  | refl =>
    exact ⟨s2, Star.refl s2, heq⟩
  | tail hreach1' hstep ih =>
    -- Get intermediate state from IH
    obtain ⟨s2_mid, hreach2_mid, heq_mid⟩ := ih
    -- hstep : HasStepND _ _, need to extract StepND
    obtain ⟨step_nd⟩ := hstep
    -- Apply simulation for the last step
    obtain ⟨s2f, hreach2_last, heq_final⟩ := h_sim heq_mid step_nd
    -- Combine reachabilities
    exact ⟨s2f, Star.trans hreach2_mid hreach2_last, heq_final⟩

/-! =========== PART 7: STRENGTHENED SINGLE-STEP TINI =========== -/

/--
**Strengthened Single-Step TINI**: Returns stuttering reachability witness.

This is the key refactoring of single_step_TINI that returns explicit
evidence of how s2' is reached from s2.
-/
theorem single_step_TINI_strong (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    (h_step_confinement : step_confinement L)
    (s1 s2 s1' : State)
    (heq : low_equivalent L s1 s2)
    (hstep : StepND s1 s1') :
    ∃ s2', StutterReachND s2 s2' ∧ low_equivalent L s1' s2' := by
  by_cases h_low : is_low_step L hstep.step
  case pos =>
    -- Low step: use step_consistent_nd which preserves non-declass
    have h_sc_nd : step_consistent_nd L := step_consistent_implies_nd L h_step_consistent
    obtain ⟨s2', ⟨h_nd2⟩, heq'⟩ := h_sc_nd heq hstep h_low
    exact ⟨s2', Star.single ⟨h_nd2⟩, heq'⟩
  case neg =>
    -- High step: stutter (zero steps on right)
    have h_high : is_high_step L hstep.step := by
      simp only [is_high_step, is_low_step] at *
      exact lt_of_not_ge h_low
    have h_conf := h_step_confinement s1 s1' hstep.step h_high
    have hmono := high_step_no_downgrade L hstep.step h_high hstep.ndeclass
    have heq' : low_equivalent L s1' s2 := by
      constructor
      · exact high_step_preserves_low_equiv_trans L hmono h_conf heq.1
      · -- s2 low-equiv-left to s1' follows by transitivity:
        -- heq.2 : low_equivalent_left L s2 s1
        -- h_conf : low_equivalent_left L s1 s1'
        exact low_equivalent_left_trans heq.2 h_conf
    exact ⟨s2, Star.refl s2, heq'⟩

/--
**LStutterSim holds from unwinding conditions**.

This shows that the stuttering simulation property follows from
step_consistent and step_confinement.
-/
theorem LStutterSim_of_unwinding (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    (h_step_confinement : step_confinement L) :
    LStutterSim L := by
  intro s1 s2 s1' heq hstep
  exact single_step_TINI_strong L h_step_consistent h_step_confinement s1 s2 s1' heq hstep

/-! =========== PART 8: HIGH STEPS PRESERVE EQUIVALENCE =========== -/

/--
High steps preserve low equivalence along a Star of high steps.

If all steps in a StutterReachND are high, low equivalence is preserved.
-/
theorem high_star_preserves_low_equiv (L : SecurityLevel)
    (h_step_confinement : step_confinement L)
    {s sf : State}
    (hreach : StutterReachND s sf)
    (h_all_high : ∀ s' s'' (step_nd : StepND s' s''),
        StutterReachND s s' → is_high_step L step_nd.step) :
    low_equivalent_left L s sf := by
  induction hreach with
  | refl =>
    constructor
    · intro pid _; rfl
    · intro rid _; rfl
  | @tail b c hreach' hstep ih =>
    -- Extract the StepND from HasStepND
    obtain ⟨step_nd⟩ := hstep
    have h_high : is_high_step L step_nd.step := h_all_high b c step_nd hreach'
    have h_conf := h_step_confinement b c step_nd.step h_high
    -- ih is the induction hypothesis for the prefix
    -- The original h_all_high covers the prefix since all steps before b are reachable from s
    exact low_equivalent_left_trans ih h_conf

/-! =========== PART 9: STUTTER REACH TO REACHABLE CONVERSION =========== -/

/-- Append a step at the end of a trace -/
def Trace.snoc {s s' s'' : State} (t : Trace s s') (st : Step s' s'') : Trace s s'' :=
  match t with
  | .nil _ => Trace.cons st (Trace.nil s'')
  | .cons st' rest => Trace.cons st' (Trace.snoc rest st)

/-- Snoc preserves no_declassify property -/
theorem Trace.snoc_no_declassify {s s' s'' : State} (t : Trace s s') (st : Step s' s'')
    (h_t : t.no_declassify) (h_st : st.is_declassify = false) :
    (Trace.snoc t st).no_declassify := by
  induction t generalizing s'' with
  | nil => exact ⟨h_st, trivial⟩
  | cons st' rest ih =>
    have ⟨h_st', h_rest⟩ := h_t
    exact ⟨h_st', ih st h_rest h_st⟩

/--
Convert StutterReachND back to a Trace.
This is needed to satisfy the ReachableNoDeclass witness requirement.
-/
theorem stutter_reach_to_trace {s s' : State} (h : StutterReachND s s') :
    ∃ t : Trace s s', t.no_declassify := by
  induction h with
  | refl =>
    exact ⟨Trace.nil s, trivial⟩
  | tail hreach hstep ih =>
    obtain ⟨t, h_nd⟩ := ih
    obtain ⟨step_nd⟩ := hstep
    exact ⟨Trace.snoc t step_nd.step, Trace.snoc_no_declassify t step_nd.step h_nd step_nd.ndeclass⟩

/-- StutterReachND implies ReachableNoDeclass -/
theorem stutter_reach_to_reachable_no_declass {s s' : State}
    (h : StutterReachND s s') : ReachableNoDeclass s s' := by
  obtain ⟨t, h_nd⟩ := stutter_reach_to_trace h
  exact ⟨t, h_nd⟩

/-! =========== PART 10: FULL STUCK PRESERVATION =========== -/

/--
**Key Lemma**: If sf1 is fully stuck (no Step at all) and sf1 ≈_L s2,
then s2 cannot take ANY low non-declass step.

This follows from step_consistent with roles swapped: if s2 could take a low step,
sf1 would need to match, but sf1 can't step at all.
-/
lemma no_low_step_from_stuck_equiv (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    {sf1 s2 s2' : State}
    (heq : low_equivalent L sf1 s2)
    (h_stuck : ∀ s'', Step sf1 s'' → False)
    (st : Step s2 s2')
    (h_nd : st.is_declassify = false)
    (h_low : is_low_step L st) :
    False := by
  -- sf1 has no Step at all, so certainly no StepND
  have h_stuck_nd : StuckND sf1 := by
    intro s'' step_nd
    exact h_stuck s'' step_nd.step
  -- Construct StepND from st
  let st_nd : StepND s2 s2' := ⟨st, h_nd⟩
  -- Use no_low_step_of_stuck_left: sf1 is stuck and sf1 ≈_L s2, so s2 can't take low step
  exact no_low_step_of_stuck_left L h_step_consistent heq h_stuck_nd st_nd h_low

/--
**Key Lemma**: If sf1 is fully stuck (no Step at all) and sf1 ≈_L s2,
then s2 can only take high non-declass steps.
-/
lemma any_step_from_stuck_equiv_is_high (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    {sf1 s2 s2' : State}
    (heq : low_equivalent L sf1 s2)
    (h_stuck : ∀ s'', Step sf1 s'' → False)
    (st : Step s2 s2')
    (h_nd : st.is_declassify = false) :
    is_high_step L st := by
  by_contra h_not_high
  have h_low : is_low_step L st := by
    simp only [is_high_step, is_low_step] at *
    exact le_of_not_gt h_not_high
  exact no_low_step_from_stuck_equiv L h_step_consistent heq h_stuck st h_nd h_low

/-! =========== PART 11: HIGH PATH PRESERVATION =========== -/

/--
High non-declass steps preserve full low_equivalent (both directions).

When a high step is taken, both low_equivalent_left directions are preserved.
-/
theorem high_step_preserves_full_low_equiv (L : SecurityLevel)
    (h_step_confinement : step_confinement L)
    {sf s s' : State}
    (heq : low_equivalent L sf s)
    (st : Step s s')
    (h_nd : st.is_declassify = false)
    (h_high : is_high_step L st) :
    low_equivalent L sf s' := by
  have h_conf := h_step_confinement s s' st h_high
  have h_mono := high_step_no_downgrade L st h_high h_nd
  constructor
  -- low_equivalent_left L sf s' : sf's low parts = s''s low parts
  · exact low_equivalent_left_trans heq.1 h_conf
  -- low_equivalent_left L s' sf : s''s low parts = sf's low parts
  · exact high_step_preserves_low_equiv_trans L h_mono h_conf heq.2

/--
A trace of high non-declass steps preserves low_equivalent.

Used when sf1 is stuck and s2 continues with only high steps.
-/
theorem high_trace_preserves_equiv (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    (h_step_confinement : step_confinement L)
    (sf : State)
    (h_stuck : ∀ s'', Step sf s'' → False)
    {s s' : State}
    (t : Trace s s')
    (h_nd : t.no_declassify)
    (heq : low_equivalent L sf s) :
    low_equivalent L sf s' := by
  induction t with
  | nil => exact heq
  | cons st rest ih =>
    have ⟨h_st_nd, h_rest_nd⟩ := h_nd
    -- st is high because sf is stuck
    have h_high := any_step_from_stuck_equiv_is_high L h_step_consistent heq h_stuck st h_st_nd
    -- After st, we have low_equiv preserved
    have heq' := high_step_preserves_full_low_equiv L h_step_confinement heq st h_st_nd h_high
    -- Apply IH with the new equivalence
    exact ih h_rest_nd heq'

/-! =========== PART 12: TERMINATION TRANSFER =========== -/

/--
**Termination Transfer Lemma**: If sf is stuck, sf ≈_L s, and s terminates,
then s reaches some stuck state sf' with sf ≈_L sf'.

This is the key lemma for TINI: when one side is stuck and equivalent,
the other side's terminating path consists only of high steps (which preserve equiv).

The proof uses high_trace_preserves_equiv: since sf is fully stuck, any step
from s must be high (by no_low_step_from_stuck_equiv), so the entire terminating
trace consists of high steps that preserve low_equivalent.
-/
theorem termination_preserves_equiv (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    (h_step_confinement : step_confinement L)
    {sf s : State}
    (heq : low_equivalent L sf s)
    (h_stuck_sf : ∀ s'', Step sf s'' → False)
    (h_term_s : TerminatesNoDeclass s) :
    ∃ sf', ReachableNoDeclass s sf' ∧
           (∀ s'', Step sf' s'' → False) ∧
           low_equivalent L sf sf' := by
  -- Extract the terminating path from h_term_s
  obtain ⟨sf', ⟨t, h_nd⟩, h_stuck_sf'⟩ := h_term_s
  -- The trace consists only of high steps (because sf is stuck and equivalent)
  -- Use high_trace_preserves_equiv to show sf ≈_L sf'
  have heq' := high_trace_preserves_equiv L h_step_consistent h_step_confinement sf h_stuck_sf t h_nd heq
  exact ⟨sf', ⟨t, h_nd⟩, h_stuck_sf', heq'⟩

/-! =========== PART 13: JOINT TRACE SIMULATION =========== -/

/--
**Joint Trace Simulation Lemma**

This is the core lemma for TINI: given two low-equivalent states that both terminate,
their final states are also low-equivalent.

The proof works by joint induction on both terminating traces:
- When both can step: apply single_step_TINI to maintain equivalence
- When one is stuck: the other can only take high steps (preserving equivalence)
- When both are stuck: done

This lemma captures the key insight that stuttering bisimulation extends to
terminating executions.
-/
theorem joint_trace_simulation (L : SecurityLevel)
    (h_step : step_consistent L)
    (h_conf : step_confinement L)
    {s1 s2 sf1 sf2 : State}
    (heq : low_equivalent L s1 s2)
    (t1 : Trace s1 sf1)
    (h_nd1 : t1.no_declassify)
    (h_stuck1 : ∀ s'', Step sf1 s'' → False)
    (t2 : Trace s2 sf2)
    (h_nd2 : t2.no_declassify)
    (h_stuck2 : ∀ s'', Step sf2 s'' → False) :
    low_equivalent L sf1 sf2 := by
  -- Induction on t1, generalizing all variables that depend on the changing states
  -- sf1 must be generalized because h_stuck1's type depends on it implicitly via t1
  induction t1 generalizing s2 sf2 t2 with
  | nil =>
    -- t1 : Trace s1 s1 (nil trace), so here sf1 was unified with s1
    -- h_stuck1 : ∀ s'', Step s1 s'' → False (s1 is stuck)
    -- heq : low_equivalent L s1 s2
    -- We need: low_equivalent L s1 sf2
    -- Since s1 is stuck and s1 ≈_L s2, all steps in t2 must be high
    exact high_trace_preserves_equiv L h_step h_conf _ h_stuck1 t2 h_nd2 heq
  | @cons s1_start s1_mid sf1_end st1 rest1 ih =>
    -- t1 = cons st1 rest1 where st1 : Step s1_start s1_mid, rest1 : Trace s1_mid sf1_end
    have ⟨h_st1_nd, h_rest1_nd⟩ := h_nd1
    -- Case split on t2
    cases t2 with
    | nil =>
      -- t2 : Trace s2 s2 (nil trace), so sf2 was unified with s2
      -- h_stuck2 : ∀ s'', Step s2 s'' → False (s2 is stuck from start)
      -- Since s2 is stuck and s1_start ≈_L s2, all steps from s1 must be high
      have heq_sym : low_equivalent L s2 s1_start := low_equivalent_symm heq
      have h_high := any_step_from_stuck_equiv_is_high L h_step heq_sym h_stuck2 st1 h_st1_nd
      -- After high step, equivalence is preserved: s2 ≈_L s1_mid
      have heq' := high_step_preserves_full_low_equiv L h_conf heq_sym st1 h_st1_nd h_high
      -- rest1 goes from s1_mid to sf1_end, all steps high because s2 stuck
      have heq'' : low_equivalent L s2 sf1_end :=
        high_trace_preserves_equiv L h_step h_conf _ h_stuck2 rest1 h_rest1_nd heq'
      exact low_equivalent_symm heq''
    | cons st2 rest2 =>
      -- Both traces have steps: t2 = cons st2 rest2
      -- st2 : Step s2 s2_mid for some s2_mid, rest2 : Trace s2_mid sf2
      have ⟨h_st2_nd, h_rest2_nd⟩ := h_nd2

      -- Case split on whether st1 is low or high
      by_cases h_st1_low : is_low_step L st1
      case neg =>
        -- st1 is HIGH: stutter on s2, continue with full t2
        have h_st1_high : is_high_step L st1 := by
          simp only [is_high_step, is_low_step] at *
          exact lt_of_not_ge h_st1_low
        have h_conf_st1 := h_conf s1_start s1_mid st1 h_st1_high
        have hmono := high_step_no_downgrade L st1 h_st1_high h_st1_nd
        have heq' : low_equivalent L s1_mid s2 := by
          constructor
          · exact high_step_preserves_low_equiv_trans L hmono h_conf_st1 heq.1
          · exact low_equivalent_left_trans heq.2 h_conf_st1
        exact ih heq' h_rest1_nd h_stuck1 (Trace.cons st2 rest2) ⟨h_st2_nd, h_rest2_nd⟩ h_stuck2
      case pos =>
        -- st1 is LOW: get matching step via low_step_match_same_type
        -- Note: now includes is_low_step L st_match directly in return type
        have h_match := low_step_match_same_type L h_step heq st1 h_st1_low
        obtain ⟨s2_match, st_match, h_match_low, h_same_declass, heq_match⟩ := h_match
        have h_match_nd : st_match.is_declassify = false := by rw [h_same_declass, h_st1_nd]

        -- Now case split on whether st2 is low or high
        by_cases h_st2_low : is_low_step L st2
        case pos =>
          -- st2 is LOW: use determinism to show s2_match = s2_mid
          -- h_match_low already available from low_step_match_same_type
          -- Now apply determinism: st_match and st2 are both low non-declass from s2
          have h_eq_dest : s2_match = _ := low_step_deterministic L st_match st2
            h_match_low h_st2_low (by rw [h_match_nd, h_st2_nd])
          -- Substitute and apply IH
          subst h_eq_dest
          exact ih heq_match h_rest1_nd h_stuck1 rest2 h_rest2_nd h_stuck2
        case neg =>
          -- st2 is HIGH: scan rest2 for the first LOW step to match st1
          -- This is the standard "stutter on the right" approach.
          have h_st2_high : is_high_step L st2 := by
            simp only [is_high_step, is_low_step] at *
            exact lt_of_not_ge h_st2_low

          -- High step preserves equivalence: s1 ≈_L s2 → s1 ≈_L s2_mid
          -- high_step_preserves_full_low_equiv takes (heq : L sf s) (st : Step s s')
          -- and gives (L sf s'), so we use heq directly with st2
          have heq_s1_s2mid : low_equivalent L s1_start _ :=
            high_step_preserves_full_low_equiv L h_conf heq st2 h_st2_nd h_st2_high

          -- Scan rest2 looking for the first LOW step
          -- This is structural recursion on the trace
          let rec scanRight :
              ∀ {s2cur sf2} (t2cur : Trace s2cur sf2),
              low_equivalent L s1_start s2cur →
              t2cur.no_declassify →
              (∀ s'', Step sf2 s'' → False) →
              low_equivalent L sf1_end sf2 := fun t2cur heq_cur h_nd2_cur h_stuck2_cur => by
            cases t2cur with
            | nil =>
              -- t2 ended but st1 was LOW - need matching step, contradiction
              -- low_step_match_same_type says s2cur must have a step
              have h_match_cur := low_step_match_same_type L h_step heq_cur st1 h_st1_low
              obtain ⟨_, st_cur, _, _, _⟩ := h_match_cur
              -- But s2cur = sf2 and sf2 is stuck
              exact False.elim (h_stuck2_cur _ st_cur)
            | cons st2cur rest2cur =>
              have ⟨h_st2cur_nd, h_rest2cur_nd⟩ := h_nd2_cur
              by_cases h_st2cur_low : is_low_step L st2cur
              case pos =>
                -- Found a LOW step! Use determinism to match st1
                have h_match_cur := low_step_match_same_type L h_step heq_cur st1 h_st1_low
                obtain ⟨s2match_cur, st_match_cur, h_match_cur_low, h_same_declass_cur, heq_match_cur⟩ := h_match_cur
                have h_match_cur_nd : st_match_cur.is_declassify = false := by
                  rw [h_same_declass_cur, h_st1_nd]
                -- Determinism: st_match_cur and st2cur both low non-declass from s2cur
                -- h_match_cur_low already available from low_step_match_same_type
                have h_eq_dest_cur : s2match_cur = _ := low_step_deterministic L st_match_cur st2cur
                  h_match_cur_low h_st2cur_low (by rw [h_match_cur_nd, h_st2cur_nd])
                -- Now apply outer IH
                subst h_eq_dest_cur
                exact ih heq_match_cur h_rest1_nd h_stuck1 rest2cur h_rest2cur_nd h_stuck2_cur
              case neg =>
                -- Another HIGH step, continue scanning
                have h_st2cur_high : is_high_step L st2cur := by
                  simp only [is_high_step, is_low_step] at *
                  exact lt_of_not_ge h_st2cur_low
                -- heq_cur : s1_start ≈_L s2cur, st2cur : Step s2cur s2cur_next
                -- high_step_preserves_full_low_equiv gives s1_start ≈_L s2cur_next
                have heq_next : low_equivalent L s1_start _ :=
                  high_step_preserves_full_low_equiv L h_conf heq_cur st2cur h_st2cur_nd h_st2cur_high
                exact scanRight rest2cur heq_next h_rest2cur_nd h_stuck2_cur

          -- Apply scanRight to rest2
          exact scanRight rest2 heq_s1_s2mid h_rest2_nd h_stuck2

/-! =========== PART 14: MAIN TINI THEOREM =========== -/

/--
**TINI Noninterference (Main Theorem)**

If two states are L-equivalent and both executions terminate WITHOUT declassification,
then the final states are also L-equivalent.

This theorem converts the previous axiom TINI_noninterference to a proven theorem
using the stuttering bisimulation infrastructure developed above.

The proof uses joint_trace_simulation which maintains equivalence across both
terminating traces via joint induction.
-/
theorem TINI_noninterference_thm (L : SecurityLevel)
    (_h_output : output_consistent L)
    (h_step : step_consistent L)
    (h_conf : step_confinement L)
    (s1 s2 : State)
    (heq : low_equivalent L s1 s2)
    (h_term1 : TerminatesNoDeclass s1)
    (h_term2 : TerminatesNoDeclass s2) :
    ∃ sf1 sf2 : State,
      ReachableNoDeclass s1 sf1 ∧
      ReachableNoDeclass s2 sf2 ∧
      (∀ s'', Step sf1 s'' → False) ∧
      (∀ s'', Step sf2 s'' → False) ∧
      low_equivalent L sf1 sf2 := by
  -- Extract the terminating states and traces
  obtain ⟨sf1, ⟨t1, h_nd1⟩, h_stuck1⟩ := h_term1
  obtain ⟨sf2, ⟨t2, h_nd2⟩, h_stuck2⟩ := h_term2

  -- Apply joint trace simulation
  have heq_final := joint_trace_simulation L h_step h_conf heq t1 h_nd1 h_stuck1 t2 h_nd2 h_stuck2

  -- Assemble the witnesses
  exact ⟨sf1, sf2, ⟨t1, h_nd1⟩, ⟨t2, h_nd2⟩, h_stuck1, h_stuck2, heq_final⟩

/-! =========== SUMMARY =========== -/

/-
STATUS: Infrastructure complete - all sorries resolved.

PROVEN INFRASTRUCTURE:
- Star: Generic reflexive-transitive closure with trans, single, cons
- StepND: Non-declassification steps (Type-valued for field access)
- HasStepND: Propositional wrapper (Nonempty StepND)
- StutterReachND: Star HasStepND (stuttering reachability)
- LStutterSim: One-sided stuttering simulation property
- StuckND, LowStuck: Stuck state definitions
- trace_to_stutter_reach: Convert Trace to StutterReachND
- trace_stutter_lift: Trace lifting lemma (key for TINI)
- single_step_TINI_strong: Strengthened single-step with reachability witness
- LStutterSim_of_unwinding: Simulation follows from unwinding conditions
- high_star_preserves_low_equiv: High-step traces preserve low equivalence

KEY LEMMAS:
- no_low_step_of_stuck_left: Stuck left + low-equiv → no low steps on right
- stuck_forces_high_steps: Stuck left → all right steps are high
- stuck_implies_low_stuck: Stuck left → right is low-stuck

ALL SORRIES RESOLVED:

1. Declassify case (stuck_implies_low_stuck): Fixed by updating LowStuck definition
   to exclude declassify steps (matching StuckND behavior)

2. Non-declass preservation (no_low_step_of_stuck_left, single_step_TINI_strong):
   Fixed via step_consistent_nd which uses the type preservation theorem

3. High step symmetry (single_step_TINI_strong): Uses low_equivalent_left_trans

AXIOM → THEOREM CONVERSIONS (2026-01-01):
- low_step_match_same_type: NOW THEOREM, derived from strengthened step_consistent
  which returns is_low_step L st2 and st2.is_declassify = st1.is_declassify.
- low_step_match_level: ELIMINATED (subsumed by low_step_match_same_type).
  The theorem now returns is_low_step L st2 directly, making this unnecessary.
- step_consistent_implies_nd: NOW THEOREM, trivially derived from strengthened
  step_consistent via low_step_match_same_type.

REMAINING AXIOM:
- low_step_deterministic: Low steps from same source with same is_declassify
  have the same destination. This is a semantic property of the step relation
  that encodes deterministic execution of low-observable operations.
  Per consultation: could be weakened to "deterministic by label" but kept
  as TCB assumption for now.

APPROACH: Strengthened step_consistent signature (NoninterferenceBase.lean)
  Old: ∃ s2', (Nonempty (Step s2 s2')) ∧ low_equivalent L s1' s2'
  New: ∃ s2' (st2 : Step s2 s2'),
         is_low_step L st2 ∧
         st2.is_declassify = st1.is_declassify ∧
         low_equivalent L s1' s2'
  This captures that matching steps preserve operation type AND level.

LOC: ~400 lines of infrastructure
-/

/-! =========== PART 14: TINI NONINTERFERENCE THEOREM =========== -/

/--
**TINI Noninterference Theorem**

The main termination-insensitive noninterference theorem.
Derived from joint_trace_simulation by extracting traces from
TerminatesNoDeclass witnesses.

This was previously an axiom in Noninterference.lean, now proven
via the stuttering bisimulation infrastructure.
-/
theorem TINI_noninterference (L : SecurityLevel)
    (h_output : output_consistent L)
    (h_step : step_consistent L)
    (h_conf : step_confinement L)
    (s1 s2 : State)
    (heq : low_equivalent L s1 s2)
    (h_term1 : TerminatesNoDeclass s1)
    (h_term2 : TerminatesNoDeclass s2) :
    ∃ sf1 sf2 : State,
      ReachableNoDeclass s1 sf1 ∧
      ReachableNoDeclass s2 sf2 ∧
      (∀ s'', Step sf1 s'' → False) ∧
      (∀ s'', Step sf2 s'' → False) ∧
      low_equivalent L sf1 sf2 := by
  -- Extract concrete traces from termination witnesses
  rcases h_term1 with ⟨sf1, ⟨t1, h_nd1⟩, h_stuck1⟩
  rcases h_term2 with ⟨sf2, ⟨t2, h_nd2⟩, h_stuck2⟩
  -- Apply joint_trace_simulation
  have heq_final := joint_trace_simulation L h_step h_conf heq t1 h_nd1 h_stuck1 t2 h_nd2 h_stuck2
  -- Package result
  exact ⟨sf1, sf2, ⟨t1, h_nd1⟩, ⟨t2, h_nd2⟩, h_stuck1, h_stuck2, heq_final⟩

end Lion.Stuttering
