/-
Lion/Theorems/NoninterferenceBase.lean
======================================

Base definitions shared by Noninterference and StutteringBisimulation.

Extracted to break the import cycle:
  NoninterferenceBase -> StutteringBisimulation -> Noninterference

This file contains:
- Trace type and predicates
- Security level classification (is_low_step, is_high_step)
- Unwinding condition definitions
- Termination predicates

No axioms or theorems that require StutteringBisimulation.
-/

import Lion.State.State
import Lion.Step.Step

namespace Lion.Noninterference

open Lion

/-! =========== PART 1: EXECUTION MODEL =========== -/

/--
An execution trace is a sequence of states connected by steps.
-/
inductive Trace : State → State → Type where
  | nil (s : State) : Trace s s
  | cons {s s' s'' : State} : Step s s' → Trace s' s'' → Trace s s''

/-- Length of a trace -/
def Trace.length {s s' : State} : Trace s s' → Nat
  | .nil _ => 0
  | .cons _ t => 1 + t.length

/-- A trace contains no declassify steps -/
def Trace.no_declassify {s s' : State} : Trace s s' → Prop
  | .nil _ => True
  | .cons st t => st.is_declassify = false ∧ t.no_declassify

/-- Reachability without declassification -/
def ReachableNoDeclass (s s' : State) : Prop :=
  ∃ t : Trace s s', t.no_declassify

/-- Termination without declassification steps -/
def TerminatesNoDeclass (s : State) : Prop :=
  ∃ s', ReachableNoDeclass s s' ∧ (∀ s'', Step s' s'' → False)

/-! =========== PART 2: STEP SECURITY CLASSIFICATION =========== -/

/--
Security level of a step: determined by the executing plugin's level.
Kernel steps are treated as Secret (highest level, trusted).
-/
def step_level {s s' : State} (st : Step s s') : SecurityLevel :=
  st.level

/--
A step is "low" (visible to level L observer) if step_level <= L.
-/
def is_low_step (L : SecurityLevel) {s s' : State} (st : Step s s') : Prop :=
  step_level st ≤ L

/--
A step is "high" (invisible to level L observer) if step_level > L.
-/
def is_high_step (L : SecurityLevel) {s s' : State} (st : Step s s') : Prop :=
  step_level st > L

/-! =========== PART 3: UNWINDING CONDITIONS =========== -/

/--
**Output Consistency**: L-equivalent states produce L-equivalent observations.

If two states look the same at level L, any output visible at level L
must be identical.
-/
def output_consistent (L : SecurityLevel) : Prop :=
  ∀ (s1 s2 : State),
    low_equivalent L s1 s2 →
    -- For any low-level plugin observation
    ∀ pid, (s1.plugins pid).level ≤ L →
      s1.plugins pid = s2.plugins pid

/--
**Step Consistency (Local Respect)**: L-equivalent states step to
L-equivalent states when the step is L-visible.

This ensures that low-level computations behave identically on
L-equivalent states.

**Strengthened form** (2026-01-01): Returns the matching step explicitly with
its low-ness and declassify-type preservation. This eliminates the need for
separate `low_step_match_same_type` and `low_step_match_level` axioms.

Rationale: When s1 and s2 are L-equivalent and st1 is a low step:
1. Low plugins have identical state in both (by low_equivalent)
2. The matching step st2 operates on identical low plugin state
3. Therefore st2 has the same operation type (same is_declassify)
4. And st2 is also low (same plugin level)

This captures the semantic invariant that was previously axiomized.
-/
def step_consistent (L : SecurityLevel) : Prop :=
  ∀ (s1 s2 s1' : State),
    low_equivalent L s1 s2 →
    ∀ (st1 : Step s1 s1'),
      is_low_step L st1 →
      ∃ (s2' : State) (st2 : Step s2 s2'),
        is_low_step L st2 ∧
        st2.is_declassify = st1.is_declassify ∧
        low_equivalent L s1' s2'

/--
**Step Confinement**: High steps preserve L-equivalence of the original state.

When a high-security step executes, it cannot modify any low-security
observable state. The post-state remains L-equivalent to the pre-state.
-/
def step_confinement (L : SecurityLevel) : Prop :=
  ∀ (s s' : State),
    ∀ (st : Step s s'),
      is_high_step L st →
      low_equivalent_left L s s'

/-! =========== PART 4: LABEL PROPERTIES =========== -/

/--
**Labels No Downgrade Property**

Labels do not downgrade from s to s'. (Monotone "upward" in security level).
This is the bridge property needed to prove transitivity of low-equivalence
across high steps.
-/
def labels_no_downgrade (s s' : State) : Prop :=
  (∀ pid, (s.plugins pid).level ≤ (s'.plugins pid).level) ∧
  (∀ rid, (s.resources rid).level ≤ (s'.resources rid).level)

/-! =========== PART 5: LABEL PRESERVATION THEOREMS =========== -/

/--
**Step Labels No Downgrade (Non-Declassify)**

For non-declassify steps, plugin and resource levels never decrease.
This is provable from the frame theorems:
- plugin_internal: level preserved exactly
- host_call (non-declassify): caller level preserved, others unchanged
- kernel_internal: all plugins unchanged

Resources are always unchanged by all step types.
-/
theorem step_labels_no_downgrade {s s' : State} (st : Step s s')
    (h_not_declass : st.is_declassify = false) :
    labels_no_downgrade s s' := by
  constructor
  -- Plugin levels: show (s.plugins pid).level ≤ (s'.plugins pid).level
  · intro pid
    cases st with
    | plugin_internal pid' pi hpre hexec =>
      by_cases h_eq : pid = pid'
      · subst h_eq
        exact le_of_eq (plugin_internal_level_preserved pid pi s s' hexec).symm
      · have : s'.plugins pid = s.plugins pid := plugin_internal_frame pid' pi s s' hexec pid h_eq
        simp only [this, le_refl]
    | host_call hc a auth hr hparse hpre hexec =>
      by_cases h_eq : pid = hc.caller
      · subst h_eq
        -- Convert Bool = false to ≠
        have h_neq : hc.function ≠ .declassify := by
          simp only [Step.is_declassify] at h_not_declass
          exact fun h => by simp [h] at h_not_declass
        exact le_of_eq (host_call_caller_level_preserved hc a auth hr s s' h_neq hexec).symm
      · have : s'.plugins pid = s.plugins pid := host_call_plugin_frame hc a auth hr s s' hexec pid h_eq
        simp only [this, le_refl]
    | kernel_internal op hexec =>
      cases op with
      | time_tick =>
        have ⟨_, h_plugins, _⟩ := time_tick_only_time s s' hexec
        simp only [congrFun h_plugins pid, le_refl]
      | route_one dst =>
        simp only [congrFun (route_one_memory_unchanged dst s s' hexec) pid, le_refl]
      | workflow_tick wid =>
        simp only [congrFun (workflow_tick_plugins_unchanged wid s s' hexec) pid, le_refl]
      | unblock_send dst =>
        simp only [congrFun (unblock_send_plugins_unchanged dst s s' hexec) pid, le_refl]
  -- Resource levels: show (s.resources rid).level ≤ (s'.resources rid).level
  · intro rid
    cases st with
    | plugin_internal pid pi hpre hexec =>
      have : s'.resources = s.resources := plugin_internal_resources_unchanged pid pi s s' hexec
      simp only [this, le_refl]
    | host_call hc a auth hr hparse hpre hexec =>
      have : s'.resources = s.resources := host_call_resources_unchanged hc a auth hr s s' hexec
      simp only [this, le_refl]
    | kernel_internal op hexec =>
      cases op with
      | time_tick =>
        have : s'.resources = s.resources := (time_tick_comprehensive_frame s s' hexec).2.2.2.1
        simp only [congrFun this rid, le_refl]
      | route_one dst =>
        simp only [congrFun (route_one_resource_unchanged dst s s' hexec) rid, le_refl]
      | workflow_tick wid =>
        simp only [congrFun (workflow_tick_resources_unchanged wid s s' hexec) rid, le_refl]
      | unblock_send dst =>
        simp only [congrFun (unblock_send_resources_unchanged dst s s' hexec) rid, le_refl]

/--
**High steps do not downgrade labels (Non-Declassify)**

For non-declassify high steps, labels never decrease.
Declassify is intentional declassification and handled separately.

Previously axiom, now theorem via step_labels_no_downgrade.
-/
theorem high_step_no_downgrade (L : SecurityLevel)
    {s s' : State} (st : Step s s')
    (h_high : is_high_step L st)
    (h_not_declass : st.is_declassify = false) :
    labels_no_downgrade s s' :=
  step_labels_no_downgrade st h_not_declass

/--
**Theorem (High Step Preserves Low Equiv Transitivity)**

If s1' low-agrees with s1, and s1 low-agrees with s2,
then s1' low-agrees with s2.

This follows from the fact that high steps preserve plugin/resource levels,
so low-ness in s1' implies low-ness in s1.

Previously axiom, now theorem via labels_no_downgrade bridge.
-/
theorem high_step_preserves_low_equiv_trans (L : SecurityLevel)
    {s1 s1' s2 : State}
    (hmono : labels_no_downgrade s1 s1')
    (h11' : low_equivalent_left L s1 s1')
    (h12 : low_equivalent_left L s1 s2) :
    low_equivalent_left L s1' s2 := by
  constructor
  · intro pid hlow'
    -- low in s1' implies low in s1 by monotonicity (no downgrade)
    have hlow1 : (s1.plugins pid).level ≤ L := le_trans (hmono.1 pid) hlow'
    have eq11' : s1.plugins pid = s1'.plugins pid := h11'.1 pid hlow1
    have eq12 : s1.plugins pid = s2.plugins pid := h12.1 pid hlow1
    exact eq11'.symm.trans eq12
  · intro rid hlow'
    have hlow1 : (s1.resources rid).level ≤ L := le_trans (hmono.2 rid) hlow'
    have eq11' : s1.resources rid = s1'.resources rid := h11'.2 rid hlow1
    have eq12 : s1.resources rid = s2.resources rid := h12.2 rid hlow1
    exact eq11'.symm.trans eq12

end Lion.Noninterference
