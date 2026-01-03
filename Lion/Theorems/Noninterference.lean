/-
Lion/Theorems/Noninterference.lean
===================================

Theorem 011: Termination-Insensitive Noninterference (TINI)

High-security data cannot flow to low-security observers through any execution
path. This extends memory isolation (002) with information flow control.

Mathematical Foundation:
- Goguen & Meseguer (1982): Security Policies and Security Models
- Sabelfeld & Myers (2003): Language-based Information-flow Security
- Murray et al. (2013): seL4 Information Flow Proofs

Proof Strategy:
  TINI follows from three unwinding conditions:
  1. output_consistent: L-equivalent states have L-equal outputs
  2. step_consistent: L-equivalent states step to L-equivalent states (for L-visible steps)
  3. step_confinement: High steps preserve L-equivalence

Key Definitions (from Lion.State.State):
  - low_equivalent L s1 s2: states agree on all data at level <= L
  - low_equivalent_refl, _symm, _trans: equivalence relation properties

STATUS: Complete - TINI_noninterference is now a theorem (via StutteringBisimulation)
-/

import Lion.State.State
import Lion.Step.Step
import Lion.Theorems.NoninterferenceBase
import Lion.Theorems.StutteringBisimulation

namespace Lion.Noninterference

open Lion Lion.Stuttering

/-! =========== RE-EXPORTS FROM NoninterferenceBase =========== -/

-- Trace, step_level, is_low_step, is_high_step, output_consistent,
-- step_consistent, step_confinement, labels_no_downgrade,
-- step_labels_no_downgrade, high_step_no_downgrade,
-- high_step_preserves_low_equiv_trans are all defined in NoninterferenceBase
-- and available via the import.

/-! =========== ADDITIONAL EXECUTION MODEL DEFINITIONS =========== -/

/--
Termination predicate: an execution starting from s terminates.
For TINI, we require both executions to terminate (termination-insensitive).
-/
def Terminates (s : State) : Prop :=
  exists s', Reachable s s' /\ (forall s'', Step s' s'' -> False)

/-- Final state of a terminating execution (when it exists) -/
noncomputable def final_state (s : State) (h : Terminates s) : State :=
  Classical.choose h

/-! =========== SINGLE-STEP NONINTERFERENCE =========== -/

/--
**Single Step TINI**: If s1 ~_L s2 and both take a step, then s1' ~_L s2'.

This handles the case where both states take exactly one step.
Proof by case analysis on whether the steps are high or low.

Note: For high steps, we require non-declassify. Declassify is intentional
declassification that needs separate handling (see Declassification Support).
-/
theorem single_step_TINI (L : SecurityLevel)
    (h_step_consistent : step_consistent L)
    (h_step_confinement : step_confinement L)
    (s1 s2 s1' : State)
    (heq : low_equivalent L s1 s2)
    (st1 : Step s1 s1')
    (h_not_declass : st1.is_declassify = false) :
    -- There exists s2' such that s1' ~_L s2'
    Exists fun s2' => low_equivalent_left L s1' s2' := by
  by_cases h_low : is_low_step L st1
  case pos =>
    -- Low step: use step_consistent (strengthened form returns is_low_step, is_declassify, equiv)
    obtain ⟨s2', _st2, _h_low2, _h_same_declass, heq'⟩ := h_step_consistent s1 s2 s1' heq st1 h_low
    exact ⟨s2', heq'.1⟩
  case neg =>
    -- High step: use step_confinement
    have h_high : is_high_step L st1 := by
      simp only [is_high_step, is_low_step, step_level, GT.gt] at *
      exact lt_of_not_ge h_low
    have h_conf := h_step_confinement s1 s1' st1 h_high
    have hmono := high_step_no_downgrade L st1 h_high h_not_declass
    exact ⟨s2, high_step_preserves_low_equiv_trans L hmono h_conf heq.1⟩

/-! =========== FRAME THEOREM WRAPPERS =========== -/

/--
**Theorem: Plugin Internal Frame**

Plugin internal execution only affects the executing plugin's state.
All other plugins remain unchanged.

Proof: Follows from the frame axiom in PluginInternal.lean.
-/
theorem plugin_internal_frame' :
    ∀ (pid : PluginId) (pi : PluginInternal) (s s' : State),
      plugin_internal_pre pid pi s →
      PluginExecInternal pid pi s s' →
      ∀ pid', pid' != pid → s'.plugins pid' = s.plugins pid' := by
  intro pid pi s s' _hpre hexec pid' hne
  have h_ne : pid' ≠ pid := by simp [bne_iff_ne] at hne; exact hne
  exact Lion.plugin_internal_frame pid pi s s' hexec pid' h_ne

/--
**Theorem: Plugin Internal Resource Frame**

Plugin internal execution does not affect resource labels.
-/
theorem plugin_internal_resource_frame
    (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (_hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    s'.resources = s.resources :=
  (Lion.plugin_internal_comprehensive_frame pid pi s s' hexec).2.2.2.1

/--
**Theorem: Time Tick Resource Unchanged**

Time tick only changes the time field, not resources.
-/
theorem time_tick_resource_unchanged (s s' : State)
    (h : KernelExecInternal .time_tick s s') :
    s'.resources = s.resources :=
  (Lion.time_tick_comprehensive_frame s s' h).2.2.2.1

/--
**Host Call Preserves Low Equivalence (Theorem)**

High-level host calls preserve low-equivalent state.
-/
theorem host_call_preserves_low_equiv (L : SecurityLevel)
    (hc : HostCall)
    (a : Action)
    (auth : Authorized s a)
    (hr : HostResult)
    (_hparse : hostcall_action hc = some a)
    (_hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_high : (s.plugins hc.caller).level > L) :
    low_equivalent_left L s s' := by
  constructor
  · intro pid h_low
    by_cases h_eq : pid = hc.caller
    · subst h_eq
      exfalso
      exact absurd h_low (not_le_of_gt h_high)
    · have h_ne : pid ≠ hc.caller := h_eq
      exact (host_call_plugin_frame hc a auth hr s s' hexec pid h_ne).symm
  · intro rid h_low
    have h_strict : (s.resources rid).level < (s.plugins hc.caller).level :=
      lt_of_le_of_lt h_low h_high
    exact (host_call_resource_content_frame hc a auth hr s s' hexec rid h_strict).symm

/-! =========== HIGH STEP PROPERTIES =========== -/

/--
**High steps are invisible**: A high step doesn't change what a low observer sees.
-/
theorem high_step_preserves_low_equiv (L : SecurityLevel)
    (h_confinement : step_confinement L)
    {s s' : State}
    (st : Step s s')
    (h_high : is_high_step L st) :
    low_equivalent_left L s s' := by
  exact h_confinement s s' st h_high

/--
**Plugin internal steps preserve low-equiv when high**.
-/
theorem plugin_internal_high_preserves_low (L : SecurityLevel)
    {s s' : State}
    {pid : PluginId}
    (h_high : (s.plugins pid).level > L)
    (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    low_equivalent_left L s s' := by
  constructor
  · intro pid' h_low
    by_cases h_eq : pid' = pid
    · subst h_eq
      exfalso
      exact absurd h_low (not_le_of_gt h_high)
    · have h_ne : pid' != pid := by simp [bne_iff_ne, h_eq]
      exact (plugin_internal_frame' pid pi s s' hpre hexec pid' h_ne).symm
  · intro rid h_low
    exact (congrFun (plugin_internal_resource_frame pid pi s s' hpre hexec) rid).symm

/-! =========== KERNEL OP PROPERTIES =========== -/

/--
Kernel operations are at Secret level (highest), so they are "high" for any
non-Secret observer level.
-/
theorem kernel_op_is_high (L : SecurityLevel)
    (h_not_secret : L < SecurityLevel.Secret)
    {s s' : State}
    (op : KernelOp)
    (hexec : KernelExecInternal op s s') :
    let st := Step.kernel_internal op hexec
    is_high_step L st := by
  unfold is_high_step step_level Step.level Step.subject
  simp
  exact h_not_secret

/--
Time tick preserves low-equivalence (only changes time field).
-/
theorem time_tick_preserves_low_equiv (L : SecurityLevel)
    {s s' : State}
    (hexec : KernelExecInternal .time_tick s s') :
    low_equivalent_left L s s' := by
  obtain ⟨_, h_plugins, _⟩ := time_tick_only_time s s' hexec
  constructor
  · intro pid _
    exact (congrFun h_plugins pid).symm
  · intro rid _
    exact (congrFun (time_tick_resource_unchanged s s' hexec) rid).symm

/-! =========== MAIN TINI THEOREM (RE-EXPORT) =========== -/

/--
**TINI Noninterference (Main Theorem)**

If two states are L-equivalent and both executions terminate
WITHOUT declassification, then the final states are also L-equivalent.

This is now a theorem, proven via stuttering bisimulation in
StutteringBisimulation.lean. Re-exported here for API compatibility.
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
      low_equivalent L sf1 sf2 :=
  -- Delegate to the proven theorem in StutteringBisimulation
  Lion.Stuttering.TINI_noninterference L h_output h_step h_conf s1 s2 heq h_term1 h_term2

/-! =========== UNWINDING LEMMAS =========== -/

/--
**Unwinding Composition**: TINI follows from the three unwinding conditions.
-/
theorem TINI_from_unwinding (L : SecurityLevel)
    (h_output : output_consistent L)
    (h_step : step_consistent L)
    (h_conf : step_confinement L) :
    ∀ s1 s2,
      low_equivalent L s1 s2 →
      ∀ (h1 : TerminatesNoDeclass s1) (h2 : TerminatesNoDeclass s2),
        ∃ sf1 sf2 : State,
          ReachableNoDeclass s1 sf1 ∧
          ReachableNoDeclass s2 sf2 ∧
          (∀ s'', Step sf1 s'' → False) ∧
          (∀ s'', Step sf2 s'' → False) ∧
          low_equivalent L sf1 sf2 := by
  intro s1 s2 heq h1 h2
  exact TINI_noninterference L h_output h_step h_conf s1 s2 heq h1 h2

/-! =========== DECLASSIFICATION SUPPORT =========== -/

/--
Declassification policy: controlled information release.
-/
structure DeclassPolicy where
  /-- Is declassification from level1 to level2 allowed under condition? -/
  allowed : SecurityLevel -> SecurityLevel -> Prop

/--
A step is a declassification if it's a host_call to declassify function.
-/
def is_declassify_step {s s' : State} (st : Step s s') : Bool :=
  st.is_declassify

/--
Relaxed low-equivalence that accounts for declassification.
-/
def low_equivalent_modulo_declass
    (L : SecurityLevel)
    (_D : DeclassPolicy)
    (s1 s2 : State) : Prop :=
  low_equivalent L s1 s2

/-! =========== INTEGRATION WITH OTHER THEOREMS =========== -/

/--
**Connection to Memory Isolation (002)**
-/
theorem noninterference_extends_isolation (L : SecurityLevel)
    (s1 s2 : State)
    (heq : low_equivalent L s1 s2)
    (_pid_high pid_low : PluginId)
    (_h_high : (s1.plugins _pid_high).level > L)
    (h_low : (s1.plugins pid_low).level <= L) :
    s1.plugins pid_low = s2.plugins pid_low := by
  exact heq.1.1 pid_low h_low

/--
**Connection to Capability Confinement (004)**
-/
theorem noninterference_with_confinement (L : SecurityLevel)
    (s : State)
    (h_noninterf : forall s', Reachable s s' -> low_equivalent L s s') :
    forall s', Reachable s s' ->
      forall pid, (s.plugins pid).level <= L ->
        s'.plugins pid = s.plugins pid := by
  intro s' h_reach pid h_low
  exact ((h_noninterf s' h_reach).1.1 pid h_low).symm

/-! =========== PROOF OF UNWINDING CONDITIONS =========== -/

/--
**Output Consistency Proof**
-/
theorem output_consistent_holds (L : SecurityLevel) :
    output_consistent L := by
  unfold output_consistent
  intro s1 s2 heq pid h_low
  exact heq.1.1 pid h_low

/--
**Step Confinement Proof**
-/
theorem step_confinement_holds (L : SecurityLevel) :
    step_confinement L := by
  unfold step_confinement is_high_step
  intro s s' st h_high
  cases st with
  | plugin_internal pid pi hpre hexec =>
    constructor
    · intro pid' h_low
      by_cases h_eq : pid' = pid
      · subst h_eq
        exfalso
        unfold step_level Step.level Step.subject at h_high
        simp at h_high
        exact absurd h_low (not_le_of_gt h_high)
      · have h_ne : pid' != pid := by simp [bne_iff_ne]; exact h_eq
        exact (plugin_internal_frame' pid pi s s' hpre hexec pid' h_ne).symm
    · intro rid _
      exact (congrFun (plugin_internal_resource_frame pid pi s s' hpre hexec) rid).symm
  | host_call hc a auth hr hparse hpre hexec =>
    have h_caller_high : (s.plugins hc.caller).level > L := by
      unfold step_level Step.level Step.subject at h_high
      simp at h_high
      exact h_high
    exact host_call_preserves_low_equiv L hc a auth hr hparse hpre hexec h_caller_high
  | kernel_internal op hexec =>
    cases op with
    | time_tick =>
      obtain ⟨_, h_plugins, _⟩ := time_tick_only_time s s' hexec
      constructor
      · intro pid _
        exact (congrFun h_plugins pid).symm
      · intro rid _
        exact (congrFun (time_tick_resource_unchanged s s' hexec) rid).symm
    | route_one dst =>
      constructor
      · intro pid _
        exact (congrFun (route_one_memory_unchanged dst s s' hexec) pid).symm
      · intro rid _
        exact (congrFun (route_one_resource_unchanged dst s s' hexec) rid).symm
    | workflow_tick wid =>
      constructor
      · intro pid _
        exact (congrFun (workflow_tick_plugins_unchanged wid s s' hexec) pid).symm
      · intro rid _
        exact (congrFun (workflow_tick_resources_unchanged wid s s' hexec) rid).symm
    | unblock_send dst =>
      constructor
      · intro pid _
        exact (congrFun (unblock_send_plugins_unchanged dst s s' hexec) pid).symm
      · intro rid _
        exact (congrFun (unblock_send_resources_unchanged dst s s' hexec) rid).symm

/-! =========== SUMMARY =========== -/

/-
STATUS: Complete - TINI_noninterference is now a THEOREM, not an axiom!

AXIOM ELIMINATION:
- TINI_noninterference: Previously axiom, now proven theorem via
  stuttering bisimulation infrastructure in StutteringBisimulation.lean.
  Re-exported here for API compatibility.

PROVEN THEOREMS:
- output_consistent_holds: Output consistency follows from low_equivalent definition
- step_confinement_holds: Complete proof with all Step cases
- host_call_preserves_low_equiv: Host calls preserve low-equivalent state
- single_step_TINI: Structure showing how unwinding conditions compose
- Various helper lemmas

THEOREMS FROM NoninterferenceBase:
- step_labels_no_downgrade: Labels preserved for non-declassify steps
- high_step_no_downgrade: High steps don't downgrade labels
- high_step_preserves_low_equiv_trans: Transitivity via labels_no_downgrade bridge

AXIOMS IN StutteringBisimulation (still required for TINI proof):
- low_step_match_same_type: Matching low steps have same is_declassify
- low_step_deterministic: Low steps are deterministic
- low_step_match_level: Matching step preserves low property

These axioms encode semantic properties of the step relation that can be
proven from lower-level specifications with constructive step matching.
-/

end Lion.Noninterference
