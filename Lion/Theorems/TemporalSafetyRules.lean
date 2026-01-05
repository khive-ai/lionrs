/-
Lion/Theorems/TemporalSafetyRules.lean
=====================================

Step rules for temporal safety preservation.
Tagged with @[step_rule] for use with step_cases tactic.

This demonstrates the pattern for automating Step case analysis.
-/

import Lion.Theorems.TemporalSafety
import Lion.Tactic.StepCases

namespace Lion

open Lion.Tactic.StepCases

/-! =========== STEP RULES FOR TEMPORAL SAFETY =========== -/

/--
Rule: plugin_internal preserves temporal safety.
Ghost state is unchanged by plugin execution.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_preserves_temporal {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    State.temporal_safety s s' := by
  intro addr h_in
  have h_ghost := plugin_internal_preserves_ghost pid pi hpre hexec
  simp only [h_ghost]
  exact h_in

/--
Rule: host_call preserves temporal safety.
Memory operations safely update ghost state.
-/
@[step_rule Step.host_call]
theorem host_call_preserves_temporal {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    State.temporal_safety s s' :=
  host_call_preserves_freed hc a auth hr hparse hpre hexec

/--
Rule: kernel_internal preserves temporal safety.
Kernel operations don't deallocate.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_preserves_temporal {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    State.temporal_safety s s' :=
  kernel_internal_preserves_freed op hexec

/-! =========== DEMO: Using step_cases =========== -/

/--
Demo: step_preserves_temporal_safety using step_cases.

This reduces the proof from explicit case analysis to automatic dispatch.
-/
theorem step_preserves_temporal_safety_auto {s s' : State} (st : Step s s') :
    State.temporal_safety s s' := by
  step_cases st
  -- After step_cases, we have 3 goals, one per constructor
  -- Each goal has the constructor arguments in context
  -- We apply the corresponding @[step_rule] lemma
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_preserves_temporal pid pi hpre hexec
  case host_call hc a auth hr hparse hpre hexec =>
    exact host_call_preserves_temporal hc a auth hr hparse hpre hexec
  case kernel_internal op hexec =>
    exact kernel_internal_preserves_temporal op hexec

/-! =========== IDEAL: Full step_cases_auto =========== -/

/-
With step_cases_auto, the proof would be just:

theorem step_preserves_temporal_safety_ideal {s s' : State} (st : Step s s') :
    State.temporal_safety s s' := by
  step_cases_auto st

But step_cases_auto needs the @[step_rule] lemmas to have exactly matching
argument patterns. Currently it's a work in progress.
-/

end Lion
