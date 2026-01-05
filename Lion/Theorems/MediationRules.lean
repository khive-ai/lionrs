/-
Lion/Theorems/MediationRules.lean
=================================

Step rules for mediation properties.
Tagged with @[step_rule] for use with step_cases tactic.

Extracts per-constructor lemmas from the main Mediation theorems.
-/

import Lion.Theorems.Mediation
import Lion.Tactic.StepCases

namespace Lion

open Lion.Tactic.StepCases

/-! =========== STEP RULES FOR COMPLETE MEDIATION =========== -/

/--
Rule: plugin_internal is not effectful, so complete_mediation holds vacuously.
The antecedent `is_effectful st = true` is false for plugin_internal.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_complete_mediation {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    is_effectful (Step.plugin_internal pid pi hpre hexec) = true →
    step_properly_mediated (Step.plugin_internal pid pi hpre hexec) := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/--
Rule: host_call is effectful and properly mediated by construction.
The Authorized witness contains capability and policy proofs.
-/
@[step_rule Step.host_call]
theorem host_call_complete_mediation {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    is_effectful (Step.host_call hc a auth hr hparse hpre hexec) = true →
    step_properly_mediated (Step.host_call hc a auth hr hparse hpre hexec) := by
  intro _
  unfold step_properly_mediated
  exact ⟨auth.cap, auth.ctx, rfl, rfl, auth.h_cap, auth.h_pol⟩

/--
Rule: kernel_internal is not effectful, so complete_mediation holds vacuously.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_complete_mediation {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    is_effectful (Step.kernel_internal op hexec) = true →
    step_properly_mediated (Step.kernel_internal op hexec) := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/-! =========== STEP RULES FOR NO BYPASS =========== -/

/--
Rule: plugin_internal cannot bypass (not effectful).
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_no_bypass {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    is_effectful (Step.plugin_internal pid pi hpre hexec) = true →
    ∃ (a : Action) (cap : Capability) (ctx : PolicyContext),
      capability_check s a cap ∧ policy_check s.kernel.policy a ctx = .permit := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/--
Rule: host_call has no bypass - authorization is required.
-/
@[step_rule Step.host_call]
theorem host_call_no_bypass {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    is_effectful (Step.host_call hc a auth hr hparse hpre hexec) = true →
    ∃ (a : Action) (cap : Capability) (ctx : PolicyContext),
      capability_check s a cap ∧ policy_check s.kernel.policy a ctx = .permit := by
  intro _
  exact ⟨a, auth.cap, auth.ctx, auth.h_cap, auth.h_pol⟩

/--
Rule: kernel_internal cannot bypass (not effectful).
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_no_bypass {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    is_effectful (Step.kernel_internal op hexec) = true →
    ∃ (a : Action) (cap : Capability) (ctx : PolicyContext),
      capability_check s a cap ∧ policy_check s.kernel.policy a ctx = .permit := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/-! =========== STEP RULES FOR NO AMBIENT AUTHORITY =========== -/

/--
Rule: plugin_internal has no ambient authority concern (not effectful).
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_no_ambient_authority {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    is_effectful (Step.plugin_internal pid pi hpre hexec) = true →
    ∃ (capId : CapId), capId ∈ (s.plugins pid).heldCaps := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/--
Rule: host_call requires presenting a capability (no ambient authority).
The caller must hold the capability.
-/
@[step_rule Step.host_call]
theorem host_call_no_ambient_authority {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    is_effectful (Step.host_call hc a auth hr hparse hpre hexec) = true →
    ∃ (capId : CapId), capId ∈ (s.plugins hc.caller).heldCaps := by
  intro _
  refine ⟨auth.cap.id, ?_⟩
  have h_holder : auth.cap.id ∈ (s.plugins a.subject).heldCaps := auth.holder_has_cap
  -- Extract `a.subject = hc.caller` from `host_call_pre` + `hparse`
  have h_subj : a.subject = hc.caller := by
    rcases hpre.1 with ⟨a', h_parse', h_subj'⟩
    have h_some : (some a) = some a' := hparse.symm.trans h_parse'
    have h_eq : a' = a := by cases h_some; rfl
    simpa [h_eq] using h_subj'
  simpa [h_subj] using h_holder

/--
Rule: kernel_internal has no ambient authority concern (not effectful).
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_no_ambient_authority {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    is_effectful (Step.kernel_internal op hexec) = true →
    ∃ (capId : CapId), capId ∈ (∅ : Finset CapId) := by
  intro heff
  simp [is_effectful, Step.is_effectful] at heff

/-! =========== STEP RULES FOR TAMPERPROOF =========== -/

/--
Rule: plugin_internal preserves kernel state (tamperproof).
Untrusted code cannot modify authorization state.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_tamperproof {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (_hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    s'.kernel = s.kernel :=
  plugin_internal_kernel_unchanged pid pi s s' hexec

/--
Rule: host_call tamperproof property is trivially True.
-/
@[step_rule Step.host_call]
theorem host_call_tamperproof {s s' : State}
    (_hc : HostCall) (_a : Action) (_auth : Authorized s _a)
    (_hr : HostResult) (_hparse : hostcall_action _hc = some _a)
    (_hpre : host_call_pre _hc s)
    (_hexec : KernelExecHost _hc _a _auth _hr s s') :
    True := trivial

/--
Rule: kernel_internal tamperproof property is trivially True.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_tamperproof {s s' : State}
    (_op : KernelOp) (_hexec : KernelExecInternal _op s s') :
    True := trivial

/-! =========== STEP RULES FOR COMPLETENESS =========== -/

/--
Rule: plugin_internal is not effectful (completeness forward direction).
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_not_effectful {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    is_effectful (Step.plugin_internal pid pi hpre hexec) = false := by
  simp only [is_effectful, Step.is_effectful]

/--
Rule: host_call is effectful (completeness forward direction).
-/
@[step_rule Step.host_call]
theorem host_call_is_effectful {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    is_effectful (Step.host_call hc a auth hr hparse hpre hexec) = true := by
  simp only [is_effectful, Step.is_effectful]

/--
Rule: kernel_internal is not effectful (completeness forward direction).
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_not_effectful {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    is_effectful (Step.kernel_internal op hexec) = false := by
  simp only [is_effectful, Step.is_effectful]

/-! =========== DEMO: Using step_cases for Mediation =========== -/

/--
Demo: complete_mediation using step_cases and step rules.
-/
theorem complete_mediation_auto {s s' : State} (st : Step s s') :
    is_effectful st = true → step_properly_mediated st := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_complete_mediation pid pi hpre hexec
  case host_call hc a auth hr hparse hpre hexec =>
    exact host_call_complete_mediation hc a auth hr hparse hpre hexec
  case kernel_internal op hexec =>
    exact kernel_internal_complete_mediation op hexec

/--
Demo: no_bypass using step_cases and step rules.
-/
theorem no_bypass_auto {s s' : State} (st : Step s s') :
    is_effectful st = true →
    ∃ (a : Action) (cap : Capability) (ctx : PolicyContext),
      capability_check s a cap ∧ policy_check s.kernel.policy a ctx = .permit := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_no_bypass pid pi hpre hexec
  case host_call hc a auth hr hparse hpre hexec =>
    exact host_call_no_bypass hc a auth hr hparse hpre hexec
  case kernel_internal op hexec =>
    exact kernel_internal_no_bypass op hexec

/--
Demo: tamperproof using step_cases and step rules.
-/
theorem tamperproof_auto {s s' : State} (st : Step s s') :
    match st with
    | .plugin_internal _ _ _ _ => s'.kernel = s.kernel
    | _ => True := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_tamperproof pid pi hpre hexec
  case host_call hc a auth hr hparse hpre hexec =>
    exact host_call_tamperproof hc a auth hr hparse hpre hexec
  case kernel_internal op hexec =>
    exact kernel_internal_tamperproof op hexec

end Lion
