/-
Lion/Theorems/PolicySoundnessRules.lean
========================================

Step rules for policy soundness theorems.
Tagged with @[step_rule] for use with step_cases tactic.

Pattern: Each Step constructor gets a wrapper lemma proving that
denied actions cannot be executed via that constructor.
-/

import Lion.Theorems.PolicySoundness
import Lion.Tactic.StepCases

namespace Lion

open Lion.Tactic.StepCases

/-! =========== ACTION MATCH PREDICATE =========== -/

/-- The predicate used in denied_action_no_step to identify action execution.
    Returns True iff the step executes action `a`. -/
def step_executes_action {s s' : State} (st : Step s s') (a : Action) : Prop :=
  match st with
  | .host_call _ a' _ _ _ _ _ => a' = a
  | _ => False

/-! =========== STEP RULES FOR POLICY SOUNDNESS =========== -/

/--
Rule: plugin_internal cannot execute any action.
Plugin internal steps don't cross the trust boundary,
so they never match the action predicate.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_no_action_exec {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s')
    (a : Action) :
    ¬ step_executes_action (Step.plugin_internal pid pi hpre hexec) a := by
  simp [step_executes_action]

/--
Rule: host_call with denied policy cannot execute.
If policy denies action `a` for all contexts, then
no host_call can execute `a` (since Authorized requires permit).
-/
@[step_rule Step.host_call]
theorem host_call_denied_no_exec {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (a_target : Action)
    (h_deny : ∀ ctx, policy_check s.kernel.policy a_target ctx = .deny) :
    ¬ step_executes_action (Step.host_call hc a auth hr hparse hpre hexec) a_target := by
  simp [step_executes_action]
  intro heq
  subst heq
  -- auth.h_pol says policy_check ... = .permit
  have h_permit := auth.h_pol
  -- h_deny says policy_check ... = .deny for all contexts
  have h_d := h_deny auth.ctx
  -- Contradiction: permit = deny
  rw [h_d] at h_permit
  cases h_permit

/--
Rule: kernel_internal cannot execute any action.
Kernel internal operations are TCB operations,
not plugin-initiated actions.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_no_action_exec {s s' : State}
    (op : KernelOp)
    (hexec : KernelExecInternal op s s')
    (a : Action) :
    ¬ step_executes_action (Step.kernel_internal op hexec) a := by
  simp [step_executes_action]

/-! =========== SINGLE-CONTEXT STEP RULES =========== -/

/--
Rule: host_call with single-context deny cannot execute at that context.
If policy denies action `a` at context `ctx`, and the authorization
uses that exact context, the step is impossible.
-/
@[step_rule Step.host_call]
theorem host_call_ctx_denied_no_exec {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (ctx : PolicyContext)
    (h_deny : policy_check s.kernel.policy a ctx = .deny)
    (h_ctx_eq : auth.ctx = ctx) :
    False := by
  have h_permit := auth.h_pol
  rw [h_ctx_eq, h_deny] at h_permit
  cases h_permit

/-! =========== COMPOSITE RULES =========== -/

/--
Composite rule: No step can execute a universally denied action.
This wraps denied_action_no_step for direct application.
-/
theorem no_step_for_denied_action {s s' : State} (st : Step s s') (a : Action)
    (h_deny : ∀ ctx, policy_check s.kernel.policy a ctx = .deny) :
    ¬ step_executes_action st a := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
      exact plugin_internal_no_action_exec pid pi hpre hexec a
  | host_call hc a' auth hr hparse hpre hexec =>
      exact host_call_denied_no_exec hc a' auth hr hparse hpre hexec a h_deny
  | kernel_internal op hexec =>
      exact kernel_internal_no_action_exec op hexec a

/-! =========== DEMO: Using step_cases for policy soundness =========== -/

/--
Demo: denied_action_no_step reformulated with step_cases.
Shows how the step rules enable automatic case dispatch.
-/
theorem denied_action_no_step_via_rules {s s' : State} (a : Action)
    (h_deny : ∀ ctx, policy_check s.kernel.policy a ctx = .deny) :
    ¬ ∃ (st : Step s s'), step_executes_action st a := by
  intro hex
  rcases hex with ⟨st, hact⟩
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_no_action_exec pid pi hpre hexec a hact
  case host_call hc a' auth hr hparse hpre hexec =>
    exact host_call_denied_no_exec hc a' auth hr hparse hpre hexec a h_deny hact
  case kernel_internal op hexec =>
    exact kernel_internal_no_action_exec op hexec a hact

/-! =========== INDETERMINATE STEP RULES =========== -/

/--
Rule: Indeterminate policy also blocks host_call.
If policy_eval returns indeterminate at a context,
no host_call can use that context for authorization.
-/
theorem host_call_indeterminate_no_exec {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (ctx : PolicyContext)
    (h_indet : policy_eval s.kernel.policy a ctx = .indeterminate)
    (h_ctx_eq : auth.ctx = ctx) :
    False := by
  have h_permit := auth.h_pol
  rw [h_ctx_eq] at h_permit
  simp [policy_check, h_indet] at h_permit

end Lion
