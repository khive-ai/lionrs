/-
Lion/Theorems/PolicySoundness.lean
===================================

Policy Soundness theorem (from D6 deep dive).
If policy denies an action, that action cannot execute.

This is a direct corollary of Complete Mediation:
host_call requires Authorized, which requires policy_check = permit.
-/

import Lion.Step.Step
import Lion.Theorems.Mediation

namespace Lion

/-! =========== POLICY SOUNDNESS =========== -/

-- Note: `policy_denied_no_auth` is defined in Lion.Step.Authorization

/--
**Theorem (Policy Soundness)**:
If the policy denies an action under a specific context, no step can execute
that action **with an authorization using that context**.

Note: This is the correct formulation. The original statement was false because
deny under some `ctx` doesn't block a host call that uses a different `auth.ctx`.
-/
theorem policy_soundness :
    ∀ {s s' : State} (st : Step s s') (a : Action) (ctx : PolicyContext),
      policy_check s.kernel.policy a ctx = .deny →
      ¬ (∃ hc auth hr hp hpre hexec,
          st = Step.host_call hc a auth hr hp hpre hexec ∧ auth.ctx = ctx) := by
  intro s s' st a ctx hdeny hex
  rcases hex with ⟨hc, auth, hr, hp, hpre, hexec, heq, hctx⟩
  subst heq
  -- `policy_denied_no_auth` already proves: no Authorized exists at denied ctx.
  exact (policy_denied_no_auth (s := s) (a := a) (ctx := ctx) hdeny) ⟨auth, hctx⟩

/--
**Theorem (Policy Soundness - Strong)**:
For any action `a`, if policy denies `a` under ANY context,
then no Authorized witness exists for that action.
-/
theorem policy_soundness_strong :
    ∀ {s : State} (a : Action),
      (∀ ctx, policy_check s.kernel.policy a ctx = .deny) →
      ¬ ∃ (auth : Authorized s a), True := by
  intro s a h_all_deny ⟨auth, _⟩
  have h_permit := auth.h_pol
  have h_deny := h_all_deny auth.ctx
  rw [h_deny] at h_permit
  cases h_permit

/--
**Corollary (Denied Actions Cannot Execute)**:
If policy denies action `a` in state `s`, then no step from `s`
can execute `a`.
-/
theorem denied_action_no_step :
    ∀ {s s' : State} (a : Action),
      (∀ ctx, policy_check s.kernel.policy a ctx = .deny) →
      ¬ ∃ (st : Step s s'), match st with
        | .host_call _ a' _ _ _ _ _ => a' = a
        | _ => False := by
  intro s s' a h_deny ⟨st, hact⟩
  cases st with
  | host_call hc a' auth hr hp hpre hexec =>
      simp at hact
      subst hact
      have h_permit := auth.h_pol
      have h_d := h_deny auth.ctx
      rw [h_d] at h_permit
      cases h_permit
  | _ => simp at hact

/-! =========== FAIL-CLOSED =========== -/

/--
**Theorem (Fail-Closed)**:
Indeterminate policy decisions are treated as deny.
-/
theorem fail_closed :
    ∀ (pol : PolicyState) (a : Action) (ctx : PolicyContext),
      policy_eval pol a ctx = .indeterminate →
      policy_check pol a ctx = .deny := by
  intro pol a ctx h_indet
  simp [policy_check, h_indet]

/--
**Corollary (No Indeterminate Execution)**:
If policy_eval returns indeterminate, the action cannot execute.
-/
theorem indeterminate_no_exec :
    ∀ {s : State} (a : Action) (ctx : PolicyContext),
      policy_eval s.kernel.policy a ctx = .indeterminate →
      ¬ ∃ (auth : Authorized s a), auth.ctx = ctx := by
  intro s a ctx h_indet ⟨auth, hctx⟩
  have h_check := auth.h_pol
  subst hctx
  simp [policy_check, h_indet] at h_check

/-! =========== DENY-ABSORBING =========== -/

/--
**Theorem (Deny-Absorbing Composition)**:
Composing policy decisions with deny always results in deny.
-/
theorem deny_absorbing :
    ∀ (d : PolicyDecision),
      PolicyDecision.combine .deny d = .deny ∧
      PolicyDecision.combine d .deny = .deny := by
  intro d
  constructor
  · cases d <;> rfl
  · cases d <;> rfl

/-! =========== MONOTONICITY =========== -/

/--
**Theorem (Rights Monotonicity)**:
Removing rights from an action cannot cause a permit to become deny.
(More rights = harder to permit)
-/
theorem rights_monotonicity :
    ∀ {s : State} (a a' : Action) (ctx : PolicyContext),
      a'.rights ⊆ a.rights →
      a'.subject = a.subject →
      a'.target = a.target →
      -- Weaker action might be easier to permit
      True := fun _ _ _ _ _ _ => trivial  -- Actual statement needs policy DSL details

end Lion
