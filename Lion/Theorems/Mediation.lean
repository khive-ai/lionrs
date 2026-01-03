/-
Lion/Theorems/Mediation.lean
=============================

Complete Mediation theorem (from D3 deep dive).
Every effectful operation is mediated by capability AND policy check.

This is trivially true by construction: you cannot build a `Step.host_call`
without providing an `Authorized` witness, which contains all the proofs.
-/

import Lion.Step.Step

namespace Lion

/-! =========== EFFECTFUL CLASSIFICATION =========== -/

/-- An operation is effectful iff it's a host call -/
def is_effectful {s s' : State} (st : Step s s') : Bool :=
  st.is_effectful

/-! =========== PROPER MEDIATION =========== -/

/-- A step is properly mediated iff it has valid authorization -/
def step_properly_mediated {s s' : State} (st : Step s s') : Prop :=
  match st with
  | .host_call _ a auth _ _ _ _ =>
      ∃ cap ctx,
        auth.cap = cap ∧
        auth.ctx = ctx ∧
        capability_check s a cap ∧
        policy_check s.kernel.policy a ctx = .permit
  | _ => True

/-! =========== COMPLETE MEDIATION THEOREM =========== -/

/--
**Theorem (Complete Mediation)**:
Every effectful operation is properly mediated.

Proof: By case analysis on Step.
- plugin_internal: Not effectful, trivially true.
- host_call: Effectful. The `Authorized` witness in the constructor
  contains h_cap (capability_check) and h_pol (policy_check = permit).
- kernel_internal: Not effectful, trivially true.

This is the **key theorem** that makes the whole architecture work.
-/
theorem complete_mediation :
    ∀ {s s' : State} (st : Step s s'),
      is_effectful st = true → step_properly_mediated st := by
  intro s s' st heff
  cases st with
  | plugin_internal pid pi hpre hexec =>
      -- plugin_internal is not effectful
      simp [is_effectful, Step.is_effectful] at heff
  | host_call hc a auth hr hparse hpre hexec =>
      -- host_call is effectful and properly mediated by construction
      unfold step_properly_mediated
      exact ⟨auth.cap, auth.ctx, rfl, rfl, auth.h_cap, auth.h_pol⟩
  | kernel_internal op hexec =>
      -- kernel_internal is not effectful
      simp [is_effectful, Step.is_effectful] at heff

/--
**Corollary (No Bypass)**:
There is no execution path that allows an effectful operation
without proper authorization.
-/
theorem no_bypass :
    ∀ {s s' : State} (st : Step s s'),
      is_effectful st = true →
      ∃ (a : Action) (cap : Capability) (ctx : PolicyContext),
        capability_check s a cap ∧
        policy_check s.kernel.policy a ctx = .permit := by
  intro s s' st heff
  cases st with
  | host_call hc a auth hr hparse hpre hexec =>
      exact ⟨a, auth.cap, auth.ctx, auth.h_cap, auth.h_pol⟩
  | plugin_internal pid pi hpre hexec =>
      simp [is_effectful, Step.is_effectful] at heff
  | kernel_internal op hexec =>
      simp [is_effectful, Step.is_effectful] at heff

/-! =========== NO AMBIENT AUTHORITY =========== -/

/--
**Theorem (No Ambient Authority - Step)**:
An effectful operation requires presenting a capability.
There is no "ambient" authority based on identity alone.
-/
theorem no_ambient_authority_step :
    ∀ {s s' : State} (st : Step s s'),
      is_effectful st = true →
      -- With Handle/State Separation: held capIds, not full caps
      ∃ (capId : CapId), capId ∈ match st with
        | .host_call hc _ _ _ _ _ _ => (s.plugins hc.caller).heldCaps
        | _ => ∅ := by
  intro s s' st heff
  cases st with
  | host_call hc a auth hr hparse hpre hexec =>
      refine ⟨auth.cap.id, ?_⟩
      have h_holder : auth.cap.id ∈ (s.plugins a.subject).heldCaps := auth.holder_has_cap
      -- Extract `a.subject = hc.caller` from `host_call_pre` + `hparse`.
      have h_subj : a.subject = hc.caller := by
        rcases hpre.1 with ⟨a', h_parse', h_subj'⟩
        have h_some : (some a) = some a' :=
          hparse.symm.trans h_parse'
        have h_eq : a' = a := by
          cases h_some
          rfl
        simpa [h_eq] using h_subj'
      simpa [h_subj] using h_holder
  | plugin_internal pid pi hpre hexec =>
      simp [is_effectful, Step.is_effectful] at heff
  | kernel_internal op hexec =>
      simp [is_effectful, Step.is_effectful] at heff

/-! =========== REFERENCE MONITOR PROPERTIES =========== -/

/--
**Theorem (Tamperproof)**:
Authorization state cannot be modified by untrusted code.
Plugin-internal steps do not affect kernel state.
-/
theorem tamperproof :
    ∀ {s s' : State} (st : Step s s'),
      match st with
      | .plugin_internal _ _ _ _ => s'.kernel = s.kernel
      | _ => True := by
  intro s s' st
  cases st with
  | plugin_internal pid pi hpre hexec =>
      exact plugin_internal_kernel_unchanged pid pi s s' hexec
  | _ => trivial

/--
**Theorem (Complete)**:
Every trust-boundary crossing is a host_call.
(By construction: no other Step constructor can cross the boundary)
-/
theorem completeness :
    ∀ {s s' : State} (st : Step s s'),
      is_effectful st = true ↔ ∃ hc a auth hr hp hpre hexec,
        st = Step.host_call hc a auth hr hp hpre hexec := by
  intro s s' st
  constructor
  · intro heff
    cases st with
    | host_call hc a auth hr hp hpre hexec =>
        exact ⟨hc, a, auth, hr, hp, hpre, hexec, rfl⟩
    | _ => simp [is_effectful, Step.is_effectful] at heff
  · intro ⟨hc, a, auth, hr, hp, hpre, hexec, heq⟩
    subst heq
    simp [is_effectful, Step.is_effectful]

end Lion
