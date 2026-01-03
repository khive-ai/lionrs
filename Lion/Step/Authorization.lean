/-
Lion/Step/Authorization.lean
=============================

Authorization witness for proof-carrying steps.
Bakes complete mediation into the type system.
-/

import Lion.Core.Policy
import Lion.Core.Crypto
import Lion.State.State
import Lion.State.Kernel

namespace Lion

/-! =========== INTEGRITY LEVELS (BIBA) =========== -/

/-- Resource integrity level based on owner.
    Used for Biba "no write-up" enforcement. -/
def resource_integrity (s : State) (rid : MemAddr) : SecurityLevel :=
  match s.ghost.resources.get? rid with
  | some (.allocated owner) => (s.plugins owner).level
  | _ => .Public  -- Unallocated/freed has no integrity

/--
Biba write check: writer's integrity level must dominate target's.
This is the Biba "no write-up" enforcement for resource modification.
-/
def biba_write_ok (s : State) (a : Action) : Prop :=
  Right.Write ∈ a.rights → (s.plugins a.subject).level ≥ resource_integrity s a.target

/-! =========== CAPABILITY VALIDITY =========== -/

/-- Check capability seal and revocation status -/
def cap_isValid (s : State) (c : Capability) : Prop :=
  Capability.verify_seal s.kernel.hmacKey c ∧
  s.kernel.revocation.is_valid c.id

/-- Full capability check for authorization -/
def capability_check (s : State) (a : Action) (cap : Capability) : Prop :=
  cap.holder = a.subject ∧
  cap.target = a.target ∧
  a.rights ⊆ cap.rights ∧
  cap_isValid s cap ∧
  cap.id ∈ (s.plugins a.subject).heldCaps

/-! =========== AUTHORIZATION WITNESS =========== -/

/--
Authorization witness carrying all proofs required for a host call.
This is the key to proof-by-construction: you cannot construct an
`Authorized` without providing all the proofs.

Design rationale from architecture:
- h_cap: Capability matches the action (001)
- h_pol: Policy permits the action (009)
- h_valid: Capability chain is valid (005)
- h_live: Target resource is live (006)
- h_conf: Rights are confined (004)
- h_biba: Biba integrity constraint for writes (Integrity NI)
-/
structure Authorized (s : State) (a : Action) where
  /-- The capability being used -/
  cap : Capability

  /-- Policy evaluation context -/
  ctx : PolicyContext

  /-- Capability check passes -/
  h_cap : capability_check s a cap

  /-- Policy permits this action -/
  h_pol : policy_check s.kernel.policy a ctx = PolicyDecision.permit

  /-- Capability is inductively valid (005 - revocation) -/
  h_valid : IsValid s.kernel.revocation.caps cap.id

  /-- Target resource is live (006 - temporal safety) -/
  h_live : ∀ r, a.target = r → MetaState.is_live s.ghost r

  /-- Rights are confined to capability rights (004 - confinement) -/
  h_conf : a.rights ⊆ cap.rights

  /-- Biba integrity: writer level dominates target level for writes (Integrity NI) -/
  h_biba : biba_write_ok s a

namespace Authorized

/-- Authorization implies capability ID is held -/
theorem holder_has_cap {s : State} {a : Action} (auth : Authorized s a) :
    auth.cap.id ∈ (s.plugins a.subject).heldCaps := auth.h_cap.2.2.2.2

/-- Authorization implies policy permit -/
theorem policy_permitted {s : State} {a : Action} (auth : Authorized s a) :
    policy_check s.kernel.policy a auth.ctx = .permit := auth.h_pol

/-- Authorization implies capability seal is valid -/
theorem cap_sealed {s : State} {a : Action} (auth : Authorized s a) :
    Capability.verify_seal s.kernel.hmacKey auth.cap := auth.h_cap.2.2.2.1.1

/-- Authorization implies rights are subset -/
theorem rights_confined {s : State} {a : Action} (auth : Authorized s a) :
    a.rights ⊆ auth.cap.rights := auth.h_conf

/-- Authorization implies Biba write constraint -/
theorem biba_satisfied {s : State} {a : Action} (auth : Authorized s a) :
    biba_write_ok s a := auth.h_biba

/-- If Write right is used, actor's level dominates target's integrity level -/
theorem write_requires_dominance {s : State} {a : Action} (auth : Authorized s a)
    (h_write : Right.Write ∈ a.rights) :
    (s.plugins a.subject).level ≥ resource_integrity s a.target :=
  auth.h_biba h_write

end Authorized

/-! =========== AUTHORIZATION HELPERS =========== -/

/-- Action is properly mediated (has valid authorization) -/
def properly_mediated (s : State) (a : Action) : Prop :=
  ∃ (_auth : Authorized s a), True

/-- No ambient authority: must have capability to act -/
theorem no_ambient_authority {s : State} {a : Action} (auth : Authorized s a) :
    ∃ (cap : Capability), cap.id ∈ (s.plugins a.subject).heldCaps ∧ a.rights ⊆ cap.rights :=
  ⟨auth.cap, auth.holder_has_cap, auth.rights_confined⟩

/-- Policy denied implies no authorization possible -/
theorem policy_denied_no_auth {s : State} {a : Action} {ctx : PolicyContext}
    (h_deny : policy_check s.kernel.policy a ctx = .deny) :
    ¬ ∃ (auth : Authorized s a), auth.ctx = ctx := by
  intro ⟨auth, h_ctx⟩
  -- auth.h_pol says policy_check ... auth.ctx = .permit
  -- h_ctx says auth.ctx = ctx
  -- h_deny says policy_check ... ctx = .deny
  -- Contradiction: permit ≠ deny
  have h_permit := auth.h_pol
  rw [← h_ctx] at h_deny
  rw [h_deny] at h_permit
  cases h_permit

/-!
## v1 Capability-Policy Integration Algebra (ch4-6 L118-130)

The combined authorization function forms an algebra:
  authorize(p, c, a) = φ(p, a) ∧ κ(c, a)

For multiple capabilities C = {c₁, c₂, ..., cₖ}:
  authorize(p, C, a) = φ(p, a) ∧ ∨_{c ∈ C} κ(c, a)

This allows access if the policy permits AND any capability authorizes it.
-/

/-! =========== v1 EXPLICIT AUTHORIZE FUNCTIONS =========== -/

/--
**v1 Definition: Combined Authorization Predicate (ch4-6:L122-130)**

authorize(p, c, a) = φ(p, a) ∧ κ(c, a)

Returns True if BOTH policy permits AND capability check passes.
This is the explicit formulation matching v1 specification.
-/
def authorize (s : State) (cap : Capability) (a : Action) (ctx : PolicyContext) : Prop :=
  policy_check s.kernel.policy a ctx = .permit ∧ capability_check s a cap

/--
**v1 Definition: Multi-Capability Authorization Predicate**

authorize(p, C, a) = φ(p, a) ∧ (∨_{c ∈ C} κ(c, a))

Returns True if policy permits AND at least one capability authorizes.
-/
def authorize_multi (s : State) (caps : List Capability) (a : Action) (ctx : PolicyContext) : Prop :=
  policy_check s.kernel.policy a ctx = .permit ∧
  ∃ cap ∈ caps, capability_check s a cap

/--
**Theorem: authorize matches Authorized witness construction**

If we have an Authorized witness, then authorize holds for that cap.
-/
theorem authorized_implies_authorize {s : State} {a : Action} (auth : Authorized s a) :
    authorize s auth.cap a auth.ctx :=
  ⟨auth.h_pol, auth.h_cap⟩

/--
**Theorem: authorize is monotonic in capabilities**

If authorize holds for cap, it holds for any list containing cap.
-/
theorem authorize_to_authorize_multi {s : State} {cap : Capability} {a : Action} {ctx : PolicyContext}
    (caps : List Capability) (h_mem : cap ∈ caps) (h_auth : authorize s cap a ctx) :
    authorize_multi s caps a ctx := by
  obtain ⟨h_pol, h_cap⟩ := h_auth
  exact ⟨h_pol, cap, h_mem, h_cap⟩

/--
**Theorem: Policy denial blocks authorize**

If policy denies, authorize returns False.
-/
theorem policy_deny_blocks_authorize {s : State} {cap : Capability} {a : Action} {ctx : PolicyContext}
    (h_deny : policy_check s.kernel.policy a ctx = .deny) :
    ¬ authorize s cap a ctx := by
  intro ⟨h_pol, _⟩
  rw [h_deny] at h_pol
  cases h_pol

/--
**Theorem: Capability failure blocks authorize**

If capability check fails, authorize returns False.
-/
theorem cap_fail_blocks_authorize {s : State} {cap : Capability} {a : Action} {ctx : PolicyContext}
    (h_fail : ¬ capability_check s a cap) :
    ¬ authorize s cap a ctx := by
  intro ⟨_, h_cap⟩
  exact h_fail h_cap

/--
**v1 Theorem: Authorization Composition (Single Capability)**

Authorization requires both policy permit AND capability check.
This is the formal statement of `authorize(p, c, a) = φ(p, a) ∧ κ(c, a)`.
-/
theorem authorize_composition {s : State} {a : Action} (auth : Authorized s a) :
    policy_check s.kernel.policy a auth.ctx = .permit ∧ capability_check s a auth.cap :=
  ⟨auth.h_pol, auth.h_cap⟩

/--
**v1 Theorem: Policy is Necessary for Authorization**

If policy denies, no capability can authorize the action.
-/
theorem policy_necessary {s : State} {a : Action} {ctx : PolicyContext}
    (h_deny : policy_check s.kernel.policy a ctx = .deny) :
    ∀ (cap : Capability), ¬ ∃ (auth : Authorized s a), auth.ctx = ctx ∧ auth.cap = cap := by
  intro cap ⟨auth, h_ctx, _⟩
  have h_permit := auth.h_pol
  rw [← h_ctx] at h_deny
  rw [h_deny] at h_permit
  cases h_permit

/--
**v1 Theorem: Capability is Necessary for Authorization**

Authorization requires a valid capability that matches the action.
-/
theorem capability_necessary {s : State} {a : Action} (auth : Authorized s a) :
    ∃ (cap : Capability),
      cap.holder = a.subject ∧
      cap.target = a.target ∧
      a.rights ⊆ cap.rights ∧
      cap_isValid s cap :=
  ⟨auth.cap, auth.h_cap.1, auth.h_cap.2.1, auth.h_cap.2.2.1, auth.h_cap.2.2.2.1⟩

/--
**v1 Theorem: Authorization Implies Mediation**

Any authorized action is properly mediated through the kernel.
This is the core complete mediation guarantee.
-/
theorem authorize_implies_mediated {s : State} {a : Action} (auth : Authorized s a) :
    properly_mediated s a :=
  ⟨auth, trivial⟩

/--
**v1 Theorem: Authorization Soundness**

If an action is authorized, then:
1. Policy permits it
2. A valid capability exists
3. Rights are confined
4. Resources are live
5. Biba integrity is satisfied
-/
theorem authorize_sound {s : State} {a : Action} (auth : Authorized s a) :
    policy_check s.kernel.policy a auth.ctx = .permit ∧
    capability_check s a auth.cap ∧
    a.rights ⊆ auth.cap.rights ∧
    (∀ r, a.target = r → MetaState.is_live s.ghost r) ∧
    biba_write_ok s a :=
  ⟨auth.h_pol, auth.h_cap, auth.h_conf, auth.h_live, auth.h_biba⟩

/-!
### Multi-Capability Authorization

v1 ch4-6 L126-130: For multiple capabilities C = {c₁, ..., cₖ}:
  authorize(p, C, a) = φ(p, a) ∧ ∨_{c ∈ C} κ(c, a)

This is modeled by the fact that authorization uses a single capability,
but any capability that satisfies the check suffices.
-/

/--
**Definition: Multi-Capability Authorization**

An action is authorized by a set of capabilities if policy permits
AND at least one capability in the set authorizes the action.
-/
def multi_cap_authorized (s : State) (a : Action) (ctx : PolicyContext)
    (caps : List Capability) : Prop :=
  policy_check s.kernel.policy a ctx = .permit ∧
  ∃ cap ∈ caps, capability_check s a cap ∧
    IsValid s.kernel.revocation.caps cap.id ∧
    (∀ r, a.target = r → MetaState.is_live s.ghost r) ∧
    biba_write_ok s a

/--
**v1 Theorem: Single-to-Multi Capability Lifting**

If an action is authorized with a single capability, it's authorized
with any list containing that capability.
-/
theorem single_to_multi_cap {s : State} {a : Action} (auth : Authorized s a)
    (caps : List Capability) (h_mem : auth.cap ∈ caps) :
    multi_cap_authorized s a auth.ctx caps := by
  constructor
  · exact auth.h_pol
  · exact ⟨auth.cap, h_mem, auth.h_cap, auth.h_valid, auth.h_live, auth.h_biba⟩

/--
**v1 Theorem: Multi-Cap Authorization is Monotonic**

Adding capabilities to a set preserves authorization.
If authorized with caps, also authorized with caps ++ more_caps.
-/
theorem multi_cap_monotonic {s : State} {a : Action} {ctx : PolicyContext}
    {caps more_caps : List Capability}
    (h : multi_cap_authorized s a ctx caps) :
    multi_cap_authorized s a ctx (caps ++ more_caps) := by
  obtain ⟨h_pol, cap, h_in, h_check, h_valid, h_live, h_biba⟩ := h
  constructor
  · exact h_pol
  · exact ⟨cap, List.mem_append_left more_caps h_in, h_check, h_valid, h_live, h_biba⟩

/--
**v1 Theorem: Policy Dominates Multi-Cap Authorization**

If policy denies, no set of capabilities can authorize.
-/
theorem policy_dominates_multi_cap {s : State} {a : Action} {ctx : PolicyContext}
    {caps : List Capability}
    (h_deny : policy_check s.kernel.policy a ctx = .deny) :
    ¬ multi_cap_authorized s a ctx caps := by
  intro ⟨h_pol, _⟩
  rw [h_deny] at h_pol
  cases h_pol

end Lion
