/-
Lion/Core/Policy.lean
======================

Policy evaluation for access control (Theorem 009).
Fail-closed: indeterminate → deny.
-/

import Lion.Core.Identifiers
import Lion.Core.Rights

namespace Lion

/-! =========== POLICY (009) =========== -/

/-- Policy evaluation result -/
inductive PolicyDecision where
  | permit
  | deny
  | indeterminate
deriving DecidableEq, Repr, Inhabited

namespace PolicyDecision

/-- Deny-absorbing composition -/
def combine (d₁ d₂ : PolicyDecision) : PolicyDecision :=
  match d₁, d₂ with
  | .deny, _ => .deny
  | _, .deny => .deny
  | .permit, .permit => .permit
  | _, _ => .indeterminate

theorem combine_deny_left (d : PolicyDecision) : combine .deny d = .deny := by
  cases d <;> rfl

theorem combine_deny_right (d : PolicyDecision) : combine d .deny = .deny := by
  cases d <;> rfl

/-!
### v1 Policy Composition Algebra (ch4-6 Theorem 4.3-4.7)

The v1 spec defines policy composition operators that form a closed algebra:
- AND (∧): Both policies must permit
- OR (∨): Either policy permits
- NOT (¬): Invert decision (permit ↔ deny)
- Override (⊕): First determinate wins

These operators preserve soundness and satisfy standard algebraic laws.
-/

/-- Policy AND: Both must permit, any deny propagates -/
def and_policy (d₁ d₂ : PolicyDecision) : PolicyDecision :=
  match d₁, d₂ with
  | .permit, .permit => .permit
  | .deny, _ => .deny
  | _, .deny => .deny
  | _, _ => .indeterminate

/-- Policy OR: Either permits, both deny required for deny -/
def or_policy (d₁ d₂ : PolicyDecision) : PolicyDecision :=
  match d₁, d₂ with
  | .permit, _ => .permit
  | _, .permit => .permit
  | .deny, .deny => .deny
  | _, _ => .indeterminate

/-- Policy NOT: Invert permit/deny, indeterminate stays -/
def not_policy (d : PolicyDecision) : PolicyDecision :=
  match d with
  | .permit => .deny
  | .deny => .permit
  | .indeterminate => .indeterminate

/-- Policy Override: First determinate decision wins -/
def override_policy (d₁ d₂ : PolicyDecision) : PolicyDecision :=
  match d₁ with
  | .indeterminate => d₂
  | _ => d₁

/-! #### v1 Theorem 4.3: Policy Closure (compositions preserve soundness) -/

theorem and_policy_closure (d₁ d₂ : PolicyDecision) :
    and_policy d₁ d₂ = .permit ∨ and_policy d₁ d₂ = .deny ∨ and_policy d₁ d₂ = .indeterminate := by
  cases d₁ <;> cases d₂ <;> simp [and_policy]

theorem or_policy_closure (d₁ d₂ : PolicyDecision) :
    or_policy d₁ d₂ = .permit ∨ or_policy d₁ d₂ = .deny ∨ or_policy d₁ d₂ = .indeterminate := by
  cases d₁ <;> cases d₂ <;> simp [or_policy]

/-! #### Commutativity -/

theorem and_policy_comm (d₁ d₂ : PolicyDecision) : and_policy d₁ d₂ = and_policy d₂ d₁ := by
  cases d₁ <;> cases d₂ <;> rfl

theorem or_policy_comm (d₁ d₂ : PolicyDecision) : or_policy d₁ d₂ = or_policy d₂ d₁ := by
  cases d₁ <;> cases d₂ <;> rfl

/-! #### Associativity -/

theorem and_policy_assoc (d₁ d₂ d₃ : PolicyDecision) :
    and_policy (and_policy d₁ d₂) d₃ = and_policy d₁ (and_policy d₂ d₃) := by
  cases d₁ <;> cases d₂ <;> cases d₃ <;> rfl

theorem or_policy_assoc (d₁ d₂ d₃ : PolicyDecision) :
    or_policy (or_policy d₁ d₂) d₃ = or_policy d₁ (or_policy d₂ d₃) := by
  cases d₁ <;> cases d₂ <;> cases d₃ <;> rfl

/-! #### Identity Elements (v1 ch4-6 L44-45) -/

theorem and_policy_permit_left (d : PolicyDecision) : and_policy .permit d = d := by
  cases d <;> rfl

theorem and_policy_permit_right (d : PolicyDecision) : and_policy d .permit = d := by
  cases d <;> rfl

theorem or_policy_deny_left (d : PolicyDecision) : or_policy .deny d = d := by
  cases d <;> rfl

theorem or_policy_deny_right (d : PolicyDecision) : or_policy d .deny = d := by
  cases d <;> rfl

/-! #### Absorption Laws (v1 ch4-6 L48-49) -/

theorem and_policy_absorption (p q : PolicyDecision) :
    and_policy p (or_policy p q) = p := by
  cases p <;> cases q <;> rfl

theorem or_policy_absorption (p q : PolicyDecision) :
    or_policy p (and_policy p q) = p := by
  cases p <;> cases q <;> rfl

/-! #### Distributivity Laws (Boolean Algebra Completion) -/

/--
Distributivity of AND over OR (Kleene three-valued logic).
p AND (q OR r) = (p AND q) OR (p AND r)
-/
theorem and_or_distrib (p q r : PolicyDecision) :
    and_policy p (or_policy q r) = or_policy (and_policy p q) (and_policy p r) := by
  cases p <;> cases q <;> cases r <;> rfl

/--
Distributivity of OR over AND (Kleene three-valued logic).
p OR (q AND r) = (p OR q) AND (p OR r)
-/
theorem or_and_distrib (p q r : PolicyDecision) :
    or_policy p (and_policy q r) = and_policy (or_policy p q) (or_policy p r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-! #### Complement Laws (Three-Valued - Excluded Middle Fails!) -/

/--
Complement under AND: p AND (NOT p).
In Kleene logic: indet AND indet = indet (NOT deny!)
-/
theorem and_complement (p : PolicyDecision) :
    and_policy p (not_policy p) = match p with
      | .permit => .deny
      | .deny => .deny
      | .indeterminate => .indeterminate := by
  cases p <;> rfl

/--
Complement under OR: p OR (NOT p).
In Kleene logic: indet OR indet = indet (NOT permit! - excluded middle fails)
-/
theorem or_complement (p : PolicyDecision) :
    or_policy p (not_policy p) = match p with
      | .permit => .permit
      | .deny => .permit
      | .indeterminate => .indeterminate := by
  cases p <;> rfl

/-- Law of Excluded Middle fails for indeterminate (three-valued logic) -/
theorem excluded_middle_fails_indet :
    or_policy .indeterminate (not_policy .indeterminate) ≠ .permit := by decide

/-- Law of Non-Contradiction fails for indeterminate (three-valued logic) -/
theorem non_contradiction_fails_indet :
    and_policy .indeterminate (not_policy .indeterminate) ≠ .deny := by decide

/-! #### De Morgan's Laws (v1 ch4-6 L53-54) -/

theorem not_and_demorgan (p q : PolicyDecision) :
    not_policy (and_policy p q) = or_policy (not_policy p) (not_policy q) := by
  cases p <;> cases q <;> rfl

theorem not_or_demorgan (p q : PolicyDecision) :
    not_policy (or_policy p q) = and_policy (not_policy p) (not_policy q) := by
  cases p <;> cases q <;> rfl

/-! #### NOT Properties -/

theorem not_policy_involutive (d : PolicyDecision) : not_policy (not_policy d) = d := by
  cases d <;> rfl

theorem not_policy_permit : not_policy .permit = .deny := rfl
theorem not_policy_deny : not_policy .deny = .permit := rfl
theorem not_policy_indeterminate : not_policy .indeterminate = .indeterminate := rfl

/-! #### Override Properties (v1 ch4-6 L68-73) -/

theorem override_policy_assoc (d₁ d₂ d₃ : PolicyDecision) :
    override_policy (override_policy d₁ d₂) d₃ = override_policy d₁ (override_policy d₂ d₃) := by
  cases d₁ <;> rfl

theorem override_policy_indeterminate_left (d : PolicyDecision) :
    override_policy .indeterminate d = d := rfl

theorem override_policy_determinate_absorbs (d₁ d₂ : PolicyDecision)
    (h : d₁ ≠ .indeterminate) : override_policy d₁ d₂ = d₁ := by
  cases d₁ <;> simp [override_policy]
  · exact absurd rfl h

/-! #### Implication Operator (v1 ch4-2 L95-99) -/

/--
Policy Implication: p₁ => p₂
Equivalent to NOT p₁ OR p₂ in classical logic.

- If p₁ is PERMIT, return p₂ (antecedent satisfied, check consequent)
- If p₁ is DENY, return PERMIT (false antecedent makes implication vacuously true)
- If p₁ is INDETERMINATE, return INDETERMINATE (cannot evaluate)
-/
def implies_policy (d₁ d₂ : PolicyDecision) : PolicyDecision :=
  match d₁ with
  | .permit => d₂
  | .deny => .permit
  | .indeterminate => .indeterminate

/--
Note: In three-valued logic, implies_policy is NOT equivalent to NOT p₁ OR p₂.
The difference is: implies_policy .indeterminate d = .indeterminate
             but:  or_policy (not_policy .indeterminate) d = or_policy .indeterminate d
                   which is .permit if d = .permit, else .indeterminate

The v1 spec defines implication as a PRIMITIVE operator, not syntactic sugar.
-/
theorem implies_policy_equiv_not_or_when_determinate (d₁ d₂ : PolicyDecision)
    (h : d₁ ≠ .indeterminate) :
    implies_policy d₁ d₂ = or_policy (not_policy d₁) d₂ := by
  cases d₁ <;> cases d₂ <;> first | rfl | simp_all

theorem implies_policy_permit_left (d : PolicyDecision) :
    implies_policy .permit d = d := rfl

theorem implies_policy_deny_left (d : PolicyDecision) :
    implies_policy .deny d = .permit := rfl

theorem implies_policy_indeterminate_left (d : PolicyDecision) :
    implies_policy .indeterminate d = .indeterminate := rfl

/-! #### Idempotence (Boolean Algebra) -/

theorem and_policy_idem (p : PolicyDecision) : and_policy p p = p := by
  cases p <;> rfl

theorem or_policy_idem (p : PolicyDecision) : or_policy p p = p := by
  cases p <;> rfl

/-! #### Deny Dominance -/

theorem and_policy_deny_left (d : PolicyDecision) : and_policy .deny d = .deny := by
  cases d <;> rfl

theorem and_policy_deny_right (d : PolicyDecision) : and_policy d .deny = .deny := by
  cases d <;> rfl

/-! #### Permit Dominance (for OR) -/

theorem or_policy_permit_left (d : PolicyDecision) : or_policy .permit d = .permit := by
  cases d <;> rfl

theorem or_policy_permit_right (d : PolicyDecision) : or_policy d .permit = .permit := by
  cases d <;> rfl

end PolicyDecision

/-- Action to be authorized -/
structure Action where
  subject : PluginId
  target  : ResourceId
  rights  : Rights
  kind    : String
deriving DecidableEq
-- Note: Cannot derive Repr due to Rights (Finset) lacking Repr instance

/-- Context for policy evaluation -/
structure PolicyContext where
  now        : Time
  callOrigin : Option PluginId  -- For confused deputy prevention
deriving Repr

/--
PolicyState: Concrete policy type wrapping a decision function.
This replaces the previous `opaque PolicyState` to enable constructive defaults.

The decision function approach keeps PolicyState in Type 0 (no universe issues)
while still allowing arbitrary policy logic to be injected.
-/
structure PolicyState where
  /-- The policy decision function -/
  decide : Action → PolicyContext → PolicyDecision

/-- Default policy state: deny-all (safest default, fail-closed) -/
instance : Inhabited PolicyState where
  default := { decide := fun _ _ => .deny }

/-- Policy evaluation: delegate to the decision function -/
def policy_eval (pol : PolicyState) (a : Action) (ctx : PolicyContext) : PolicyDecision :=
  pol.decide a ctx

/-- Fail-closed policy check: indeterminate → deny -/
def policy_check (pol : PolicyState) (a : Action) (ctx : PolicyContext) : PolicyDecision :=
  match policy_eval pol a ctx with
  | .permit        => .permit
  | .deny          => .deny
  | .indeterminate => .deny  -- Fail-closed

/-- Fail-closed ensures no ambiguous access -/
theorem policy_check_fail_closed (pol : PolicyState) (a : Action) (ctx : PolicyContext) :
    policy_check pol a ctx ≠ .indeterminate := by
  simp [policy_check]
  split <;> simp

/-- Policy soundness: denied action cannot execute -/
theorem policy_check_sound (pol : PolicyState) (a : Action) (ctx : PolicyContext) :
    policy_check pol a ctx = .permit ∨ policy_check pol a ctx = .deny := by
  simp [policy_check]
  split
  · left; rfl
  · right; rfl
  · right; rfl

end Lion
