/-
Lion/Deploy/Authorization.lean
==============================

Formal proofs for scope-based authorization (ADR-003).
Proves scope-based access control with wildcard expansion and Rights mapping.

Key Properties:
1. Scope wildcard expansion: `service:*` matches any `service:X`
2. Scope to Rights mapping: Scopes correctly map to Rights
3. Auth chain first-match semantics: First matching scope wins
4. Superuser scope: `*:*` grants all access

STATUS: FIXED - Mathlib4 API compatibility (Dec 2025).
-/

import Lion.Core.Rights
import Mathlib.Data.List.Basic

namespace Lion.Deploy.Auth

open Lion

/-! =========== PART 1: SCOPE TYPES =========== -/

/-- A Scope is a hierarchical access pattern: "service:operation" -/
structure Scope where
  service : String
  operation : String
deriving DecidableEq, Repr

namespace Scope

/-- Constructor from string parts -/
def fromParts (svc op : String) : Scope := ⟨svc, op⟩

/-- Wildcard operation constant -/
def wildcard : String := "*"

/-- Superuser scope: full access -/
def superuser : Scope := ⟨"*", "*"⟩

/-- Service wildcard scope: all operations on a service -/
def serviceWildcard (svc : String) : Scope := ⟨svc, "*"⟩

/-- Check if scope has wildcard operation -/
def isWildcard (s : Scope) : Bool := s.operation == "*"

/-- Check if scope is superuser (*:*) -/
def isSuperuser (s : Scope) : Bool := s.service == "*" && s.operation == "*"

end Scope

/-! =========== PART 2: SCOPE MATCHING =========== -/

/-- Scope matching relation: does scope `s` grant access to target `t`? -/
def scopeMatches (s t : Scope) : Prop :=
  -- Superuser matches everything
  s.isSuperuser
  -- Exact match
  ∨ (s.service == t.service && s.operation == t.operation)
  -- Wildcard match: service:* matches service:anything
  ∨ (s.service == t.service && s.isWildcard)

/-- Decidable instance for scope matching. -/
instance (s t : Scope) : Decidable (scopeMatches s t) := by
  unfold scopeMatches
  infer_instance

/-! =========== PART 3: SCOPE MATCHING THEOREMS =========== -/

/-- Superuser scope matches any target -/
theorem superuser_matches_all (t : Scope) : scopeMatches Scope.superuser t := by
  unfold scopeMatches Scope.superuser Scope.isSuperuser
  -- prove the first disjunct
  left
  simp

/-- Exact scope match -/
theorem exact_match (s : Scope) : scopeMatches s s := by
  unfold scopeMatches
  -- prove the "exact match" disjunct
  right; left
  simp

/-- Wildcard matches any operation on same service -/
theorem wildcard_matches_service (svc op : String) :
    scopeMatches (Scope.serviceWildcard svc) ⟨svc, op⟩ := by
  unfold scopeMatches Scope.serviceWildcard Scope.isWildcard Scope.isSuperuser
  right; right
  simp

/-- Wildcard expansion: service:* matches service:X for any X -/
theorem wildcard_expansion (svc : String) (op : String) :
    let wildScope := Scope.serviceWildcard svc
    let targetScope := ⟨svc, op⟩
    scopeMatches wildScope targetScope := by
  -- `simpa` zeta-reduces the `let`s
  simpa using wildcard_matches_service svc op

/-! =========== PART 4: SCOPE LIST AUTHORIZATION =========== -/

/-- Check if any scope in a list matches the target (first-match semantics) -/
def anyMatches (scopes : List Scope) (target : Scope) : Prop :=
  ∃ s ∈ scopes, scopeMatches s target

/-- Decidable instance for anyMatches. -/
instance (scopes : List Scope) (target : Scope) : Decidable (anyMatches scopes target) := by
  unfold anyMatches
  infer_instance

/-- Empty scope list grants no access -/
theorem empty_scopes_deny (t : Scope) : ¬ anyMatches [] t := by
  simp [anyMatches]

/-- Superuser in list grants access to anything -/
theorem superuser_in_list_grants_all (scopes : List Scope) (t : Scope)
    (h : Scope.superuser ∈ scopes) : anyMatches scopes t := by
  exact ⟨Scope.superuser, h, superuser_matches_all t⟩

/-- First-match: if first scope matches, authorization succeeds -/
theorem first_match_succeeds (s : Scope) (rest : List Scope) (t : Scope)
    (h : scopeMatches s t) : anyMatches (s :: rest) t := by
  exact ⟨s, by simp, h⟩

/-- Monotonicity: more scopes can only grant more access -/
theorem scopes_monotonic (scopes : List Scope) (s : Scope) (t : Scope)
    (h : anyMatches scopes t) : anyMatches (s :: scopes) t := by
  rcases h with ⟨matched, h_mem, h_match⟩
  exact ⟨matched, List.mem_cons_of_mem s h_mem, h_match⟩

/-! =========== PART 5: SCOPE TO RIGHTS MAPPING =========== -/

/-- Map a semantic scope suffix to a Right -/
def scopeSuffixToRight : String → Option Right
  | "read" => some .Read
  | "write" => some .Write
  | "execute" => some .Execute
  | "create" => some .Create
  | "delete" => some .Delete
  | "send" => some .Send
  | "receive" => some .Receive
  | "delegate" => some .Delegate
  | "revoke" => some .Revoke
  | _ => none

/-- Map a single scope to Rights -/
def scopeToRights (s : Scope) : Rights :=
  if s.isSuperuser then
    Rights.all
  else if s.isWildcard then
    Rights.all  -- Service wildcard grants all rights for that service
  else
    match scopeSuffixToRight s.operation with
    | some r => {r}
    | none => ∅

/-- Combine rights from multiple scopes -/
def scopesToRights (scopes : List Scope) : Rights :=
  scopes.foldl (fun acc s => acc ∪ scopeToRights s) ∅

/-! =========== PART 6: RIGHTS MAPPING THEOREMS =========== -/

/-- Superuser scope grants all rights -/
theorem superuser_grants_all_rights :
    scopeToRights Scope.superuser = Rights.all := by
  simp [scopeToRights, Scope.superuser, Scope.isSuperuser, Scope.isWildcard]

/-- Wildcard scope grants all rights -/
theorem wildcard_grants_all_rights (svc : String) (h : svc ≠ "*") :
    scopeToRights (Scope.serviceWildcard svc) = Rights.all := by
  -- This is true even when svc = "*", but we keep your original statement.
  simp [scopeToRights, Scope.serviceWildcard, Scope.isSuperuser, Scope.isWildcard]

/-! =========== PART 7: AUTHORIZATION DECISION =========== -/

/-- Authorization result -/
inductive AuthzResult where
  | Authorized
  | Denied (required : Scope) (available : List Scope)
deriving Repr

/-- Authorize an operation given scopes -/
def authorize (scopes : List Scope) (target : Scope) : AuthzResult :=
  if h : anyMatches scopes target then
    .Authorized
  else
    .Denied target scopes

/-- Authorization is sound: Authorized implies access granted -/
theorem authorize_sound (scopes : List Scope) (target : Scope)
    (h : authorize scopes target = .Authorized) : anyMatches scopes target := by
  by_cases hm : anyMatches scopes target
  · exact hm
  · -- in this branch, authorize must be Denied, contradicting `h`
    have hEq : (AuthzResult.Denied target scopes) = .Authorized := by
      simpa [authorize, hm] using h
    cases hEq

/-- Authorization is complete: access granted implies Authorized -/
theorem authorize_complete (scopes : List Scope) (target : Scope)
    (h : anyMatches scopes target) : authorize scopes target = .Authorized := by
  simp [authorize, h]

/-! =========== PART 8: DEFAULT REQUIREMENT POLICIES =========== -/

/-- Default requirement policy -/
inductive DefaultRequirement where
  | AllowAuthenticated     -- Allow if authenticated
  | DenyUnlessExplicit     -- Deny unless explicitly allowed
  | RequireServiceWildcard -- Require service:* scope
deriving DecidableEq, Repr

/-- Apply default policy when no explicit rule matches -/
def applyDefault (policy : DefaultRequirement) (scopes : List Scope) (target : Scope)
    : AuthzResult :=
  match policy with
  | .AllowAuthenticated => .Authorized
  | .DenyUnlessExplicit => .Denied target scopes
  | .RequireServiceWildcard =>
    let wildcard := Scope.serviceWildcard target.service
    if anyMatches scopes wildcard ∨ anyMatches scopes Scope.superuser then
      .Authorized
    else
      .Denied wildcard scopes

/-- AllowAuthenticated always grants access -/
theorem allow_authenticated_grants (scopes : List Scope) (target : Scope) :
    applyDefault .AllowAuthenticated scopes target = .Authorized := rfl

/-- DenyUnlessExplicit always denies -/
theorem deny_unless_explicit_denies (scopes : List Scope) (target : Scope) :
    applyDefault .DenyUnlessExplicit scopes target = .Denied target scopes := rfl

end Lion.Deploy.Auth
