/-
Lion/Capability/Basic.lean
==========================

Capability use tracking and common definitions for capability theorems.

This module provides:
1. Use counting types (UseCount, MaxUses)
2. Exhaustion predicates
3. Capability derivation relations
4. Re-exports of core capability types

Architecture integration:
- Built on: Lion.Core.Crypto (Capability structure)
- Built on: Lion.State.Kernel (CapTable, IsValid)
- Used by: UseLimits, Confinement, Revocation theorems

STATUS: COMPLETE - All definitions verified.
-/

import Lion.Core.Crypto
import Lion.Core.Rights
import Lion.State.Kernel

namespace Lion.Capability

open Lion

/-! =========== PART 1: USE COUNT TYPES =========== -/

/-- Use count is a natural number tracking how many times a capability has been used -/
abbrev UseCount := Nat

/-- Maximum uses allowed for a capability (none = unlimited) -/
abbrev MaxUses := Option Nat

/-- Extended capability with use tracking -/
structure TrackedCapability where
  cap : Capability
  use_count : UseCount
  max_uses : MaxUses

namespace TrackedCapability

/-- A capability has been exhausted if use_count ≥ max_uses -/
def is_exhausted (tc : TrackedCapability) : Prop :=
  match tc.max_uses with
  | none => False  -- Unlimited uses
  | some n => tc.use_count ≥ n

/-- A capability can be used if not exhausted -/
def can_use (tc : TrackedCapability) : Prop :=
  ¬tc.is_exhausted

/-- Increment use count -/
def use (tc : TrackedCapability) : TrackedCapability where
  cap := tc.cap
  use_count := tc.use_count + 1
  max_uses := tc.max_uses

/-- Remaining uses (none = unlimited) -/
def remaining_uses (tc : TrackedCapability) : Option Nat :=
  match tc.max_uses with
  | none => none
  | some n => some (n - tc.use_count)

end TrackedCapability

/-! =========== PART 2: DERIVATION RELATIONS =========== -/

/-- Capability derivation: c₂ is derived from c₁ (one-step or direct) -/
inductive Derives (caps : CapTable) : Capability → Capability → Prop where
  | refl (c : Capability) (h : caps.get? c.id = some c) :
      Derives caps c c
  | delegation (c₁ c₂ : Capability)
      (h₁ : caps.get? c₁.id = some c₁)
      (h₂ : caps.get? c₂.id = some c₂)
      (h_parent : c₂.parent = some c₁.id) :
      Derives caps c₂ c₁

/-- Reflexive-transitive closure of derivation -/
inductive DerivesTransitive (caps : CapTable) : Capability → Capability → Prop where
  | refl (c : Capability) (h : caps.get? c.id = some c) :
      DerivesTransitive caps c c
  | step (c₁ c₂ c₃ : Capability)
      (h₁₂ : Derives caps c₁ c₂)
      (h₂₃ : DerivesTransitive caps c₂ c₃) :
      DerivesTransitive caps c₁ c₃

/-! =========== PART 3: TRACKED CAPABILITY DERIVATION =========== -/

/-- Tracked derivation with use count propagation -/
structure TrackedDerivation (tc₁ tc₂ : TrackedCapability) : Prop where
  /-- Underlying capability derivation -/
  cap_derives : tc₁.cap.parent = some tc₂.cap.id ∨ tc₁.cap = tc₂.cap
  /-- Use count never decreases -/
  use_count_le : tc₂.use_count ≤ tc₁.use_count
  /-- If parent has finite limit n, child has finite limit m ≤ n (Option B from ChatGPT) -/
  max_uses_mono : ∀ n, tc₂.max_uses = some n → ∃ m, tc₁.max_uses = some m ∧ m ≤ n

/-- Well-formed tracked capability table -/
structure TrackedCapTable where
  caps : CapTable
  tracking : CapId → Option TrackedCapability
  /-- Tracking is consistent with capability table -/
  consistent : ∀ cid tc, tracking cid = some tc →
    caps.get? cid = some tc.cap

/-! =========== PART 4: BASIC PROPERTIES =========== -/

/-- Use count is decidably comparable to max uses -/
def exhausted_decidable (tc : TrackedCapability) : Decidable tc.is_exhausted := by
  unfold TrackedCapability.is_exhausted
  cases tc.max_uses with
  | none => exact isFalse (fun h => h)
  | some n => exact inferInstanceAs (Decidable (tc.use_count ≥ n))

/-- Exhaustion implies cannot use -/
theorem exhausted_implies_cannot_use (tc : TrackedCapability) :
    tc.is_exhausted → ¬tc.can_use := by
  intro h_exhausted h_can_use
  unfold TrackedCapability.can_use at h_can_use
  exact h_can_use h_exhausted

/-- Can use implies not exhausted -/
theorem can_use_implies_not_exhausted (tc : TrackedCapability) :
    tc.can_use → ¬tc.is_exhausted := by
  intro h_can_use
  exact h_can_use

/-- Using a capability increases use count by 1 -/
theorem use_increments_count (tc : TrackedCapability) :
    tc.use.use_count = tc.use_count + 1 := rfl

/-- Using preserves max uses -/
theorem use_preserves_max (tc : TrackedCapability) :
    tc.use.max_uses = tc.max_uses := rfl

/-- Using preserves underlying capability -/
theorem use_preserves_cap (tc : TrackedCapability) :
    tc.use.cap = tc.cap := rfl

/-! =========== PART 5: VALIDITY INTEGRATION =========== -/

/-- Tracked capability is valid if underlying capability is valid -/
def TrackedCapability.isValid (tct : TrackedCapTable) (tc : TrackedCapability) : Prop :=
  IsValid tct.caps tc.cap.id

/-- Valid tracked capability can be looked up (requires cap to be in table) -/
theorem valid_tracked_lookup (tct : TrackedCapTable) (tc : TrackedCapability)
    (h_consistent : tct.tracking tc.cap.id = some tc) :
    tct.caps.get? tc.cap.id = some tc.cap :=
  tct.consistent tc.cap.id tc h_consistent

/-! =========== SUMMARY ===========

Capability Basic Module

This module provides the foundation for capability use tracking:

1. **UseCount/MaxUses Types**: Natural number tracking for capability usage
2. **TrackedCapability**: Extended capability with use count and max uses
3. **Exhaustion Predicates**: is_exhausted, can_use for use limit checking
4. **Derivation Relations**: Derives, DerivesTransitive for capability chains
5. **TrackedDerivation**: Derivation with use count/max uses propagation rules

These definitions support the UseLimits theorem (CH2-THM-8) and integrate
with the existing capability confinement and revocation theorems.
-/

end Lion.Capability
