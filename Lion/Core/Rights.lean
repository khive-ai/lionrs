/-
Lion/Core/Rights.lean
======================

Rights algebra for capability-based access control (Theorem 004).
10-right system with intersection as combine.
-/

import Mathlib.Data.Finset.Basic

namespace Lion

/-! =========== RIGHTS ALGEBRA (004) =========== -/

/-- Individual access rights -/
inductive Right where
  | Read
  | Write
  | Execute
  | Create
  | Delete
  | Send
  | Receive
  | Delegate
  | Revoke
  | Declassify  -- For controlled downgrading (011)
deriving DecidableEq, Repr, Hashable, Inhabited

namespace Right

/-- Convert to natural for ordering/hashing -/
def toNat : Right → Nat
  | .Read      => 0
  | .Write     => 1
  | .Execute   => 2
  | .Create    => 3
  | .Delete    => 4
  | .Send      => 5
  | .Receive   => 6
  | .Delegate  => 7
  | .Revoke    => 8
  | .Declassify => 9

instance : Ord Right where
  compare r₁ r₂ := compare r₁.toNat r₂.toNat

end Right

/-- Set of rights (using Finset for decidable operations) -/
abbrev Rights := Finset Right

-- Note: Finset doesn't have Repr, but we don't need it for proofs

namespace Rights

/-- Rights ordering: r₁ ≤ r₂ iff r₁ ⊆ r₂ -/
def le (r₁ r₂ : Rights) : Prop := r₁ ⊆ r₂

instance : LE Rights where le := le

instance : DecidableRel (α := Rights) (· ≤ ·) := fun r₁ r₂ =>
  inferInstanceAs (Decidable (r₁ ⊆ r₂))

/-- Combine rights via intersection (for delegation) -/
def combine (r₁ r₂ : Rights) : Rights := r₁ ∩ r₂

/-- Rights cannot grow through delegation -/
theorem combine_le_left (r₁ r₂ : Rights) : combine r₁ r₂ ≤ r₁ :=
  Finset.inter_subset_left

theorem combine_le_right (r₁ r₂ : Rights) : combine r₁ r₂ ≤ r₂ :=
  Finset.inter_subset_right

/-- Confinement: delegated rights must be subset of parent rights -/
theorem confinement {parent child : Rights} (h : child ≤ parent) :
    ∀ r ∈ child, r ∈ parent := fun _ hr => h hr

/-- Empty rights set -/
def empty : Rights := ∅

/-- Full rights set -/
def all : Rights := {
  .Read, .Write, .Execute, .Create, .Delete,
  .Send, .Receive, .Delegate, .Revoke, .Declassify
}

end Rights

end Lion
