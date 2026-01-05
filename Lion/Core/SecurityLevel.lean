/-
Lion/Core/SecurityLevel.lean
=============================

Security lattice for information flow control (Theorem 011).
4-level lattice: Public < Internal < Confidential < Secret
-/

import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Basic

namespace Lion

/-! =========== SECURITY LATTICE (011) =========== -/

/-- Security classification levels forming a lattice -/
inductive SecurityLevel where
  | Public
  | Internal
  | Confidential
  | Secret
deriving DecidableEq, Repr, Inhabited

namespace SecurityLevel

/-- Convert security level to natural number for ordering -/
def toNat : SecurityLevel → Nat
  | .Public       => 0
  | .Internal     => 1
  | .Confidential => 2
  | .Secret       => 3

/-- Information flow relation: l₁ flows to l₂ -/
def flows_to (l₁ l₂ : SecurityLevel) : Prop :=
  l₁.toNat ≤ l₂.toNat

theorem flows_to_refl (l : SecurityLevel) : flows_to l l := Nat.le_refl _

theorem flows_to_trans {l₁ l₂ l₃ : SecurityLevel}
    (h₁ : flows_to l₁ l₂) (h₂ : flows_to l₂ l₃) : flows_to l₁ l₃ :=
  Nat.le_trans h₁ h₂

theorem flows_to_antisymm {l₁ l₂ : SecurityLevel}
    (h₁ : flows_to l₁ l₂) (h₂ : flows_to l₂ l₁) : l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> first | rfl | (simp only [flows_to, toNat] at h₁ h₂; omega)

/-- toNat is injective -/
theorem toNat_injective : Function.Injective toNat := by
  intro l₁ l₂ h
  cases l₁ <;> cases l₂ <;> first | rfl | (simp only [toNat] at h; omega)

/-- LinearOrder instance for SecurityLevel (total order via toNat embedding).
    Provides: LE, LT, Preorder, PartialOrder, LinearOrder, decidability -/
instance : LinearOrder SecurityLevel := LinearOrder.lift' toNat toNat_injective

/-- flows_to coincides with the LE from LinearOrder -/
theorem flows_to_iff_le (l₁ l₂ : SecurityLevel) : flows_to l₁ l₂ ↔ l₁ ≤ l₂ := Iff.rfl

/-- Least upper bound (join) -/
def join (l₁ l₂ : SecurityLevel) : SecurityLevel :=
  if l₁.toNat ≥ l₂.toNat then l₁ else l₂

/-- Greatest lower bound (meet) -/
def meet (l₁ l₂ : SecurityLevel) : SecurityLevel :=
  if l₁.toNat ≤ l₂.toNat then l₁ else l₂

/-- Top element of the lattice -/
def top : SecurityLevel := .Secret

/-- Bottom element of the lattice -/
def bot : SecurityLevel := .Public

theorem bot_le (l : SecurityLevel) : bot ≤ l := by
  simp only [LE.le, bot, toNat]
  exact Nat.zero_le _

theorem le_top (l : SecurityLevel) : l ≤ top := by
  cases l <;> native_decide

/-- Join is upper bound -/
theorem le_join_left (l₁ l₂ : SecurityLevel) : l₁ ≤ join l₁ l₂ := by
  cases l₁ <;> cases l₂ <;> native_decide

theorem le_join_right (l₁ l₂ : SecurityLevel) : l₂ ≤ join l₁ l₂ := by
  cases l₁ <;> cases l₂ <;> native_decide

/-- Meet is lower bound -/
theorem meet_le_left (l₁ l₂ : SecurityLevel) : meet l₁ l₂ ≤ l₁ := by
  cases l₁ <;> cases l₂ <;> native_decide

theorem meet_le_right (l₁ l₂ : SecurityLevel) : meet l₁ l₂ ≤ l₂ := by
  cases l₁ <;> cases l₂ <;> native_decide

/-! ### Mathlib4 Lattice Instances

The following instances integrate SecurityLevel with Mathlib's order hierarchy.

Sources:
- Mathlib/Order/BoundedOrder/Basic.lean: OrderBot, OrderTop, BoundedOrder
- Mathlib/Order/Lattice.lean: Lattice, DistribLattice (auto-derived from LinearOrder)
- LinearOrder automatically provides Lattice/DistribLattice via max/min as sup/inf
-/

/-- OrderBot instance: Public is the bottom element of the security lattice.
    Required: bot element and proof that bot ≤ x for all x. -/
instance : OrderBot SecurityLevel where
  bot := .Public
  bot_le := bot_le

/-- OrderTop instance: Secret is the top element of the security lattice.
    Required: top element and proof that x ≤ top for all x. -/
instance : OrderTop SecurityLevel where
  top := .Secret
  le_top := le_top

/-- BoundedOrder: SecurityLevel has both top and bottom elements.
    Constructed from the OrderBot and OrderTop instances above.
    See: Mathlib/Order/BoundedOrder/Basic.lean -/
instance : BoundedOrder SecurityLevel where
  toOrderTop := inferInstance
  toOrderBot := inferInstance

/-- Lattice and DistribLattice instances are automatically derived from LinearOrder.

    In Mathlib4, any LinearOrder is automatically a DistribLattice:
    - sup a b = max a b (from LinearOrder)
    - inf a b = min a b (from LinearOrder)
    - The distributive law a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) holds in any chain.

    See: Mathlib/Order/Lattice.lean line ~550:
      instance (priority := 100) {α : Type u} [LinearOrder α] : DistribLattice α

    These are available via inferInstance - we note them here for documentation.
-/
example : Lattice SecurityLevel := inferInstance
example : DistribLattice SecurityLevel := inferInstance

end SecurityLevel

end Lion
