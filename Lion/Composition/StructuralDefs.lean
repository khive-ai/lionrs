/-
Lion/Composition/StructuralDefs.lean
====================================

Shared structural invariant definitions for compositional security.

These definitions are used by both Bridge.lean and StructuralInvariants.lean,
factored out here to avoid import cycles.
-/

import Lion.Composition.ComponentSafe

namespace Lion

/-! =========== STRUCTURAL INVARIANTS =========== -/

/--
Invariant: All capability IDs held by plugins exist in the revocation table.

With Handle/State Separation, plugins hold CapId handles (not Capability copies).
This invariant ensures referential integrity: handles point to real entries.

This is a structural invariant maintained by all operations. The kernel adds
the cap to the table and the capId to heldCaps atomically in cap_accept.
-/
def HeldCapsInTable (s : State) : Prop :=
  ∀ pid capId, capId ∈ (s.plugins pid).heldCaps →
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap

/--
Invariant: Held capability IDs reference caps with correct holder field.

Each capability ID in a plugin's heldCaps, when looked up in the table,
has holder = that plugin's ID. This is maintained by cap_accept which
only adds caps with holder = recipient.
-/
def HeldCapsOwnedCorrectly (s : State) : Prop :=
  ∀ pid capId, capId ∈ (s.plugins pid).heldCaps →
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap ∧ cap.holder = pid

/--
Weaker, stable version of HeldCapsInTable that only requires existence.
This is stable under revocation (which flips valid=false but keeps the entry).
With Handle/State Separation, this is actually equivalent to HeldCapsInTable!
-/
def HeldCapsInTableWeak (s : State) : Prop :=
  ∀ pid capId, capId ∈ (s.plugins pid).heldCaps →
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap

/--
Bundle of structural invariants needed for ComponentSafe derivation.

These invariants, combined with SystemInvariant, allow us to derive
ComponentSafe without Step case analysis - we re-derive component safety
from post-state invariants rather than tracking what each step changed.

Handle/State Separation Model:
- We do NOT include HeldCapsIsValid here
- Validity is checked at USE time (cap_invoke, cap_delegate preconditions)
- After revocation, handles remain but IsValid fails when used
- This avoids the impossible invariant "cannot hold revoked cap"
-/
structure ComponentStructInv (s : State) : Prop where
  held_in_table : HeldCapsInTable s
  held_owned : HeldCapsOwnedCorrectly s

end Lion
