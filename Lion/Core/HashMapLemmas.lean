/-
Lion/Core/HashMapLemmas.lean
=============================

Helper lemmas for Std.HashMap operations.
Used to simplify proofs about capability table updates.
-/

import Lion.State.Kernel

namespace Lion.HashMapLemmas

open Std

variable {A B : Type} [BEq A] [Hashable A] [EquivBEq A] [LawfulHashable A] [LawfulBEq A]

lemma get?_insert_of_ne
    (m : Std.HashMap A B) (k : A) (v : B) {a : A} (h : a ≠ k) :
    (m.insert k v).get? a = m.get? a := by
  have hkna : k ≠ a := fun hk => h hk.symm
  have hbeq : (k == a) = false := beq_eq_false_iff_ne.2 hkna
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbeq]

lemma get?_insert_self
    (m : Std.HashMap A B) (k : A) (v : B) :
    (m.insert k v).get? k = some v := by
  simp [Std.HashMap.get?_eq_getElem?]

end Lion.HashMapLemmas
