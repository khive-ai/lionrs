/-
Lion/Core/HashMapLemmas.lean
=============================

Helper lemmas for Std.HashMap operations.
Used to simplify proofs about capability table updates.

STATUS: COMPLETE - All lemmas proven
-/

import Lion.State.Kernel
import Std.Data.HashMap.Lemmas

namespace Lion.HashMapLemmas

open Std

variable {A B : Type} [BEq A] [Hashable A] [EquivBEq A] [LawfulHashable A] [LawfulBEq A]

lemma get?_insert_of_ne
    (m : Std.HashMap A B) (k : A) (v : B) {a : A} (h : a ≠ k) :
    (m.insert k v).get? a = m.get? a := by
  have hkna : k ≠ a := fun hk => h hk.symm
  have hbeq : (k == a) = false := beq_eq_false_iff_ne.2 hkna
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbeq]

omit [LawfulBEq A] in
lemma get?_insert_self
    (m : Std.HashMap A B) (k : A) (v : B) :
    (m.insert k v).get? k = some v := by
  simp [Std.HashMap.get?_eq_getElem?]

/-! =========== getD lemmas (get with default) =========== -/

omit [LawfulBEq A] in
/-- getD after insert when key matches -/
lemma getD_insert_self
    (m : Std.HashMap A B) (k : A) (v : B) (default : B) :
    (m.insert k v).getD k default = v := by
  simp

/-- getD after insert when keys differ -/
lemma getD_insert_of_ne
    (m : Std.HashMap A B) (k : A) (v : B) {a : A} (default : B) (h : a ≠ k) :
    (m.insert k v).getD a default = m.getD a default := by
  have hkna : k ≠ a := fun hk => h hk.symm
  have hbeq : (k == a) = false := beq_eq_false_iff_ne.2 hkna
  simp [Std.HashMap.getD_insert, hbeq]

/-! =========== Structural lemmas for footprint proofs =========== -/

/-- Insert preserves other keys' values -/
lemma insert_preserves_other
    (m : Std.HashMap A B) (k k' : A) (v : B) (h : k' ≠ k) :
    (m.insert k v).get? k' = m.get? k' :=
  get?_insert_of_ne m k v h

/-! =========== Contains lemmas =========== -/

omit [LawfulBEq A] in
/-- contains after insert when key matches -/
lemma contains_insert_self
    (m : Std.HashMap A B) (k : A) (v : B) :
    (m.insert k v).contains k = true := by
  simp

/-- contains after insert when keys differ -/
lemma contains_insert_of_ne
    (m : Std.HashMap A B) (k : A) (v : B) {a : A} (h : a ≠ k) :
    (m.insert k v).contains a = m.contains a := by
  have hkna : k ≠ a := fun hk => h hk.symm
  have hbeq : (k == a) = false := beq_eq_false_iff_ne.2 hkna
  simp [Std.HashMap.contains_insert, hbeq]

/-! =========== HashMap.map lemmas =========== -/

omit [EquivBEq A] in
/-- If key exists in original map, key exists in mapped map with transformed value -/
lemma get?_map_of_mem (m : Std.HashMap A B) (f : A → B → B) (k : A) (v : B)
    (h : m.get? k = some v) :
    (m.map f).get? k = some (f k v) := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]
  simp only [Std.HashMap.get?_eq_getElem?] at h
  simp [h]

omit [EquivBEq A] in
/-- If key doesn't exist in original map, key doesn't exist in mapped map -/
lemma get?_map_of_not_mem (m : Std.HashMap A B) (f : A → B → B) (k : A)
    (h : m.get? k = none) :
    (m.map f).get? k = none := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]
  simp only [Std.HashMap.get?_eq_getElem?] at h
  simp [h]

/-- getD after map when key exists -/
lemma getD_map_of_mem (m : Std.HashMap A B) (f : A → B → B) (k : A) (v : B) (default : B)
    (h : m.get? k = some v) :
    (m.map f).getD k default = f k v := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  rw [Std.HashMap.getElem?_map]
  simp only [Std.HashMap.get?_eq_getElem?] at h
  simp [h, Option.getD]

/-- getD after map when key doesn't exist -/
lemma getD_map_of_not_mem (m : Std.HashMap A B) (f : A → B → B) (k : A) (default : B)
    (h : m.get? k = none) :
    (m.map f).getD k default = default := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  rw [Std.HashMap.getElem?_map]
  simp only [Std.HashMap.get?_eq_getElem?] at h
  simp [h, Option.getD]

end Lion.HashMapLemmas
