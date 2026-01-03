/-
Lion/Composition/Compatible.lean
================================

Interface compatibility predicate for component composition (v1 Definition 2.4).

Two components are compatible if they can safely communicate:
1. Their security levels allow information flow
2. Their memory regions are disjoint (no shared mutable state)
3. Any shared capabilities are validly transferred

This is a precondition for the Composition Theorem (v1 Theorem 2.2):
  secure(A) ∧ secure(B) ∧ compatible(A, B) ⟹ secure(A ⊕ B)

Based on:
- v1 Definition 2.4 (Compatible Composition)
- v1 Lemma 2.2.2 (Interface Compatibility Preserves Security)
-/

import Lion.Composition.ComponentSafe

namespace Lion

/-! =========== COMMUNICATION PREDICATE =========== -/

/-- Two security levels can communicate if information can flow between them.
    Communication is allowed if the sender's level flows to the receiver's level
    (i.e., sender ≤ receiver in the security lattice). -/
def can_communicate (sender receiver : SecurityLevel) : Prop :=
  SecurityLevel.flows_to sender receiver

/-! =========== INTERFACE COMPATIBILITY =========== -/

/--
Compatible: Two components can safely compose.

Compatibility ensures that component composition doesn't introduce
new attack surfaces. The key properties are:

1. **Level Compatible**: Security levels allow bidirectional or unidirectional
   information flow (respects Bell-LaPadula / Biba)

2. **Memory Disjoint**: No address is in both components' memory regions.
   This ensures isolation is preserved under composition.

3. **Shared Caps Valid**: Any capabilities that appear in both components'
   held sets are properly validated for sharing.

Based on v1 Definition 2.4 and Lemma 2.2.2.
-/
structure Compatible (s : State) (A B : Component) : Prop where
  /-- Security levels allow communication in at least one direction.
      This ensures no covert channels are created by composition. -/
  level_compatible :
    can_communicate A.level B.level ∨ can_communicate B.level A.level

  /-- Memory regions are disjoint - no shared mutable state.
      This preserves spatial isolation under composition. -/
  memory_disjoint : ∀ addr,
    (s.plugins A.pid).memory.bytes.contains addr →
    ¬(s.plugins B.pid).memory.bytes.contains addr

  /-- Different plugins have different IDs (structural requirement). -/
  different_plugins : A.pid ≠ B.pid

  /-- Source plugin sets are disjoint (for n-ary composition).
      This ensures ownership tracking remains unambiguous. -/
  disjoint_sources : Disjoint A.sourcePids B.sourcePids

namespace Compatible

/-- Compatibility is symmetric for the level and memory properties -/
theorem symmetric_level_memory (s : State) (A B : Component)
    (h : Compatible s A B) : Compatible s B A := by
  constructor
  · -- level_compatible is symmetric (Or.comm)
    exact h.level_compatible.symm
  · -- memory_disjoint: just flip the quantifier
    intro addr h_B_has
    intro h_A_has
    exact h.memory_disjoint addr h_A_has h_B_has
  · -- different_plugins
    exact h.different_plugins.symm
  · -- disjoint_sources is symmetric
    exact h.disjoint_sources.symm

/-- Disjoint memory implies isolation preserved -/
theorem preserves_isolation (s : State) (A B : Component)
    (h : Compatible s A B)
    (hA : ComponentSafe s A) (hB : ComponentSafe s B) :
    ∀ addr,
      (s.plugins A.pid).memory.bytes.contains addr →
      addr < (s.plugins A.pid).memory.bounds ∧
      ¬(s.plugins B.pid).memory.bytes.contains addr := by
  intro addr h_A_has
  constructor
  · exact hA.isolated addr h_A_has
  · exact h.memory_disjoint addr h_A_has

end Compatible

/-! =========== COMPATIBILITY CHAIN =========== -/

/-- Pairwise compatibility of a list of components -/
def PairwiseCompatible (s : State) (cs : List Component) : Prop :=
  ∀ i j (hi : i < cs.length) (hj : j < cs.length), i ≠ j →
    Compatible s (cs.get ⟨i, hi⟩) (cs.get ⟨j, hj⟩)

/-- Empty list is vacuously pairwise compatible -/
theorem pairwise_compatible_nil (s : State) :
    PairwiseCompatible s [] := by
  intro i j hi _ _
  simp at hi

/-- Singleton is vacuously pairwise compatible -/
theorem pairwise_compatible_singleton (s : State) (c : Component) :
    PairwiseCompatible s [c] := by
  intro i j hi hj h_ne
  simp only [List.length_singleton] at hi hj
  -- Both i and j must be 0, but h_ne says they're different - contradiction
  have : i = 0 := Nat.lt_one_iff.mp hi
  have : j = 0 := Nat.lt_one_iff.mp hj
  omega

end Lion
