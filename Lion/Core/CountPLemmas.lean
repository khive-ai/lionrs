/-
Lion/Core/CountPLemmas.lean
===========================

Helper lemmas for List.countP updates needed for workflow measure proofs.

These lemmas establish how countP changes when the predicate changes
for exactly one element in the list.
-/

import Mathlib.Data.List.Count
import Mathlib.Data.List.Basic

namespace Lion

/-! =========== COUNTING LEMMAS =========== -/

section CountPUpdate

variable {α : Type*}

/--
**Lemma (Bool equality implies iff)**

Helper to convert Bool equality to iff for countP_congr.
-/
theorem bool_eq_to_iff {a b : Bool} (h : a = b) : (a = true ↔ b = true) := by
  rw [h]

/--
**Lemma (countP with function update - decrease)**

When we update a function `f` so that element `a` no longer satisfies the predicate,
and `a` appears exactly once in the list, countP decreases by 1.

This captures: pending count decreases when node goes pending -> active.
-/
theorem countP_update_decreases [DecidableEq α] (l : List α) (a : α) (f g : α → Bool)
    (h_mem : a ∈ l)
    (h_nodup : l.Nodup)
    (h_old : f a = true)
    (h_new : g a = false)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.countP g + 1 = l.countP f := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [List.countP_cons]
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      -- a is the head
      subst h_eq
      -- g a = false, so (if g a = true then 1 else 0) = 0
      have hg : (if g a = true then 1 else 0) = 0 := by simp [h_new]
      -- f a = true, so (if f a = true then 1 else 0) = 1
      have hf : (if f a = true then 1 else 0) = 1 := by simp [h_old]
      rw [hg, hf]
      -- All other elements unchanged
      have h_tl_unchanged : ∀ x ∈ tl, g x = f x := by
        intro x hx
        have h_ne : x ≠ a := by
          intro heq
          subst heq
          exact (List.nodup_cons.mp h_nodup).1 hx
        exact h_unchanged x (List.mem_cons.mpr (Or.inr hx)) h_ne
      have h_countP_eq : tl.countP g = tl.countP f := by
        apply List.countP_congr
        intro x hx
        exact bool_eq_to_iff (h_tl_unchanged x hx)
      rw [h_countP_eq]
    | inr h_tl =>
      -- a is in the tail
      have h_nodup_tl := (List.nodup_cons.mp h_nodup).2
      have h_ne : hd ≠ a := by
        intro heq
        subst heq
        exact (List.nodup_cons.mp h_nodup).1 h_tl
      have h_hd_same : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_ne
      -- Both if-then-else evaluate to the same thing
      have h_if_eq : (if g hd = true then 1 else 0) = (if f hd = true then 1 else 0) := by
        simp [h_hd_same]
      rw [h_if_eq]
      have h_tl_unchanged : ∀ x ∈ tl, x ≠ a → g x = f x := by
        intro x hx h_ne'
        exact h_unchanged x (List.mem_cons.mpr (Or.inr hx)) h_ne'
      have := ih h_tl h_nodup_tl h_tl_unchanged
      omega

/--
**Lemma (countP with function update - increase)**

When we update a function `f` so that element `a` now satisfies the predicate,
and `a` appears exactly once in the list, countP increases by 1.

This captures: active count increases when node goes pending -> active.
-/
theorem countP_update_increases [DecidableEq α] (l : List α) (a : α) (f g : α → Bool)
    (h_mem : a ∈ l)
    (h_nodup : l.Nodup)
    (h_old : f a = false)
    (h_new : g a = true)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.countP g = l.countP f + 1 := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [List.countP_cons]
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      -- a is the head
      subst h_eq
      -- g a = true, so (if g a = true then 1 else 0) = 1
      have hg : (if g a = true then 1 else 0) = 1 := by simp [h_new]
      -- f a = false, so (if f a = true then 1 else 0) = 0
      have hf : (if f a = true then 1 else 0) = 0 := by simp [h_old]
      rw [hg, hf]
      have h_tl_unchanged : ∀ x ∈ tl, g x = f x := by
        intro x hx
        have h_ne : x ≠ a := by
          intro heq
          subst heq
          exact (List.nodup_cons.mp h_nodup).1 hx
        exact h_unchanged x (List.mem_cons.mpr (Or.inr hx)) h_ne
      have h_countP_eq : tl.countP g = tl.countP f := by
        apply List.countP_congr
        intro x hx
        exact bool_eq_to_iff (h_tl_unchanged x hx)
      rw [h_countP_eq]
    | inr h_tl =>
      -- a is in the tail
      have h_nodup_tl := (List.nodup_cons.mp h_nodup).2
      have h_ne : hd ≠ a := by
        intro heq
        subst heq
        exact (List.nodup_cons.mp h_nodup).1 h_tl
      have h_hd_same : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_ne
      have h_if_eq : (if g hd = true then 1 else 0) = (if f hd = true then 1 else 0) := by
        simp [h_hd_same]
      rw [h_if_eq]
      have h_tl_unchanged : ∀ x ∈ tl, x ≠ a → g x = f x := by
        intro x hx h_ne'
        exact h_unchanged x (List.mem_cons.mpr (Or.inr hx)) h_ne'
      have := ih h_tl h_nodup_tl h_tl_unchanged
      omega

end CountPUpdate

section CountPPreserved

variable {α : Type*}

/--
**Lemma (countP preserved)**

When the predicate is unchanged on all list elements, countP is unchanged.
-/
theorem countP_update_preserved (l : List α) (f g : α → Bool)
    (h_unchanged : ∀ x ∈ l, g x = f x) :
    l.countP g = l.countP f := by
  apply List.countP_congr
  intro x hx
  constructor <;> intro h
  · rw [← h_unchanged x hx]; exact h
  · rw [h_unchanged x hx]; exact h

/--
**Lemma (countP positive implies exists)**

If countP is positive, there exists an element satisfying the predicate.
-/
theorem countP_pos_exists (l : List α) (p : α → Bool)
    (h_pos : l.countP p > 0) :
    ∃ x ∈ l, p x = true := by
  induction l with
  | nil => simp at h_pos
  | cons hd tl ih =>
    simp only [List.countP_cons] at h_pos
    by_cases hp : p hd
    · exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), hp⟩
    · have h_cond : (if p hd = true then 1 else 0) = 0 := by simp [hp]
      rw [h_cond] at h_pos
      obtain ⟨x, hx_mem, hx_p⟩ := ih h_pos
      exact ⟨x, List.mem_cons.mpr (Or.inr hx_mem), hx_p⟩

/--
**Lemma (member satisfying predicate implies positive countP)**

If an element in the list satisfies the predicate, countP is positive.
-/
theorem countP_pos_of_mem_sat (l : List α) (p : α → Bool) (a : α)
    (h_mem : a ∈ l)
    (h_sat : p a = true) :
    l.countP p ≥ 1 := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [List.countP_cons]
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      subst h_eq
      have h_cond : (if p a = true then 1 else 0) = 1 := by simp [h_sat]
      rw [h_cond]
      omega
    | inr h_tl =>
      have := ih h_tl
      omega

end CountPPreserved

/-! =========== WORKFLOW-SPECIFIC COUNTING =========== -/

section WorkflowCounting

/--
**Theorem (Pending to Active Decreases Pending Count)**

When node n transitions from pending to active:
- pending_count decreases by 1 (assuming n is in the node list and list is Nodup)
-/
theorem pending_to_active_decreases
    (nodes : List Nat) (old_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_nodup : nodes.Nodup)
    (h_was_pending : old_states n = true) :
    let new_states := fun x => if x = n then false else old_states x
    nodes.countP new_states + 1 = nodes.countP old_states := by
  intro new_states
  apply countP_update_decreases nodes n old_states new_states h_mem h_nodup h_was_pending
  · simp [new_states]
  · intro x _ hne
    simp [new_states, hne]

/--
**Theorem (Active to Completed Decreases Active Count)**

When node n transitions from active to completed:
- active_count decreases by 1 (assuming n is in the node list and list is Nodup)
-/
theorem active_to_completed_decreases
    (nodes : List Nat) (old_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_nodup : nodes.Nodup)
    (h_was_active : old_states n = true) :
    let new_states := fun x => if x = n then false else old_states x
    nodes.countP new_states + 1 = nodes.countP old_states := by
  exact pending_to_active_decreases nodes old_states n h_mem h_nodup h_was_active

/--
**Theorem (Pending Count Non-Negative Bound)**

After decreasing pending count, result is non-negative (implicit in Nat).
If count was positive and we decreased, new count = old - 1.
-/
theorem pending_count_decrease_eq
    (nodes : List Nat) (old_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_nodup : nodes.Nodup)
    (h_was_pending : old_states n = true) :
    let new_states := fun x => if x = n then false else old_states x
    nodes.countP old_states ≥ 1 ∧
    nodes.countP new_states = nodes.countP old_states - 1 := by
  intro new_states
  have h_pos := countP_pos_of_mem_sat nodes old_states n h_mem h_was_pending
  have h_dec := pending_to_active_decreases nodes old_states n h_mem h_nodup h_was_pending
  -- h_dec says: nodes.countP new_states + 1 = nodes.countP old_states
  constructor
  · exact h_pos
  · -- From h_dec: new + 1 = old, so new = old - 1 (since old >= 1)
    have : nodes.countP new_states + 1 = nodes.countP old_states := h_dec
    omega

/--
**Theorem (Active Count Increases When Node Becomes Active)**

When node n transitions from pending to active:
- active_count increases by 1 (assuming n is in the node list and list is Nodup)
-/
theorem pending_to_active_increases_active
    (nodes : List Nat) (old_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_nodup : nodes.Nodup)
    (h_was_not_active : old_states n = false) :
    let new_states := fun x => if x = n then true else old_states x
    nodes.countP new_states = nodes.countP old_states + 1 := by
  intro new_states
  apply countP_update_increases nodes n old_states new_states h_mem h_nodup h_was_not_active
  · simp [new_states]
  · intro x _ hne
    simp [new_states, hne]

end WorkflowCounting

/-! =========== MEASURE ARITHMETIC =========== -/

section MeasureArithmetic

/--
**Lemma (Start Node Measure Decreases)**

When pending -> active:
- pending decreases by 1 (worth 1000)
- active increases by 1 (worth 100)
- Net change: -1000 + 100 = -900

This proves the measure strictly decreases.
-/
theorem start_measure_decreases (pending_old active_old : Nat)
    (h_pending_pos : pending_old ≥ 1) :
    let pending_new := pending_old - 1
    let active_new := active_old + 1
    pending_new * 1000 + active_new * 100 < pending_old * 1000 + active_old * 100 := by
  intro pending_new active_new
  simp only [pending_new, active_new]
  omega

/--
**Lemma (Complete/Fail Node Measure Decreases)**

When active -> completed/failed:
- active decreases by 1 (worth 100)
- Net change: -100
-/
theorem complete_measure_decreases (active_old : Nat)
    (h_active_pos : active_old ≥ 1) :
    let active_new := active_old - 1
    active_new * 100 < active_old * 100 := by
  intro active_new
  simp only [active_new]
  omega

end MeasureArithmetic

end Lion
