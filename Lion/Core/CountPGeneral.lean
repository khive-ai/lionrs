/-
Lion/Core/CountPGeneral.lean
============================

General countP lemmas that do NOT require Nodup.

Key insight: For measure decrease proofs, we don't need exact counts.
If element `a` appears k >= 1 times in the list, countP changes by k.
Since k >= 1 (from h_mem), strict decrease still holds.
-/

import Mathlib.Data.List.Count
import Mathlib.Data.List.Basic

namespace Lion

/-! =========== GENERAL COUNTING LEMMAS (NO NODUP) =========== -/

section CountPGeneral

variable {α : Type*}

/--
**Lemma (countP with predicate weakening)**

If g x implies f x for all x, then countP g <= countP f.
-/
theorem countP_mono_pred (l : List α) (f g : α → Bool)
    (h_impl : ∀ x ∈ l, g x = true → f x = true) :
    l.countP g ≤ l.countP f := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons]
    have ih_applied : tl.countP g ≤ tl.countP f := by
      apply ih
      intro x hx
      exact h_impl x (List.mem_cons.mpr (Or.inr hx))
    by_cases hg : g hd = true
    · -- g hd = true, so f hd = true by h_impl
      have hf : f hd = true := h_impl hd (List.mem_cons.mpr (Or.inl rfl)) hg
      -- (if g hd = true then 1 else 0) = (if true = true then 1 else 0) = 1
      -- (if f hd = true then 1 else 0) = (if true = true then 1 else 0) = 1
      have hcg : (if g hd = true then 1 else 0) = 1 := by rw [hg]; rfl
      have hcf : (if f hd = true then 1 else 0) = 1 := by rw [hf]; rfl
      rw [hcg, hcf]
      exact Nat.add_le_add_right ih_applied 1
    · -- g hd = false
      simp only [Bool.not_eq_true] at hg
      have hcg : (if g hd = true then 1 else 0) = 0 := by rw [hg]; rfl
      rw [hcg]
      by_cases hf : f hd = true
      · have hcf : (if f hd = true then 1 else 0) = 1 := by rw [hf]; rfl
        rw [hcf]
        exact Nat.le_add_right_of_le ih_applied
      · simp only [Bool.not_eq_true] at hf
        have hcf : (if f hd = true then 1 else 0) = 0 := by rw [hf]; rfl
        rw [hcf]
        exact ih_applied

/--
**Lemma (countP strictly decreases when element stops satisfying)**

When we update so that element `a` no longer satisfies the predicate,
and `a` is in the list, countP strictly decreases.

NO NODUP REQUIRED. If `a` appears multiple times, countP decreases by
the count of `a`, which is >= 1 since a ∈ l.

This is the key lemma for proving workflow measure decrease.
-/
theorem countP_update_decreases_general [DecidableEq α] (l : List α) (a : α) (f g : α → Bool)
    (h_mem : a ∈ l)
    (h_old : f a = true)
    (h_new : g a = false)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.countP g < l.countP f := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [List.countP_cons]
    by_cases h_hd_eq : hd = a
    · -- hd = a
      -- g hd = g a = false, f hd = f a = true
      have hg_hd : g hd = false := by rw [h_hd_eq]; exact h_new
      have hf_hd : f hd = true := by rw [h_hd_eq]; exact h_old
      simp [hg_hd, hf_hd]
      -- Goal: tl.countP g < tl.countP f + 1
      -- We have tl.countP g <= tl.countP f
      suffices h : tl.countP g ≤ tl.countP f by omega
      -- For x in tl: if x = a, then g x = false <= f x; if x ≠ a, g x = f x
      apply countP_mono_pred
      intro x hx hgx
      by_cases h_x_eq : x = a
      · -- x = a, but g a = false, contradicts hgx
        rw [h_x_eq, h_new] at hgx
        exact absurd hgx Bool.false_ne_true
      · -- x ≠ a, so g x = f x
        have := h_unchanged x (List.mem_cons.mpr (Or.inr hx)) h_x_eq
        rw [← this]
        exact hgx
    · -- hd ≠ a
      have h_mem_tl : a ∈ tl := by
        cases List.mem_cons.mp h_mem with
        | inl h => exact absurd h.symm h_hd_eq
        | inr h => exact h
      have h_same : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_hd_eq
      have h_unchanged_tl : ∀ x ∈ tl, x ≠ a → g x = f x := fun x hx hne =>
        h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne
      have h_ih := ih h_mem_tl h_unchanged_tl
      by_cases hf : f hd = true
      · -- f hd = true, g hd = true (since g hd = f hd)
        have hg : g hd = true := by rw [h_same]; exact hf
        simp [hg, hf]
        omega
      · -- f hd = false, g hd = false
        simp only [Bool.not_eq_true] at hf
        have hg : g hd = false := by rw [h_same]; exact hf
        simp [hg, hf]
        exact h_ih

/--
**Lemma (countP strictly increases when element starts satisfying)**

When we update so that element `a` now satisfies the predicate,
and `a` is in the list, countP strictly increases.

NO NODUP REQUIRED.
-/
theorem countP_update_increases_general [DecidableEq α] (l : List α) (a : α) (f g : α → Bool)
    (h_mem : a ∈ l)
    (h_old : f a = false)
    (h_new : g a = true)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.countP g > l.countP f := by
  -- This is symmetric to countP_update_decreases_general
  have := countP_update_decreases_general l a g f h_mem h_new h_old
    (fun x hx hne => (h_unchanged x hx hne).symm)
  exact this

/--
**Lemma (Exact countP change equals count)**

When element `a` changes from satisfying to not satisfying the predicate,
the decrease in countP equals the count of `a` in the list.

This is crucial for proving that pending_drop = active_rise in start_node.
-/
theorem countP_change_eq_count [DecidableEq α] (l : List α) (a : α) (f g : α → Bool)
    (h_old : f a = true)
    (h_new : g a = false)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.countP f = l.countP g + l.count a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons, List.count_cons]
    by_cases h_hd_eq : hd = a
    · -- hd = a
      have hf_hd : f hd = true := by rw [h_hd_eq]; exact h_old
      have hg_hd : g hd = false := by rw [h_hd_eq]; exact h_new
      have h_beq_true : (hd == a) = true := by simp only [beq_iff_eq, h_hd_eq]
      simp [hf_hd, hg_hd, h_beq_true]
      -- IH: tl.countP f = tl.countP g + tl.count a
      have h_ih := ih (fun x hx hne => h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne)
      omega
    · -- hd ≠ a
      have h_same : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_hd_eq
      have h_beq_false : (hd == a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact h_hd_eq
      simp only [h_beq_false]
      by_cases hf : f hd = true
      · have hg : g hd = true := by rw [h_same]; exact hf
        simp [hf, hg]
        have h_ih := ih (fun x hx hne => h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne)
        omega
      · simp only [Bool.not_eq_true] at hf
        have hg : g hd = false := by rw [h_same]; exact hf
        simp [hf, hg]
        exact ih (fun x hx hne => h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne)

/--
**Corollary: pending_drop and active_rise are both count(n)**

For start_node: both the decrease in pending and increase in active
equal List.count n nodes.
-/
theorem countP_symmetric_change [DecidableEq α] (l : List α) (a : α) (f_old g_new f_other g_other : α → Bool)
    (h_f_old_a : f_old a = true)
    (h_g_new_a : g_new a = false)
    (h_f_other_a : f_other a = false)
    (h_g_other_a : g_other a = true)
    (h_f_unchanged : ∀ x ∈ l, x ≠ a → g_new x = f_old x)
    (h_g_unchanged : ∀ x ∈ l, x ≠ a → g_other x = f_other x) :
    l.countP f_old - l.countP g_new = l.countP g_other - l.countP f_other := by
  -- LHS = count a (by countP_change_eq_count)
  -- RHS = count a (by countP_change_eq_count on the other pair)
  have h_lhs := countP_change_eq_count l a f_old g_new h_f_old_a h_g_new_a h_f_unchanged
  -- For RHS, we have f_other a = false, g_other a = true (opposite direction)
  -- countP g_other = countP f_other + count a
  have h_rhs := countP_change_eq_count l a g_other f_other h_g_other_a h_f_other_a
    (fun x hx hne => (h_g_unchanged x hx hne).symm)
  -- h_lhs: countP f_old = countP g_new + count a → countP f_old - countP g_new = count a
  -- h_rhs: countP g_other = countP f_other + count a → countP g_other - countP f_other = count a
  omega

end CountPGeneral

/-! =========== WORKFLOW-SPECIFIC LEMMAS (NO NODUP) =========== -/

section WorkflowCountingGeneral

/--
**Theorem (Pending Decreases - General)**

When node n transitions from pending to not-pending (e.g., active):
- pending_count strictly decreases

NO NODUP REQUIRED.
-/
theorem pending_decreases_general
    (nodes : List Nat) (old_states new_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_was_pending : old_states n = true)
    (h_not_pending : new_states n = false)
    (h_unchanged : ∀ x ∈ nodes, x ≠ n → new_states x = old_states x) :
    nodes.countP new_states < nodes.countP old_states :=
  countP_update_decreases_general nodes n old_states new_states h_mem h_was_pending h_not_pending h_unchanged

/--
**Theorem (Active Increases - General)**

When node n transitions from not-active to active:
- active_count strictly increases

NO NODUP REQUIRED.
-/
theorem active_increases_general
    (nodes : List Nat) (old_states new_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_was_not_active : old_states n = false)
    (h_now_active : new_states n = true)
    (h_unchanged : ∀ x ∈ nodes, x ≠ n → new_states x = old_states x) :
    nodes.countP new_states > nodes.countP old_states :=
  countP_update_increases_general nodes n old_states new_states h_mem h_was_not_active h_now_active h_unchanged

/--
**Theorem (Active Decreases - General)**

When node n transitions from active to not-active (completed/failed):
- active_count strictly decreases

NO NODUP REQUIRED.
-/
theorem active_decreases_general
    (nodes : List Nat) (old_states new_states : Nat → Bool) (n : Nat)
    (h_mem : n ∈ nodes)
    (h_was_active : old_states n = true)
    (h_not_active : new_states n = false)
    (h_unchanged : ∀ x ∈ nodes, x ≠ n → new_states x = old_states x) :
    nodes.countP new_states < nodes.countP old_states :=
  countP_update_decreases_general nodes n old_states new_states h_mem h_was_active h_not_active h_unchanged

end WorkflowCountingGeneral

/-! =========== MEASURE ARITHMETIC (General) =========== -/

section MeasureArithmeticGeneral

/--
**Lemma (Start Measure Decreases - General)**

When pending_count decreases by at least 1 and active_count increases by at least 1:
- Net change in measure = -(pending_drop * 1000) + (active_rise * 100)
- If pending_drop >= active_rise >= 1, net change <= -900

In the no-dup case, pending_drop = active_rise = 1.
In the general case (with duplicates), pending_drop = active_rise = count(n) >= 1.
Either way, measure strictly decreases.
-/
theorem start_measure_decreases_general
    (pending_old pending_new active_old active_new : Nat)
    (h_pending_dec : pending_new < pending_old)
    (h_active_inc : active_new > active_old)
    -- Key constraint: the decrease in pending >= increase in active
    -- (true when both equal count(n))
    (h_balance : pending_old - pending_new ≥ active_new - active_old) :
    pending_new * 1000 + active_new * 100 < pending_old * 1000 + active_old * 100 := by
  -- Let d = pending_old - pending_new >= 1
  -- Let r = active_new - active_old >= 1
  -- h_balance says d >= r
  -- Old measure contribution: pending_old * 1000 + active_old * 100
  -- New measure contribution: pending_new * 1000 + active_new * 100
  --   = (pending_old - d) * 1000 + (active_old + r) * 100
  --   = pending_old * 1000 - d * 1000 + active_old * 100 + r * 100
  --   = old - d * 1000 + r * 100
  --   = old - (d * 1000 - r * 100)
  -- Since d >= r >= 1: d * 1000 - r * 100 >= d * 1000 - d * 100 = d * 900 >= 900 > 0
  -- So new < old
  have h_d_pos : pending_old - pending_new ≥ 1 := Nat.sub_pos_of_lt h_pending_dec
  have h_r_pos : active_new - active_old ≥ 1 := Nat.sub_pos_of_lt h_active_inc
  -- The decrease in weighted pending exceeds the increase in weighted active
  -- d * 1000 > r * 100 because d >= r and 1000 > 100
  have h_key : (pending_old - pending_new) * 1000 > (active_new - active_old) * 100 := by
    -- d * 1000 >= r * 1000 (since d >= r)
    -- r * 1000 > r * 100 (since r >= 1 and 1000 > 100)
    have h1 : (pending_old - pending_new) * 1000 ≥ (active_new - active_old) * 1000 :=
      Nat.mul_le_mul_right 1000 h_balance
    have h2 : (active_new - active_old) * 1000 > (active_new - active_old) * 100 := by
      have : active_new - active_old ≥ 1 := h_r_pos
      omega
    omega
  omega

/--
**Lemma (Complete/Fail Measure Decreases - General)**

When active_count decreases by at least 1, measure decreases by at least 100.
-/
theorem complete_measure_decreases_general
    (active_old active_new : Nat)
    (h_active_dec : active_new < active_old) :
    active_new * 100 < active_old * 100 := by
  have h_d_pos : active_old - active_new ≥ 1 := Nat.sub_pos_of_lt h_active_dec
  omega

end MeasureArithmeticGeneral

/-! =========== FOLDL SUM LEMMAS (for retry) =========== -/

section FoldlSumGeneral

variable {α : Type*}

/--
**Helper lemma**: foldl with addition from offset c is c + foldl from 0.
-/
theorem foldl_add_offset
    (l : List α) (f : α → Nat) (c : Nat) :
    l.foldl (fun acc x => acc + f x) c = c + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (c + f hd), ih (0 + f hd)]
    omega

/--
**Helper lemma**: foldl with addition is monotonic when g x <= f x for all x.
-/
theorem foldl_add_le_of_pointwise_le
    (l : List α) (f g : α → Nat)
    (h_le : ∀ x ∈ l, g x ≤ f x) :
    l.foldl (fun acc x => acc + g x) 0 ≤ l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd_le : g hd ≤ f hd := h_le hd (List.mem_cons.mpr (Or.inl rfl))
    have h_tl_le : ∀ x ∈ tl, g x ≤ f x := fun x hx => h_le x (List.mem_cons.mpr (Or.inr hx))
    have h_ih : tl.foldl (fun acc x => acc + g x) 0 ≤ tl.foldl (fun acc x => acc + f x) 0 := ih h_tl_le
    rw [foldl_add_offset tl g (0 + g hd), foldl_add_offset tl f (0 + f hd)]
    omega

/--
**Theorem (foldl add with single element decrease)**

When we update a function so that element `a` has a smaller value,
and `a` is in the list, the sum strictly decreases.

NO NODUP REQUIRED. If `a` appears multiple times, sum decreases by
count(a) × decrease_amount, which is >= decrease_amount >= 1.
-/
theorem foldl_add_strict_decrease_of_single [DecidableEq α]
    (l : List α) (a : α) (f g : α → Nat)
    (h_mem : a ∈ l)
    (h_dec : g a < f a)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.foldl (fun acc x => acc + g x) 0 < l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil =>
    simp only [List.not_mem_nil] at h_mem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases h_hd_eq : hd = a
    · -- hd = a: g hd < f hd
      -- For elements in tl: either x = a (g x < f x) or x ≠ a (g x = f x <= f x)
      have h_tl_le : ∀ x ∈ tl, g x ≤ f x := by
        intro x hx
        by_cases hxa : x = a
        · rw [hxa]; exact Nat.le_of_lt h_dec
        · exact Nat.le_of_eq (h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hxa)
      -- Use foldl_add_offset to rewrite
      rw [foldl_add_offset tl g (0 + g hd), foldl_add_offset tl f (0 + f hd)]
      have h_le : tl.foldl (fun acc x => acc + g x) 0 ≤ tl.foldl (fun acc x => acc + f x) 0 :=
        foldl_add_le_of_pointwise_le tl f g h_tl_le
      -- g hd < f hd since hd = a
      have h_hd_lt : g hd < f hd := by rw [h_hd_eq]; exact h_dec
      omega
    · -- hd ≠ a: g hd = f hd, and a must be in tl
      have h_a_in_tl : a ∈ tl := by
        cases List.mem_cons.mp h_mem with
        | inl h => exact absurd h.symm h_hd_eq
        | inr h => exact h
      have h_eq_hd : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_hd_eq
      have h_unchanged_tl : ∀ x ∈ tl, x ≠ a → g x = f x :=
        fun x hx hne => h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne
      -- Apply IH to get: tl.foldl (· + g ·) 0 < tl.foldl (· + f ·) 0
      have h_ih := ih h_a_in_tl h_unchanged_tl
      -- Use foldl_add_offset to shift the inequality
      rw [foldl_add_offset tl g (0 + g hd), foldl_add_offset tl f (0 + f hd), h_eq_hd]
      omega

/--
**Theorem (Exact foldl decrease equals count × delta)**

When we update a function so that element `a` decreases by `delta`,
the sum decreases by exactly `count(a) × delta`.

This is crucial for proving retry_decreases_measure where we need
to show retries_drop = count(n) × 1 = count(n) = pending_rise = active_drop.
-/
theorem foldl_add_change_eq_count_mul [DecidableEq α]
    (l : List α) (a : α) (f g : α → Nat) (delta : Nat)
    (h_dec : f a = g a + delta)
    (h_unchanged : ∀ x ∈ l, x ≠ a → g x = f x) :
    l.foldl (fun acc x => acc + f x) 0 = l.foldl (fun acc x => acc + g x) 0 + l.count a * delta := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.count_cons]
    have h_ih := ih (fun x hx hne => h_unchanged x (List.mem_cons.mpr (Or.inr hx)) hne)
    rw [foldl_add_offset tl f (0 + f hd), foldl_add_offset tl g (0 + g hd)]
    rw [foldl_add_offset tl f 0, foldl_add_offset tl g 0] at h_ih
    by_cases h_hd_eq : hd = a
    · -- hd = a: f hd = g hd + delta
      have hf_hd : f hd = g hd + delta := by rw [h_hd_eq]; exact h_dec
      have h_beq_true : (hd == a) = true := by simp only [beq_iff_eq, h_hd_eq]
      simp only [h_beq_true, ↓reduceIte, Nat.add_mul, Nat.one_mul]
      -- Goal: 0 + f hd + foldl f = 0 + g hd + foldl g + (count * delta + delta)
      omega
    · -- hd ≠ a: g hd = f hd
      have h_same : g hd = f hd := h_unchanged hd (List.mem_cons.mpr (Or.inl rfl)) h_hd_eq
      have h_beq_false : (hd == a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact h_hd_eq
      -- Simplify the if-then-else in count
      have h_ite : (if (hd == a) = true then 1 else 0) = 0 := by
        rw [h_beq_false]
        rfl
      simp only [h_ite, Nat.add_zero]
      -- Goal: 0 + f hd + foldl f = 0 + g hd + foldl g + count * delta
      omega

end FoldlSumGeneral

end Lion
