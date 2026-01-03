/-
Lion/State/Kernel.lean
=======================

Kernel state for the trusted computing base.
-/

import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Lion.Core.Identifiers
import Lion.Core.Crypto
import Lion.Core.Policy

namespace Lion

/-! =========== REVOCATION STATE (005) =========== -/

/-- Capability table in kernel -/
abbrev CapTable := Std.HashMap CapId Capability

/-- Revocation epoch tracking -/
structure RevocationState where
  caps      : CapTable
  epoch     : Nat  -- Global revocation epoch
-- Note: Cannot derive Repr due to HashMap lacking Repr instance

namespace RevocationState

/-- Empty revocation state -/
def empty : RevocationState where
  caps := {}
  epoch := 0

/-- Check if capability exists and is valid -/
def is_valid (rs : RevocationState) (capId : CapId) : Bool :=
  match rs.caps.get? capId with
  | some cap => cap.valid
  | none => false

/-- Revoke capability by ID (single cap only, use revoke_transitive for full revocation) -/
def revoke (rs : RevocationState) (capId : CapId) : RevocationState :=
  match rs.caps.get? capId with
  | some cap =>
      { rs with caps := rs.caps.insert capId { cap with valid := false } }
  | none => rs

/-- Check if ancestorId is in the parent chain of capId.
    Uses fuel for termination (ParentLt guarantees termination with fuel = capId). -/
def has_ancestor (caps : CapTable) (capId ancestorId : CapId) (fuel : Nat := capId) : Bool :=
  if fuel = 0 then false
  else match caps.get? capId with
  | none => false
  | some cap =>
      match cap.parent with
      | none => false
      | some pid => pid == ancestorId || has_ancestor caps pid ancestorId (fuel - 1)

/-- Revoke capability and all descendants transitively.
    Sets valid=false on capId and any cap whose parent chain includes capId.
    Preserves ValidParentPresent invariant.

    Uses HashMap.map for cleaner proofs via getElem?_map lemma. -/
def revoke_transitive (rs : RevocationState) (capId : CapId) : RevocationState :=
  let newCaps := rs.caps.map fun k v =>
    if k == capId || has_ancestor rs.caps k capId then
      { v with valid := false }
    else
      v
  { rs with caps := newCaps }

/-! =========== REVOKE_TRANSITIVE LEMMAS =========== -/

/-- Helper: In revoke set means id = capId OR has capId as ancestor -/
def in_revoke_set (caps : CapTable) (k capId : CapId) : Bool :=
  k == capId || has_ancestor caps k capId

/-- Fuel monotonicity: has_ancestor with smaller fuel implies has_ancestor with larger fuel -/
lemma has_ancestor_fuel_mono (caps : CapTable) (capId ancestorId : CapId) :
    ∀ {f f' : Nat}, has_ancestor caps capId ancestorId f = true → f ≤ f' →
      has_ancestor caps capId ancestorId f' = true := by
  intro f f' h_true h_le
  induction f generalizing capId f' with
  | zero =>
    -- has_ancestor with fuel 0 returns false, contradiction
    unfold has_ancestor at h_true
    simp at h_true
  | succ n ih =>
    -- n.succ ≤ f' means f' ≥ 1, so f' = m.succ for some m
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ n) h_le))
    -- Unfold both has_ancestors
    unfold has_ancestor at h_true ⊢
    simp only [Nat.succ_ne_zero, ↓reduceIte] at h_true ⊢
    -- Match on caps.get? capId
    cases h_get : caps.get? capId with
    | none =>
      simp only [h_get] at h_true
      cases h_true  -- false = true is a contradiction
    | some cap =>
      simp only [h_get] at h_true ⊢
      -- Match on cap.parent
      cases h_parent : cap.parent with
      | none =>
        simp only [h_parent] at h_true
        cases h_true  -- false = true is a contradiction
      | some p =>
        simp only [h_parent, Bool.or_eq_true, beq_iff_eq] at h_true ⊢
        cases h_true with
        | inl h_eq => exact Or.inl h_eq
        | inr h_rec =>
          apply Or.inr
          -- Need: has_ancestor caps p ancestorId m = true
          -- Have: has_ancestor caps p ancestorId n = true (h_rec)
          -- Since n.succ ≤ m.succ, we have n ≤ m
          -- Note: n + 1 - 1 = n by Nat.add_sub_cancel
          have h_rec' : has_ancestor caps p ancestorId n = true := by
            simp only [Nat.add_sub_cancel] at h_rec; exact h_rec
          exact @ih p m h_rec' (Nat.le_of_succ_le_succ h_le)

/-- If parent is in revoke set, child is also in revoke set.
    Requires: parent_lt invariant (cap.parent = some p → p < cap.id) -/
lemma parent_in_set_implies_child_in_set (caps : CapTable) (k p revokeId : CapId) (c : Capability) :
    -- parent_lt invariant: parent id is strictly less than child id
    (∀ {id : CapId} {cap : Capability} {pid : CapId},
      caps.get? id = some cap → cap.parent = some pid → pid < id) →
    caps.get? k = some c →
    c.parent = some p →
    in_revoke_set caps p revokeId = true →
    in_revoke_set caps k revokeId = true := by
  intro h_parent_lt h_get h_parent h_p_in_set
  unfold in_revoke_set at *
  simp only [Bool.or_eq_true, beq_iff_eq] at *
  -- Get p < k from parent_lt
  have h_lt : p < k := h_parent_lt h_get h_parent
  -- k ≠ 0 since p < k and p ≥ 0
  have h_k_ne_zero : k ≠ 0 := Nat.ne_zero_of_lt h_lt
  right
  -- Unfold has_ancestor for k
  unfold has_ancestor
  split
  case isTrue h_eq => exact absurd h_eq h_k_ne_zero
  case isFalse _ =>
    -- Look up k, get c with parent p
    -- Goal has: match caps.get? k with ...
    -- h_get : caps.get? k = some c
    simp only [h_get, h_parent, Bool.or_eq_true, beq_iff_eq]
    cases h_p_in_set with
    | inl h_eq => exact Or.inl h_eq
    | inr h_anc =>
      apply Or.inr
      -- has_ancestor caps p revokeId (default fuel p) = true
      -- Need: has_ancestor caps p revokeId (k - 1) = true
      -- Since p < k, we have k - 1 ≥ p (for k > 0)
      apply has_ancestor_fuel_mono caps p revokeId h_anc
      exact Nat.le_sub_one_of_lt h_lt

/-- revoke_transitive only modifies the valid field.
    Key insight: map only does {v with valid := false}, preserving all other fields.
    Uses getElem?_map lemma for clean proof. -/
theorem revoke_transitive_preserves_structure (rs : RevocationState) (capId : CapId) :
    ∀ k c, (rs.revoke_transitive capId).caps.get? k = some c →
    ∃ c', rs.caps.get? k = some c' ∧
      c.id = c'.id ∧ c.rights = c'.rights ∧
      c.target = c'.target ∧ c.parent = c'.parent ∧ c.epoch = c'.epoch ∧
      c.holder = c'.holder ∧ c.signature = c'.signature := by
  intro k c h_get
  unfold revoke_transitive at h_get
  simp only at h_get
  -- Convert get? to getElem? notation for lemma application
  rw [Std.HashMap.get?_eq_getElem?] at h_get
  -- Apply getElem?_map: (map f m)[k]? = Option.map (f k) m[k]?
  rw [Std.HashMap.getElem?_map] at h_get
  -- h_get : Option.map (f k) (rs.caps[k]?) = some c
  cases h_orig : rs.caps[k]? with
  | none =>
    -- If original had no entry, map returns none, contradiction
    simp [h_orig] at h_get
  | some c' =>
    -- Original had c', map applies f to get c
    simp [h_orig] at h_get
    -- h_get : f k c' = c where f k v = if condition then {v with valid:=false} else v
    use c'
    constructor
    · -- rs.caps.get? k = some c'
      rw [Std.HashMap.get?_eq_getElem?]
      exact h_orig
    -- Now prove structural fields are equal
    -- Split on condition: if condition = true then {c' with valid := false} else c'
    split at h_get
    · -- In revoke set: c = {c' with valid := false}
      cases h_get
      simp only [and_self]
    · -- Not in revoke set: c = c'
      cases h_get
      simp only [and_self]

/-- revoke_transitive preserves keys_match (cap.id = key).
    Key insight: map doesn't change cap.id, only valid field. -/
theorem revoke_transitive_preserves_keys_match (rs : RevocationState) (capId : CapId) :
    (∀ {k : CapId} {c : Capability}, rs.caps.get? k = some c → c.id = k) →
    (∀ {k : CapId} {c : Capability}, (rs.revoke_transitive capId).caps.get? k = some c → c.id = k) := by
  intro h_keys_match
  intro (k : CapId) (c : Capability) (h_get : (rs.revoke_transitive capId).caps.get? k = some c)
  -- From structure preservation: c.id = c'.id where c' is original cap at k
  obtain ⟨c', h_c'_get, h_id_eq, _⟩ := revoke_transitive_preserves_structure rs capId k c h_get
  -- c.id = c'.id and c'.id = k (from h_keys_match)
  rw [h_id_eq]
  exact h_keys_match h_c'_get

/-- revoke_transitive preserves parent_lt (parent.id < cap.id).
    Key insight: map doesn't change cap.id or cap.parent, only valid field. -/
theorem revoke_transitive_preserves_parent_lt (rs : RevocationState) (capId : CapId) :
    (∀ {id : CapId} {c : Capability} {p : CapId}, rs.caps.get? id = some c → c.parent = some p → p < id) →
    (∀ {id : CapId} {c : Capability} {p : CapId}, (rs.revoke_transitive capId).caps.get? id = some c → c.parent = some p → p < id) := by
  intro h_parent_lt
  intro (k : CapId) (c : Capability) (p : CapId)
       (h_get : (rs.revoke_transitive capId).caps.get? k = some c) (h_parent : c.parent = some p)
  -- From structure preservation: c.parent = c'.parent and lookup is at key k
  obtain ⟨c', h_c'_get, h_id_eq, _, _, h_parent_eq, _, _, _⟩ :=
    revoke_transitive_preserves_structure rs capId k c h_get
  -- c.parent = c'.parent, so c'.parent = some p
  have h_c'_parent : c'.parent = some p := by rw [← h_parent_eq]; exact h_parent
  -- Apply h_parent_lt with id=k: p < k
  -- h_c'_get : rs.caps.get? k = some c'
  have h_lt : p < k := @h_parent_lt k c' p h_c'_get h_c'_parent
  exact h_lt

/-- Key lemma: If cap NOT in revoke set, valid field unchanged.
    Converse: If cap.valid=true after, then it was valid=true before AND not in revoke set. -/
theorem revoke_transitive_valid_preserved (rs : RevocationState) (capId : CapId) :
    ∀ k c, (rs.revoke_transitive capId).caps.get? k = some c →
    c.valid = true →
    ¬in_revoke_set rs.caps k capId ∧
    ∃ c', rs.caps.get? k = some c' ∧ c'.valid = true := by
  intro k c h_get h_valid
  unfold revoke_transitive at h_get
  simp only at h_get
  -- Apply getElem?_map
  rw [Std.HashMap.get?_eq_getElem?] at h_get
  rw [Std.HashMap.getElem?_map] at h_get
  -- h_get : Option.map (f k) (rs.caps[k]?) = some c
  cases h_orig : rs.caps[k]? with
  | none =>
    -- Impossible: map of none is none
    simp [h_orig] at h_get
  | some c' =>
    -- c = f k c' where f applies the if-then-else
    simp only [h_orig, Option.map_some] at h_get
    -- Now we have: (if condition then {c' with valid:=false} else c') = c
    -- And h_valid says c.valid = true
    by_cases h_cond : (k == capId || has_ancestor rs.caps k capId) = true
    · -- In revoke set: c = {c' with valid := false}, so c.valid = false
      simp only [h_cond, ↓reduceIte] at h_get
      cases h_get
      -- h_valid : false = true - contradiction
      cases h_valid
    · -- Not in revoke set: c = c'
      simp only [h_cond] at h_get
      cases h_get
      -- Now c = c', c.valid = true means c'.valid = true
      constructor
      · -- ¬in_revoke_set rs.caps k capId
        unfold in_revoke_set
        exact h_cond
      · -- ∃ c', rs.caps.get? k = some c' ∧ c'.valid = true
        use c'
        constructor
        · rw [Std.HashMap.get?_eq_getElem?]; exact h_orig
        · exact h_valid

/-- If cap.valid=true after revoke_transitive, then the cap is UNCHANGED from pre-state.
    This is stronger than valid_preserved: it says the exact same cap object exists.
    Key insight: valid=true forces the else branch of the map, returning original cap. -/
theorem revoke_transitive_get?_of_valid_true (rs : RevocationState) (capId : CapId) :
    ∀ k c, (rs.revoke_transitive capId).caps.get? k = some c →
    c.valid = true →
    rs.caps.get? k = some c := by
  intro k c h_get h_valid
  unfold revoke_transitive at h_get
  simp only at h_get
  rw [Std.HashMap.get?_eq_getElem?] at h_get
  rw [Std.HashMap.getElem?_map] at h_get
  cases h_orig : rs.caps[k]? with
  | none =>
    simp [h_orig] at h_get
  | some c' =>
    simp only [h_orig, Option.map_some] at h_get
    -- h_get: (if cond then {c' with valid:=false} else c') = c
    by_cases h_cond : (k == capId || has_ancestor rs.caps k capId) = true
    · -- In revoke set: c = {c' with valid := false}, but h_valid says c.valid = true
      simp only [h_cond, ↓reduceIte] at h_get
      cases h_get
      -- h_valid : false = true - contradiction
      cases h_valid
    · -- Not in revoke set: c = c'
      simp only [h_cond] at h_get
      -- h_get : c' = c, so c = c'
      cases h_get
      rw [Std.HashMap.get?_eq_getElem?]
      exact h_orig

/-- revoke_transitive preserves capability signatures -/
theorem revoke_transitive_preserves_signature (rs : RevocationState) (capId : CapId) :
    ∀ k c, (rs.revoke_transitive capId).caps.get? k = some c →
    ∃ c', rs.caps.get? k = some c' ∧ c.signature = c'.signature := by
  intro k c h_get
  obtain ⟨c', h_get', _, _, _, _, _, _, hsig⟩ :=
    revoke_transitive_preserves_structure rs capId k c h_get
  exact ⟨c', h_get', hsig⟩

/-- Critical lemma: If c.valid=true AND c.parent=some pid after revoke,
    then the parent p also has p.valid=true after revoke.

    PROOF SKETCH:
    - c.valid=true means c NOT in revoke set (revoke_transitive_valid_preserved)
    - c NOT in revoke set means: c.id ≠ capId AND ¬has_ancestor caps c.id capId
    - c.parent = some pid, so c's parent chain = [pid, ...parent's chain...]
    - If pid WERE in revoke set, then has_ancestor caps c.id capId would be true
      (since capId is in c's ancestor chain via pid)
    - Contradiction, so pid NOT in revoke set
    - Therefore p.valid unchanged OR p.valid was already false
    - ValidParentPresent says if c.valid=true in pre, parent.valid=true in pre
    - So p.valid=true in pre, and since p NOT in revoke set, p.valid=true in post -/
theorem revoke_transitive_preserves_parent_valid (rs : RevocationState) (capId : CapId) :
    -- Pre-condition: parent_lt holds (parent id < cap id)
    (∀ {id : CapId} {cap : Capability} {pid : CapId},
      rs.caps.get? id = some cap → cap.parent = some pid → pid < id) →
    -- Pre-condition: ValidParentPresent holds in pre-state
    (∀ {id : CapId} {c : Capability} {p : CapId}, rs.caps.get? id = some c → c.valid = true → c.parent = some p →
      ∃ pcap, rs.caps.get? p = some pcap ∧ pcap.valid = true) →
    -- Post-condition: ValidParentPresent holds in post-state
    (∀ {id : CapId} {c : Capability} {p : CapId}, (rs.revoke_transitive capId).caps.get? id = some c →
      c.valid = true → c.parent = some p →
      ∃ pcap, (rs.revoke_transitive capId).caps.get? p = some pcap ∧ pcap.valid = true) := by
  intro h_parent_lt_inv h_pre
  intro (k : CapId) (c : Capability) (p : CapId)
       (h_get : (rs.revoke_transitive capId).caps.get? k = some c) (h_valid : c.valid = true)
       (h_parent : c.parent = some p)
  -- Step 1: From valid_preserved, c is NOT in revoke set and ∃ c' with c'.valid = true
  obtain ⟨h_not_in_set, c', h_c'_get, h_c'_valid⟩ := revoke_transitive_valid_preserved rs capId k c h_get h_valid
  -- Step 2: From structure preservation, c.parent = c'.parent
  obtain ⟨c'', h_c''_get, _, _, _, h_parent_eq, _, _, _⟩ :=
    revoke_transitive_preserves_structure rs capId k c h_get
  -- c' = c'' (both are the original cap at k)
  have h_c'_eq_c'' : c' = c'' := by
    have h1 : some c' = some c'' := h_c'_get.symm.trans h_c''_get
    injection h1
  rw [h_c'_eq_c''] at h_c'_valid h_c'_get
  -- c''.parent = c.parent = some p
  have h_c''_parent : c''.parent = some p := by rw [← h_parent_eq]; exact h_parent
  -- Step 3: From h_pre, get parent cap pcap with pcap.valid = true in pre-state
  obtain ⟨pcap, h_pcap_get, h_pcap_valid⟩ := h_pre h_c''_get h_c'_valid h_c''_parent
  -- Step 4: Show parent p is NOT in revoke set
  -- Key insight: If p WERE in revoke set, then has_ancestor caps k capId would be true
  -- because k's parent chain starts with p, and p is in revoke set means
  -- either p = capId or capId is ancestor of p, either way capId is in k's ancestor chain
  have h_p_not_in_set : ¬in_revoke_set rs.caps p capId := by
    unfold in_revoke_set at h_not_in_set ⊢
    -- h_not_in_set : ¬(k == capId || has_ancestor rs.caps k capId) = true
    intro h_p_in_set
    -- Show: if p in revoke set, then k is in revoke set (contradiction)
    apply h_not_in_set
    simp only [Bool.or_eq_true, beq_iff_eq]
    -- Need to show: k = capId ∨ has_ancestor rs.caps k capId = true
    -- Use parent_in_set_implies_child_in_set:
    -- If parent p is in revoke set, then child k is also in revoke set
    have h_k_in_set := parent_in_set_implies_child_in_set rs.caps k p capId c''
      h_parent_lt_inv h_c''_get h_c''_parent h_p_in_set
    unfold in_revoke_set at h_k_in_set
    simp only [Bool.or_eq_true, beq_iff_eq] at h_k_in_set
    exact h_k_in_set
  -- Step 5: Since p not in revoke set, pcap in post-state with same valid field
  -- Since p is NOT in revoke set, pcap is returned unchanged by the map
  use pcap
  constructor
  · -- Show parent exists in post-state
    unfold revoke_transitive
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]
    rw [Std.HashMap.get?_eq_getElem?] at h_pcap_get
    simp only [h_pcap_get, Option.map_some]
    -- The if-then-else: p not in revoke set, so we get pcap unchanged
    -- h_p_not_in_set : ¬(p == capId || has_ancestor rs.caps p capId) = true
    -- This means the condition is false
    unfold in_revoke_set at h_p_not_in_set
    have h_cond_false : (p == capId || has_ancestor rs.caps p capId) = false := by
      cases h_cond : (p == capId || has_ancestor rs.caps p capId) with
      | true =>
        simp only [h_cond] at h_p_not_in_set
        exact absurd trivial h_p_not_in_set
      | false => rfl
    simp only [h_cond_false, Bool.false_eq_true, ↓reduceIte]
  · -- Show parent is valid
    exact h_pcap_valid

/-- Insert capability -/
def insert (rs : RevocationState) (cap : Capability) : RevocationState :=
  { rs with caps := rs.caps.insert cap.id cap }

end RevocationState

/-! =========== INDUCTIVE VALIDITY (005) =========== -/

-- Note: Forward declaration of State removed (not needed in Lean4)

/--
Inductive Validity: A capability is valid iff:
1. It exists in the kernel
2. Its 'valid' flag is true
3. If it has a parent, the parent is also Inductively Valid

Design rationale: Avoids Lean's `partial` keyword, enables structural induction.
When parent is revoked, children become invalid because their validity proof
requires parent's validity proof which no longer exists.
-/
inductive IsValid (caps : CapTable) : CapId → Prop where
  | root {c : Capability} :
      caps.get? c.id = some c →
      c.valid = true →
      c.parent = none →
      IsValid caps c.id

  | child {c : Capability} {p_id : CapId} :
      caps.get? c.id = some c →
      c.valid = true →
      c.parent = some p_id →
      IsValid caps p_id →  -- Recursive: parent must be valid
      IsValid caps c.id

/-- Extract capability from IsValid witness -/
theorem IsValid.get_cap {caps : CapTable} {cid : CapId} (h : IsValid caps cid) :
    ∃ c, caps.get? cid = some c ∧ c.valid = true := by
  cases h with
  | root h_get h_valid _ => exact ⟨_, h_get, h_valid⟩
  | child h_get h_valid _ _ => exact ⟨_, h_get, h_valid⟩

/-- Descendant relation for revocation propagation -/
inductive IsDescendant (caps : CapTable) : CapId → CapId → Prop where
  | direct (c p : CapId) :
      (caps.get? c).bind (·.parent) = some p →
      IsDescendant caps c p
  | trans (c mid p : CapId) :
      IsDescendant caps c mid → IsDescendant caps mid p →
      IsDescendant caps c p

/-- Revocation propagates to descendants -/
theorem revocation_propagates {caps : CapTable} {parent child : CapId} :
    IsDescendant caps child parent →
    ¬ IsValid caps parent →
    ¬ IsValid caps child := by
  intro h_desc h_not_valid h_valid_child
  induction h_desc with
  | direct c p h_parent =>
      -- h_parent says child c has parent p in caps
      cases h_valid_child with
      | root h_get h_vld h_no_parent =>
          -- Root case: c has no parent, but h_parent says it does
          simp only [Option.bind_eq_some_iff] at h_parent
          obtain ⟨cap, h_get_cap, h_cap_parent⟩ := h_parent
          rw [h_get] at h_get_cap
          cases h_get_cap
          rw [h_no_parent] at h_cap_parent
          cases h_cap_parent
      | child h_get h_vld h_has_parent h_parent_valid =>
          -- Child case: c has parent p_id, and p_id is valid
          simp only [Option.bind_eq_some_iff] at h_parent
          obtain ⟨cap, h_get_cap, h_cap_parent⟩ := h_parent
          rw [h_get] at h_get_cap
          cases h_get_cap
          rw [h_has_parent] at h_cap_parent
          cases h_cap_parent
          exact h_not_valid h_parent_valid
  | trans c mid p h_cm h_mp ih_cm ih_mp =>
      have h_mid_not_valid : ¬ IsValid caps mid := ih_mp h_not_valid
      exact ih_cm h_mid_not_valid h_valid_child

/-! =========== KERNEL STATE =========== -/

/-- Complete kernel state (TCB) -/
structure KernelState where
  hmacKey    : Key
  policy     : PolicyState
  revocation : RevocationState
  now        : Time
-- Note: Cannot derive Repr due to opaque Key/PolicyState types

namespace KernelState

/-- Initial kernel state -/
def initial (key : Key) (pol : PolicyState) : KernelState where
  hmacKey := key
  policy := pol
  revocation := RevocationState.empty
  now := 0

/-- Advance kernel time -/
def tick (ks : KernelState) : KernelState :=
  { ks with now := ks.now + 1 }

/-- Check capability is not revoked -/
def cap_not_revoked (ks : KernelState) (cap : Capability) : Prop :=
  ks.revocation.is_valid cap.id

end KernelState

end Lion
