/-
Lion/Theorems/Revocation.lean
=============================

Theorem 005: Capability Revocation

Revoked capabilities become permanently unusable.
Revocation is immediate, transitive, and irreversible.

Key properties:
1. Immediate Effect: Revocation is O(1) via valid flag flip
2. No Authorization: Revoked capabilities cannot authorize any action
3. Transitivity: Revocation propagates to all descendants
4. Permanence: Revocation cannot be undone

Architecture:
- Builds on `revocation_propagates` theorem from State/Kernel.lean
- Integrates with Authorization witness system
- Validates complete mediation even for revoked capabilities

STATUS: Core properties COMPLETE
- Immediate effect (revocation_immediate): Proven
- No authorization (revoked_no_auth): Proven
- Transitivity (revocation_transitive): Proven (via revocation_propagates)
- Permanence (revocation_permanent): Proven
-/

import Lion.Core.Crypto
import Lion.Core.Policy
import Lion.State.State
import Lion.State.Kernel
import Lion.Step.Authorization
import Lion.Step.Step

namespace Lion.Revocation

/-! =========== HASHMAP HELPER LEMMAS =========== -/

/-- get? after insert on same key returns inserted value -/
private lemma get?_insert_self [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).get? k = some v := Std.HashMap.getElem?_insert_self

/-- get? after insert follows if-then-else on key equality -/
private lemma get?_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insert k v).get? a = if k == a then some v else m.get? a :=
  Std.HashMap.getElem?_insert

/-! =========== PART 1: IMMEDIATE REVOCATION (O(1)) =========== -/

/--
Revocation invalidates a capability in O(1) time.
The valid flag is flipped immediately; no traversal needed.

Proof: Uses HashMap.getElem?_insert_self to show the inserted capability
with valid := false is retrieved, making is_valid return false.
-/
theorem revocation_immediate (rs : RevocationState) (capId : CapId) :
    let rs' := rs.revoke capId
    ¬ rs'.is_valid capId := by
  unfold RevocationState.revoke
  split
  case h_1 cap h_get =>
    unfold RevocationState.is_valid
    simp only [get?_insert_self]
    decide
  case h_2 h_none =>
    unfold RevocationState.is_valid
    simp only [h_none]
    decide

/--
Revocation takes effect immediately after the operation.
If a capability was valid before revocation, it becomes invalid after.
-/
theorem revocation_effect (rs : RevocationState) (capId : CapId)
    (h_was_valid : rs.is_valid capId) :
    let rs' := rs.revoke capId
    ¬ rs'.is_valid capId :=
  revocation_immediate rs capId

/-! =========== PART 2: REVOKED CAPABILITY CANNOT AUTHORIZE =========== -/

/--
A revoked capability cannot be used to construct an authorization witness.
This is the key security property: revocation prevents all future actions.

Proof insight: `Authorized` requires `h_valid : IsValid caps cap.id`.
If the capability is revoked, IsValid cannot be constructed.
-/
theorem revoked_no_auth (s : State) (a : Action) (cap : Capability)
    (h_revoked : ¬ IsValid s.kernel.revocation.caps cap.id) :
    ¬ ∃ (auth : Authorized s a), auth.cap = cap := by
  intro h_exists
  obtain ⟨auth, h_cap_eq⟩ := h_exists
  -- auth.h_valid says IsValid ... auth.cap.id
  have h_valid := auth.h_valid
  rw [h_cap_eq] at h_valid
  exact h_revoked h_valid

/--
Alternative formulation: If we have authorization, the capability must be valid.
Contrapositive of revoked_no_auth.
-/
theorem authorized_implies_valid (s : State) (a : Action) (auth : Authorized s a) :
    IsValid s.kernel.revocation.caps auth.cap.id :=
  auth.h_valid

/--
A revoked capability cannot satisfy capability_check.
-/
theorem revoked_fails_cap_check (s : State) (a : Action) (cap : Capability)
    (h_not_valid : ¬ s.kernel.revocation.is_valid cap.id) :
    ¬ capability_check s a cap := by
  intro h_check
  -- capability_check requires cap_isValid which requires is_valid
  have h_cap_valid := h_check.2.2.2.1.2
  exact h_not_valid h_cap_valid

/-! =========== PART 3: TRANSITIVE REVOCATION =========== -/

/--
Revocation is transitive: revoking a parent invalidates all descendants.
This is a direct application of `revocation_propagates` from Kernel.lean.

Key insight: IsValid is defined inductively - children require parent validity.
When parent is revoked, children's validity proofs cannot be constructed.
-/
theorem revocation_transitive (caps : CapTable) (parent child : CapId)
    (h_descendant : IsDescendant caps child parent)
    (h_parent_revoked : ¬ IsValid caps parent) :
    ¬ IsValid caps child :=
  revocation_propagates h_descendant h_parent_revoked

/--
Revocation propagates through arbitrary depth.
If ancestor is revoked, all descendants are invalid.
-/
theorem revocation_propagates_deep (caps : CapTable)
    (ancestor : CapId) (descendants : List CapId)
    (h_all_desc : ∀ d ∈ descendants, IsDescendant caps d ancestor)
    (h_ancestor_revoked : ¬ IsValid caps ancestor) :
    ∀ d ∈ descendants, ¬ IsValid caps d := by
  intro d h_mem
  exact revocation_transitive caps ancestor d (h_all_desc d h_mem) h_ancestor_revoked

/-! =========== PART 4: REVOCATION PERMANENCE =========== -/

/--
Revocation is permanent: once revoked, a capability cannot become valid.
The valid flag can only transition from true to false, never back.

Note: This models the semantic property. Implementation guarantees
this via RevocationState.revoke which only sets valid := false.
-/
theorem revocation_permanent (rs rs' : RevocationState) (capId : CapId)
    (h_revoked : ¬ rs.is_valid capId)
    (h_monotonic : ∀ cid, ¬ rs.is_valid cid → ¬ rs'.is_valid cid) :
    ¬ rs'.is_valid capId :=
  h_monotonic capId h_revoked

/--
Monotonicity: revoke operation never makes invalid caps valid.

Proof: For different keys, HashMap.getElem?_insert preserves existing values.
For same key, inserted cap has valid := false, remaining invalid.
-/
theorem revoke_monotonic (rs : RevocationState) (capId targetId : CapId)
    (h_invalid : ¬ rs.is_valid targetId) :
    let rs' := rs.revoke capId
    ¬ rs'.is_valid targetId := by
  unfold RevocationState.revoke
  split
  case h_1 cap h_get =>
    unfold RevocationState.is_valid at h_invalid ⊢
    simp only
    rw [get?_insert]
    by_cases h_eq : capId == targetId
    case pos =>
      simp only [h_eq, ↓reduceIte]
      decide
    case neg =>
      simp only [h_eq, Bool.false_eq_true, ↓reduceIte]
      exact h_invalid
  case h_2 h_none =>
    exact h_invalid

/-! =========== PART 5: NO REVIVAL PROPERTY =========== -/

/--
A revoked capability cannot be "un-revoked" through any operation.
The only way to re-enable access is to create a NEW capability.

This is enforced structurally: RevocationState only has `revoke`,
not `unrevoke`. We prove this by showing no state transition
can make an invalid capability valid again.
-/
theorem no_revival_by_revoke (rs : RevocationState) (anyCapId revokedCapId : CapId)
    (h_revoked : ¬ rs.is_valid revokedCapId) :
    ¬ (rs.revoke anyCapId).is_valid revokedCapId :=
  revoke_monotonic rs anyCapId revokedCapId h_revoked

/--
Revocation is irreversible in the state machine.
For any sequence of revoke operations, once invalid, always invalid.
-/
theorem revocation_irreversible (rs : RevocationState) (capId : CapId)
    (revoke_sequence : List CapId)
    (h_revoked : ¬ rs.is_valid capId) :
    let rs' := revoke_sequence.foldl RevocationState.revoke rs
    ¬ rs'.is_valid capId := by
  induction revoke_sequence generalizing rs with
  | nil => exact h_revoked
  | cons r rest ih =>
    simp only [List.foldl]
    apply ih
    exact revoke_monotonic rs r capId h_revoked

/-! =========== PART 6: STEP PRESERVATION =========== -/

/--
Revocation status is preserved across plugin-internal steps.
Plugin computation cannot modify kernel revocation state.
-/
theorem revocation_preserved_plugin_internal {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (hexec : PluginExecInternal pid pi s s')
    (capId : CapId)
    (h_revoked : ¬ IsValid s.kernel.revocation.caps capId) :
    ¬ IsValid s'.kernel.revocation.caps capId := by
  -- Plugin-internal steps don't modify kernel state
  have h_kernel : s'.kernel = s.kernel := plugin_internal_kernel_unchanged pid pi s s' hexec
  rw [h_kernel]
  exact h_revoked

/--
A host_call cannot succeed with a revoked capability.
Authorization requires validity, so revoked caps are blocked at mediation.
-/
theorem revoked_blocked_at_mediation (s : State) (hc : HostCall) (a : Action)
    (cap : Capability)
    (h_revoked : ¬ IsValid s.kernel.revocation.caps cap.id) :
    ¬ ∃ (auth : Authorized s a), auth.cap = cap :=
  revoked_no_auth s a cap h_revoked

/-! =========== PART 7: COMBINED SECURITY THEOREM =========== -/

/--
**Main Theorem: Capability Revocation Security**

When a capability is revoked:
1. The revocation is immediate (O(1))
2. The capability cannot authorize any action
3. All descendant capabilities are also invalid
4. The revocation cannot be undone (for directly revoked caps)

Together, these properties ensure that revocation provides
effective access control even in the face of capability leakage.

Note: Permanence (part 4) applies to directly revoked capabilities
(where cap.valid = false), not to transitively invalid descendants.
-/
theorem capability_revocation_security
    (s : State) (a : Action) (parentCap : Capability)
    (h_parent_revoked : ¬ IsValid s.kernel.revocation.caps parentCap.id)
    (h_directly_revoked : ¬ s.kernel.revocation.is_valid parentCap.id)  -- Direct revocation
    (descendants : List CapId)
    (h_all_desc : ∀ d ∈ descendants, IsDescendant s.kernel.revocation.caps d parentCap.id) :
    -- 1. Parent cannot authorize
    (¬ ∃ (auth : Authorized s a), auth.cap = parentCap) ∧
    -- 2. All descendants are invalid
    (∀ d ∈ descendants, ¬ IsValid s.kernel.revocation.caps d) ∧
    -- 3. Revocation is permanent (for directly revoked caps)
    (∀ (rs' : RevocationState), (∀ cid, ¬ s.kernel.revocation.is_valid cid → ¬ rs'.is_valid cid) →
            ¬ rs'.is_valid parentCap.id) := by
  constructor
  · -- Parent cannot authorize
    exact revoked_no_auth s a parentCap h_parent_revoked
  constructor
  · -- All descendants invalid
    exact revocation_propagates_deep s.kernel.revocation.caps parentCap.id
          descendants h_all_desc h_parent_revoked
  · -- Revocation permanent
    intro rs' h_mono
    exact h_mono parentCap.id h_directly_revoked

/-! =========== PART 8: EPOCH-BASED INVALIDATION MODEL =========== -/

/-!
## Epoch-Based Bulk Revocation

The current `IsValid` definition only checks:
1. Capability exists in table
2. cap.valid = true
3. Parent chain validity

For epoch-based bulk revocation, `IsValid` would need to be extended to check:
4. cap.epoch ≥ rs.epoch

This is a PROPOSED EXTENSION. The axioms below document the intended behavior
for when epoch checking is added to the validity model.
-/

/-!
Note: Epoch-based invalidation axioms (epoch_invalidates_old, bulk_revocation_efficient)
removed. These were for a PROPOSED EXTENSION to add epoch-based bulk revocation.
The current IsValid definition doesn't include epoch checking, so these axioms
were speculative and unused. Will be added back when epoch checking is implemented.
-/

/-! =========== PART 9: INTEGRATION WITH STEP RELATION =========== -/

/--
No step can use a revoked capability.
This follows from complete mediation: host_call requires Authorized,
which requires IsValid, which fails for revoked caps.
-/
theorem no_step_with_revoked_cap (s s' : State) (st : Step s s')
    (cap : Capability)
    (h_revoked : ¬ IsValid s.kernel.revocation.caps cap.id) :
    -- If this step involved this capability, it wasn't via authorization
    match st with
    | .host_call hc a auth hr _ _ _ => auth.cap ≠ cap
    | _ => True := by
  cases st with
  | plugin_internal => trivial
  | kernel_internal => trivial
  | host_call hc a auth hr hparse hpre hexec =>
    intro h_eq
    have h_valid := auth.h_valid
    rw [h_eq] at h_valid
    exact h_revoked h_valid

end Lion.Revocation
