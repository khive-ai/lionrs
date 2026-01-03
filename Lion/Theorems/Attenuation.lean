/-
Lion/Theorems/Attenuation.lean
==============================

Capability Attenuation Algebra.

Defines authority as (target, rights) pair and proves:
1. Direct delegation attenuates authority
2. Delegation chain attenuates authority (POLA)
3. Target preservation along chains
4. Intersection (meet) cannot exceed inputs

Based on v1 Theorem 5.1 (Attenuation) and integrates with
existing Confinement.lean definitions.
-/

import Lion.State.Kernel
import Lion.Theorems.Confinement

namespace Lion

/-!
# Capability Attenuation Algebra

This module defines a tiny algebra over capabilities:

* `Authority := (target, rights)`
* `≤` on authority means: same target, and rights subset
* `valid_delegation child parent` implies `child.authority ≤ parent.authority`
* `InDelegationChain caps cap root` implies `cap.authority ≤ root.authority`

This is the algebraic core used by confinement-style theorems.
-/

namespace Capability

/-- Authority carried by a capability: what it points at, and what rights it grants. -/
structure Authority where
  target : ResourceId
  rights : Rights
deriving DecidableEq

/-- Extract the authority granted by a capability. -/
def authority (cap : Capability) : Authority :=
  { target := cap.target, rights := cap.rights }

namespace Authority

/-- `a ≤ b` means "a does not exceed b": same target, rights are a subset. -/
def le (a b : Authority) : Prop :=
  a.target = b.target ∧ a.rights ⊆ b.rights

instance : LE Authority := ⟨le⟩

@[simp] theorem le_iff (a b : Authority) :
    (a ≤ b) ↔ (a.target = b.target ∧ a.rights ⊆ b.rights) := Iff.rfl

instance : PartialOrder Authority where
  le := le
  le_refl := by
    intro a
    exact ⟨rfl, fun r hr => hr⟩
  le_trans := by
    intro a b c hab hbc
    exact ⟨hab.1.trans hbc.1, fun r hr => hbc.2 (hab.2 hr)⟩
  le_antisymm := by
    intro a b hab hba
    cases a with
    | mk a_target a_rights =>
      cases b with
      | mk b_target b_rights =>
        have h_t : a_target = b_target := hab.1
        have h_rights : a_rights = b_rights := Finset.ext fun x =>
          ⟨fun hx => hab.2 hx, fun hx => hba.2 hx⟩
        cases h_t; cases h_rights; rfl

end Authority
end Capability

namespace Confinement

/-!
We reuse the existing Confinement notions:

* `valid_delegation child parent : Prop` (already defined)
* `InDelegationChain caps cap root : Prop` (already defined)
* `confinement_chain : InDelegationChain ... -> cap.rights ⊆ root.rights` (already proven)

We add "authority" versions of those results.
-/

/-- Direct derivation "edge": parent is present and delegation constraints hold. -/
def DerivedFrom (caps : CapTable) (child parent : Capability) : Prop :=
  caps.get? parent.id = some parent ∧ valid_delegation child parent

/-- Root-to-descendant derivation: just the existing delegation-chain predicate. -/
abbrev Derived (caps : CapTable) (root cap : Capability) : Prop :=
  InDelegationChain caps cap root

/-- Direct delegation cannot amplify authority. -/
theorem derivedFrom_reduces_authority (caps : CapTable) (child parent : Capability)
    (h : DerivedFrom caps child parent) :
    child.authority ≤ parent.authority := by
  have hdel : valid_delegation child parent := h.2
  have ht : child.target = parent.target := hdel.2.2
  have hr : child.rights ⊆ parent.rights := hdel.2.1
  simp only [Capability.authority, Capability.Authority.le_iff]
  exact ⟨ht, hr⟩

/-- Helper: extract the proof that a capability in a chain is in the table. -/
theorem chain_cap_in_table (caps : CapTable) (cap root : Capability)
    (h : InDelegationChain caps cap root) :
    caps.get? cap.id = some cap := by
  cases h with
  | refl c h_in => exact h_in
  | step c mid root' h_c_in _ _ => exact h_c_in

/-- Along any delegation chain, the target stays constant (requires well_formed_table). -/
theorem delegation_chain_preserves_target
    (caps : CapTable) (cap root : Capability)
    (h_wf : well_formed_table caps)
    (h : InDelegationChain caps cap root) :
    cap.target = root.target := by
  induction h with
  | refl c _ => rfl
  | step c mid root' h_c_in h_parent h_tail ih =>
    -- Get parent capability from well_formed_table
    obtain ⟨p, h_p_in, h_valid⟩ := h_wf c mid.id h_c_in h_parent
    have h_c_p_target : c.target = p.target := h_valid.2.2
    -- Show p = mid by uniqueness of keys
    -- From h_parent: c.parent = some mid.id
    -- From h_p_in: caps.get? mid.id = some p
    -- From chain_cap_in_table: caps.get? mid.id = some mid
    have h_mid_in : caps.get? mid.id = some mid := chain_cap_in_table caps mid root' h_tail
    have h_p_eq_mid : p = mid := by
      have : some p = some mid := h_p_in.symm.trans h_mid_in
      cases this; rfl
    rw [h_p_eq_mid] at h_c_p_target
    -- c.target = mid.target, and mid.target = root'.target by IH
    exact h_c_p_target.trans ih

/-- Delegation-chain attenuation: authority can only decrease from root to descendant.
    Requires well_formed_table to ensure target preservation. -/
theorem derived_chain_reduces_authority
    (caps : CapTable) (root cap : Capability)
    (h_wf : well_formed_table caps)
    (h : InDelegationChain caps cap root) :
    cap.authority ≤ root.authority := by
  have hr : cap.rights ⊆ root.rights := confinement_chain caps cap root h_wf h
  have ht : cap.target = root.target := delegation_chain_preserves_target caps cap root h_wf h
  simp only [Capability.authority, Capability.Authority.le_iff]
  exact ⟨ht, hr⟩

/-- If the cap table satisfies `table_invariant`, every parent link attenuates authority. -/
theorem parent_link_reduces_authority_of_table_invariant
    (caps : CapTable) (h_inv : table_invariant caps)
    (capId parentId : CapId) (cap parent : Capability)
    (h_get : caps.get? capId = some cap)
    (h_parent : cap.parent = some parentId)
    (h_get_parent : caps.get? parentId = some parent) :
    cap.authority ≤ parent.authority := by
  -- table_invariant = well_keyed_table ∧ well_formed_table
  have h_wf : well_formed_table caps := h_inv.2
  have h_wk : well_keyed_table caps := h_inv.1
  -- Get cap.id = capId from well_keyed_table
  have h_cap_id : cap.id = capId := h_wk capId cap h_get
  -- Use well_formed_table with cap and parentId
  have h_wf_link := h_wf cap parentId (by rw [h_cap_id]; exact h_get) h_parent
  obtain ⟨p, h_p_in, h_valid⟩ := h_wf_link
  -- p = parent by uniqueness
  have h_p_eq : p = parent := by
    have : some p = some parent := h_p_in.symm.trans h_get_parent
    cases this; rfl
  -- valid_delegation gives target and rights constraints
  have ht : cap.target = p.target := h_valid.2.2
  have hr : cap.rights ⊆ p.rights := h_valid.2.1
  -- Rewrite p to parent
  rw [h_p_eq] at ht hr
  simp only [Capability.authority, Capability.Authority.le_iff]
  exact ⟨ht, hr⟩

/-!
### "Meet" algebra for rights (intersection)

If you "combine" two authorities by intersecting rights, the result cannot exceed either input.
(You still need the same target to compare against both sides.)
-/

/-- If two capabilities share a target, intersecting their rights yields authority ≤ each input. -/
theorem intersection_authority_bounded
    (cap1 cap2 : Capability)
    (h_same_target : cap1.target = cap2.target) :
    let combined : Capability.Authority :=
      { target := cap1.target, rights := cap1.rights ∩ cap2.rights }
    combined ≤ cap1.authority ∧ combined ≤ cap2.authority := by
  intro combined
  constructor
  · simp only [Capability.Authority.le_iff, Capability.authority]
    exact ⟨rfl, Finset.inter_subset_left⟩
  · simp only [Capability.Authority.le_iff, Capability.authority]
    exact ⟨h_same_target, Finset.inter_subset_right⟩

/-!
### v1 Attenuation Algebra Properties (ch4-6)

The v1 spec defines attenuation as:
  attenuate(c, constraints) = (authority_c, permissions_c ∩ new_perms,
                               constraints_c ∪ constraints, depth_c + 1)

Key properties:
  - Monotonic: authority(attenuate(c,σ)) ⊆ authority(c)
  - Transitive: attenuate(attenuate(c,σ1),σ2) = attenuate(c, σ1 ∪ σ2)

In our model, attenuation is modeled via delegation chains. The properties
are proven in terms of the Authority partial order.
-/

/--
**v1 Theorem: Attenuation Monotonicity**

Any capability derived from a parent has authority ≤ parent's authority.
This is the core POLA (Principle of Least Authority) guarantee.

v1 ch4-6 L140-141: "Monotonic: authority(attenuate(c,σ)) ⊆ authority(c)"
-/
theorem attenuation_monotonic (caps : CapTable) (child parent : Capability)
    (h_derived : DerivedFrom caps child parent) :
    child.authority ≤ parent.authority :=
  derivedFrom_reduces_authority caps child parent h_derived

/--
**v1 Theorem: Attenuation Transitivity**

If A attenuates to B, and B attenuates to C, then C's authority ≤ A's authority.
This follows from transitivity of the Authority partial order.

v1 ch4-6 L142-143: "Transitive: attenuate(attenuate(c,σ1),σ2) = attenuate(c, σ1∪σ2)"

In our model, this means: along any delegation chain, authority only decreases.
-/
theorem attenuation_transitive (a b c : Capability.Authority)
    (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c :=
  le_trans hab hbc

/--
**v1 Theorem: Chain Attenuation**

For any delegation chain from root to descendant, the descendant's authority
is bounded by the root's authority. This is the full POLA theorem.
-/
theorem chain_attenuation (caps : CapTable) (root descendant : Capability)
    (h_wf : well_formed_table caps)
    (h_chain : InDelegationChain caps descendant root) :
    descendant.authority ≤ root.authority :=
  derived_chain_reduces_authority caps root descendant h_wf h_chain

/--
**Theorem: Attenuation Preserves Target**

Delegation cannot change the resource a capability refers to.
The target is invariant along any delegation chain.
-/
theorem attenuation_preserves_target (caps : CapTable) (root descendant : Capability)
    (h_wf : well_formed_table caps)
    (h_chain : InDelegationChain caps descendant root) :
    descendant.target = root.target :=
  delegation_chain_preserves_target caps descendant root h_wf h_chain

/--
**Theorem: Attenuation is Reflexive**

A capability's authority is ≤ itself (reflexivity of partial order).
This is the base case for chain attenuation.
-/
theorem attenuation_reflexive (auth : Capability.Authority) :
    auth ≤ auth :=
  le_refl auth

/--
**Theorem: Attenuation Antisymmetric**

If two authorities are mutually ≤, they are equal.
This ensures the authority ordering is well-defined.
-/
theorem attenuation_antisymmetric (a b : Capability.Authority)
    (hab : a ≤ b) (hba : b ≤ a) :
    a = b :=
  le_antisymm hab hba

/--
**v1 Theorem: Rights Attenuation**

Delegation can only reduce rights, never amplify them.
This is a direct corollary of valid_delegation.
-/
theorem rights_attenuation (child parent : Capability)
    (h_valid : valid_delegation child parent) :
    child.rights ⊆ parent.rights :=
  h_valid.2.1

/--
**v1 Theorem: No Authority Amplification**

A fundamental security property: there is no way to create a capability
with more authority than its parent. Combined with unforgeability,
this ensures the authority graph is monotonically decreasing.
-/
theorem no_authority_amplification (caps : CapTable) (c : Capability)
    (h_inv : table_invariant caps)
    (h_in : caps.get? c.id = some c)
    (parentId : CapId)
    (h_parent : c.parent = some parentId) :
    ∃ parent, caps.get? parentId = some parent ∧
              c.authority ≤ parent.authority := by
  obtain ⟨parent, h_parent_in, h_valid⟩ := h_inv.2 c parentId h_in h_parent
  refine ⟨parent, h_parent_in, ?_⟩
  simp only [Capability.authority, Capability.Authority.le_iff]
  exact ⟨h_valid.2.2, h_valid.2.1⟩

end Confinement
end Lion
