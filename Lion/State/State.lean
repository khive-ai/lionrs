/-
Lion/State/State.lean
======================

Unified global state for Lion microkernel.
-/

import Std.Data.HashMap
import Lion.Core.Identifiers
import Lion.Core.SecurityLevel
import Lion.State.Memory
import Lion.State.Plugin
import Lion.State.Actor
import Lion.State.Workflow
import Lion.State.Kernel

namespace Lion

/-! =========== RESOURCE INFO (011) =========== -/

/-- Resource metadata -/
structure ResourceInfo where
  level : SecurityLevel
deriving Repr

/-! =========== UNIFIED GLOBAL STATE =========== -/

/-- Complete system state -/
structure State where
  kernel    : KernelState
  plugins   : PluginId → PluginState
  actors    : ActorId → ActorRuntime
  resources : ResourceId → ResourceInfo
  workflows : WorkflowId → WorkflowInstance
  ghost     : MetaState  -- Ghost state for verification (renamed from `meta`)
  time      : Time

/-- Lightweight Repr for debugging -/
instance : Repr State where
  reprPrec _ _ := "«Lion.State»"

namespace State

/-- Get plugin memory -/
def plugin_memory (s : State) (pid : PluginId) : LinearMemory :=
  (s.plugins pid).memory

/-- Get plugin security level -/
def plugin_level (s : State) (pid : PluginId) : SecurityLevel :=
  (s.plugins pid).level

/-- Get resource security level -/
def resource_level (s : State) (rid : ResourceId) : SecurityLevel :=
  (s.resources rid).level

/-- Get capability from kernel -/
def get_cap (s : State) (capId : CapId) : Option Capability :=
  s.kernel.revocation.caps.get? capId

/-- Capability is valid in current state -/
def cap_is_valid (s : State) (capId : CapId) : Prop :=
  IsValid s.kernel.revocation.caps capId

/-- Plugin holds capability by ID -/
def plugin_holds (s : State) (pid : PluginId) (capId : CapId) : Prop :=
  capId ∈ (s.plugins pid).heldCaps

/-! =========== ALLOCATION/FREE HELPERS =========== -/

/-- Allocate resource, update ghost history -/
def apply_alloc (s : State) (owner : PluginId) (size : Nat) : State :=
  let addr := s.ghost.resources.size  -- Next available address
  let new_ghost := s.ghost.alloc addr owner
  { s with ghost := new_ghost }

/-- Free resource, mark as dead in ghost history -/
def apply_free (s : State) (addr : MemAddr) : State :=
  { s with ghost := s.ghost.free addr }

/-! ### apply_alloc Frame Lemmas

These lemmas prove that `apply_alloc` only modifies `ghost`,
leaving all other State fields unchanged. Used for correspondence
preservation proofs (Q11).
-/

@[simp] theorem apply_alloc_kernel (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).kernel = s.kernel := rfl

@[simp] theorem apply_alloc_plugins (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).plugins = s.plugins := rfl

@[simp] theorem apply_alloc_actors (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).actors = s.actors := rfl

@[simp] theorem apply_alloc_resources (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).resources = s.resources := rfl

@[simp] theorem apply_alloc_workflows (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).workflows = s.workflows := rfl

@[simp] theorem apply_alloc_time (s : State) (owner : PluginId) (size : Nat) :
    (s.apply_alloc owner size).time = s.time := rfl

/-! ### apply_free Frame Lemmas -/

@[simp] theorem apply_free_kernel (s : State) (addr : MemAddr) :
    (s.apply_free addr).kernel = s.kernel := rfl

@[simp] theorem apply_free_plugins (s : State) (addr : MemAddr) :
    (s.apply_free addr).plugins = s.plugins := rfl

@[simp] theorem apply_free_actors (s : State) (addr : MemAddr) :
    (s.apply_free addr).actors = s.actors := rfl

@[simp] theorem apply_free_resources (s : State) (addr : MemAddr) :
    (s.apply_free addr).resources = s.resources := rfl

@[simp] theorem apply_free_workflows (s : State) (addr : MemAddr) :
    (s.apply_free addr).workflows = s.workflows := rfl

@[simp] theorem apply_free_time (s : State) (addr : MemAddr) :
    (s.apply_free addr).time = s.time := rfl

/-- Revoke capability (O(1) - just flip bit) -/
def apply_revoke (s : State) (capId : CapId) : State :=
  { s with kernel := { s.kernel with
      revocation := s.kernel.revocation.revoke capId } }

/-! =========== ISOLATION PREDICATES =========== -/

/-- Memory isolation after step -/
def preserves_isolation (s s' : State) (active : PluginId) : Prop :=
  ∀ pid, pid ≠ active → s'.plugins pid = s.plugins pid

/-- Temporal safety: freed resources stay freed -/
def temporal_safety (s s' : State) : Prop :=
  ∀ addr, addr ∈ s.ghost.freed_set → addr ∈ s'.ghost.freed_set

end State

/-! =========== LOW EQUIVALENCE (011) =========== -/

/-- One-way low equivalence: all low (≤ L) components of `s₁` agree with `s₂`. -/
def low_equivalent_left (L : SecurityLevel) (s₁ s₂ : State) : Prop :=
  (∀ pid, (s₁.plugins pid).level ≤ L → s₁.plugins pid = s₂.plugins pid) ∧
  (∀ rid, (s₁.resources rid).level ≤ L → s₁.resources rid = s₂.resources rid)

/-- States agree on all data at level ≤ L (for noninterference). Symmetric by construction. -/
def low_equivalent (L : SecurityLevel) (s₁ s₂ : State) : Prop :=
  low_equivalent_left L s₁ s₂ ∧ low_equivalent_left L s₂ s₁

/-- Low equivalence is reflexive -/
theorem low_equivalent_refl (L : SecurityLevel) (s : State) :
    low_equivalent L s s := by
  refine ⟨?_, ?_⟩ <;> constructor <;> intro _ _ <;> rfl

/-- Low equivalence is symmetric -/
theorem low_equivalent_symm {L : SecurityLevel} {s₁ s₂ : State} :
    low_equivalent L s₁ s₂ → low_equivalent L s₂ s₁ := by
  intro h
  exact ⟨h.2, h.1⟩

/-- One-way low equivalence is transitive. -/
theorem low_equivalent_left_trans {L : SecurityLevel} {s₁ s₂ s₃ : State} :
    low_equivalent_left L s₁ s₂ →
    low_equivalent_left L s₂ s₃ →
    low_equivalent_left L s₁ s₃ := by
  intro h12 h23
  constructor
  · intro pid hlow1
    have h_eq12 : s₁.plugins pid = s₂.plugins pid := h12.1 pid hlow1
    have hlow2 : (s₂.plugins pid).level ≤ L := by
      simpa [h_eq12] using hlow1
    have h_eq23 : s₂.plugins pid = s₃.plugins pid := h23.1 pid hlow2
    exact h_eq12.trans h_eq23
  · intro rid hlow1
    have h_eq12 : s₁.resources rid = s₂.resources rid := h12.2 rid hlow1
    have hlow2 : (s₂.resources rid).level ≤ L := by
      simpa [h_eq12] using hlow1
    have h_eq23 : s₂.resources rid = s₃.resources rid := h23.2 rid hlow2
    exact h_eq12.trans h_eq23

/-- Low equivalence is transitive -/
theorem low_equivalent_trans {L : SecurityLevel} {s₁ s₂ s₃ : State} :
    low_equivalent L s₁ s₂ →
    low_equivalent L s₂ s₃ →
    low_equivalent L s₁ s₃ := by
  intro h12 h23
  refine ⟨?_, ?_⟩
  · exact low_equivalent_left_trans h12.1 h23.1
  · exact low_equivalent_left_trans h23.2 h12.2

end Lion
