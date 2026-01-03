/-
Lion/State/Memory.lean
=======================

Linear memory model for WASM sandboxes (Theorems 002, 006).
Structural isolation via HashMap partitioning.
-/

import Std.Data.HashMap
import Mathlib.Data.Finset.Basic
import Lion.Core.Identifiers

namespace Lion

/-! =========== LINEAR MEMORY (002, 006) =========== -/

/-- Linear memory region for a plugin (WASM model) -/
structure LinearMemory where
  bytes  : Std.HashMap MemAddr UInt8
  bounds : Nat
deriving Repr

namespace LinearMemory

/-- Address is within bounds -/
def addr_in_bounds (mem : LinearMemory) (addr : MemAddr) (len : Size) : Prop :=
  addr + len ≤ mem.bounds

/-- Empty linear memory with given size -/
def empty (size : Nat) : LinearMemory where
  bytes := {}
  bounds := size

/-- Read byte at address (returns 0 for uninitialized) -/
def read (mem : LinearMemory) (addr : MemAddr) : UInt8 :=
  mem.bytes.getD addr 0

/-- Write byte at address -/
def write (mem : LinearMemory) (addr : MemAddr) (val : UInt8) : LinearMemory where
  bytes := mem.bytes.insert addr val
  bounds := mem.bounds

end LinearMemory

/-! =========== TEMPORAL SAFETY - GHOST STATE (006) =========== -/

/-- Resource lifecycle status -/
inductive ResourceStatus where
  | unallocated
  | allocated (owner : PluginId)
  | freed
deriving Repr, DecidableEq

/-- Ghost state for verification (not runtime) -/
structure MetaState where
  resources : Std.HashMap MemAddr ResourceStatus
  freed_set : Finset MemAddr

namespace MetaState

/-- Empty meta state -/
def empty : MetaState where
  resources := {}
  freed_set := {}

/-- Resource is live (allocated and not freed) -/
def is_live (ms : MetaState) (addr : MemAddr) : Prop :=
  match ms.resources.get? addr with
  | some (.allocated _) => addr ∉ ms.freed_set
  | _ => False

/-- Mark resource as allocated -/
def alloc (ms : MetaState) (addr : MemAddr) (owner : PluginId) : MetaState where
  resources := ms.resources.insert addr (.allocated owner)
  freed_set := ms.freed_set

/-- Mark resource as freed -/
def free (ms : MetaState) (addr : MemAddr) : MetaState where
  resources := ms.resources.insert addr .freed
  freed_set := ms.freed_set ∪ {addr}

/--
**Lemma (HashMap Insert Then Get)**:
For Std.HashMap, get? after insert on the same key returns the inserted value.

This is a standard HashMap property. In Lean4's Std library, simp handles this
via the HashMap rewrite lemmas.
-/
theorem resources_get?_insert_self
    (m : Std.HashMap MemAddr ResourceStatus) (k : MemAddr) (v : ResourceStatus) :
    (m.insert k v).get? k = some v := by
  simp

/-- Allocation makes resource live -/
theorem alloc_makes_live (ms : MetaState) (addr : MemAddr) (owner : PluginId)
    (h_not_freed : addr ∉ ms.freed_set) :
    is_live (ms.alloc addr owner) addr := by
  -- Expand definitions; simp handles HashMap lookup automatically.
  simp [is_live, alloc, h_not_freed]

/-- Allocation preserves liveness for ALL addresses (including the allocated one).
    Key insight: If t was live before alloc, it's still live after alloc:
    - If t = addr: old lookup was allocated (hence live), new lookup is also allocated
    - If t ≠ addr: lookup and freed_set unchanged -/
theorem alloc_preserves_is_live (ms : MetaState) (addr : MemAddr) (owner : PluginId) (t : MemAddr) :
    is_live ms t → is_live (ms.alloc addr owner) t := by
  intro h_live
  unfold is_live at h_live ⊢
  unfold alloc
  simp only
  -- Get the old lookup result and extract facts from h_live
  rw [Std.HashMap.get?_eq_getElem?] at h_live
  cases h_orig : ms.resources[t]? with
  | none =>
    -- If old lookup was none, h_live is False (contradiction)
    simp only [h_orig] at h_live
  | some st =>
    simp only [h_orig] at h_live
    cases st with
    | unallocated =>
      -- unallocated gives False
      cases h_live
    | freed =>
      -- freed gives False
      cases h_live
    | allocated oldOwner =>
      -- h_live now reduces to: t ∉ ms.freed_set
      -- Now prove is_live after insert
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      by_cases h : addr == t
      · -- addr = t: new lookup gives .allocated owner
        simp only [h, ↓reduceIte]
        exact h_live
      · -- addr ≠ t: lookup unchanged
        simp only [h, Bool.false_eq_true, ↓reduceIte, h_orig]
        exact h_live

/-- Freeing makes resource not live -/
theorem free_makes_not_live (ms : MetaState) (addr : MemAddr) :
    ¬ is_live (ms.free addr) addr := by
  -- After `free`, the map contains `.freed` at `addr`, so `is_live` is False by definition.
  simp [is_live, free]

/-- Freeing preserves liveness for other addresses.
    Key insight: If t was live before free and t ≠ addr, it's still live after:
    - resources lookup unchanged for t ≠ addr
    - freed_set gains only addr, so t ∉ freed_set' since t ≠ addr -/
theorem free_preserves_is_live (ms : MetaState) (addr t : MemAddr) :
    t ≠ addr → is_live ms t → is_live (ms.free addr) t := by
  intro h_ne h_live
  unfold is_live at h_live ⊢
  unfold free
  simp only
  rw [Std.HashMap.get?_eq_getElem?] at h_live
  cases h_orig : ms.resources[t]? with
  | none => simp only [h_orig] at h_live
  | some st =>
    simp only [h_orig] at h_live
    cases st with
    | unallocated => cases h_live
    | freed => cases h_live
    | allocated owner =>
      -- h_live : t ∉ ms.freed_set
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      have h_beq_false : (addr == t) = false := by rw [beq_eq_false_iff_ne]; exact Ne.symm h_ne
      simp only [h_beq_false, Bool.false_eq_true, ↓reduceIte, h_orig]
      -- Goal: t ∉ ms.freed_set ∪ {addr}  (Finset union)
      simp only [Finset.mem_union, Finset.mem_singleton]
      intro h_or
      cases h_or with
      | inl h_in => exact h_live h_in
      | inr h_eq => exact h_ne h_eq

end MetaState

/-! =========== MEMORY ISOLATION PREDICATE (002) =========== -/

/-- Plugins map (structural isolation) -/
abbrev PluginMemoryMap := PluginId → LinearMemory

/-- Memory isolation: non-active plugins unchanged after step -/
def memory_isolated (mem mem' : PluginMemoryMap) (active_pid : PluginId) : Prop :=
  ∀ pid, pid ≠ active_pid → mem pid = mem' pid

/-- Isolation is symmetric -/
theorem memory_isolated_symm {mem mem' : PluginMemoryMap} {pid : PluginId}
    (h : memory_isolated mem mem' pid) :
    ∀ other, other ≠ pid → mem' other = mem other :=
  fun other hne => (h other hne).symm

end Lion
