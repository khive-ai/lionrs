/-
Lion/State/Plugin.lean
=======================

Plugin state for WASM sandbox instances.

Design Note (2026-01-02): heldCaps stores CapId references, not Capability copies.
This follows the Handle/State Separation pattern:
- Plugins hold handles (CapId) - immutable references
- Kernel holds state (Capability with valid flag) - mutable
- Validity is checked at USE time via kernel table lookup
- Revocation just flips valid=false in table, no plugin cleanup needed

This avoids state duplication and makes revocation semantics clean.
-/

import Lion.Core.SecurityLevel
import Lion.Core.Crypto
import Lion.State.Memory

namespace Lion

/-! =========== PLUGIN STATE =========== -/

/-- Plugin-local state (WASM globals, tables, etc.)
    Concrete (Unit) for derived instances - actual state is abstract. -/
def PluginLocal := Unit
deriving DecidableEq, Repr

instance : Inhabited PluginLocal := ⟨()⟩

/-- State of a single plugin instance -/
structure PluginState where
  level      : SecurityLevel       -- Security classification
  memory     : LinearMemory        -- Linear memory sandbox
  heldCaps   : Finset CapId        -- Capability IDs held (handles, not copies)
  localState : PluginLocal         -- Opaque internal state
-- Note: Cannot derive Repr due to Finset/opaque types

/-- Default plugin: Public level (no clearance), empty memory, no caps.
    This is the semantically correct default - uninitialized plugins
    have no security privileges. Required for PluginIdWithinU64 proofs. -/
noncomputable instance : Inhabited PluginState where
  default := {
    level := .Public
    memory := LinearMemory.empty 0
    heldCaps := ∅
    localState := default
  }

/-- Default plugin has Public level -/
theorem PluginState.default_level : (default : PluginState).level = .Public := rfl

noncomputable section

namespace PluginState

/-- Empty plugin with given security level and memory size -/
def empty (level : SecurityLevel) (memSize : Nat) : PluginState where
  level := level
  memory := LinearMemory.empty memSize
  heldCaps := ∅
  localState := default

/-- Plugin holds a capability by ID -/
def holds_cap (ps : PluginState) (capId : CapId) : Prop :=
  capId ∈ ps.heldCaps

/-- Grant capability ID to plugin (idempotent). -/
def grant_cap (ps : PluginState) (capId : CapId) : PluginState :=
  { ps with heldCaps := insert capId ps.heldCaps }

/-- Remove capability ID from plugin -/
def revoke_cap (ps : PluginState) (capId : CapId) : PluginState :=
  { ps with heldCaps := ps.heldCaps.erase capId }

/-- grant_cap adds the cap ID -/
theorem grant_cap_mem (ps : PluginState) (capId : CapId) :
    capId ∈ (ps.grant_cap capId).heldCaps := by
  simp [grant_cap, Finset.mem_insert]

/-- grant_cap preserves existing cap IDs -/
theorem grant_cap_preserves (ps : PluginState) (capId newId : CapId)
    (h : capId ∈ ps.heldCaps) :
    capId ∈ (ps.grant_cap newId).heldCaps := by
  simp [grant_cap, Finset.mem_insert]
  exact Or.inr h

/-- revoke_cap removes the cap ID -/
theorem revoke_cap_not_mem (ps : PluginState) (capId : CapId) :
    capId ∉ (ps.revoke_cap capId).heldCaps := by
  simp [revoke_cap, Finset.mem_erase]

/-- revoke_cap preserves other cap IDs -/
theorem revoke_cap_preserves (ps : PluginState) (capId otherId : CapId)
    (h_in : otherId ∈ ps.heldCaps) (h_ne : otherId ≠ capId) :
    otherId ∈ (ps.revoke_cap capId).heldCaps := by
  simp [revoke_cap, Finset.mem_erase]
  exact ⟨h_ne, h_in⟩

/-! ### Frame lemmas for grant_cap

These lemmas prove that grant_cap only modifies heldCaps,
leaving all other PluginState fields unchanged.
-/

/-- grant_cap preserves memory -/
@[simp] theorem grant_cap_memory (ps : PluginState) (capId : CapId) :
    (ps.grant_cap capId).memory = ps.memory := rfl

/-- grant_cap preserves memory bounds -/
@[simp] theorem grant_cap_memory_bounds (ps : PluginState) (capId : CapId) :
    (ps.grant_cap capId).memory.bounds = ps.memory.bounds := rfl

/-- grant_cap preserves security level -/
@[simp] theorem grant_cap_level (ps : PluginState) (capId : CapId) :
    (ps.grant_cap capId).level = ps.level := rfl

/-- grant_cap preserves local state -/
@[simp] theorem grant_cap_localState (ps : PluginState) (capId : CapId) :
    (ps.grant_cap capId).localState = ps.localState := rfl

end PluginState

end

end Lion
