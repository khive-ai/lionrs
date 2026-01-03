/-
Lion/Step/PluginInternal.lean
==============================

Plugin-internal computation (sandboxed, untrusted).
-/

import Lion.Core.Identifiers
import Lion.State.Memory
import Lion.State.State

namespace Lion

/-! =========== PLUGIN INTERNAL =========== -/

/-- Plugin internal computation descriptor -/
structure PluginInternal where
  reads          : List (MemAddr × Size)  -- Memory regions read
  writes         : List (MemAddr × Size)  -- Memory regions written
  consume_mailbox : Bool                  -- Whether to consume from mailbox
deriving Repr

/-- Precondition for plugin internal computation -/
def plugin_internal_pre (pid : PluginId) (pi : PluginInternal) (s : State) : Prop :=
  -- Not blocked on another actor
  (s.actors pid).blockedOn = none ∧
  -- Read regions in bounds
  (∀ r ∈ pi.reads,
    LinearMemory.addr_in_bounds (s.plugins pid).memory r.1 r.2) ∧
  -- Write regions in bounds
  (∀ w ∈ pi.writes,
    LinearMemory.addr_in_bounds (s.plugins pid).memory w.1 w.2) ∧
  -- If consuming mailbox, mailbox must not be empty
  (pi.consume_mailbox = true → (s.actors pid).mailbox ≠ [])

/-! =========== PLUGIN EXECUTION =========== -/

/--
Plugin internal execution relation.
**Constructive definition** - enables frame facts to be proven as theorems.

Plugin internal execution (WASM sandbox) only affects:
- The executing plugin's memory bytes
- The executing plugin's local state

It CANNOT modify:
- Other plugins' state
- Kernel state
- Actor state
- Resources
- Workflows
- Ghost state
- Time
- Security-critical fields (level, heldCaps, memory.bounds)
-/
def PluginExecInternal (pid : PluginId) (pi : PluginInternal) (s s' : State) : Prop :=
  ∃ (newBytes : Std.HashMap MemAddr UInt8) (newLocal : PluginLocal),
    let newPlugin : PluginState := {
      level := (s.plugins pid).level,
      heldCaps := (s.plugins pid).heldCaps,
      memory := { bytes := newBytes, bounds := (s.plugins pid).memory.bounds },
      localState := newLocal
    }
    s' = { s with plugins := Function.update s.plugins pid newPlugin }

/-! =========== COMPREHENSIVE FRAME THEOREM =========== -/

/--
**Comprehensive Frame Theorem for Plugin Internal Execution**

Plugin internal execution (WASM sandbox) only affects:
- The executing plugin's memory contents
- The executing plugin's local state

It CANNOT modify:
- Other plugins' state
- Kernel state
- Actor state
- Resources
- Workflows
- Ghost state
- Time
- Security-critical fields (level, heldCaps, memory.bounds)

PROVEN from constructive definition - no longer an axiom.
-/
theorem plugin_internal_comprehensive_frame
    (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    -- Other components unchanged
    s'.kernel = s.kernel ∧
    (∀ other, other ≠ pid → s'.plugins other = s.plugins other) ∧
    s'.actors = s.actors ∧
    s'.resources = s.resources ∧
    s'.workflows = s.workflows ∧
    s'.ghost = s.ghost ∧
    s'.time = s.time ∧
    -- Security-critical fields of executing plugin preserved
    (s'.plugins pid).level = (s.plugins pid).level ∧
    (s'.plugins pid).heldCaps = (s.plugins pid).heldCaps ∧
    (s'.plugins pid).memory.bounds = (s.plugins pid).memory.bounds := by
  -- Unfold the definition and extract the equality
  simp only [PluginExecInternal] at h
  rcases h with ⟨newBytes, newLocal, rfl⟩
  -- All fields except plugins are unchanged by {s with plugins := ...}
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  -- For plugins: Function.update only changes pid
  · intro other hne
    simp only [Function.update]
    split
    · rename_i heq
      exact absurd heq hne
    · rfl
  -- Security-critical fields: Function.update s.plugins pid newPlugin at pid = newPlugin
  -- and newPlugin preserves level, heldCaps, memory.bounds by construction
  · simp only [Function.update]
    split
    · rfl
    · rename_i hne; exact False.elim (hne trivial)
  · simp only [Function.update]
    split
    · rfl
    · rename_i hne; exact False.elim (hne trivial)
  · simp only [Function.update]
    split
    · rfl
    · rename_i hne; exact False.elim (hne trivial)

/-! =========== DERIVED FRAME THEOREMS =========== -/

/-- Plugin internal execution only affects its own state -/
theorem plugin_internal_frame (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    ∀ other, other ≠ pid → s'.plugins other = s.plugins other :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.1

/-- Plugin internal execution doesn't affect kernel -/
theorem plugin_internal_kernel_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.kernel = s.kernel :=
  (plugin_internal_comprehensive_frame pid pi s s' h).1

/-- Plugin internal execution doesn't affect actors -/
theorem plugin_internal_actors_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.actors = s.actors :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.1

/-- Plugin internal execution doesn't affect resources -/
theorem plugin_internal_resources_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.resources = s.resources :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.1

/-- Plugin internal execution doesn't affect workflows -/
theorem plugin_internal_workflows_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.workflows = s.workflows :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.1

/-- Plugin internal execution doesn't affect ghost state -/
theorem plugin_internal_ghost_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.ghost = s.ghost :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.2.1

/-- Plugin internal execution doesn't affect time -/
theorem plugin_internal_time_unchanged (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    s'.time = s.time :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.2.2.1

/-- Plugin internal execution preserves memory bounds -/
theorem plugin_internal_bounds_preserved (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    (s'.plugins pid).memory.bounds = (s.plugins pid).memory.bounds :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.2.2.2.2.2

/-!
## Security-Critical Field Invariants

Plugin internal execution (WASM sandbox) can only modify:
- Linear memory contents
- Local state (WASM globals, tables, etc.)

It CANNOT modify security-critical kernel-managed fields:
- Security level (only kernel can declassify/upgrade)
- Held capabilities (only kernel can grant/revoke via host calls)

This prevents "capability forgery via self-state mutation" attack
where a malicious plugin edits its own heldCaps field.
-/

/-- Plugin internal execution preserves security level.
    Only kernel operations can change a plugin's security classification. -/
theorem plugin_internal_level_preserved (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    (s'.plugins pid).level = (s.plugins pid).level :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.2.2.2.1

/-- Plugin internal execution preserves held capabilities.
    Capabilities can only be granted/revoked through authorized host calls.
    This prevents the "self-mutation forgery" attack identified in adversarial review. -/
theorem plugin_internal_caps_preserved (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    (s'.plugins pid).heldCaps = (s.plugins pid).heldCaps :=
  (plugin_internal_comprehensive_frame pid pi s s' h).2.2.2.2.2.2.2.2.1

/-- Combined security invariant for plugin internal execution -/
theorem plugin_internal_security_invariant (pid : PluginId) (pi : PluginInternal) (s s' : State)
    (h : PluginExecInternal pid pi s s') :
    (s'.plugins pid).level = (s.plugins pid).level ∧
    (s'.plugins pid).heldCaps = (s.plugins pid).heldCaps :=
  ⟨plugin_internal_level_preserved pid pi s s' h,
   plugin_internal_caps_preserved pid pi s s' h⟩

/-!
### WASM Memory Bounds Enforcement

This property is now bundled into `RuntimeIsolation` in
`Lion/Core/RuntimeIsolation.lean`. Import that file to use the
`plugin_internal_respects_bounds` theorem.

The WASM sandbox guarantees that all bytes stored in plugin linear memory
are within declared bounds (bounds checking on all load/store operations).
-/

end Lion
