/-
Lion/Composition/ComponentSafe.lean
===================================

Component-level safety predicate (v1 Definition 2.5).

The compositional security thesis: "If parts are safe, entirety is safe"
requires defining what it means for an individual component to be safe.

This file defines:
1. Component - a plugin with its held capabilities and security level
2. ComponentSafe - four-part security predicate
   - Unforgeable: all held capabilities are properly sealed
   - Confined: capabilities exist in table (handle integrity, not validity)
   - Isolated: memory is within WASM bounds
   - Compliant: capabilities are properly owned by source plugins

Handle/State Separation Model:
- Plugins hold CapId handles, not Capability copies
- Validity checked at USE time (cap_invoke, cap_delegate), not possession time
- Revoked caps remain as handles but fail IsValid check when used

Based on:
- v1 Definition 2.5 (Component Security)
- v1 Theorem 2.2 (Security Composition)
-/

import Lion.Composition.SystemInvariant

namespace Lion

/-! =========== COMPONENT STRUCTURE =========== -/

/--
A Component is a logical unit of execution in the Lion system.
It represents a plugin along with its held capabilities and security level.

Components are the units of compositional reasoning - we prove each component
is safe, then prove composition preserves safety.

The `sourcePids` field tracks which plugins contribute capabilities to this
component. For a simple component, this is just {pid}. For composed components,
it's the union of source pids. This enables the compliant property to verify
that held capabilities have valid holders.
-/
structure Component where
  /-- Primary plugin identifier (for isolation/memory) -/
  pid : PluginId
  /-- Set of source plugin IDs (for ownership tracking) -/
  sourcePids : Finset PluginId
  /-- Set of capability IDs this component holds -/
  heldCapIds : Finset CapId
  /-- Security classification level -/
  level : SecurityLevel
deriving DecidableEq

namespace Component

/-- Extract component from state for a given plugin.
    With Handle/State Separation, heldCaps is already Finset CapId. -/
noncomputable def fromPlugin (s : State) (pid : PluginId) : Component where
  pid := pid
  sourcePids := {pid}  -- Single plugin is its own source
  -- heldCaps is already Finset CapId (handles, not copies)
  heldCapIds := (s.plugins pid).heldCaps
  level := (s.plugins pid).level

/-- Empty component with no capabilities -/
def empty (pid : PluginId) (level : SecurityLevel) : Component where
  pid := pid
  sourcePids := {pid}
  heldCapIds := ∅
  level := level

end Component

/-! =========== COMPONENT SAFETY PREDICATE =========== -/

/--
ComponentSafe: Four-part security predicate (v1 Definition 2.5).

A component is safe if:
1. **Unforgeable**: All capabilities it holds are properly sealed with kernel HMAC
2. **Confined (revocation-safe)**: Its capabilities are valid (IsValid) in the table
   - This means the cap exists and is not revoked
   - Note: This is NOT rights-based authority confinement; that is a separate concern
     handled by Confinement.table_invariant at the system level
3. **Isolated**: Its memory operations stay within WASM bounds
4. **Compliant**: Its capabilities have holders ∈ sourcePids (ownership tracking)

This predicate enables compositional reasoning: if A and B are each ComponentSafe,
and they are Compatible, then their composition is also ComponentSafe.
-/
structure ComponentSafe (s : State) (c : Component) : Prop where
  /-- All capabilities held are properly sealed with kernel HMAC.
      This prevents forgery - capabilities cannot be manufactured. -/
  unforgeable : ∀ capId ∈ c.heldCapIds,
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap ∧
           Capability.verify_seal s.kernel.hmacKey cap

  /-- Capabilities exist in the kernel table (handle integrity).
      With Handle/State Separation, we check EXISTENCE here, not validity.
      Validity is checked at USE time (cap_invoke, cap_delegate preconditions).
      This ensures handles are not dangling pointers. -/
  confined : ∀ capId ∈ c.heldCapIds,
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap

  /-- Memory is isolated within WASM bounds.
      Addresses accessed are within the declared memory bounds. -/
  isolated : ∀ addr,
    (s.plugins c.pid).memory.bytes.contains addr →
    addr < (s.plugins c.pid).memory.bounds

  /-- Capabilities are held by a source plugin (holder ∈ sourcePids).
      This ensures proper ownership tracking, even for composed components. -/
  compliant : ∀ capId ∈ c.heldCapIds,
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap ∧
           cap.holder ∈ c.sourcePids

namespace ComponentSafe

/-- ComponentSafe implies memory isolation for this component -/
theorem implies_memory_isolated (s : State) (c : Component)
    (h : ComponentSafe s c) : ∀ addr,
    (s.plugins c.pid).memory.bytes.contains addr →
    addr < (s.plugins c.pid).memory.bounds :=
  h.isolated

/-- ComponentSafe implies all held caps exist in table (handle integrity) -/
theorem implies_caps_exist (s : State) (c : Component)
    (h : ComponentSafe s c) (capId : CapId) (h_held : capId ∈ c.heldCapIds) :
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap := by
  exact h.confined capId h_held

/-- ComponentSafe implies all held caps are sealed -/
theorem implies_caps_sealed (s : State) (c : Component)
    (h : ComponentSafe s c) (capId : CapId) (h_held : capId ∈ c.heldCapIds) :
    ∃ cap, s.kernel.revocation.caps.get? capId = some cap ∧
           Capability.verify_seal s.kernel.hmacKey cap :=
  h.unforgeable capId h_held

end ComponentSafe

/-! =========== SYSTEM-WIDE COMPONENT SAFETY =========== -/

/-- All components in the system are safe -/
noncomputable def AllComponentsSafe (s : State) : Prop :=
  ∀ pid : PluginId, ComponentSafe s (Component.fromPlugin s pid)

/-- AllComponentsSafe implies MemoryIsolated (connects to SystemInvariant) -/
theorem all_components_safe_implies_memory_isolated (s : State)
    (h : AllComponentsSafe s) : MemoryIsolated s := by
  intro pid addr h_contains
  exact (h pid).isolated addr h_contains

/-- AllComponentsSafe implies each plugin's caps are sealed -/
theorem all_components_safe_implies_unforgeable (s : State)
    (h : AllComponentsSafe s) (pid : PluginId) :
    ∀ capId ∈ (Component.fromPlugin s pid).heldCapIds,
      ∃ cap, s.kernel.revocation.caps.get? capId = some cap ∧
             Capability.verify_seal s.kernel.hmacKey cap :=
  (h pid).unforgeable

end Lion
