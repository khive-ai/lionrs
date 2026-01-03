/-
Lion/Core/Identifiers.lean
===========================

Core identifier types for Lion microkernel.
-/

namespace Lion

/-! =========== IDENTIFIERS =========== -/

/-- Plugin identifier (WASM module instance) -/
abbrev PluginId := Nat

/-- Actor identifier (concurrent execution context) -/
abbrev ActorId := PluginId

/-- Resource identifier (kernel-managed objects) -/
abbrev ResourceId := Nat

/-- Capability identifier -/
abbrev CapId := Nat

/-- Workflow instance identifier -/
abbrev WorkflowId := Nat

/-- Message identifier -/
abbrev MsgId := Nat

/-- Logical time (monotonic counter) -/
abbrev Time := Nat

/-- Memory size in bytes -/
abbrev Size := Nat

/-- Memory address (linear memory offset) -/
abbrev MemAddr := Nat

end Lion
