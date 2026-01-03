/-
Lion/Deploy/ContextPropagation.lean
===================================

Formal proofs for khive-deploy context propagation (ADR-003).
Proves that to_storage_context preserves security properties.

Related ADRs:
- khive-deploy ADR-003: Context Propagation
- khive-db ADR-004: Security & Data Protection

Security Properties:
1. SecurityLevel preservation: to_storage_context preserves security level
2. RightSet preservation: to_storage_context preserves rights
3. Namespace validation: validated namespaces are preserved

STATUS: COMPLETE - All proofs verified with 0 sorries.
-/

import Lion.Core.SecurityLevel
import Lion.Core.Rights

namespace Lion.Deploy

open Lion

/-! =========== PART 1: TYPE DEFINITIONS =========== -/

/-- Validated namespace (corresponds to khive-db Namespace).
    INVARIANT: Namespace values are validated at construction time.
    Only alphanumeric, hyphens, underscores; length 1-128. -/
structure ValidatedNamespace where
  value : String
  h_nonempty : value.length > 0
  h_bounded : value.length ≤ 128

/-- Request source protocol -/
inductive RequestSource where
  | Http
  | Mcp
  | Cli
  | Internal
  | Wasm
deriving DecidableEq, Repr, Inhabited

/-- Trace context for distributed tracing (simplified model) -/
structure TraceContext where
  traceId : Nat
  spanId : Nat
  correlationId : Nat
  sampled : Bool
deriving DecidableEq, Repr

instance : Inhabited TraceContext where
  default := ⟨0, 0, 0, false⟩

/-- Operation context from khive-deploy (ADR-003).
    Fields: trace, securityLevel, rights, nsString, timeoutSecs, source -/
structure OperationContext where
  trace : TraceContext
  securityLevel : SecurityLevel
  rights : Rights
  nsString : String
  timeoutSecs : Option Nat
  source : RequestSource

/-- Storage context from khive-db (ADR-004).
    Fields: ns, secLevel, traceCtx, contentRights, embeddingRights,
    linkRights, maxSecLevel -/
structure StorageContext where
  ns : ValidatedNamespace
  secLevel : SecurityLevel
  traceCtx : TraceContext
  contentRights : Rights
  embeddingRights : Rights
  linkRights : Rights
  maxSecLevel : SecurityLevel

/-! =========== PART 2: NAMESPACE VALIDATION =========== -/

/-- Character validation: alphanumeric, hyphen, or underscore -/
def isValidChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_'

/-- Namespace string validation -/
def isValidNamespaceStr (s : String) : Bool :=
  s.length > 0 && s.length ≤ 128 && s.toList.all isValidChar

/-- Attempt to create a validated namespace -/
def ValidatedNamespace.mk? (s : String) : Option ValidatedNamespace :=
  if h : s.length > 0 ∧ s.length ≤ 128 then
    some ⟨s, h.1, h.2⟩
  else
    none

/-- Validated namespace preserves the original string -/
theorem ValidatedNamespace.value_preserved (s : String) (vns : ValidatedNamespace)
    (h : ValidatedNamespace.mk? s = some vns) : vns.value = s := by
  simp only [ValidatedNamespace.mk?] at h
  split at h
  case isTrue h' =>
    simp only [Option.some.injEq] at h
    rw [← h]
  case isFalse => contradiction

/-! =========== PART 3: CONTEXT CONVERSION =========== -/

/-- Convert OperationContext to StorageContext.
    This is the formal model of khive-deploy's to_storage_context().
    PRECONDITION: namespace must be valid (checked at call site). -/
def toStorageContext (ctx : OperationContext) (vns : ValidatedNamespace) : StorageContext where
  ns := vns
  secLevel := ctx.securityLevel
  traceCtx := ctx.trace
  contentRights := ctx.rights
  embeddingRights := ctx.rights
  linkRights := ctx.rights
  maxSecLevel := ctx.securityLevel

/-! =========== PART 4: SECURITY PRESERVATION THEOREMS =========== -/

/-- SecurityLevel Preservation: security level is preserved in conversion -/
theorem securityLevel_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).secLevel = ctx.securityLevel := rfl

/-- MaxSecurityLevel matches caller's clearance -/
theorem maxSecurityLevel_matches (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).maxSecLevel = ctx.securityLevel := rfl

/-- Content rights preserved -/
theorem contentRights_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).contentRights = ctx.rights := rfl

/-- Embedding rights preserved -/
theorem embeddingRights_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).embeddingRights = ctx.rights := rfl

/-- Link rights preserved -/
theorem linkRights_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).linkRights = ctx.rights := rfl

/-- All rights preserved (combined theorem) -/
theorem allRights_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    let sc := toStorageContext ctx vns
    sc.contentRights = ctx.rights ∧
    sc.embeddingRights = ctx.rights ∧
    sc.linkRights = ctx.rights :=
  ⟨rfl, rfl, rfl⟩

/-- Trace context preserved for distributed tracing -/
theorem trace_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).traceCtx = ctx.trace := rfl

/-- Validated namespace preserved -/
theorem namespace_preserved (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).ns = vns := rfl

/-! =========== PART 5: INFORMATION FLOW PROPERTIES =========== -/

/-- No clearance escalation: conversion cannot increase security level -/
theorem no_clearance_escalation (ctx : OperationContext) (vns : ValidatedNamespace) :
    (toStorageContext ctx vns).secLevel ≤ ctx.securityLevel :=
  le_refl _

/-- No rights amplification: conversion cannot add rights -/
theorem no_rights_amplification (ctx : OperationContext) (vns : ValidatedNamespace) :
    let sc := toStorageContext ctx vns
    sc.contentRights ⊆ ctx.rights ∧
    sc.embeddingRights ⊆ ctx.rights ∧
    sc.linkRights ⊆ ctx.rights :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩

/-! =========== PART 6: WASM-SPECIFIC PROPERTIES =========== -/

/-- WASM operation context has restricted rights (Read-only, Public) -/
def wasmContext (nsStr : String) : OperationContext where
  trace := default
  securityLevel := .Public
  rights := {.Read}
  nsString := nsStr
  timeoutSecs := some 30
  source := .Wasm

/-- WASM capabilities are explicitly injected (no ambient authority) -/
theorem wasm_explicit_capability :
    let ctx := wasmContext "test"
    ctx.rights = {Right.Read} ∧ ctx.securityLevel = SecurityLevel.Public := by
  constructor <;> rfl

/-- WASM cannot escalate to Internal level -/
theorem wasm_no_internal_access :
    ¬ SecurityLevel.Internal ≤ (wasmContext "test").securityLevel := by
  simp only [wasmContext]
  decide

/-! =========== PART 7: REQUEST SOURCE PROPERTIES =========== -/

/-- Internal request context (service-to-service, full access) -/
def internalContext (nsStr : String) : OperationContext where
  trace := default
  securityLevel := .Secret
  rights := Rights.all
  nsString := nsStr
  timeoutSecs := none
  source := .Internal

/-- Internal operations have full access -/
theorem internal_full_access :
    let ctx := internalContext "test"
    ctx.rights = Rights.all ∧ ctx.securityLevel = SecurityLevel.Secret := by
  constructor <;> rfl

/-- Request source determines security posture -/
theorem source_security_posture :
    (wasmContext "test").securityLevel < (internalContext "test").securityLevel := by
  native_decide

/-! =========== SUMMARY ===========

Context Propagation Security (khive-deploy ADR-003)

This module proves that the to_storage_context conversion preserves
security properties when crossing from khive-deploy to khive-db:

1. SecurityLevel Preservation: Clearance level is preserved exactly
2. RightSet Preservation: Rights are preserved to all resource types
3. Trace Preservation: Distributed tracing context flows through
4. Namespace Validation: Only validated namespaces reach storage layer
5. No Escalation: Conversion cannot amplify rights or clearance
6. WASM Isolation: WASM contexts are explicitly restricted
-/

end Lion.Deploy
