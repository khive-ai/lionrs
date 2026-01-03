/-
Lion Microkernel Formal Verification
=====================================

This library formalizes the security properties of the Lion microkernel:
- Capability unforgeability
- Capability uniqueness (ID-based identity)
- Memory isolation (temporal + spatial)
- Deadlock freedom
- Capability confinement (rights monotonicity)
- Capability revocation
- Temporal safety (no use-after-free)
- Spatial safety (bounds checking, memory isolation)
- Constraint immutability (TOCTOU prevention)
- Message delivery
- Workflow termination
- Policy soundness
- Security composition
- Noninterference (confidentiality + integrity)
- Complete mediation

Architecture: STEP_STATE_ARCHITECTURE.md (2025-12-22)
-/

import Lion.Core.Identifiers
import Lion.Core.SecurityLevel
import Lion.Core.Rights
import Lion.Core.Policy
import Lion.Core.Crypto
import Lion.Core.RuntimeIsolation

import Lion.State.Memory
import Lion.State.Plugin
import Lion.State.Actor
import Lion.State.Workflow
import Lion.State.Kernel
import Lion.State.State

import Lion.Step.Authorization
import Lion.Step.HostCall
import Lion.Step.PluginInternal
import Lion.Step.KernelOp
import Lion.Step.Step
import Lion.Step.Footprint
import Lion.Step.HostCallFootprint  -- Q13: Fine-grained footprint for correspondence

import Lion.Theorems.Mediation
import Lion.Theorems.PolicySoundness
import Lion.Theorems.Unforgeability
import Lion.Theorems.SpatialSafety
import Lion.Theorems.IntegrityNoninterference
import Lion.Theorems.TemporalSafety
import Lion.Theorems.DeadlockFreedom
import Lion.Theorems.Confinement
import Lion.Theorems.Attenuation           -- Authority algebra, attenuation theorems
import Lion.Theorems.WorkflowAlgebra       -- Workflow composition algebra (v1 Theorem 4.5)
import Lion.Theorems.Noninterference
import Lion.Theorems.StutteringBisimulation  -- A11-A12: Stuttering bisimulation for TINI
import Lion.Theorems.Revocation
import Lion.Theorems.Termination
import Lion.Theorems.WorkflowAuthorization  -- Workflow-Policy integration
import Lion.Theorems.MessageDelivery
import Lion.Theorems.RuntimeTrustBundle      -- Bundled runtime assumptions
import Lion.Theorems.ConstraintImmutability  -- TOCTOU prevention
import Lion.Theorems.CapabilityUniqueness    -- Capability ID uniqueness

-- Capability module (use tracking, limits)
import Lion.Capability.Basic                   -- TrackedCapability, use tracking types
import Lion.Capability.UseLimits               -- Use limits enforcement (CH2-THM-8)

-- Memory module (separation logic)
import Lion.Memory.SeparationLogic             -- Frame rule, compositional memory reasoning

-- Contracts and Composition
import Lion.Contracts.Interface
import Lion.Contracts.RuntimeCorrespondence  -- RuntimeBridge bundle
import Lion.Contracts.StepAffects
import Lion.Contracts.MemContract
import Lion.Contracts.CapContract
import Lion.Contracts.PolicyContract
import Lion.Contracts.AllContracts
import Lion.Composition.SystemInvariant
import Lion.Composition.SecurityComposition
import Lion.Composition.ComponentSafe         -- Compositional security: 4-part predicate
import Lion.Composition.Compatible            -- Interface compatibility for composition
import Lion.Composition.CompositionTheorem    -- v1 Theorem 2.2: parts safe → whole safe
import Lion.Composition.StructuralDefs        -- Shared structural invariant definitions
import Lion.Composition.StructuralInvariants  -- A9/A10: HeldCapsOwnedCorrectly/InTable proofs
import Lion.Composition.Bridge                -- SystemInvariant ↔ ComponentSafe bridge
import Lion.Composition.AttackCoverage        -- Attack coverage traceability theorem
import Lion.Composition.PolicyWorkflowBridge  -- Policy ↔ Workflow ↔ Composition bridges
import Lion.Composition.EndToEnd              -- v1 ch5.3: End-to-End Correctness Capstone

-- khive-deploy proofs
import Lion.Deploy.ContextPropagation  -- ADR-003: Context propagation
import Lion.Deploy.WasmSafety          -- ADR-002: WASM memory bounds & isolation
import Lion.Deploy.BatchExecution      -- ADR-002: Batch termination & order
import Lion.Deploy.Authorization       -- ADR-003: Scope-based authorization

-- Refinement proofs (Rust ↔ Lean correspondence)
import Lion.Refinement.Correspondence  -- Type correspondence relations
import Lion.Refinement.Authorization   -- Authorization refinement (4 axioms, 0 sorries)
import Lion.Refinement.HostCall        -- HostCall refinement (2 axioms, 0 sorries)
import Lion.Refinement.KernelOp        -- KernelOp refinement (1 axiom, 0 sorries)
import Lion.Refinement.PluginInternal  -- PluginInternal refinement (1 axiom, 0 sorries)
import Lion.Refinement.Step            -- Full system refinement (8 axioms total, 0 sorries)
import Lion.Refinement.Memory          -- Memory refinement (2 axioms, 0 sorries)
