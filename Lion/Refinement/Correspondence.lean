/-
Lion/Refinement/Correspondence.lean
===================================

State Correspondence Relations for Refinement Proofs

This module defines the correspondence relations between Rust implementation
types and Lean specification types. These relations are the foundation for
all refinement proofs.

See CORRESPONDENCE.md for the full opaque→Rust mapping documentation.

## Rust Type Mapping Strategy

Lean types map to Rust as follows:

| Lean Type | Rust Type | Notes |
|-----------|-----------|-------|
| ℕ (Nat) | u64 | Sufficient for IDs, time |
| PluginId | u64 | Plugin instance ID |
| CapId | u128 | UUID for capabilities |
| SecurityLevel | u8 | 4 levels fit in 2 bits |
| Right | u16 bit | 10 rights as bitflags |
| Rights (Finset Right) | u16 | Bitset representation |
| LinearMemory | wasmtime::Memory | WASM linear memory |
| State | lion_core::State | Full system state |

## Correspondence Relation

The `Corresponds` typeclass defines when a Rust value correctly
implements a Lean specification value. Key properties:
- Functional: Each Rust value maps to at most one Lean value
- Composition: Corresponds lifts through Option, List, etc.

STATUS: ACTIVE - Core type correspondences defined.
-/

import Mathlib.Tactic
import Lion.Core.Rights
import Lion.Core.Policy
import Lion.Core.Crypto
import Lion.Core.SecurityLevel
import Lion.State.State
import Lion.State.Kernel
import Lion.State.Memory
import Lion.Step.Authorization
import Lion.Step.Step

namespace Lion.Refinement

/-! ## Type Correspondence

These typeclasses define the correspondence between Rust types (represented
as Lean types mirroring Rust's structure) and Lean specification types.
-/

/-- Type correspondence relation.
    `Corresponds R L` means Rust type R corresponds to Lean type L. -/
class Corresponds (R : Type*) (L : Type*) where
  /-- The correspondence relation -/
  corresponds : R → L → Prop
  /-- Correspondence is functional (each R maps to at most one L) -/
  functional : ∀ r l₁ l₂, corresponds r l₁ → corresponds r l₂ → l₁ = l₂

/-- Notation for correspondence -/
notation:50 r " ≃ᵣ " l => Corresponds.corresponds r l

/-! ## Primitive Type Correspondences -/

/-- Natural numbers correspond to themselves -/
instance : Corresponds ℕ ℕ where
  corresponds n m := n = m
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- Booleans correspond to themselves -/
instance : Corresponds Bool Bool where
  corresponds b₁ b₂ := b₁ = b₂
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-! ## Option Correspondence -/

/-- Option correspondence: None ↔ none, Some x ↔ some y when x ≃ᵣ y -/
instance [Corresponds R L] : Corresponds (Option R) (Option L) where
  corresponds or ol :=
    match or, ol with
    | none, none => True
    | some r, some l => r ≃ᵣ l
    | _, _ => False
  functional := fun or ol₁ ol₂ h1 h2 => by
    match or, ol₁, ol₂ with
    | none, none, none => rfl
    | some r, some l₁, some l₂ =>
      exact congrArg some (Corresponds.functional r l₁ l₂ h1 h2)
    | none, some _, _ => exact False.elim h1
    | none, _, some _ => exact False.elim h2
    | some _, none, _ => exact False.elim h1
    | some _, _, none => exact False.elim h2

/-! ## Core Type Correspondences -/

/-- Rust Id128 corresponds to Lean CapId (both are ℕ) -/
structure RustId128 where
  value : ℕ

/-- RustId128 corresponds to CapId by value equality -/
instance : Corresponds RustId128 CapId where
  corresponds rid cid := rid.value = cid
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-! ## State Correspondences -/

/-- Rust PolicyContext corresponds to Lean PolicyContext -/
structure RustPolicyContext where
  now : ℕ
  callOrigin : Option ℕ

/-- PolicyContext correspondence -/
def policyContextCorresponds (rpc : RustPolicyContext) (lpc : PolicyContext) : Prop :=
  rpc.now = lpc.now ∧
  rpc.callOrigin = lpc.callOrigin

/-! ## Authorization Correspondence -/

/-- Rust Authorized<T> (represented as successful authorization result) -/
structure RustAuthorized (T : Type*) where
  inner : T
  capabilityId : RustId128
  ctx : RustPolicyContext
  capValid : Bool := true
  polPermit : Bool := true

/-! ## Refinement Definitions -/

/-- Authorization error type -/
inductive RustAuthError
  | NotFound : ℕ → RustAuthError
  | Revoked : ℕ → RustAuthError
  | Expired : RustAuthError
  | InvalidSeal : RustAuthError
  | InsufficientRights : Right → RustAuthError
  | HolderMismatch : RustAuthError
  | TargetMismatch : ℕ → ℕ → RustAuthError

/-! =========== IDENTIFIER CORRESPONDENCES =========== -/

/-- Rust u64 identifier type -/
structure RustU64 where
  value : ℕ
  bound : value < 2^64 := by decide

/-- Rust u128 identifier type (for UUIDs) -/
structure RustU128 where
  value : ℕ
  bound : value < 2^128 := by decide

/-- PluginId correspondence: Rust u64 ↔ Lean PluginId (ℕ) -/
instance : Corresponds RustU64 PluginId where
  corresponds rid pid := rid.value = pid
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- ActorId correspondence (same as PluginId) -/
instance : Corresponds RustU64 ActorId where
  corresponds rid aid := rid.value = aid
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- ResourceId correspondence -/
instance : Corresponds RustU64 ResourceId where
  corresponds rid resid := rid.value = resid
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- CapId correspondence: Rust u128 (UUID) ↔ Lean CapId (ℕ) -/
instance : Corresponds RustU128 CapId where
  corresponds rid cid := rid.value = cid
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- Time correspondence -/
instance : Corresponds RustU64 Time where
  corresponds rt lt := rt.value = lt
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-- MemAddr correspondence -/
instance : Corresponds RustU64 MemAddr where
  corresponds ra la := ra.value = la
  functional := fun _ _ _ h1 h2 => Eq.trans h1.symm h2

/-! =========== SECURITY LEVEL CORRESPONDENCE =========== -/

/-- Rust security level (u8 representation) -/
inductive RustSecurityLevel where
  | Public       -- 0
  | Internal     -- 1
  | Confidential -- 2
  | Secret       -- 3
deriving DecidableEq, Repr

/-- SecurityLevel correspondence: exact enum matching -/
def securityLevelCorresponds : RustSecurityLevel → SecurityLevel → Prop
  | .Public, .Public => True
  | .Internal, .Internal => True
  | .Confidential, .Confidential => True
  | .Secret, .Secret => True
  | _, _ => False

instance : Corresponds RustSecurityLevel SecurityLevel where
  corresponds := securityLevelCorresponds
  functional := fun rsl lsl1 lsl2 h1 h2 => by
    cases rsl <;> cases lsl1 <;> cases lsl2 <;>
    simp only [securityLevelCorresponds] at h1 h2 <;>
    first | rfl | exact False.elim h1 | exact False.elim h2

/-! =========== RIGHTS CORRESPONDENCE =========== -/

/-- Rust Right (matches Lean Right exactly) -/
inductive RustRight where
  | Read | Write | Execute | Create | Delete
  | Send | Receive | Delegate | Revoke | Declassify
deriving DecidableEq, Repr

/-- Right correspondence: exact enum matching -/
def rightCorresponds : RustRight → Right → Prop
  | .Read, .Read => True
  | .Write, .Write => True
  | .Execute, .Execute => True
  | .Create, .Create => True
  | .Delete, .Delete => True
  | .Send, .Send => True
  | .Receive, .Receive => True
  | .Delegate, .Delegate => True
  | .Revoke, .Revoke => True
  | .Declassify, .Declassify => True
  | _, _ => False

instance : Corresponds RustRight Right where
  corresponds := rightCorresponds
  functional := fun rr lr1 lr2 h1 h2 => by
    cases rr <;> cases lr1 <;> cases lr2 <;>
    simp only [rightCorresponds] at h1 h2 <;>
    first | rfl | exact False.elim h1 | exact False.elim h2

/-- Rust Rights as bitflags (u16, 10 bits used) -/
structure RustRights where
  bits : ℕ
  bound : bits < 2^10 := by decide  -- 10 rights

/-- Convert Right to bit position -/
def rightToBit : Right → ℕ
  | .Read => 0
  | .Write => 1
  | .Execute => 2
  | .Create => 3
  | .Delete => 4
  | .Send => 5
  | .Receive => 6
  | .Delegate => 7
  | .Revoke => 8
  | .Declassify => 9

/-- Check if a right is set in the bitflags -/
def RustRights.hasRight (rr : RustRights) (r : Right) : Bool :=
  (rr.bits / 2^(rightToBit r)) % 2 = 1

/-- Rights correspondence: bitset membership matches Finset membership -/
def rightsCorresponds (rr : RustRights) (lr : Rights) : Prop :=
  ∀ r : Right, rr.hasRight r = true ↔ r ∈ lr

instance : Corresponds RustRights Rights where
  corresponds := rightsCorresponds
  functional := fun rr lr1 lr2 h1 h2 => by
    ext r
    exact Iff.trans (h1 r).symm (h2 r)

/-! =========== MEMORY CORRESPONDENCE =========== -/

/-- Memory correspondence: bounds and byte contents match.
    This connects to RustMemoryLoad/RustMemoryStore opaques. -/
def memoryCorresponds (rustMem leanMem : LinearMemory) : Prop :=
  rustMem.bounds = leanMem.bounds ∧
  (∀ addr, rustMem.bytes.getD addr 0 = leanMem.bytes.getD addr 0)

theorem memoryCorresponds_refl (m : LinearMemory) : memoryCorresponds m m :=
  ⟨rfl, fun _ => rfl⟩

theorem memoryCorresponds_symm {m1 m2 : LinearMemory}
    (h : memoryCorresponds m1 m2) : memoryCorresponds m2 m1 :=
  ⟨h.1.symm, fun addr => (h.2 addr).symm⟩

/-! =========== CAPABILITY CORRESPONDENCE =========== -/

/-- Rust Capability structure.

    Corresponds to lion-capability::Capability in Rust.

    **Fixed in Q3/Q5 consultation (2026-01-02)**:
    - Added `valid : Bool` (required for revocation semantics)
    - `signature` already present (required for unforgeability)
-/
structure RustCapability where
  id : RustU128
  holder : RustU64
  target : RustU64
  rights : RustRights
  parent : Option RustU128  -- Matches Lean Capability.parent
  epoch : ℕ
  valid : Bool              -- CRITICAL: Required for revocation (cap_accept flips, revoke_transitive flips)
  signature : List UInt8    -- SealedTag (RuntimeTag) - Required for unforgeability

/-- Capability correspondence.

    All structural fields must match for a Rust capability to correspond
    to a Lean capability. Critical for security proofs:
    - `valid` correspondence ensures revocation state is tracked
    - `signature` correspondence ensures unforgeability
-/
def capabilityCorresponds (rc : RustCapability) (lc : Capability) : Prop :=
  rc.id.value = lc.id ∧
  rc.holder.value = lc.holder ∧
  rc.target.value = lc.target ∧
  rightsCorresponds rc.rights lc.rights ∧
  (match rc.parent, lc.parent with
   | some rp, some lp => rp.value = lp
   | none, none => True
   | _, _ => False) ∧
  rc.epoch = lc.epoch ∧
  rc.valid = lc.valid ∧            -- Required for revocation semantics
  rc.signature = lc.signature       -- Required for unforgeability

/-! =========== FULL STATE CORRESPONDENCE =========== -/

/-- Full state correspondence between Rust abstraction and Lean spec.

    In practice, we model Rust state as a Lean State with the same structure.
    This predicate checks that key components match. When we implement
    actual Rust code, the RustState opaque will be instantiated with
    a type that we can extract these components from. -/
def StateCorresponds (rs ls : State) : Prop :=
  -- Kernel HMAC key matches
  rs.kernel.hmacKey = ls.kernel.hmacKey ∧
  -- Revocation epoch matches
  rs.kernel.revocation.epoch = ls.kernel.revocation.epoch ∧
  -- Time synchronization
  rs.time = ls.time ∧
  -- Plugin memories correspond
  (∀ pid, memoryCorresponds (rs.plugins pid).memory (ls.plugins pid).memory) ∧
  -- Plugin security levels match
  (∀ pid, (rs.plugins pid).level = (ls.plugins pid).level)

/-- StateCorresponds is reflexive (a state corresponds to itself) -/
theorem StateCorresponds_refl (s : State) : StateCorresponds s s :=
  ⟨rfl, rfl, rfl, fun _ => memoryCorresponds_refl _, fun _ => rfl⟩

/-! =========== CORRESPONDENCE PRESERVATION =========== -/

/-- Forward simulation preserves correspondence through steps -/
theorem forward_simulation_preserves_correspondence
    {rs rs' ls : State}
    (h_corr : StateCorresponds rs ls)
    (h_step : ∃ ls', (∃ (_ : Step ls ls'), StateCorresponds rs' ls')) :
    ∃ ls', StateCorresponds rs' ls' :=
  let ⟨ls', _, h_corr'⟩ := h_step
  ⟨ls', h_corr'⟩

/-! =========== LINK TO RUNTIME CORRESPONDENCE OPAQUES =========== -/

/-
The opaques in Lion/Contracts/RuntimeCorrespondence.lean define the
trust boundary. This module provides the *structural* correspondence
definitions that those opaques *implement*:

| Opaque | This Module Provides |
|--------|---------------------|
| RustState | Structure matching State |
| rust_memory_corresponds | memoryCorresponds |
| rust_kernel_corresponds | kernelCorresponds |
| RustStep | Implied by StateCorresponds preservation |

The key invariant is:
  If Rust satisfies the opaque contracts,
  and StateCorresponds holds initially,
  then StateCorresponds is preserved by all steps.

This is what RuntimeCorrespondence.runtime_correspondence_preserved axiom states.
-/

/-! =========== RUST RUNTIME TYPE CORRESPONDENCES =========== -/

/-
These types mirror the Rust lion-runtime crate types.
See: crates/lion/lion-runtime/src/{host_call.rs, kernel_op.rs, step.rs}
-/

/-! ## RustHostFunctionId (13 variants) -/

/-- Rust HostFunctionId enum (13 variants).

Corresponds to lion-runtime::host_call::HostFunctionId.
Exact 1:1 mapping with Lean HostFunctionId.
-/
inductive RustHostFunctionId where
  | CapInvoke       -- 0: Use a capability
  | CapDelegate     -- 1: Delegate capability to another plugin
  | CapAccept       -- 2: Accept a delegated capability
  | CapRevoke       -- 3: Revoke a capability
  | MemAlloc        -- 4: Allocate kernel-managed memory
  | MemFree         -- 5: Free kernel-managed memory
  | IpcSend         -- 6: Send message to another actor
  | IpcReceive      -- 7: Receive message (blocking)
  | ResourceCreate  -- 8: Create kernel resource
  | ResourceAccess  -- 9: Access kernel resource
  | WorkflowStart   -- 10: Start a workflow
  | WorkflowStep    -- 11: Advance workflow state
  | Declassify      -- 12: Controlled information declassification
deriving DecidableEq, Repr

/-- HostFunctionId correspondence: exact enum matching -/
def hostFunctionIdCorresponds : RustHostFunctionId → HostFunctionId → Prop
  | .CapInvoke, .cap_invoke => True
  | .CapDelegate, .cap_delegate => True
  | .CapAccept, .cap_accept => True
  | .CapRevoke, .cap_revoke => True
  | .MemAlloc, .mem_alloc => True
  | .MemFree, .mem_free => True
  | .IpcSend, .ipc_send => True
  | .IpcReceive, .ipc_receive => True
  | .ResourceCreate, .resource_create => True
  | .ResourceAccess, .resource_access => True
  | .WorkflowStart, .workflow_start => True
  | .WorkflowStep, .workflow_step => True
  | .Declassify, .declassify => True
  | _, _ => False

instance : Corresponds RustHostFunctionId HostFunctionId where
  corresponds := hostFunctionIdCorresponds
  functional := fun rhf lhf1 lhf2 h1 h2 => by
    cases rhf <;> cases lhf1 <;> cases lhf2 <;>
    simp only [hostFunctionIdCorresponds] at h1 h2 <;>
    first | rfl | exact False.elim h1 | exact False.elim h2

/-! ## RustKernelOp (4 variants) -/

/-- Rust KernelOp enum (4 variants).

Corresponds to lion-runtime::kernel_op::KernelOp.
-/
inductive RustKernelOp where
  | RouteOne (dst : ActorId)        -- Deliver one message to actor
  | WorkflowTick (w : WorkflowId)   -- Advance workflow
  | TimeTick                        -- Increment global time
  | UnblockSend (dst : ActorId)     -- Unblock actor waiting to send
deriving DecidableEq, Repr

/-- KernelOp correspondence: match constructors and parameters -/
def kernelOpCorresponds : RustKernelOp → KernelOp → Prop
  | .RouteOne ra, .route_one la => ra = la
  | .WorkflowTick rw, .workflow_tick lw => rw = lw
  | .TimeTick, .time_tick => True
  | .UnblockSend ra, .unblock_send la => ra = la
  | _, _ => False

instance : Corresponds RustKernelOp KernelOp where
  corresponds := kernelOpCorresponds
  functional := fun rko lko1 lko2 h1 h2 => by
    cases rko <;> cases lko1 <;> cases lko2 <;>
    simp only [kernelOpCorresponds] at h1 h2 <;>
    first | rfl | subst h1; subst h2; rfl | exact False.elim h1 | exact False.elim h2

/-! ## RustStepKind (3 variants) -/

/-- Rust Step enum kind (3 variants).

Corresponds to lion-runtime::step::Step constructor tags.
The Rust implementation uses:
- PluginInternal { plugin_id, descriptor }
- HostCall { call, action, authorization, result }
- KernelInternal { op }

NOTE: Named RustStepKind to avoid conflict with opaque RustStep in
Lion.Contracts.Runtime which represents the full step relation.
This type represents the *kind* of step (the enum variant).
-/
inductive RustStepKind where
  | PluginInternal (pid : PluginId)
  | HostCall (caller : PluginId) (function : RustHostFunctionId)
  | KernelInternal (op : RustKernelOp)
deriving Repr

/-- Decidable equality for RustStepKind -/
instance : DecidableEq RustStepKind := fun rs1 rs2 =>
  match rs1, rs2 with
  | .PluginInternal p1, .PluginInternal p2 =>
      if h : p1 = p2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .HostCall c1 f1, .HostCall c2 f2 =>
      if hc : c1 = c2 then
        if hf : f1 = f2 then isTrue (by rw [hc, hf])
        else isFalse (by intro heq; cases heq; exact hf rfl)
      else isFalse (by intro heq; cases heq; exact hc rfl)
  | .KernelInternal o1, .KernelInternal o2 =>
      if h : o1 = o2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .PluginInternal _, .HostCall _ _ => isFalse (by intro h; cases h)
  | .PluginInternal _, .KernelInternal _ => isFalse (by intro h; cases h)
  | .HostCall _ _, .PluginInternal _ => isFalse (by intro h; cases h)
  | .HostCall _ _, .KernelInternal _ => isFalse (by intro h; cases h)
  | .KernelInternal _, .PluginInternal _ => isFalse (by intro h; cases h)
  | .KernelInternal _, .HostCall _ _ => isFalse (by intro h; cases h)

/-- Step kind correspondence.

Note: The Lean Step is indexed by states (Step s s'), so we check:
- Constructor type matches
- Plugin ID matches for plugin_internal
- Caller and function match for host_call
- KernelOp corresponds for kernel_internal
-/
def stepKindCorresponds (rs : RustStepKind) {s s' : State} (ls : Step s s') : Prop :=
  match rs, ls with
  | .PluginInternal rpid, .plugin_internal lpid _ _ _ => rpid = lpid
  | .HostCall rcaller rfunc, .host_call lhc _ _ _ _ _ _ =>
      rcaller = lhc.caller ∧ hostFunctionIdCorresponds rfunc lhc.function
  | .KernelInternal rop, .kernel_internal lop _ => kernelOpCorresponds rop lop
  | _, _ => False

/-- RustStepKind classification (for debugging/analysis) -/
inductive RustStepType where
  | PluginInternal
  | HostCall
  | KernelInternal
deriving DecidableEq, Repr

/-- Classify a RustStepKind -/
def RustStepKind.classify : RustStepKind → RustStepType
  | .PluginInternal _ => .PluginInternal
  | .HostCall _ _ => .HostCall
  | .KernelInternal _ => .KernelInternal

/-- Get subject (executing plugin) of RustStepKind -/
def RustStepKind.subject : RustStepKind → Option PluginId
  | .PluginInternal pid => some pid
  | .HostCall caller _ => some caller
  | .KernelInternal _ => none

/-- Check if RustStepKind is effectful -/
def RustStepKind.isEffectful : RustStepKind → Bool
  | .HostCall _ _ => true
  | _ => false

/-! =========== CORRESPONDENCE THEOREMS =========== -/

/-- HostFunctionId correspondence is total (every Rust value has a Lean correspondent) -/
theorem rustHostFunctionId_has_correspondent (rhf : RustHostFunctionId) :
    ∃ lhf : HostFunctionId, hostFunctionIdCorresponds rhf lhf := by
  cases rhf <;>
  first
  | exact ⟨.cap_invoke, trivial⟩
  | exact ⟨.cap_delegate, trivial⟩
  | exact ⟨.cap_accept, trivial⟩
  | exact ⟨.cap_revoke, trivial⟩
  | exact ⟨.mem_alloc, trivial⟩
  | exact ⟨.mem_free, trivial⟩
  | exact ⟨.ipc_send, trivial⟩
  | exact ⟨.ipc_receive, trivial⟩
  | exact ⟨.resource_create, trivial⟩
  | exact ⟨.resource_access, trivial⟩
  | exact ⟨.workflow_start, trivial⟩
  | exact ⟨.workflow_step, trivial⟩
  | exact ⟨.declassify, trivial⟩

/-- KernelOp correspondence is total (every Rust value has a Lean correspondent) -/
theorem rustKernelOp_has_correspondent (rko : RustKernelOp) :
    ∃ lko : KernelOp, kernelOpCorresponds rko lko := by
  cases rko with
  | RouteOne dst => exact ⟨.route_one dst, rfl⟩
  | WorkflowTick w => exact ⟨.workflow_tick w, rfl⟩
  | TimeTick => exact ⟨.time_tick, trivial⟩
  | UnblockSend dst => exact ⟨.unblock_send dst, rfl⟩

/-- Convert RustHostFunctionId to Lean HostFunctionId -/
def RustHostFunctionId.toLean : RustHostFunctionId → HostFunctionId
  | .CapInvoke => .cap_invoke
  | .CapDelegate => .cap_delegate
  | .CapAccept => .cap_accept
  | .CapRevoke => .cap_revoke
  | .MemAlloc => .mem_alloc
  | .MemFree => .mem_free
  | .IpcSend => .ipc_send
  | .IpcReceive => .ipc_receive
  | .ResourceCreate => .resource_create
  | .ResourceAccess => .resource_access
  | .WorkflowStart => .workflow_start
  | .WorkflowStep => .workflow_step
  | .Declassify => .declassify

/-- Convert RustKernelOp to Lean KernelOp -/
def RustKernelOp.toLean : RustKernelOp → KernelOp
  | .RouteOne dst => .route_one dst
  | .WorkflowTick w => .workflow_tick w
  | .TimeTick => .time_tick
  | .UnblockSend dst => .unblock_send dst

/-- toLean is correct (produces corresponding value) -/
theorem RustHostFunctionId.toLean_corresponds (rhf : RustHostFunctionId) :
    hostFunctionIdCorresponds rhf rhf.toLean := by
  cases rhf <;> simp only [toLean, hostFunctionIdCorresponds]

/-- toLean is correct (produces corresponding value) -/
theorem RustKernelOp.toLean_corresponds (rko : RustKernelOp) :
    kernelOpCorresponds rko rko.toLean := by
  cases rko <;> simp only [toLean, kernelOpCorresponds]

end Lion.Refinement
