/-
Lion/Contracts/RuntimeCorrespondence.lean
=========================================

Runtime correspondence invariant: Rust and Lean states are synchronized.

This unifies the 5 Rust refinement axioms into a single correspondence
invariant that is preserved by state transitions.

APPROACH:
- Instead of 5 separate "Rust X → Lean Y" axioms
- Define "Rust and Lean agree on state" as an invariant
- Single axiom: correspondence is preserved by transitions

ADVANTAGE:
- Fewer axioms (5 → 1)
- Matches reality: Rust/Lean evolve together
- Composable: add fields without new axioms

STATUS: IMPLEMENTED (Q11) - Full-state correspondence with 9 fields.
-/

import Mathlib.Tactic
import Lion.State.State
import Lion.State.Memory
import Lion.Step.Step
import Lion.Step.HostCall
import Lion.Step.KernelOp
import Lion.Step.PluginInternal

namespace Lion.Contracts.Runtime

open Lion

/-! ## Rust Runtime State Model

We model the Rust runtime state that corresponds to Lean State.
This is abstract - the actual Rust state is opaque from Lean's perspective.
-/

/-- Abstract Rust runtime state (opaque from Lean perspective) -/
opaque RustState : Type

/-- Rust plugin memory state -/
opaque RustPluginMemory : Type

/-- Rust kernel state -/
opaque RustKernelState : Type

/-
NEW (Q11): Additional Rust-side *views* needed for full-state correspondence.
All remain opaque to keep the TCB small.
-/

/-- Rust plugin security level view -/
opaque RustPluginLevel : Type

/-- Rust plugin held-capabilities view -/
opaque RustHeldCaps : Type

/-- Rust actor runtime view -/
opaque RustActorRuntime : Type

/-- Rust resources view -/
opaque RustResources : Type

/-- Rust workflows view -/
opaque RustWorkflows : Type

/-- Rust ghost/allocator view (may be partial) -/
opaque RustGhostView : Type

/--
**Rust Type Instances Bundle**

Bundles the Inhabited instances needed for opaque Rust types.
These are required before we can define opaque accessor functions.

Expanded (Q11) to include all new correspondence types.
-/
structure RustTypeInstances : Type 1 where
  plugin_memory_inhabited : Inhabited RustPluginMemory
  kernel_state_inhabited  : Inhabited RustKernelState
  plugin_level_inhabited  : Inhabited RustPluginLevel
  heldCaps_inhabited      : Inhabited RustHeldCaps
  actor_runtime_inhabited : Inhabited RustActorRuntime
  resources_inhabited     : Inhabited RustResources
  workflows_inhabited     : Inhabited RustWorkflows
  ghost_view_inhabited    : Inhabited RustGhostView

/-- Single axiom for Rust type instances (bundle) -/
axiom rust_type_instances : RustTypeInstances

-- Provide instances for opaque function definitions
noncomputable instance : Inhabited RustPluginMemory := rust_type_instances.plugin_memory_inhabited
noncomputable instance : Inhabited RustKernelState  := rust_type_instances.kernel_state_inhabited
noncomputable instance : Inhabited RustPluginLevel  := rust_type_instances.plugin_level_inhabited
noncomputable instance : Inhabited RustHeldCaps     := rust_type_instances.heldCaps_inhabited
noncomputable instance : Inhabited RustActorRuntime := rust_type_instances.actor_runtime_inhabited
noncomputable instance : Inhabited RustResources    := rust_type_instances.resources_inhabited
noncomputable instance : Inhabited RustWorkflows    := rust_type_instances.workflows_inhabited
noncomputable instance : Inhabited RustGhostView    := rust_type_instances.ghost_view_inhabited

/-! ## Correspondence Relations -/

/-- Rust plugin memory corresponds to Lean LinearMemory -/
opaque rust_memory_corresponds (rm : RustPluginMemory) (lm : LinearMemory) : Prop

/-- Rust kernel state corresponds to Lean KernelState -/
opaque rust_kernel_corresponds (rk : RustKernelState) (lk : KernelState) : Prop

/-- Rust plugin level corresponds to Lean SecurityLevel -/
opaque rust_level_corresponds (rl : RustPluginLevel) (ll : SecurityLevel) : Prop

/-- Rust held-caps corresponds to Lean heldCaps (Finset CapId - handles, not copies) -/
opaque rust_heldCaps_corresponds (rh : RustHeldCaps) (lh : Finset CapId) : Prop

/-- Rust actor runtime corresponds to Lean ActorRuntime -/
opaque rust_actor_corresponds (ra : RustActorRuntime) (la : ActorRuntime) : Prop

/-- Rust resources correspond to Lean resources mapping -/
opaque rust_resources_corresponds (rr : RustResources) (lr : ResourceId → ResourceInfo) : Prop

/-- Rust workflows correspond to Lean workflows mapping -/
opaque rust_workflows_corresponds (rw : RustWorkflows) (lw : WorkflowId → WorkflowInstance) : Prop

/--
Rust ghost/allocator consistency with Lean MetaState.

Important: this should be interpreted as a *consistency* relation, not equality.
It is allowed to be partial (e.g. Rust tracks only allocator cursor / live-set).
-/
opaque rust_ghost_consistent (rg : RustGhostView) (lg : MetaState) : Prop

/-! ## Opaque Projections from Rust State -/

/-- Rust plugin memory for a given plugin (abstract) -/
noncomputable opaque rust_plugin_memory (rs : RustState) (pid : PluginId) : RustPluginMemory

/-- Rust kernel state (abstract) -/
noncomputable opaque rust_kernel (rs : RustState) : RustKernelState

/-- Rust plugin level (abstract) -/
noncomputable opaque rust_plugin_level (rs : RustState) (pid : PluginId) : RustPluginLevel

/-- Rust plugin heldCaps (abstract) -/
noncomputable opaque rust_plugin_heldCaps (rs : RustState) (pid : PluginId) : RustHeldCaps

/-- Rust actor runtime view (per-actor) -/
noncomputable opaque rust_actor (rs : RustState) (aid : ActorId) : RustActorRuntime

/-- Rust resources view (bulk) -/
noncomputable opaque rust_resources (rs : RustState) : RustResources

/-- Rust workflows view (bulk) -/
noncomputable opaque rust_workflows (rs : RustState) : RustWorkflows

/-- Rust ghost view (bulk/minimal) -/
noncomputable opaque rust_ghost_view (rs : RustState) : RustGhostView

/-- Extract time from Rust state -/
opaque rust_time (rs : RustState) : ℕ

/-! ## Runtime Correspondence Invariant

This bundles all Rust↔Lean correspondence into a single structure.
-/

/--
**Runtime Correspondence Invariant**: Rust and Lean states are synchronized.

This is the consolidated form of the 5 Rust refinement axioms.
Instead of saying "if Rust does X then Lean allows Y", we say
"Rust and Lean agree on the state, and will agree after any transition".

Expanded (Q11) to cover full-state components needed by refinement:
- plugin levels (security clearance)
- plugin heldCaps (capabilities currently held)
- actors (per-actor runtime state)
- resources (resource ownership)
- workflows (workflow instances)
- ghost/allocator view (allocation consistency)
-/
structure RuntimeCorrespondence (rs : RustState) (ls : State) : Prop where
  /-- Memory correspondence for all plugins -/
  memory : ∀ pid, rust_memory_corresponds (rust_plugin_memory rs pid) (ls.plugins pid).memory
  /-- Kernel state correspondence -/
  kernel : rust_kernel_corresponds (rust_kernel rs) ls.kernel
  /-- Time synchronization -/
  time_sync : rust_time rs = ls.time
  /-- Plugin security levels correspond -/
  levels : ∀ pid, rust_level_corresponds (rust_plugin_level rs pid) (ls.plugins pid).level
  /-- Plugin heldCaps correspond -/
  heldCaps : ∀ pid, rust_heldCaps_corresponds (rust_plugin_heldCaps rs pid) (ls.plugins pid).heldCaps
  /-- Actors correspond (per-actor view) -/
  actors : ∀ aid, rust_actor_corresponds (rust_actor rs aid) (ls.actors aid)
  /-- Resources correspond (bulk view) -/
  resources : rust_resources_corresponds (rust_resources rs) ls.resources
  /-- Workflows correspond (bulk view) -/
  workflows : rust_workflows_corresponds (rust_workflows rs) ls.workflows
  /-- Ghost/allocator view is consistent with Lean ghost -/
  ghost : rust_ghost_consistent (rust_ghost_view rs) ls.ghost

/--
Convenience lemma: expose ghost in the "existential witness" style if desired.

Note: `∃ g, ls.ghost = g ∧ ...` is logically equivalent to directly relating
`ls.ghost`, but sometimes nicer for proof choreography.
-/
theorem RuntimeCorrespondence.ghost_exists {rs : RustState} {ls : State}
    (h : RuntimeCorrespondence rs ls) :
    ∃ g : MetaState, ls.ghost = g ∧ rust_ghost_consistent (rust_ghost_view rs) g :=
  ⟨ls.ghost, rfl, h.ghost⟩

/-! ## Transition Correspondence

When Rust takes a step, Lean takes a corresponding step.
-/

/-- Rust execution step (abstract) -/
opaque RustStep (rs rs' : RustState) : Prop

/--
**Step Correspondence**: Corresponding states take corresponding steps.

This captures: if Rust and Lean are synchronized, and Rust takes a step,
then Lean takes a step that maintains synchronization.

Note: Step is an inductive type (not Prop), so we express correspondence
as an implication rather than a structure with Step as a field.
-/
def step_corresponds (rs rs' : RustState) (ls ls' : State) : Prop :=
  RustStep rs rs' →
  RuntimeCorrespondence rs ls →
  (∃ (_ : Step ls ls'), RuntimeCorrespondence rs' ls')

/-! ## Single Preservation Axiom

This replaces the 5 Rust refinement axioms.
-/

/--
**AXIOM: Runtime Correspondence Preserved**

If Rust and Lean states correspond, and Rust takes a step,
then there exists a Lean step that maintains correspondence.

This is the SINGLE axiom replacing:
- rust_host_exec_refines
- rust_kernel_exec_refines
- rust_plugin_exec_refines
- rust_wasm_memory_read_refines
- rust_wasm_memory_write_refines

JUSTIFICATION:
The Rust implementation is designed to implement the Lean specification.
This axiom captures that design intent as a correspondence invariant.

PROVABLE FROM: Verified Rust implementation + correspondence proof.
-/
axiom runtime_correspondence_preserved :
  ∀ (rs rs' : RustState) (ls : State),
  RuntimeCorrespondence rs ls →
  RustStep rs rs' →
  ∃ ls' : State, (∃ (_ : Step ls ls'), RuntimeCorrespondence rs' ls')

/-! ## Derived Refinements

From the single axiom, we can derive the component refinements.
-/

/--
**Derived**: Step preserves hmacKey (frame property from Step semantics).

This follows from the comprehensive frame axioms for each step type:
- plugin_internal: kernel unchanged (plugin_internal_kernel_unchanged)
- host_call: hmacKey unchanged (host_call_hmacKey_unchanged)
- kernel_internal: kernel unchanged (kernel op frame theorems)

Note: This is a pure Step property, NOT derived from correspondence.
Frame properties come from the semantic specification of steps in Lean,
not from the refinement relation.
-/
theorem step_preserves_hmacKey (ls ls' : State) (h_step : Step ls ls') :
    ls'.kernel.hmacKey = ls.kernel.hmacKey := by
  cases h_step with
  | plugin_internal pid pi hpre hexec =>
    have h_kernel := plugin_internal_kernel_unchanged pid pi ls ls' hexec
    simp only [h_kernel]
  | host_call hc a auth hr hparse hpre hexec =>
    exact host_call_hmacKey_unchanged hc a auth hr ls ls' hexec
  | kernel_internal op hexec =>
    cases op with
    | time_tick =>
      have h_kernel := (time_tick_comprehensive_frame ls ls' hexec).1
      simp only [h_kernel]
    | route_one dst =>
      have h_kernel := (route_one_comprehensive_frame dst ls ls' hexec).1
      simp only [h_kernel]
    | workflow_tick wid =>
      have h_kernel := (workflow_tick_comprehensive_frame wid ls ls' hexec).1
      simp only [h_kernel]
    | unblock_send dst =>
      have h_kernel := (unblock_send_comprehensive_frame dst ls ls' hexec).1
      simp only [h_kernel]

/-! ## Initial Correspondence

Correspondence must hold initially.

We bundle initial states and their correspondence into a single structure.
-/

/--
**Initial Correspondence Bundle**

Bundles the three initial-state axioms into a single structure:
1. RustState.initial - Initial Rust state exists
2. State.initial_state - Initial Lean state exists
3. initial_correspondence - These initial states correspond

This replaces 3 separate axioms with 1 bundled axiom.
-/
structure InitialCorrespondence : Type 1 where
  /-- Initial Rust state -/
  rust_initial : RustState
  /-- Initial Lean state -/
  lean_initial : State
  /-- Initial states correspond -/
  correspondence : RuntimeCorrespondence rust_initial lean_initial

/-- Single axiom for initial correspondence (replaces 3 axioms) -/
axiom initial_correspondence_bundle : InitialCorrespondence

-- Re-export for backward compatibility
noncomputable def RustState.initial : RustState := initial_correspondence_bundle.rust_initial
noncomputable def State.initial_state : State := initial_correspondence_bundle.lean_initial
theorem initial_correspondence :
    RuntimeCorrespondence RustState.initial State.initial_state :=
  initial_correspondence_bundle.correspondence

/-! =========== RUNTIME BRIDGE - MASTER CORRESPONDENCE BUNDLE =========== -/

/--
**RuntimeBridge - Complete Correspondence TCB**

Bundles ALL Rust↔Lean correspondence assumptions:
1. rust_type_instances: Opaque Rust types are inhabited
2. runtime_correspondence_preserved: Steps preserve correspondence
3. initial_correspondence_bundle: Initial states correspond

This is ONE of the 3 target trust bundles for Lion:
- Crypto (CryptoTrustBundle)
- Runtime (RuntimeIsolation)
- Correspondence (this bundle)

The RuntimeBridge captures the fundamental assumption that the Rust
implementation correctly implements the Lean specification.
-/
structure RuntimeBridge : Type 1 where
  /-- Rust types have Inhabited instances -/
  type_instances : RustTypeInstances
  /-- Initial states are provided and correspond -/
  initial : InitialCorrespondence
  /-- Correspondence is preserved by execution steps -/
  preserved : ∀ (rs rs' : RustState) (ls : State),
    RuntimeCorrespondence rs ls →
    RustStep rs rs' →
    ∃ ls' : State, (∃ (_ : Step ls ls'), RuntimeCorrespondence rs' ls')

/-- Derive full runtime bridge from component axioms -/
noncomputable def runtime_bridge : RuntimeBridge where
  type_instances := rust_type_instances
  initial := initial_correspondence_bundle
  preserved := runtime_correspondence_preserved

/-! ## Rust Reachability

RustReachable models which Rust states are reachable from initial state.
This is the Rust-side analog of Lean's Reachable type.
-/

/--
**Rust State Reachability**: States reachable from initial through RustStep.

This is the Rust-side analog of Lean's Reachable inductive type.
Used to express properties about all states the Rust runtime can reach.
-/
inductive RustReachable : RustState → RustState → Prop where
  | refl (rs : RustState) : RustReachable rs rs
  | step {rs rs' rs'' : RustState} : RustReachable rs rs' → RustStep rs' rs'' → RustReachable rs rs''

/-- Transitivity of RustReachable -/
theorem RustReachable.trans {rs1 rs2 rs3 : RustState} :
    RustReachable rs1 rs2 → RustReachable rs2 rs3 → RustReachable rs1 rs3 := by
  intro h12 h23
  induction h23 with
  | refl => exact h12
  | step _ hstep ih => exact RustReachable.step ih hstep

/-! ## Correspondence Preservation Through Reachability

Key integration theorem: Rust reachability implies Lean reachability
while preserving RuntimeCorrespondence.
-/

/--
**Integration Theorem: Rust Reachability Implies Lean Reachability**

If Rust states rs → rs' (via RustReachable) and rs corresponds to ls,
then there exists ls' such that ls → ls' (via Lean Reachable) and rs' corresponds to ls'.

This is the fundamental refinement theorem connecting Rust execution to Lean semantics.
-/
theorem rust_reachable_implies_lean_reachable
    (rs rs' : RustState) (ls : State)
    (h_corr : RuntimeCorrespondence rs ls)
    (h_reach : RustReachable rs rs') :
    ∃ ls', Reachable ls ls' ∧ RuntimeCorrespondence rs' ls' := by
  induction h_reach with
  | refl => exact ⟨ls, Reachable.refl ls, h_corr⟩
  | step h_reach h_step ih =>
    -- By IH, get ls_mid corresponding to rs_mid
    obtain ⟨ls_mid, h_lean_reach, h_corr_mid⟩ := ih
    -- By correspondence preservation, get ls' corresponding to rs'
    obtain ⟨ls', hstep, h_corr'⟩ := runtime_correspondence_preserved _ _ ls_mid h_corr_mid h_step
    -- Combine Lean reachabilities
    exact ⟨ls', Reachable.step h_lean_reach hstep, h_corr'⟩

/--
**Corollary: Initial Rust Reachability Implies Initial Lean Reachability**

States reachable from Rust initial state correspond to states reachable
from Lean initial state.
-/
theorem initial_rust_reachable_implies_lean_reachable
    (rs' : RustState)
    (h_reach : RustReachable RustState.initial rs') :
    ∃ ls', Reachable State.initial_state ls' ∧ RuntimeCorrespondence rs' ls' :=
  rust_reachable_implies_lean_reachable RustState.initial rs' State.initial_state
    initial_correspondence h_reach

/--
**Invariant Transfer Theorem**: Lean invariants hold on Rust-reachable states.

If P holds on all Lean-reachable states from initial, and Rust state rs'
is reachable from initial, then P holds on the corresponding Lean state.

This allows us to transfer Lean security proofs to Rust execution guarantees.
-/
theorem lean_invariant_holds_on_rust_reachable
    (P : State → Prop)
    (h_always : ∀ ls', Reachable State.initial_state ls' → P ls')
    (rs' : RustState)
    (h_reach : RustReachable RustState.initial rs') :
    ∃ ls', RuntimeCorrespondence rs' ls' ∧ P ls' := by
  obtain ⟨ls', h_lean_reach, h_corr'⟩ := initial_rust_reachable_implies_lean_reachable rs' h_reach
  exact ⟨ls', h_corr', h_always ls' h_lean_reach⟩

/-! ## Summary

This module defines the Rust↔Lean correspondence layer.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     RUST IMPLEMENTATION                         │
│  (lion-core, lion-runtime, lion-contracts crates)              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ opaque types (trust boundary)
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   RuntimeCorrespondence                         │
│  memory    : ∀ pid, RustPluginMemory ↔ LinearMemory            │
│  kernel    : RustKernelState ↔ KernelState                     │
│  time_sync : rust_time = lean_time                             │
│  levels    : ∀ pid, RustPluginLevel ↔ SecurityLevel            │
│  heldCaps  : ∀ pid, RustHeldCaps ↔ Finset CapId                │
│  actors    : ∀ aid, RustActorRuntime ↔ ActorRuntime            │
│  resources : RustResources ↔ (ResourceId → ResourceInfo)       │
│  workflows : RustWorkflows ↔ (WorkflowId → WorkflowInstance)   │
│  ghost     : RustGhostView ~ MetaState (consistency)           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ proven properties
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     LEAN SPECIFICATION                          │
│  (Lion.State, Lion.Step, Lion.Theorems)                        │
└─────────────────────────────────────────────────────────────────┘
```

## Components

1. **RuntimeCorrespondence**: Full-state correspondence (9 fields)
   - Plugins: memory, levels, heldCaps (per-plugin)
   - Global: kernel, time, actors, resources, workflows, ghost

2. **Single Preservation Axiom** (runtime_correspondence_preserved):
   Correspondence is preserved by Rust steps

3. **Initial Axiom** (initial_correspondence_bundle):
   Initial states exist and correspond

4. **RuntimeBridge**: Complete TCB bundle (all assumptions in one place)

5. **RustReachable**: Rust-side reachability (mirrors Lean's Reachable)

6. **Integration Theorems**:
   - rust_reachable_implies_lean_reachable: Rust traces → Lean traces
   - initial_rust_reachable_implies_lean_reachable: From initial state
   - lean_invariant_holds_on_rust_reachable: Transfer Lean invariants to Rust

## Axiom Count

- rust_type_instances: 1 (bundled Inhabited instances)
- initial_correspondence_bundle: 1 (bundled initial state + correspondence)
- runtime_correspondence_preserved: 1 (single preservation axiom)

**Total: 3 axioms** (vs 6+ with unbundled approach)

## Trust Boundary

The `opaque` declarations are the trust boundary:
- Lean doesn't know what's inside RustState, RustPluginMemory, etc.
- We axiomatize that Rust types are Inhabited and correspondence is preserved
- The Rust implementation must discharge these axioms

This is intentional - it keeps the Lean TCB minimal while allowing
full-state reasoning through the correspondence structure.
-/

end Lion.Contracts.Runtime
