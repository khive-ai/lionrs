/-
Lion/Composition/SystemInvariant.lean
======================================

SystemInvariant: The conjunction of all security properties.
Defined as a structure for better Lean ergonomics (projections like `hs.cap_unforgeable`).

Design decision: Use structure instead of bare conjunction.
This makes the composition proof cleaner: `exact { cap_unforgeable := ..., ... }`
-/

import Lion.State.State
import Lion.Step.Step
import Lion.Core.RuntimeIsolation
import Lion.Theorems.TemporalSafety
import Lion.Theorems.Confinement
import Lion.Theorems.Revocation
import Lion.Theorems.Noninterference

namespace Lion

/-! =========== SECURITY PREDICATES =========== -/

-- We use unique names to avoid conflicts with existing definitions.
-- These are composition-specific versions that are now connected to
-- the actual theorem statements from the individual proof modules.

/-- 001: Capability Unforgeability
    All capabilities in the table are properly sealed with kernel HMAC.
    STRENGTHENED: Links to Capability.verify_seal from Crypto.lean -/
def CapUnforgeable (s : State) : Prop :=
  ∀ capId cap,
    s.kernel.revocation.caps.get? capId = some cap →
    Capability.verify_seal s.kernel.hmacKey cap

/-- 002: Memory Spatial Safety (WASM Linear Memory Bounds Invariant)
    All bytes stored in plugin memory are within the declared bounds.

    This is the WASM sandboxing guarantee: plugins cannot access memory
    outside their allocated linear memory region. The property holds because:
    1. LinearMemory.empty starts with no bytes stored
    2. WASM runtime enforces bounds checking on all memory operations
    3. Step semantics only allow bounded memory writes

    Note: This is stronger than just "different plugins have different memory"
    (which is structural by the State type). This says the memory IS well-formed. -/
def MemoryIsolated (s : State) : Prop :=
  ∀ pid : PluginId, ∀ addr : MemAddr,
    (s.plugins pid).memory.bytes.contains addr →
    addr < (s.plugins pid).memory.bounds

/-- 003: Deadlock Freedom (safety approximation)
    At least one step is always possible. -/
def DeadlockFree (s : State) : Prop :=
  ∃ s', Nonempty (Step s s')

/-- 004: Capability Confinement
    Delegated rights are always subset of parent rights.
    STRENGTHENED: Links to Confinement.table_invariant (well_keyed ∧ well_formed) -/
def CapConfined (s : State) : Prop :=
  Confinement.table_invariant s.kernel.revocation.caps

/-- 005: Capability Revocation
    Revoked capabilities cannot be used for authorization.
    STRENGTHENED: Links to Authorization and IsValid -/
def CapRevocable (s : State) : Prop :=
  ∀ (a : Action) (cap : Capability),
    ¬ IsValid s.kernel.revocation.caps cap.id →
    ¬ ∃ (auth : Authorized s a), auth.cap = cap

/-- 006: Temporal Safety
    Freed resources cannot be accessed. -/
def TemporalSafe (s : State) : Prop :=
  ∀ addr, addr ∈ s.ghost.freed_set →
    ¬ MetaState.is_live s.ghost addr

/-- 007: Message Delivery (safety approximation for liveness)
    Mailboxes do not exceed their declared capacity.

    This is a SAFETY approximation of the liveness property
    "messages will eventually be delivered". If mailboxes stay
    within capacity, the deliver operation can always proceed
    (no permanent blocking due to overflow).

    Full liveness would require fairness assumptions about scheduling. -/
def MessageDeliveryPossible (s : State) : Prop :=
  ∀ aid : ActorId, (s.actors aid).mailbox.length ≤ (s.actors aid).capacity

/-- 008a: Workflow Has Work Invariant
    Running workflows must have pending or active nodes.

    This is STRONGER than just "can make progress" - it ensures
    running workflows actually have work to do, not just time remaining.
    The scheduler maintains this: when last node completes, workflow
    transitions to success/failure rather than staying in running state.

    This invariant enables proving time_tick preserves workflow progress
    without requiring scheduler coordination axioms. -/
def AllWorkflowsHaveWork (s : State) : Prop :=
  ∀ wid : WorkflowId, WorkflowHasWork (s.workflows wid)

/-- 008b: Workflow Termination (safety approximation for liveness)
    Running workflows have resources available for progress.

    This is a SAFETY approximation of the liveness property
    "workflows will eventually terminate". A running workflow
    can make progress if it has either:
    - Time remaining before timeout (can tick), OR
    - Pending nodes to start, OR
    - Active nodes to complete/fail/retry

    Note: With AllWorkflowsHaveWork invariant, this follows trivially
    since running workflows always have pending OR active nodes.

    Full liveness follows from workflow_measure decreasing (Workflow.lean). -/
def WorkflowProgressPossible (s : State) : Prop :=
  ∀ wid : WorkflowId,
    (s.workflows wid).status = .running →
    (s.time < (s.workflows wid).timeout_at ∨
     (s.workflows wid).pending_count > 0 ∨
     (s.workflows wid).active_count > 0)

/-- 009: Policy Soundness
    Denied actions cannot execute via authorization.
    STRENGTHENED: Links to policy_check and Authorized witness -/
def PolicySound (s : State) : Prop :=
  ∀ (a : Action) (ctx : PolicyContext),
    policy_check s.kernel.policy a ctx = .deny →
    ¬ ∃ (auth : Authorized s a), auth.ctx = ctx

/-- 011: Step Confinement (single-state proxy for noninterference)
    High steps preserve low-equivalence.
    STRENGTHENED: Links to Noninterference.low_equivalent_left -/
def StepConfinementHolds (s : State) : Prop :=
  ∀ L s' (st : Step s s'),
    (st.level > L) →
    low_equivalent_left L s s'

/-! =========== SYSTEM INVARIANT STRUCTURE =========== -/

/--
SystemInvariant: The master security property.

All 10 security properties bundled as a structure.
Using structure instead of conjunction gives:
1. Named projections (hs.cap_unforgeable instead of hs.1)
2. Cleaner construction syntax ({ cap_unforgeable := ..., ... })
3. Better error messages

Note: Liveness properties (003, 007, 008) use safety approximations.
Full liveness requires separate trace-based reasoning.
-/
structure SystemInvariant (s : State) : Prop where
  /-- 001: Capabilities cannot be forged -/
  cap_unforgeable : CapUnforgeable s

  /-- 002: Plugin memory is isolated -/
  memory_isolated : MemoryIsolated s

  /-- 003: System is not deadlocked (safety approximation) -/
  deadlock_free : DeadlockFree s

  /-- 004: Delegated rights ⊆ parent rights -/
  cap_confined : CapConfined s

  /-- 005: Revoked capabilities cannot be used -/
  cap_revocable : CapRevocable s

  /-- 006: Freed resources cannot be accessed -/
  temporal_safe : TemporalSafe s

  /-- 007: Messages can be delivered (safety approximation) -/
  message_delivery : MessageDeliveryPossible s

  /-- 008a: Running workflows have work (pending or active nodes) -/
  workflows_have_work : AllWorkflowsHaveWork s

  /-- 008b: Workflows can progress (safety approximation) -/
  workflow_progress : WorkflowProgressPossible s

  /-- 009: Denied actions cannot execute -/
  policy_sound : PolicySound s

  /-- 011: High steps preserve low-equivalence -/
  step_confinement : StepConfinementHolds s

namespace SystemInvariant

/-! =========== BASIC LEMMAS =========== -/

/-- Equivalence with conjunction (for compatibility) -/
theorem iff_conj (s : State) :
    SystemInvariant s ↔
    (CapUnforgeable s ∧
     MemoryIsolated s ∧
     DeadlockFree s ∧
     CapConfined s ∧
     CapRevocable s ∧
     TemporalSafe s ∧
     MessageDeliveryPossible s ∧
     AllWorkflowsHaveWork s ∧
     WorkflowProgressPossible s ∧
     PolicySound s ∧
     StepConfinementHolds s) := by
  constructor
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Extract safety invariant (excluding liveness approximations) -/
def to_safety (hs : SystemInvariant s) :
    CapUnforgeable s ∧
    MemoryIsolated s ∧
    CapConfined s ∧
    CapRevocable s ∧
    TemporalSafe s ∧
    PolicySound s ∧
    StepConfinementHolds s :=
  ⟨hs.cap_unforgeable, hs.memory_isolated, hs.cap_confined,
    hs.cap_revocable, hs.temporal_safe, hs.policy_sound, hs.step_confinement⟩

end SystemInvariant

/-! =========== INITIAL STATE =========== -/

/-- Default empty plugin state -/
noncomputable def empty_plugin : PluginState := {
  memory := LinearMemory.empty 0
  heldCaps := ∅
  level := .Secret
  localState := ()
}

/-- Default empty actor runtime -/
def empty_actor : ActorRuntime := ActorRuntime.empty 100  -- capacity 100

/-- Default empty workflow definition (no nodes, no edges) -/
def default_workflow_def : WorkflowDef := { nodes := [], edges := [] }

/-- Default empty workflow -/
def empty_workflow : WorkflowInstance := {
  definition := default_workflow_def
  status := .success
  node_states := fun _ => .completed
  timeout_at := 0
  retries := fun _ => 0
}

/-- Default empty resource -/
def empty_resource : ResourceInfo := {
  level := .Secret
}

/-- Default policy state: deny-all via PolicyProvider Unit -/
def default_policy_state : PolicyState := default

/-- Default kernel state -/
noncomputable def empty_kernel : KernelState := {
  hmacKey := []  -- Empty key (Key = List UInt8)
  policy := default_policy_state
  revocation := RevocationState.empty
  now := 0
}

/-- Default ghost state -/
def empty_ghost : MetaState := MetaState.empty

/-- Initial state (empty system) -/
noncomputable def init_state : State := {
  kernel := empty_kernel
  plugins := fun _ => empty_plugin
  actors := fun _ => empty_actor
  resources := fun _ => empty_resource
  workflows := fun _ => empty_workflow
  ghost := empty_ghost
  time := 0
}

/-! =========== INIT STATE SATISFIES INVARIANT =========== -/

/-- Initial state satisfies SystemInvariant -/
noncomputable def init_satisfies_invariant : SystemInvariant init_state := {
  cap_unforgeable := by
    intro capId cap h
    -- Empty caps table: get? returns none, so h is false (vacuously true)
    simp only [init_state, empty_kernel, RevocationState.empty] at h
    -- h : Std.HashMap.get? {} capId = some cap, which is false
    -- The empty HashMap returns none for any key
    exact absurd h (by simp [Std.HashMap.getElem?_empty])

  memory_isolated := by
    -- Empty plugin has LinearMemory.empty with bytes := {} (empty HashMap)
    -- So bytes.contains addr is false for all addr, making implication vacuously true
    intro pid addr h_contains
    simp only [init_state, empty_plugin, LinearMemory.empty] at h_contains
    -- h_contains : {}.contains addr which is false for empty HashMap
    exact False.elim (by simp at h_contains)

  deadlock_free := by
    -- In empty state, time_tick is always possible
    -- Construct s' = { init_state with time := 1 }
    use { init_state with time := init_state.time + 1 }
    -- Construct the Step witness via kernel_internal time_tick
    exact ⟨Step.kernel_internal .time_tick rfl⟩

  cap_confined := by
    -- Empty table is trivially well-keyed and well-formed: no capabilities exist
    -- CapConfined = table_invariant = ⟨well_keyed, well_formed⟩
    constructor
    · -- well_keyed_table: vacuously true (no entries)
      intro k c h_c_in
      simp only [init_state, empty_kernel, RevocationState.empty] at h_c_in
      exact absurd h_c_in (by simp [Std.HashMap.getElem?_empty])
    · -- well_formed_table: vacuously true (no capabilities to violate invariant)
      intro c pid h_c_in h_parent
      simp only [init_state, empty_kernel, RevocationState.empty] at h_c_in
      exact absurd h_c_in (by simp [Std.HashMap.getElem?_empty])

  cap_revocable := by
    intro a cap h_not_valid
    intro ⟨auth, h_cap_eq⟩
    -- auth.h_valid : IsValid init_state.kernel.revocation.caps auth.cap.id
    -- h_cap_eq : auth.cap = cap
    -- h_not_valid : ¬ IsValid ... cap.id
    have h_valid := auth.h_valid
    rw [h_cap_eq] at h_valid
    exact h_not_valid h_valid

  temporal_safe := by
    intro addr h
    -- Empty freed_set: addr ∈ {} is false
    simp only [init_state, empty_ghost, MetaState.empty] at h
    -- h : addr ∈ {} which is false in Finset
    exact absurd h (Finset.notMem_empty addr)

  message_delivery := by
    -- empty_actor has mailbox := [] and capacity := 100
    -- So mailbox.length (= 0) ≤ capacity (= 100)
    intro aid
    simp only [init_state, empty_actor, ActorRuntime.empty]
    decide

  workflows_have_work := by
    -- empty_workflow has status := .success (not .running)
    -- So WorkflowHasWork is vacuously true (antecedent false)
    intro wid h_running
    simp only [init_state, empty_workflow] at h_running
    -- h_running : .success = .running which is false
    exact absurd h_running (by decide)

  workflow_progress := by
    -- empty_workflow has status := .success (not .running)
    -- So the implication is vacuously true
    intro wid h_running
    simp only [init_state, empty_workflow] at h_running
    -- h_running : .success = .running which is false
    exact absurd h_running (by decide)

  policy_sound := by
    intro a ctx h_deny
    -- Use policy_denied_no_auth theorem from Authorization.lean
    exact policy_denied_no_auth h_deny

  step_confinement := by
    intro L s' st h_high
    -- Use step_confinement_holds from Noninterference.lean
    have h_conf := Noninterference.step_confinement_holds L
    unfold Noninterference.step_confinement at h_conf
    exact h_conf init_state s' st h_high
}

/-! =========== HELPER LEMMAS FOR PRESERVATION =========== -/

/-- Kernel state is unchanged by time_tick -/
theorem time_tick_kernel_unchanged (s s' : State)
    (h : KernelExecInternal .time_tick s s') :
    s'.kernel = s.kernel :=
  (time_tick_comprehensive_frame s s' h).1

/-- Kernel state is unchanged by route_one -/
theorem route_one_kernel_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    s'.kernel = s.kernel :=
  (route_one_comprehensive_frame dst s s' h).1

/-- Kernel state is unchanged by workflow_tick -/
theorem workflow_tick_kernel_unchanged (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    s'.kernel = s.kernel :=
  (workflow_tick_comprehensive_frame wid s s' h).1

/-- Kernel state is unchanged by unblock_send -/
theorem unblock_send_kernel_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    s'.kernel = s.kernel :=
  (unblock_send_comprehensive_frame dst s s' h).1

/-- CapRevocable follows from revoked_no_auth theorem -/
lemma cap_revocable_from_no_auth (s : State) :
    CapRevocable s := by
  intro a cap h_not_valid
  exact Revocation.revoked_no_auth s a cap h_not_valid

/-- PolicySound follows from policy_denied_no_auth theorem -/
lemma policy_sound_from_denied (s : State) :
    PolicySound s := by
  intro a ctx h_deny
  exact policy_denied_no_auth h_deny

/-- StepConfinementHolds follows from Noninterference.step_confinement_holds -/
lemma step_confinement_from_noninterference (s : State) :
    StepConfinementHolds s := by
  intro L s' st h_high
  -- step_confinement_holds L gives us: ∀ s s' st, is_high_step L st → low_equivalent_left L s s'
  have h_conf := Noninterference.step_confinement_holds L
  unfold Noninterference.step_confinement at h_conf
  exact h_conf s s' st h_high

/-! =========== STEP PRESERVATION THEOREMS =========== -/

/--
**Theorem: Steps preserve Memory Isolation**

All steps preserve the WASM memory bounds invariant.
Proven from:
- plugin_internal: executing plugin uses bounds axiom, others use frame
- host_call: caller uses bounds axiom, others use frame
- kernel_internal: all ops use plugins-unchanged frame
-/
theorem step_preserves_memory_isolated {s s' : State} (hstep : Step s s')
    (h_iso : MemoryIsolated s) : MemoryIsolated s' := by
  intro query_pid addr h_contains
  cases hstep with
  | plugin_internal exec_pid pi hpre hexec =>
      -- For the executing plugin: use plugin_internal_respects_bounds
      -- For other plugins: they're unchanged by the frame theorem
      by_cases h_eq : query_pid = exec_pid
      · -- Case: query_pid = exec_pid (the executing plugin)
        rw [h_eq]
        exact plugin_internal_respects_bounds exec_pid pi s s' hpre hexec addr (h_eq ▸ h_contains)
      · -- Case: query_pid ≠ exec_pid (other plugins are unchanged)
        have h_frame := plugin_internal_frame exec_pid pi s s' hexec query_pid h_eq
        rw [h_frame] at h_contains
        rw [h_frame]
        exact h_iso query_pid addr h_contains
  | host_call hc a auth hr hparse hpre hexec =>
      -- For the caller: use host_call_respects_memory_bounds
      -- For other plugins: they're unchanged by the frame theorem
      by_cases h_eq : query_pid = hc.caller
      · -- Case: query_pid = hc.caller (the caller plugin)
        subst h_eq
        -- Provide precondition: h_iso shows memory was bounded in s
        have h_pre_bounds : ∀ addr, (s.plugins hc.caller).memory.bytes.contains addr →
            addr < (s.plugins hc.caller).memory.bounds := fun addr' h => h_iso hc.caller addr' h
        have ⟨h_bounded, _h_bounds_same⟩ := host_call_respects_memory_bounds hc a auth hr s s' hexec h_pre_bounds
        exact h_bounded addr h_contains
      · -- Case: query_pid ≠ hc.caller (other plugins are unchanged)
        have h_frame := host_call_plugin_frame hc a auth hr s s' hexec query_pid h_eq
        rw [h_frame] at h_contains
        rw [h_frame]
        exact h_iso query_pid addr h_contains
  | kernel_internal op hexec =>
      -- All kernel ops preserve s'.plugins = s.plugins
      cases op with
      | time_tick =>
          have h_plugins := (time_tick_comprehensive_frame s s' hexec).2.1
          rw [h_plugins] at h_contains
          rw [h_plugins]
          exact h_iso query_pid addr h_contains
      | route_one dst =>
          have h_plugins := (route_one_comprehensive_frame dst s s' hexec).2.1
          rw [h_plugins] at h_contains
          rw [h_plugins]
          exact h_iso query_pid addr h_contains
      | workflow_tick wid =>
          have h_plugins := (workflow_tick_comprehensive_frame wid s s' hexec).2.1
          rw [h_plugins] at h_contains
          rw [h_plugins]
          exact h_iso query_pid addr h_contains
      | unblock_send dst =>
          have h_plugins := (unblock_send_comprehensive_frame dst s s' hexec).2.1
          rw [h_plugins] at h_contains
          rw [h_plugins]
          exact h_iso query_pid addr h_contains

/--
**Theorem: Steps preserve Message Delivery Possibility**

All steps preserve the mailbox capacity invariant.
Proven from:
- plugin_internal: actors unchanged
- host_call: uses host_call_respects_mailbox_capacity axiom
- kernel_internal: uses route_one_respects_mailbox_capacity or actors frame
-/
theorem step_preserves_message_delivery {s s' : State} (hstep : Step s s')
    (h_mdp : MessageDeliveryPossible s) : MessageDeliveryPossible s' := by
  intro query_aid
  cases hstep with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal execution doesn't affect actors
      have h_actors := plugin_internal_actors_unchanged pid pi s s' hexec
      rw [h_actors]
      exact h_mdp query_aid
  | host_call hc a auth hr hparse hpre hexec =>
      -- Host calls respect mailbox capacity
      exact host_call_respects_mailbox_capacity hc a auth hr s s' hexec query_aid (h_mdp query_aid)
  | kernel_internal op hexec =>
      cases op with
      | time_tick =>
          -- time_tick doesn't change actors
          have h_actors := (time_tick_comprehensive_frame s s' hexec).2.2.1
          rw [h_actors]
          exact h_mdp query_aid
      | route_one dst =>
          -- route_one respects mailbox capacity
          exact route_one_respects_mailbox_capacity dst s s' hexec query_aid (h_mdp query_aid)
      | workflow_tick wid =>
          -- workflow_tick doesn't change actors
          have h_actors := (workflow_tick_comprehensive_frame wid s s' hexec).2.2.1
          rw [h_actors]
          exact h_mdp query_aid
      | unblock_send target_dst =>
          -- unblock_send only changes blockedOn, not mailbox
          by_cases h_eq : query_aid = target_dst
          · -- For dst: only blockedOn changes, mailbox unchanged
            rw [h_eq]
            -- Use the constructive definition
            simp only [KernelExecInternal] at hexec
            subst hexec
            -- s' = {s with actors := Function.update s.actors target_dst newActor}
            -- where newActor = {s.actors target_dst with blockedOn := none}
            simp only [Function.update, dite_eq_ite, ite_true]
            -- newActor preserves mailbox and capacity
            exact h_mdp target_dst
          · -- For other actors: unchanged by frame
            have h_frame := (unblock_send_comprehensive_frame target_dst s s' hexec).2.2.1
            have h_aid_unchanged := h_frame query_aid h_eq
            rw [h_aid_unchanged]
            exact h_mdp query_aid

/--
**Theorem: Steps preserve AllWorkflowsHaveWork**

All steps preserve the has-work invariant for workflows.
Proven from:
- plugin_internal: workflows unchanged
- host_call: workflows unchanged
- kernel_internal:
  - time_tick: workflows unchanged
  - route_one: workflows unchanged
  - workflow_tick: ValidWorkflowTransition requires WorkflowHasWork
  - unblock_send: workflows unchanged
-/
theorem step_preserves_workflows_have_work {s s' : State} (hstep : Step s s')
    (h_whw : AllWorkflowsHaveWork s) : AllWorkflowsHaveWork s' := by
  intro query_wid
  cases hstep with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal doesn't affect workflows
      have h_workflows := plugin_internal_workflows_unchanged pid pi s s' hexec
      rw [h_workflows]
      exact h_whw query_wid
  | host_call hc a auth hr hparse hpre hexec =>
      -- Host calls don't affect workflows
      have h_workflows := host_call_workflows_unchanged hc a auth hr s s' hexec
      rw [h_workflows]
      exact h_whw query_wid
  | kernel_internal op hexec =>
      cases op with
      | time_tick =>
          -- time_tick doesn't change workflows
          have h_workflows := (time_tick_comprehensive_frame s s' hexec).2.2.2.2.1
          rw [h_workflows]
          exact h_whw query_wid
      | route_one dst =>
          -- route_one doesn't change workflows
          have h_workflows := (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.1
          rw [h_workflows]
          exact h_whw query_wid
      | workflow_tick tick_wid =>
          -- workflow_tick preserves WorkflowHasWork via ValidWorkflowTransition
          simp only [KernelExecInternal] at hexec
          rcases hexec with ⟨wi', hvalid, h_eq⟩
          subst h_eq
          by_cases h_wid_eq : query_wid = tick_wid
          · -- query_wid = tick_wid: use ValidWorkflowTransition
            subst h_wid_eq
            simp only [Function.update, eq_self_iff_true, dite_true]
            exact hvalid
          · -- query_wid ≠ tick_wid: use frame
            simp only [Function.update, h_wid_eq, dite_false]
            exact h_whw query_wid
      | unblock_send dst =>
          -- unblock_send doesn't change workflows
          have h_workflows := (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.1
          rw [h_workflows]
          exact h_whw query_wid

/--
**Theorem: Steps preserve Workflow Progress Possibility**

All steps preserve the workflow progress invariant.
Proven from:
- plugin_internal: workflows and time unchanged
- host_call: uses host_call_respects_workflow_progress theorem
- kernel_internal: uses AllWorkflowsHaveWork invariant + frame theorems
-/
theorem step_preserves_workflow_progress {s s' : State} (hstep : Step s s')
    (h_whw : AllWorkflowsHaveWork s)
    (h_wpp : WorkflowProgressPossible s) : WorkflowProgressPossible s' := by
  intro query_wid h_running_s'
  cases hstep with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal execution doesn't affect workflows or time
      have h_workflows := plugin_internal_workflows_unchanged pid pi s s' hexec
      have h_time := plugin_internal_time_unchanged pid pi s s' hexec
      -- h_running_s' : (s'.workflows query_wid).status = .running
      -- Use frame to show s.workflows = s'.workflows
      have h_running_s : (s.workflows query_wid).status = .running := by
        rw [h_workflows] at h_running_s'; exact h_running_s'
      have h_progress_s := h_wpp query_wid h_running_s
      -- Rewrite the conclusion using frames
      rw [h_workflows, h_time]
      exact h_progress_s
  | host_call hc a auth hr hparse hpre hexec =>
      -- Host calls preserve workflow progress
      have h_preserved := host_call_respects_workflow_progress hc a auth hr s s' hexec
      -- Use workflows unchanged from host_call frame
      have h_workflows := host_call_workflows_unchanged hc a auth hr s s' hexec
      have h_running_s : (s.workflows query_wid).status = .running := by
        rw [h_workflows] at h_running_s'; exact h_running_s'
      -- h_preserved expects the hypothesis function, not the result
      exact h_preserved query_wid h_running_s' (h_wpp query_wid)
  | kernel_internal op hexec =>
      cases op with
      | time_tick =>
          -- time_tick preserves workflow progress using AllWorkflowsHaveWork invariant
          -- Key insight: workflows unchanged, so if running in s', has work in s'
          have h_workflows := (time_tick_comprehensive_frame s s' hexec).2.2.2.2.1
          have h_running_s : (s.workflows query_wid).status = .running := by
            rw [h_workflows] at h_running_s'; exact h_running_s'
          -- AllWorkflowsHaveWork tells us running workflows have pending OR active work
          have h_has_work : WorkflowHasWork (s.workflows query_wid) := h_whw query_wid
          have h_work := h_has_work h_running_s
          -- s'.workflows = s.workflows, so the same condition holds in s'
          rw [h_workflows]
          exact Or.inr h_work
      | route_one dst =>
          -- route_one doesn't affect workflows or time
          have h_workflows := (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.1
          have h_time := (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.2.2
          have h_running_s : (s.workflows query_wid).status = .running := by
            rw [h_workflows] at h_running_s'; exact h_running_s'
          rw [h_workflows, h_time]
          exact h_wpp query_wid h_running_s
      | workflow_tick tick_wid =>
          -- workflow_tick preserves progress
          have ⟨h_ticked, h_others⟩ := workflow_tick_preserves_progress tick_wid s s' hexec
          by_cases h_eq : query_wid = tick_wid
          · -- This is the ticked workflow
            subst h_eq
            exact h_ticked h_running_s'
          · -- Other workflows: use frame + preservation
            have h_frame := (workflow_tick_comprehensive_frame tick_wid s s' hexec).2.2.2.2.1
            have h_time := (workflow_tick_comprehensive_frame tick_wid s s' hexec).2.2.2.2.2.2
            have h_wid_unchanged := h_frame query_wid h_eq
            have h_running_s : (s.workflows query_wid).status = .running := by
              rw [h_wid_unchanged] at h_running_s'; exact h_running_s'
            rw [h_wid_unchanged, h_time]
            exact h_wpp query_wid h_running_s
      | unblock_send dst =>
          -- unblock_send doesn't affect workflows or time
          have h_workflows := (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.1
          have h_time := (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.2.2
          have h_running_s : (s.workflows query_wid).status = .running := by
            rw [h_workflows] at h_running_s'; exact h_running_s'
          rw [h_workflows, h_time]
          exact h_wpp query_wid h_running_s

/-! =========== COMPOSITION THEOREM =========== -/

/--
Theorem 010: Security Composition

This is the main theorem proving SystemInvariant is preserved by all steps.

The full proof using InterfaceContract composition is in:
  Lion/Composition/SecurityComposition.lean

Here we provide the direct inductive proof using the structure of the predicates.
-/
theorem security_composition :
    ∀ s s', SystemInvariant s → Step s s' → SystemInvariant s' := by
  intro s s' hs hstep
  exact {
    -- 002: Memory Isolation (WASM bounds invariant)
    -- Uses step_preserves_memory_isolated axiom for clean proof
    memory_isolated := step_preserves_memory_isolated hstep hs.memory_isolated

    -- 001: Capability Unforgeability
    -- Seals are preserved: new caps are sealed, existing caps unchanged
    cap_unforgeable := by
      intro capId cap h_in_s'
      -- Case analysis on step type
      cases hstep with
      | plugin_internal pid pi hpre hexec =>
        -- Plugin internal steps don't modify kernel state at all
        have h_kernel := plugin_internal_kernel_unchanged pid pi s s' hexec
        -- Since kernel unchanged, caps table and hmacKey unchanged
        simp only [h_kernel] at h_in_s' ⊢
        exact hs.cap_unforgeable capId cap h_in_s'
      | host_call hc a auth hr hparse hpre hexec =>
        -- Host calls preserve capability integrity (caps have valid seals)
        -- Uses host_call_preserves_cap_integrity axiom
        exact host_call_preserves_cap_integrity hc a auth hr s s' hexec
          hs.cap_unforgeable capId cap h_in_s'
      | kernel_internal op hexec =>
        -- Kernel internal steps preserve the full kernel state
        cases op with
        | time_tick =>
          have h_kernel := time_tick_kernel_unchanged s s' hexec
          simp only [h_kernel] at h_in_s' ⊢
          exact hs.cap_unforgeable capId cap h_in_s'
        | route_one dst =>
          have h_kernel := route_one_kernel_unchanged dst s s' hexec
          simp only [h_kernel] at h_in_s' ⊢
          exact hs.cap_unforgeable capId cap h_in_s'
        | workflow_tick wid =>
          have h_kernel := workflow_tick_kernel_unchanged wid s s' hexec
          simp only [h_kernel] at h_in_s' ⊢
          exact hs.cap_unforgeable capId cap h_in_s'
        | unblock_send dst =>
          have h_kernel := unblock_send_kernel_unchanged dst s s' hexec
          simp only [h_kernel] at h_in_s' ⊢
          exact hs.cap_unforgeable capId cap h_in_s'

    -- 003: Deadlock Freedom
    deadlock_free := by
      -- After a step, time_tick is always possible (no preconditions)
      use { s' with time := s'.time + 1 }
      exact ⟨Step.kernel_internal .time_tick rfl⟩

    -- 004: Capability Confinement
    cap_confined := by
      -- Delegation invariant preserved: new delegations respect parent rights
      cases hstep with
      | plugin_internal pid pi hpre hexec =>
        have h_kernel := plugin_internal_kernel_unchanged pid pi s s' hexec
        unfold CapConfined
        simp only [h_kernel]
        exact hs.cap_confined
      | host_call hc a auth hr hparse hpre hexec =>
        -- Host calls preserve capability confinement
        -- Uses host_call_preserves_cap_confined axiom
        exact host_call_preserves_cap_confined hc a auth hr s s' hexec hs.cap_confined
      | kernel_internal op hexec =>
        cases op with
        | time_tick =>
          have h_kernel := time_tick_kernel_unchanged s s' hexec
          unfold CapConfined
          simp only [h_kernel]
          exact hs.cap_confined
        | route_one dst =>
          have h_kernel := route_one_kernel_unchanged dst s s' hexec
          unfold CapConfined
          simp only [h_kernel]
          exact hs.cap_confined
        | workflow_tick wid =>
          have h_kernel := workflow_tick_kernel_unchanged wid s s' hexec
          unfold CapConfined
          simp only [h_kernel]
          exact hs.cap_confined
        | unblock_send dst =>
          have h_kernel := unblock_send_kernel_unchanged dst s s' hexec
          unfold CapConfined
          simp only [h_kernel]
          exact hs.cap_confined

    -- 005: Capability Revocability
    cap_revocable := by
      intro a cap h_not_valid
      -- CapRevocable follows from the structure of Authorized
      -- If IsValid fails in s', no Authorized can be constructed
      exact Revocation.revoked_no_auth s' a cap h_not_valid

    -- 006: Temporal Safety
    temporal_safe := by
      intro addr h_freed
      -- Use step_preserves_temporal_safety from TemporalSafety.lean
      have h_temp := step_preserves_temporal_safety hstep
      -- h_temp says: freed_set only grows (addr in s → addr in s')
      -- h_freed : addr ∈ s'.ghost.freed_set
      -- Use use_after_free_prevented to show ¬ is_live
      exact use_after_free_prevented s' addr h_freed

    -- 007: Message Delivery (mailbox capacity invariant)
    -- Uses step_preserves_message_delivery theorem for clean proof
    message_delivery := step_preserves_message_delivery hstep hs.message_delivery

    -- 008a: Workflows Have Work (running workflows have pending or active nodes)
    -- Uses step_preserves_workflows_have_work theorem
    workflows_have_work := step_preserves_workflows_have_work hstep hs.workflows_have_work

    -- 008b: Workflow Progress (running workflows have progress resources)
    -- Uses step_preserves_workflow_progress theorem with AllWorkflowsHaveWork invariant
    workflow_progress := step_preserves_workflow_progress hstep hs.workflows_have_work hs.workflow_progress

    -- 009: Policy Soundness
    policy_sound := by
      intro a ctx h_deny
      -- PolicySound follows from policy_denied_no_auth
      exact policy_denied_no_auth h_deny

    -- 011: Step Confinement
    step_confinement := by
      intro L s'' st h_high
      -- Use step_confinement_holds from Noninterference.lean
      have h_conf := Noninterference.step_confinement_holds L
      unfold Noninterference.step_confinement at h_conf
      exact h_conf s' s'' st h_high
  }

/--
Corollary: All reachable states satisfy the invariant.
-/
theorem reachable_satisfies_invariant :
    ∀ s, Reachable init_state s → SystemInvariant s := by
  intro s hreach
  induction hreach with
  | refl => exact init_satisfies_invariant
  | step _ hstep ih => exact security_composition _ _ ih hstep

/-! =========== CONNECTION TO INDIVIDUAL THEOREMS =========== -/

/-- CapUnforgeable implies all caps have valid seals (connects to Theorem 001) -/
theorem cap_unforgeable_implies_sealed (s : State) (hs : SystemInvariant s) :
    ∀ capId cap,
      s.kernel.revocation.caps.get? capId = some cap →
      Capability.verify_seal s.kernel.hmacKey cap :=
  hs.cap_unforgeable

/-- CapConfined implies delegation chain monotonicity (connects to Theorem 004) -/
theorem cap_confined_implies_confinement (s : State) (hs : SystemInvariant s)
    (c root : Capability)
    (h_chain : Confinement.InDelegationChain s.kernel.revocation.caps c root) :
    c.rights ⊆ root.rights :=
  -- hs.cap_confined is table_invariant = (well_keyed ∧ well_formed)
  -- confinement_chain only needs well_formed_table
  Confinement.confinement_chain s.kernel.revocation.caps c root hs.cap_confined.2 h_chain

/-- CapRevocable implies revoked caps cannot authorize (connects to Theorem 005) -/
theorem cap_revocable_implies_no_auth (s : State) (hs : SystemInvariant s)
    (a : Action) (cap : Capability)
    (h_revoked : ¬ IsValid s.kernel.revocation.caps cap.id) :
    ¬ ∃ (auth : Authorized s a), auth.cap = cap :=
  hs.cap_revocable a cap h_revoked

/-- PolicySound implies denied actions cannot execute (connects to Theorem 009) -/
theorem policy_sound_implies_denied_blocked (s : State) (hs : SystemInvariant s)
    (a : Action) (ctx : PolicyContext)
    (h_deny : policy_check s.kernel.policy a ctx = .deny) :
    ¬ ∃ (auth : Authorized s a), auth.ctx = ctx :=
  hs.policy_sound a ctx h_deny

/-- StepConfinement implies high steps are invisible to low observers (connects to Theorem 011) -/
theorem step_confinement_implies_low_equiv (s : State) (hs : SystemInvariant s)
    (L : SecurityLevel) (s' : State) (st : Step s s')
    (h_high : st.level > L) :
    low_equivalent_left L s s' :=
  hs.step_confinement L s' st h_high

end Lion
