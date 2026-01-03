/-
Lion/Step/KernelOp.lean
========================

Kernel internal operations (trusted TCB).
-/

import Lion.Core.Identifiers
import Lion.State.State

namespace Lion

/-! =========== KERNEL OPERATIONS =========== -/

/-- Kernel-internal operations (no external trigger) -/
inductive KernelOp where
  | route_one (dst : ActorId)    -- Deliver one message to actor
  | workflow_tick (w : WorkflowId)  -- Advance workflow
  | time_tick                    -- Increment global time
  | unblock_send (dst : ActorId) -- Unblock actor waiting to send
deriving DecidableEq, Repr

/-! =========== WORKFLOW PROGRESS INVARIANT =========== -/

/--
**Invariant: Running workflow has work**

A running workflow must have either pending nodes or active nodes.
This ensures progress is always possible (no zombie workflows).

The scheduler maintains this: when last node completes, workflow transitions
to success/failure rather than staying in running state.
-/
def WorkflowHasWork (wi : WorkflowInstance) : Prop :=
  wi.status = .running → (wi.pending_count > 0 ∨ wi.active_count > 0)

/--
**Predicate: Valid workflow transition**

A workflow_tick transition must preserve the has-work invariant:
- Either the workflow completes (status ≠ running), OR
- The workflow still has pending or active nodes
-/
def ValidWorkflowTransition (wi' : WorkflowInstance) : Prop :=
  WorkflowHasWork wi'

/-! =========== KERNEL EXECUTION =========== -/

/--
Kernel internal execution relation.
**Constructive definition** - enables frame facts to be proven as theorems.

Each operation modifies only its designated state component:
- route_one: moves message from pending to mailbox (respects capacity)
- time_tick: increments global time
- workflow_tick: advances workflow state (preserves has-work invariant)
- unblock_send: clears blockedOn for actor
-/
def KernelExecInternal (op : KernelOp) (s s' : State) : Prop :=
  match op with
  | .route_one dst =>
      -- Move first message from pending to mailbox (if pending non-empty)
      -- Scheduler ensures mailbox doesn't exceed capacity
      ∃ msg rest,
        (s.actors dst).pending = msg :: rest ∧
        (s.actors dst).mailbox.length < (s.actors dst).capacity ∧
        let newActor : ActorRuntime := {
          (s.actors dst) with
          pending := rest,
          mailbox := (s.actors dst).mailbox ++ [msg]
        }
        s' = { s with actors := Function.update s.actors dst newActor }
  | .time_tick =>
      -- Simply increment time
      s' = { s with time := s.time + 1 }
  | .workflow_tick wid =>
      -- Advance workflow (must preserve has-work invariant)
      ∃ wi',
        ValidWorkflowTransition wi' ∧
        s' = { s with workflows := Function.update s.workflows wid wi' }
  | .unblock_send dst =>
      -- Clear blockedOn for the destination actor
      let newActor : ActorRuntime := { (s.actors dst) with blockedOn := none }
      s' = { s with actors := Function.update s.actors dst newActor }

/-! =========== COMPREHENSIVE FRAME THEOREMS =========== -/

/--
**Comprehensive Frame Theorem for route_one**

route_one(dst) only affects actors(dst).pending and actors(dst).mailbox.
All other state components are unchanged.

PROVEN from constructive definition - no longer an axiom.
-/
theorem route_one_comprehensive_frame
    (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    s'.kernel = s.kernel ∧
    s'.plugins = s.plugins ∧
    (∀ aid, aid ≠ dst → s'.actors aid = s.actors aid) ∧
    s'.resources = s.resources ∧
    s'.workflows = s.workflows ∧
    s'.ghost = s.ghost ∧
    s'.time = s.time := by
  -- Unfold the definition and extract the equality
  simp only [KernelExecInternal] at h
  rcases h with ⟨msg, rest, _, _hcap, rfl⟩
  -- All fields except actors are unchanged by {s with actors := ...}
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  -- For actors: Function.update only changes dst
  intro aid hne
  simp only [Function.update]
  split
  · -- Case: aid = dst, but we have hne : aid ≠ dst
    rename_i heq
    exact absurd heq hne
  · -- Case: aid ≠ dst
    rfl

/--
**Comprehensive Frame Theorem for time_tick**

time_tick only increments time by 1.
All other state components are unchanged.

PROVEN from constructive definition - no longer an axiom.
-/
theorem time_tick_comprehensive_frame
    (s s' : State)
    (h : KernelExecInternal .time_tick s s') :
    s'.kernel = s.kernel ∧
    s'.plugins = s.plugins ∧
    s'.actors = s.actors ∧
    s'.resources = s.resources ∧
    s'.workflows = s.workflows ∧
    s'.ghost = s.ghost ∧
    s'.time = s.time + 1 := by
  -- Unfold the definition
  simp only [KernelExecInternal] at h
  -- h : s' = { s with time := s.time + 1 }
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
**Comprehensive Frame Theorem for workflow_tick**

workflow_tick(wid) only affects workflows(wid).
All other state components are unchanged.

PROVEN from constructive definition - no longer an axiom.
-/
theorem workflow_tick_comprehensive_frame
    (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    s'.kernel = s.kernel ∧
    s'.plugins = s.plugins ∧
    s'.actors = s.actors ∧
    s'.resources = s.resources ∧
    (∀ other, other ≠ wid → s'.workflows other = s.workflows other) ∧
    s'.ghost = s.ghost ∧
    s'.time = s.time := by
  -- Unfold the definition and extract the equality
  simp only [KernelExecInternal] at h
  rcases h with ⟨wi', _hvalid, rfl⟩
  -- All fields except workflows are unchanged
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  -- For workflows: Function.update only changes wid
  intro other hne
  simp only [Function.update]
  split
  · -- Case: other = wid, but we have hne : other ≠ wid
    rename_i heq
    exact absurd heq hne
  · -- Case: other ≠ wid
    rfl

/--
**Comprehensive Frame Theorem for unblock_send**

unblock_send(dst) only affects actors(dst).blockedOn (clears it).
All other state components are unchanged.

PROVEN from constructive definition - no longer an axiom.
-/
theorem unblock_send_comprehensive_frame
    (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    s'.kernel = s.kernel ∧
    s'.plugins = s.plugins ∧
    (∀ aid, aid ≠ dst → s'.actors aid = s.actors aid) ∧
    (s'.actors dst).blockedOn = none ∧
    s'.resources = s.resources ∧
    s'.workflows = s.workflows ∧
    s'.ghost = s.ghost ∧
    s'.time = s.time := by
  -- Unfold the definition
  simp only [KernelExecInternal] at h
  -- h : s' = { s with actors := Function.update ... }
  subst h
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  -- For actors: Function.update only changes dst
  · intro aid hne
    simp only [Function.update]
    split
    · rename_i heq
      exact absurd heq hne
    · rfl
  -- blockedOn for dst is none
  · simp only [Function.update]
    split
    · -- Case: dst = dst, so we get newActor
      rfl
    · -- Case: dst ≠ dst, contradiction (¬True is False)
      rename_i hne
      exact False.elim (hne trivial)

/-! =========== DERIVED FRAME THEOREMS =========== -/

-- Derived from route_one_comprehensive_frame

theorem route_one_frame (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    ∀ aid, aid ≠ dst → s'.actors aid = s.actors aid :=
  (route_one_comprehensive_frame dst s s' h).2.2.1

theorem route_one_memory_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    s'.plugins = s.plugins :=
  (route_one_comprehensive_frame dst s s' h).2.1

theorem route_one_resource_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    s'.resources = s.resources :=
  (route_one_comprehensive_frame dst s s' h).2.2.2.1

theorem route_one_ghost_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.route_one dst) s s') :
    s'.ghost = s.ghost :=
  (route_one_comprehensive_frame dst s s' h).2.2.2.2.2.1

-- Derived from time_tick_comprehensive_frame

theorem time_tick_only_time (s s' : State)
    (h : KernelExecInternal .time_tick s s') :
    s'.time = s.time + 1 ∧ s'.plugins = s.plugins ∧ s'.actors = s.actors :=
  let frame := time_tick_comprehensive_frame s s' h
  ⟨frame.2.2.2.2.2.2, frame.2.1, frame.2.2.1⟩

theorem time_tick_ghost_unchanged (s s' : State)
    (h : KernelExecInternal .time_tick s s') :
    s'.ghost = s.ghost :=
  (time_tick_comprehensive_frame s s' h).2.2.2.2.2.1

-- Derived from workflow_tick_comprehensive_frame

theorem workflow_tick_frame (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    ∀ other, other ≠ wid → s'.workflows other = s.workflows other :=
  (workflow_tick_comprehensive_frame wid s s' h).2.2.2.2.1

theorem workflow_tick_plugins_unchanged (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    s'.plugins = s.plugins :=
  (workflow_tick_comprehensive_frame wid s s' h).2.1

theorem workflow_tick_resources_unchanged (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    s'.resources = s.resources :=
  (workflow_tick_comprehensive_frame wid s s' h).2.2.2.1

theorem workflow_tick_ghost_unchanged (wid : WorkflowId) (s s' : State)
    (h : KernelExecInternal (.workflow_tick wid) s s') :
    s'.ghost = s.ghost :=
  (workflow_tick_comprehensive_frame wid s s' h).2.2.2.2.2.1

-- Derived from unblock_send_comprehensive_frame

theorem unblock_send_frame (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    ∀ aid, aid ≠ dst → s'.actors aid = s.actors aid :=
  (unblock_send_comprehensive_frame dst s s' h).2.2.1

theorem unblock_send_plugins_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    s'.plugins = s.plugins :=
  (unblock_send_comprehensive_frame dst s s' h).2.1

theorem unblock_send_resources_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    s'.resources = s.resources :=
  (unblock_send_comprehensive_frame dst s s' h).2.2.2.2.1

theorem unblock_send_clears_blocked (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    (s'.actors dst).blockedOn = none :=
  (unblock_send_comprehensive_frame dst s s' h).2.2.2.1

theorem unblock_send_ghost_unchanged (dst : ActorId) (s s' : State)
    (h : KernelExecInternal (.unblock_send dst) s s') :
    s'.ghost = s.ghost :=
  (unblock_send_comprehensive_frame dst s s' h).2.2.2.2.2.2.1

/-! =========== KERNEL OPERATION INVARIANT PRESERVATION AXIOMS =========== -/

/--
**Theorem: route_one Respects Mailbox Capacity**

Derived from the capacity check in KernelExecInternal.route_one.
The definition requires mailbox.length < capacity before routing.
After appending one message: mailbox.length + 1 ≤ capacity.
-/
theorem route_one_respects_mailbox_capacity
    (dst : ActorId) (s s' : State)
    (hexec : KernelExecInternal (.route_one dst) s s') :
    (∀ aid : ActorId,
      (s.actors aid).mailbox.length ≤ (s.actors aid).capacity →
      (s'.actors aid).mailbox.length ≤ (s'.actors aid).capacity) := by
  intro aid h_cap_s
  -- Extract facts from route_one definition
  simp only [KernelExecInternal] at hexec
  rcases hexec with ⟨msg, rest, _h_pending, h_cap_check, rfl⟩
  -- h_cap_check : (s.actors dst).mailbox.length < (s.actors dst).capacity
  simp only [Function.update]
  split
  · -- aid = dst case
    rename_i h_eq
    subst h_eq
    -- New mailbox = old mailbox ++ [msg]
    simp only [List.length_append, List.length_singleton]
    -- mailbox.length + 1 ≤ capacity (since old length < capacity)
    exact Nat.succ_le_of_lt h_cap_check
  · -- aid ≠ dst case: actor unchanged
    exact h_cap_s

/--
**Theorem: workflow_tick Preserves Progress Possibility**

Derived from ValidWorkflowTransition constraint in KernelExecInternal.
The constraint ensures WorkflowHasWork for the new workflow instance.
-/
theorem workflow_tick_preserves_progress
    (wid : WorkflowId) (s s' : State)
    (hexec : KernelExecInternal (.workflow_tick wid) s s') :
    -- For the ticked workflow: if still running, has progress resources
    ((s'.workflows wid).status = .running →
      (s'.time < (s'.workflows wid).timeout_at ∨
       (s'.workflows wid).pending_count > 0 ∨
       (s'.workflows wid).active_count > 0)) ∧
    -- For other workflows: unchanged by workflow_tick frame
    (∀ other, other ≠ wid →
      (s.workflows other).status = .running →
      (s.time < (s.workflows other).timeout_at ∨
       (s.workflows other).pending_count > 0 ∨
       (s.workflows other).active_count > 0) →
      (s'.time < (s'.workflows other).timeout_at ∨
       (s'.workflows other).pending_count > 0 ∨
       (s'.workflows other).active_count > 0)) := by
  -- Get frame facts first
  have h_frame := workflow_tick_comprehensive_frame wid s s' hexec
  -- Extract the ValidWorkflowTransition constraint
  simp only [KernelExecInternal] at hexec
  rcases hexec with ⟨wi', hvalid, h_eq⟩
  constructor
  · -- For the ticked workflow: use ValidWorkflowTransition (WorkflowHasWork)
    intro h_running
    -- s'.workflows wid = wi' (by Function.update at wid)
    subst h_eq
    -- Simplify Function.update wid at wid = wi'
    simp only [Function.update] at h_running
    split at h_running
    · -- wid = wid case: h_running : wi'.status = .running
      -- hvalid : ValidWorkflowTransition wi' = WorkflowHasWork wi'
      -- WorkflowHasWork wi' : wi'.status = .running → pending > 0 ∨ active > 0
      have h_has_work := hvalid h_running
      -- Goal involves Function.update, simplify it too
      simp only [Function.update]
      split
      · exact Or.inr h_has_work
      · rename_i hfalse; exact absurd trivial hfalse
    · -- wid ≠ wid case: the condition is ¬(wid = wid) which is False
      rename_i hfalse; exact absurd trivial hfalse
  · -- For other workflows: use frame (unchanged)
    intro other hne _h_running h_progress
    have h_wf := h_frame.2.2.2.2.1 other hne
    have h_time := h_frame.2.2.2.2.2.2
    simp only [h_wf, h_time]
    exact h_progress

/-!
**Note: time_tick and Workflow Progress**

Previously this file contained an axiom `time_tick_preserves_workflow_progress`.
This axiom has been eliminated by introducing the `AllWorkflowsHaveWork` system
invariant in SystemInvariant.lean.

The key insight: With AllWorkflowsHaveWork as an invariant, running workflows
always have `pending_count > 0 ∨ active_count > 0`. Since time_tick doesn't
change workflows, this condition is preserved regardless of how time changes.

This eliminates the need for scheduler coordination axioms - the invariant
captures the scheduler's contract that running workflows always have work.
-/

end Lion
