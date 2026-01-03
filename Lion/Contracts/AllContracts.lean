/-
Lion/Contracts/AllContracts.lean
=================================

Remaining Interface Contracts for Security Composition.

This file contains contracts 004, 005, 006, 007, 008, and 011.

Dependency Graph (from a1, a2 research):
```
Level 0: 002 Memory Isolation (pre = True) [MemContract.lean]
    │
    ├── Level 1: 001 Capability Unforgeability (pre = memory_isolated) [CapContract.lean]
    │       │
    │       └── Level 2: 009 Policy Soundness (pre = cap_unforgeable) [PolicyContract.lean]
    │               │
    │               ├── Level 3: 004 Confinement (pre = cap_unforgeable ∧ policy_sound)
    │               │       │
    │               │       └── Level 4: 005 Revocation (pre = cap_confined)
    │               │               │
    │               │               └── Level 5: 006 Temporal Safety (pre = cap_revocable)
    │               │
    │               └── Level 3: 011 Step Confinement (pre = memory_isolated ∧ cap_confined ∧ policy_sound)
    │
    └── Level 1: 007 Message Delivery (pre = memory_isolated) [Liveness safety approx]
            │
            └── Level 2: 003 Deadlock Freedom (already in SystemInvariant)
                    │
                    └── Level 3: 008 Workflow Termination (pre = deadlock_free)
```
-/

import Lion.Contracts.Interface
import Lion.Contracts.StepAffects
import Lion.Contracts.PolicyContract
import Lion.Composition.SystemInvariant
import Lion.Theorems.TemporalSafety

namespace Lion

/-! =========== CONTRACT 004: CAPABILITY CONFINEMENT =========== -/

/--
Capability Confinement Contract (004).

Delegated capabilities cannot exceed parent's rights.

Precondition: CapUnforgeable ∧ PolicySound
- Need unforgeable caps to trust rights fields
- Need policy to enforce delegation rules
-/
noncomputable def confinementContract : InterfaceContract State Step :=
  { pre := fun s => CapUnforgeable s ∧ PolicySound s
    inv := CapConfined
    affects := fun h => step_affects_caps h
    preserve := by
      intro s s' h hinv _hpre _ha
      -- Case analysis on step type - all steps preserve kernel state
      cases h with
      | plugin_internal pid pi hpre hexec =>
        have h_kernel := plugin_internal_kernel_unchanged pid pi s s' hexec
        unfold CapConfined
        simp only [h_kernel]
        exact hinv
      | host_call hc a auth hr hparse hpre' hexec =>
        -- Host calls preserve capability confinement via host_call_preserves_cap_confined
        exact host_call_preserves_cap_confined hc a auth hr s s' hexec hinv
      | kernel_internal op hexec =>
        cases op with
        | time_tick =>
          have h_kernel := time_tick_kernel_unchanged s s' hexec
          unfold CapConfined; simp only [h_kernel]; exact hinv
        | route_one dst =>
          have h_kernel := route_one_kernel_unchanged dst s s' hexec
          unfold CapConfined; simp only [h_kernel]; exact hinv
        | workflow_tick wid =>
          have h_kernel := workflow_tick_kernel_unchanged wid s s' hexec
          unfold CapConfined; simp only [h_kernel]; exact hinv
        | unblock_send dst =>
          have h_kernel := unblock_send_kernel_unchanged dst s s' hexec
          unfold CapConfined; simp only [h_kernel]; exact hinv
    frame := by
      intro s s' h hinv _hpre hna
      -- Frame: when step_affects_caps = false, caps table is unchanged
      have ⟨h_caps, _⟩ := step_affects_caps_sound h hna
      unfold CapConfined
      simp only [h_caps]
      exact hinv
  }

/-- Contract compatibility: policy → confinement precondition. -/
theorem confinement_contract_compatible :
    ∀ s, capContract.inv s → policyContract.inv s →
      confinementContract.pre s := by
  intro s hcap hpol
  exact ⟨hcap, hpol⟩

/-! =========== CONTRACT 005: CAPABILITY REVOCATION =========== -/

/--
Capability Revocation Contract (005).

Revoked capabilities cannot be used.

Precondition: CapConfined
- Need confinement to ensure revocation propagates correctly
-/
noncomputable def revocationContract : InterfaceContract State Step :=
  { pre := CapConfined
    inv := CapRevocable
    affects := fun h => step_affects_caps h
    preserve := by
      intro s s' h _hinv _hpre _ha
      -- CapRevocable: revoked caps cannot be used
      -- Uses Revocation.revoked_no_auth theorem
      intro a cap h_not_valid
      exact Revocation.revoked_no_auth s' a cap h_not_valid
    frame := by
      intro s s' h _hinv _hpre _hna
      -- Same structural property
      intro a cap h_not_valid
      exact Revocation.revoked_no_auth s' a cap h_not_valid
  }

/-- Contract compatibility: confinement.inv → revocation.pre. -/
theorem revocation_contract_compatible :
    Contract.compatible confinementContract revocationContract := by
  intro s hconf
  exact hconf

/-! =========== CONTRACT 006: TEMPORAL SAFETY =========== -/

/--
Temporal Safety Contract (006).

Freed resources cannot be accessed (use-after-free prevention).

Precondition: CapRevocable
- Need revocation to prevent accessing freed resources via revoked caps

Note: Our TemporalSafe definition uses freed_set and MetaState.is_live.

REFACTORED per review a11.md:
- Frame proof now properly uses step_affects_ghost_sound to transport invariant
- Not re-proving from scratch, but using ghost unchanged to rewrite
-/
noncomputable def temporalContract : InterfaceContract State Step :=
  { pre := CapRevocable
    inv := TemporalSafe
    affects := fun h => step_affects_ghost h
    preserve := by
      intro s s' h _hinv _hpre _ha
      -- TemporalSafe s' : ∀ addr, addr ∈ s'.freed_set → ¬ is_live s'.ghost addr
      intro addr h_freed
      -- h_freed : addr ∈ s'.ghost.freed_set
      -- use_after_free_prevented directly proves: freed → ¬live
      exact use_after_free_prevented s' addr h_freed
    frame := by
      intro s s' h hinv _hpre hna
      -- PROPER FRAME REASONING: use step_affects_ghost_sound to show ghost unchanged
      -- Then transport TemporalSafe s to TemporalSafe s' via rewrite
      have hghost : s'.ghost = s.ghost := step_affects_ghost_sound h hna
      -- Rewrite TemporalSafe using ghost equality
      intro addr h_freed
      -- h_freed : addr ∈ s'.ghost.freed_set
      -- Rewrite to addr ∈ s.ghost.freed_set
      rw [hghost] at h_freed
      -- Now use hinv : TemporalSafe s
      have h_not_live := hinv addr h_freed
      -- h_not_live : ¬ MetaState.is_live s.ghost addr
      -- Rewrite back to s'.ghost
      simp only [← hghost] at h_not_live
      exact h_not_live
  }

/-- Contract compatibility: revocation.inv → temporal.pre. -/
theorem temporal_contract_compatible :
    Contract.compatible revocationContract temporalContract := by
  intro s hrev
  exact hrev

/-! =========== CONTRACT 007: MESSAGE DELIVERY =========== -/

/--
Message Delivery Contract (007).

Messages can always make progress toward delivery.

This is a LIVENESS property expressed as a safety approximation:
"Mailboxes stay within capacity" - ensures delivery can proceed without overflow.

Precondition: MemoryIsolated
- Need isolation to ensure message integrity during routing

REFACTORED: Real proofs using mailbox capacity axioms.
-/
noncomputable def messageDeliveryContract : InterfaceContract State Step :=
  { pre := MemoryIsolated
    inv := MessageDeliveryPossible
    affects := fun h => step_affects_actors h
    preserve := by
      intro s s' h hinv _hpre ha
      -- MessageDeliveryPossible s' : ∀ aid, mailbox.length ≤ capacity
      -- Case analysis on what step affected actors
      cases h with
      | plugin_internal pid pi hpre hexec =>
        -- Plugin internal doesn't affect actors
        simp only [step_affects_actors] at ha
      | host_call hc a auth hr hparse hpre' hexec =>
        -- IPC host calls (ipc_send, ipc_receive) affect actors
        -- Use host_call_respects_mailbox_capacity axiom
        intro aid
        have h_cap := host_call_respects_mailbox_capacity hc a auth hr s s' hexec
        exact h_cap aid (hinv aid)
      | kernel_internal op hexec =>
        -- Only route_one and unblock_send affect actors
        cases op with
        | time_tick =>
          -- time_tick doesn't affect actors
          simp only [step_affects_actors, kernelOp_affects_actors, kernelOpProfile] at ha
          exact (Bool.false_ne_true ha).elim
        | route_one dst =>
          -- route_one: use route_one_respects_mailbox_capacity axiom
          intro aid
          have h_cap := route_one_respects_mailbox_capacity dst s s' hexec
          exact h_cap aid (hinv aid)
        | workflow_tick wid =>
          -- workflow_tick doesn't affect actors
          simp only [step_affects_actors, kernelOp_affects_actors, kernelOpProfile] at ha
          exact (Bool.false_ne_true ha).elim
        | unblock_send dst =>
          -- unblock_send only clears blockedOn, doesn't change mailbox
          intro aid
          have h_frame := unblock_send_comprehensive_frame dst s s' hexec
          -- Need to show mailbox unchanged
          by_cases heq : aid = dst
          · -- For dst: unblock_send only changes blockedOn
            rw [heq]
            -- Use the constructive definition
            simp only [KernelExecInternal] at hexec
            subst hexec
            -- s' = {s with actors := Function.update s.actors dst newActor}
            -- where newActor = {s.actors dst with blockedOn := none}
            simp only [Function.update, dite_eq_ite, ite_true]
            -- newActor preserves mailbox and capacity
            exact hinv dst
          · -- For other actors: unchanged by frame
            have h_unchanged := h_frame.2.2.1 aid heq
            rw [h_unchanged]
            exact hinv aid
    frame := by
      intro s s' h hinv _hpre hna
      -- When step_affects_actors = false, actors unchanged
      -- For plugin_internal: actors unchanged
      -- For host_call (non-IPC): actors unchanged
      -- For kernel_internal (time_tick, workflow_tick): actors unchanged
      cases h with
      | plugin_internal pid pi hpre hexec =>
        have h_actors := plugin_internal_actors_unchanged pid pi s s' hexec
        intro aid
        rw [h_actors]
        exact hinv aid
      | host_call hc a auth hr hparse hpre' hexec =>
        -- Non-IPC host call: actors unchanged by frame
        simp only [step_affects_actors, is_ipc_action] at hna
        push_neg at hna
        obtain ⟨h_not_send, h_not_recv⟩ := hna
        intro aid
        -- Use the mailbox capacity axiom which is universal
        have h_cap := host_call_respects_mailbox_capacity hc a auth hr s s' hexec
        exact h_cap aid (hinv aid)
      | kernel_internal op hexec =>
        -- Only time_tick and workflow_tick have affects = false
        cases op with
        | time_tick =>
          have h_actors := (time_tick_comprehensive_frame s s' hexec).2.2.1
          intro aid
          rw [h_actors]
          exact hinv aid
        | route_one dst =>
          -- route_one has affects = true (kernelOp_affects_actors = True)
          -- hna : ¬step_affects_actors ... and step_affects_actors = True, contradiction
          have h_affects : step_affects_actors (Step.kernel_internal (.route_one dst) hexec) := by
            simp only [step_affects_actors, kernelOp_affects_actors, kernelOpProfile]
          exact absurd h_affects hna
        | workflow_tick wid =>
          have h_actors := (workflow_tick_comprehensive_frame wid s s' hexec).2.2.1
          intro aid
          rw [h_actors]
          exact hinv aid
        | unblock_send dst =>
          -- unblock_send has affects = true (kernelOp_affects_actors = True)
          have h_affects : step_affects_actors (Step.kernel_internal (.unblock_send dst) hexec) := by
            simp only [step_affects_actors, kernelOp_affects_actors, kernelOpProfile]
          exact absurd h_affects hna
  }

/-- Contract compatibility: mem.inv → messageDelivery.pre. -/
theorem message_delivery_contract_compatible :
    Contract.compatible memContract messageDeliveryContract := by
  intro s hmem
  exact hmem

/-! =========== CONTRACT 008: WORKFLOW TERMINATION =========== -/

/--
Workflow Termination Contract (008).

Workflows can always make progress toward completion.

This is a LIVENESS property expressed as a safety approximation:
"Running workflows have resources for progress" (time, pending, or active nodes).

Precondition: DeadlockFree ∧ AllWorkflowsHaveWork
- DeadlockFree: Need progress guarantee for workflow steps
- AllWorkflowsHaveWork: Running workflows have pending or active nodes
  (required for frame proof - time_tick can't break progress if workflows have work)

REFACTORED: Uses AllWorkflowsHaveWork invariant instead of time_tick axiom.
-/
noncomputable def workflowTerminationContract : InterfaceContract State Step :=
  { pre := fun s => DeadlockFree s ∧ AllWorkflowsHaveWork s
    inv := WorkflowProgressPossible
    affects := fun h => step_affects_workflows h
    preserve := by
      intro s s' h hinv _hpre ha
      -- WorkflowProgressPossible s' : ∀ wid, running → has progress resources
      cases h with
      | plugin_internal pid pi hpre hexec =>
        -- Plugin internal doesn't affect workflows (contradiction with ha)
        simp only [step_affects_workflows] at ha
      | host_call hc a auth hr hparse hpre' hexec =>
        -- Workflow syscalls (workflow_start, workflow_step) affect workflows
        -- Use host_call_respects_workflow_progress axiom
        intro wid h_running
        have h_prog := host_call_respects_workflow_progress hc a auth hr s s' hexec
        exact h_prog wid h_running (hinv wid)
      | kernel_internal op hexec =>
        -- Only workflow_tick affects workflows
        cases op with
        | time_tick =>
          -- time_tick doesn't affect workflows (contradiction with ha)
          simp only [step_affects_workflows, kernelOp_affects_workflows, kernelOpProfile] at ha
          exact (Bool.false_ne_true ha).elim
        | route_one dst =>
          -- route_one doesn't affect workflows (contradiction with ha)
          simp only [step_affects_workflows, kernelOp_affects_workflows, kernelOpProfile] at ha
          exact (Bool.false_ne_true ha).elim
        | workflow_tick wid =>
          -- workflow_tick: use workflow_tick_preserves_progress axiom
          intro wid' h_running
          have h_prog := workflow_tick_preserves_progress wid s s' hexec
          by_cases heq : wid' = wid
          · -- The ticked workflow
            subst heq
            exact h_prog.1 h_running
          · -- Other workflows: use frame part of axiom
            have h_frame := workflow_tick_comprehensive_frame wid s s' hexec
            have h_wf_unchanged := h_frame.2.2.2.2.1 wid' heq
            have h_time := h_frame.2.2.2.2.2.2
            -- Convert h_running from s' to s using frame
            have h_running_s : (s.workflows wid').status = .running := by
              rw [h_wf_unchanged] at h_running; exact h_running
            -- Use the second part of the axiom for other workflows
            exact h_prog.2 wid' heq h_running_s (hinv wid' h_running_s)
        | unblock_send dst =>
          -- unblock_send doesn't affect workflows (contradiction with ha)
          simp only [step_affects_workflows, kernelOp_affects_workflows, kernelOpProfile] at ha
          exact (Bool.false_ne_true ha).elim
    frame := by
      intro s s' h hinv hpre hna
      -- When step_affects_workflows = false, need to show progress preserved
      -- Key case: time_tick changes time but not workflows
      -- hpre contains AllWorkflowsHaveWork which ensures pending > 0 ∨ active > 0
      have h_whw := hpre.2  -- AllWorkflowsHaveWork s
      cases h with
      | plugin_internal pid pi hpre hexec =>
        -- Plugin internal: workflows unchanged
        have h_wf := plugin_internal_workflows_unchanged pid pi s s' hexec
        have h_time := plugin_internal_time_unchanged pid pi s s' hexec
        intro wid h_running
        have h_running_s : (s.workflows wid).status = .running := by
          rw [h_wf] at h_running; exact h_running
        have h_inv := hinv wid h_running_s
        -- Rewrite time and workflows back
        rw [h_wf, h_time]
        exact h_inv
      | host_call hc a auth hr hparse hpre' hexec =>
        -- Non-workflow host call: use the theorem
        intro wid h_running
        have h_prog := host_call_respects_workflow_progress hc a auth hr s s' hexec
        exact h_prog wid h_running (hinv wid)
      | kernel_internal op hexec =>
        -- time_tick, route_one, unblock_send don't affect workflows
        cases op with
        | time_tick =>
          -- time_tick: time increases, workflows unchanged
          -- Use AllWorkflowsHaveWork: running workflows have pending > 0 ∨ active > 0
          intro wid h_running
          have h_wf := (time_tick_comprehensive_frame s s' hexec).2.2.2.2.1
          have h_running_s : (s.workflows wid).status = .running := by
            rw [h_wf] at h_running; exact h_running
          -- AllWorkflowsHaveWork says: running → pending > 0 ∨ active > 0
          have h_has_work : WorkflowHasWork (s.workflows wid) := h_whw wid
          have h_work := h_has_work h_running_s
          -- workflows unchanged, so the same condition holds in s'
          rw [h_wf]
          exact Or.inr h_work
        | route_one dst =>
          -- route_one has affects = false
          have h_wf := (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.1
          have h_time := (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.2.2
          intro wid h_running
          have h_running_s : (s.workflows wid).status = .running := by
            rw [h_wf] at h_running; exact h_running
          have h_inv := hinv wid h_running_s
          rw [h_wf, h_time]
          exact h_inv
        | workflow_tick wid =>
          -- workflow_tick has affects = true, contradiction
          have h_affects : step_affects_workflows (Step.kernel_internal (.workflow_tick wid) hexec) := by
            simp only [step_affects_workflows, kernelOp_affects_workflows, kernelOpProfile]
          exact absurd h_affects hna
        | unblock_send dst =>
          -- unblock_send: workflows and time unchanged
          have h_wf := (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.1
          have h_time := (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.2.2
          intro wid h_running
          have h_running_s : (s.workflows wid).status = .running := by
            rw [h_wf] at h_running; exact h_running
          have h_inv := hinv wid h_running_s
          rw [h_wf, h_time]
          exact h_inv
  }

/-- Contract compatibility: SystemInvariant provides required preconditions. -/
theorem workflow_termination_needs_progress :
    ∀ s, DeadlockFree s ∧ AllWorkflowsHaveWork s → workflowTerminationContract.pre s := fun _ h => h

/-! =========== CONTRACT 011: STEP CONFINEMENT (NONINTERFERENCE) =========== -/

/--
Step Confinement Contract (011).

High-security steps preserve low-equivalence (one-step noninterference).

This is the SAFETY APPROXIMATION of full TINI:
- Full TINI is a hyperproperty over traces
- Step confinement is the single-step building block
- Proven via unwinding conditions in Noninterference.lean

Precondition: MemoryIsolated ∧ CapConfined ∧ PolicySound
- Memory isolation for spatial separation
- Confinement for rights integrity
- Policy for access control
-/
noncomputable def stepConfinementContract : InterfaceContract State Step :=
  { pre := fun s => MemoryIsolated s ∧ CapConfined s ∧ PolicySound s
    inv := StepConfinementHolds
    affects := fun h => step_affects_levels h
    preserve := by
      intro s s' h _hinv _hpre _ha
      -- StepConfinementHolds: ∀ L s'' st, level > L → low_equivalent_left L s' s''
      -- Use step_confinement_holds from Noninterference.lean (universal over all states)
      intro L s'' st h_high
      have h_conf := Noninterference.step_confinement_holds L
      unfold Noninterference.step_confinement at h_conf
      exact h_conf s' s'' st h_high
    frame := by
      intro s s' h _hinv _hpre _hna
      -- Same universal theorem applies
      intro L s'' st h_high
      have h_conf := Noninterference.step_confinement_holds L
      unfold Noninterference.step_confinement at h_conf
      exact h_conf s' s'' st h_high
  }

/-- Contract compatibility for step confinement. -/
theorem step_confinement_contract_compatible :
    ∀ s, MemoryIsolated s → CapConfined s → PolicySound s →
      stepConfinementContract.pre s := by
  intro s hmem hconf hpol
  exact ⟨hmem, hconf, hpol⟩

/-! =========== CONTRACT COLLECTION =========== -/

/-- All safety contracts in dependency order. -/
noncomputable def safetyContracts : List (InterfaceContract State Step) :=
  [ memContract           -- 002: Base (pre = True)
  , capContract           -- 001: pre = MemoryIsolated
  , policyContract        -- 009: pre = CapUnforgeable
  , confinementContract   -- 004: pre = CapUnforgeable ∧ PolicySound
  , revocationContract    -- 005: pre = CapConfined
  , temporalContract      -- 006: pre = CapRevocable
  , stepConfinementContract -- 011: pre = MemoryIsolated ∧ CapConfined ∧ PolicySound
  ]

/-- Liveness approximation contracts. -/
noncomputable def livenessApproxContracts : List (InterfaceContract State Step) :=
  [ messageDeliveryContract      -- 007: pre = MemoryIsolated
  , workflowTerminationContract  -- 008: pre = DeadlockFree
  ]

end Lion
