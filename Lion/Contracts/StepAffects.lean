/-
Lion/Contracts/StepAffects.lean
================================

Step classification predicates for interface contracts.
These predicates determine which steps "affect" which invariants.

Design: REFINED kernel_internal classification.
Each kernel op is classified precisely by what state it touches.
This enables proper frame proofs without "kernel_internal => True" crutch.

Refactored per review a11.md recommendations (Priority 1).
-/

import Lion.State.State
import Lion.Step.Step
import Lion.Step.HostCall
import Lion.Theorems.TemporalSafety

namespace Lion

/-! =========== ACTION CLASSIFICATION =========== -/

/-- Is this a capability-affecting action? -/
def is_cap_action (hf : HostFunctionId) : Prop :=
  hf = .cap_invoke ∨ hf = .cap_delegate ∨ hf = .cap_accept ∨ hf = .cap_revoke

/-- Is this a memory-affecting action? -/
def is_mem_action (hf : HostFunctionId) : Prop :=
  hf = .mem_alloc ∨ hf = .mem_free

/-- Is this a policy-relevant action? -/
def is_policy_action (hf : HostFunctionId) : Prop :=
  hf = .resource_create ∨ hf = .resource_access ∨ hf = .declassify

/-- Is this an IPC action? -/
def is_ipc_action (hf : HostFunctionId) : Prop :=
  hf = .ipc_send ∨ hf = .ipc_receive

/-- Is this a workflow action? -/
def is_workflow_action (hf : HostFunctionId) : Prop :=
  hf = .workflow_start ∨ hf = .workflow_step

/-- Is this the declassify action (affects security levels)? -/
def is_level_action (hf : HostFunctionId) : Prop :=
  hf = .declassify

/-! =========== DECIDABLE INSTANCES =========== -/

instance : DecidablePred is_cap_action := fun hf =>
  decidable_of_iff (hf = .cap_invoke ∨ hf = .cap_delegate ∨ hf = .cap_accept ∨ hf = .cap_revoke)
    (by simp [is_cap_action])

instance : DecidablePred is_mem_action := fun hf =>
  decidable_of_iff (hf = .mem_alloc ∨ hf = .mem_free)
    (by simp [is_mem_action])

instance : DecidablePred is_policy_action := fun hf =>
  decidable_of_iff (hf = .resource_create ∨ hf = .resource_access ∨ hf = .declassify)
    (by simp [is_policy_action])

instance : DecidablePred is_ipc_action := fun hf =>
  decidable_of_iff (hf = .ipc_send ∨ hf = .ipc_receive)
    (by simp [is_ipc_action])

instance : DecidablePred is_workflow_action := fun hf =>
  decidable_of_iff (hf = .workflow_start ∨ hf = .workflow_step)
    (by simp [is_workflow_action])

instance : DecidablePred is_level_action := fun hf =>
  decidable_of_iff (hf = .declassify)
    (by simp [is_level_action])

/-! =========== KERNEL OP PROFILE (CONSOLIDATED) =========== -/

/--
Profile capturing all effects of a kernel operation.
CONSOLIDATION: Single source of truth for kernel op properties.
When adding a new KernelOp variant, only update `kernelOpProfile`.
-/
structure KernelOpProfile where
  caps      : Bool := false  -- Affects capabilities
  mem       : Bool := false  -- Affects plugin memory
  actors    : Bool := false  -- Affects actors (mailbox, blocked)
  workflows : Bool := false  -- Affects workflows
  ghost     : Bool := false  -- Affects ghost state
  levels    : Bool := false  -- Affects security levels
  policy    : Bool := false  -- Affects policy state
  time      : Bool := false  -- Affects time
deriving DecidableEq, Repr

/--
Get the profile for a kernel op.
SINGLE CASE ANALYSIS: All other functions project from this.
-/
@[simp] def kernelOpProfile : KernelOp → KernelOpProfile
  | .time_tick       => { time := true }
  | .route_one _     => { actors := true }  -- Moves message to mailbox
  | .workflow_tick _ => { workflows := true }  -- Advances workflow state
  | .unblock_send _  => { actors := true }  -- Clears blockedOn

/-! =========== KERNEL OP CLASSIFICATION (PROJECTIONS) =========== -/

/-- Which kernel ops affect capabilities? (None - caps are only modified by host calls) -/
def kernelOp_affects_caps (op : KernelOp) : Prop := (kernelOpProfile op).caps

/-- Which kernel ops affect plugin memory? (None - plugins are only modified by plugin/host steps) -/
def kernelOp_affects_mem (op : KernelOp) : Prop := (kernelOpProfile op).mem

/-- Which kernel ops affect actors? -/
def kernelOp_affects_actors (op : KernelOp) : Prop := (kernelOpProfile op).actors

/-- Which kernel ops affect workflows? -/
def kernelOp_affects_workflows (op : KernelOp) : Prop := (kernelOpProfile op).workflows

/-- Which kernel ops affect ghost state? (None - ghost is only modified by mem_alloc/mem_free) -/
def kernelOp_affects_ghost (op : KernelOp) : Prop := (kernelOpProfile op).ghost

/-- Which kernel ops affect security levels? (None - only declassify can change levels) -/
def kernelOp_affects_levels (op : KernelOp) : Prop := (kernelOpProfile op).levels

/-- Which kernel ops affect policy state? (None - policy is opaque kernel state) -/
def kernelOp_affects_policy (op : KernelOp) : Prop := (kernelOpProfile op).policy

/-- Which kernel ops affect time? (Only time_tick) -/
def kernelOp_affects_time (op : KernelOp) : Prop := (kernelOpProfile op).time

/-! =========== STEP AFFECTS PREDICATES =========== -/

/--
Capability footprint may be touched by cap syscalls.
REFINED: kernel_internal uses kernelOp_affects_caps (all False).
-/
def step_affects_caps {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => is_cap_action hc.function
  | .kernel_internal op _ => kernelOp_affects_caps op

/--
Memory footprint may be touched by mem syscalls and plugin internal steps.
REFINED: kernel_internal uses kernelOp_affects_mem (all False).
-/
def step_affects_mem {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => True   -- Plugin internal can read/write memory
  | .host_call hc _ _ _ _ _ _ => is_mem_action hc.function
  | .kernel_internal op _ => kernelOp_affects_mem op

/--
Policy footprint may be touched by policy-relevant syscalls.
REFINED: kernel_internal uses kernelOp_affects_policy (all False).
-/
def step_affects_policy {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => is_policy_action hc.function
  | .kernel_internal op _ => kernelOp_affects_policy op

/--
Ghost state may be touched by mem_alloc or mem_free.
- mem_alloc: changes resources map
- mem_free: changes freed_set and resources map
REFINED: kernel_internal uses kernelOp_affects_ghost (all False).
-/
def step_affects_ghost {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => hc.function = .mem_free ∨ hc.function = .mem_alloc
  | .kernel_internal op _ => kernelOp_affects_ghost op

/--
Security levels may be touched by declassify.
REFINED: kernel_internal uses kernelOp_affects_levels (all False).
-/
def step_affects_levels {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => is_level_action hc.function
  | .kernel_internal op _ => kernelOp_affects_levels op

/--
Actor state (mailbox, pending, blocked) may be touched by IPC and kernel ops.
REFINED: kernel_internal uses kernelOp_affects_actors.
-/
def step_affects_actors {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => is_ipc_action hc.function
  | .kernel_internal op _ => kernelOp_affects_actors op

/--
Workflow state may be touched by workflow syscalls and kernel_internal.workflow_tick.
REFINED: kernel_internal uses kernelOp_affects_workflows.
-/
def step_affects_workflows {s s' : State} : Step s s' → Prop
  | .plugin_internal _ _ _ _ => False
  | .host_call hc _ _ _ _ _ _ => is_workflow_action hc.function
  | .kernel_internal op _ => kernelOp_affects_workflows op

/-! =========== SIMP LEMMAS =========== -/

@[simp] lemma plugin_internal_not_affects_caps {s s' pid pi hpre hexec} :
    step_affects_caps (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

@[simp] lemma plugin_internal_affects_mem {s s' pid pi hpre hexec} :
    step_affects_mem (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = True := rfl

@[simp] lemma plugin_internal_not_affects_policy {s s' pid pi hpre hexec} :
    step_affects_policy (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

@[simp] lemma plugin_internal_not_affects_ghost {s s' pid pi hpre hexec} :
    step_affects_ghost (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

@[simp] lemma plugin_internal_not_affects_levels {s s' pid pi hpre hexec} :
    step_affects_levels (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

@[simp] lemma plugin_internal_not_affects_actors {s s' pid pi hpre hexec} :
    step_affects_actors (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

@[simp] lemma plugin_internal_not_affects_workflows {s s' pid pi hpre hexec} :
    step_affects_workflows (Step.plugin_internal (s := s) (s' := s') pid pi hpre hexec) = False := rfl

/-! =========== KERNEL_INTERNAL SIMP LEMMAS =========== -/

-- All kernel ops have False for caps, mem, ghost, levels, policy
@[simp] lemma kernel_internal_not_affects_caps {s s' op hexec} :
    step_affects_caps (Step.kernel_internal (s := s) (s' := s') op hexec) = False := by
  unfold step_affects_caps kernelOp_affects_caps
  cases op <;> simp

@[simp] lemma kernel_internal_not_affects_mem {s s' op hexec} :
    step_affects_mem (Step.kernel_internal (s := s) (s' := s') op hexec) = False := by
  unfold step_affects_mem kernelOp_affects_mem
  cases op <;> simp

@[simp] lemma kernel_internal_not_affects_ghost {s s' op hexec} :
    step_affects_ghost (Step.kernel_internal (s := s) (s' := s') op hexec) = False := by
  unfold step_affects_ghost kernelOp_affects_ghost
  cases op <;> simp

@[simp] lemma kernel_internal_not_affects_levels {s s' op hexec} :
    step_affects_levels (Step.kernel_internal (s := s) (s' := s') op hexec) = False := by
  unfold step_affects_levels kernelOp_affects_levels
  cases op <;> simp

@[simp] lemma kernel_internal_not_affects_policy {s s' op hexec} :
    step_affects_policy (Step.kernel_internal (s := s) (s' := s') op hexec) = False := by
  unfold step_affects_policy kernelOp_affects_policy
  cases op <;> simp

/-! =========== FRAME THEOREMS =========== -/

/--
Theorem: Host calls that don't affect caps preserve capability table.
Derived from host_call_non_cap_kernel_unchanged (non-cap host calls preserve full kernel).
-/
theorem host_call_caps_frame {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hexec : KernelExecHost hc a auth hr s s')
    (h1 : hc.function ≠ .cap_invoke)
    (h2 : hc.function ≠ .cap_delegate)
    (h3 : hc.function ≠ .cap_accept)
    (h4 : hc.function ≠ .cap_revoke) :
    s'.kernel.revocation.caps = s.kernel.revocation.caps ∧
    s'.kernel.hmacKey = s.kernel.hmacKey := by
  have h_kernel := host_call_non_cap_kernel_unchanged hc a auth hr s s' hexec h1 h2 h3 h4
  constructor <;> simp [h_kernel]

/-! =========== SOUNDNESS THEOREMS =========== -/

/--
Soundness: if step_affects_ghost = false, then ghost state is unchanged.

This is the key theorem enabling frame proofs for temporal safety.
-/
theorem step_affects_ghost_sound {s s' : State} (st : Step s s')
    (h_not_affects : ¬ step_affects_ghost st) :
    s'.ghost = s.ghost := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal never affects ghost
      exact plugin_internal_ghost_unchanged pid pi s s' hexec
  | host_call hc a auth hr hp hpre hexec =>
      -- step_affects_ghost = (mem_free ∨ mem_alloc)
      -- h_not_affects : ¬ (mem_free ∨ mem_alloc)
      simp only [step_affects_ghost] at h_not_affects
      push_neg at h_not_affects
      obtain ⟨h_not_free, h_not_alloc⟩ := h_not_affects
      have hspec := host_call_ghost_spec (hc := hc) (a := a) (auth := auth) (hr := hr) hexec
      -- Neither mem_free nor mem_alloc: ghost unchanged
      exact hspec.2.2 h_not_free h_not_alloc
  | kernel_internal op hexec =>
      -- REFINED: kernelOp_affects_ghost is always False for all ops
      -- So kernel ops never affect ghost, use comprehensive frame theorems
      cases op with
      | time_tick =>
        exact (time_tick_comprehensive_frame s s' hexec).2.2.2.2.2.1
      | route_one dst =>
        exact (route_one_comprehensive_frame dst s s' hexec).2.2.2.2.2.1
      | workflow_tick wid =>
        exact (workflow_tick_comprehensive_frame wid s s' hexec).2.2.2.2.2.1
      | unblock_send dst =>
        exact (unblock_send_comprehensive_frame dst s s' hexec).2.2.2.2.2.2.1

/--
Soundness: if step_affects_caps = false, then capability table is unchanged.
-/
theorem step_affects_caps_sound {s s' : State} (st : Step s s')
    (h_not_affects : ¬ step_affects_caps st) :
    s'.kernel.revocation.caps = s.kernel.revocation.caps ∧
    s'.kernel.hmacKey = s.kernel.hmacKey := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal: use comprehensive frame
      have h := plugin_internal_kernel_unchanged pid pi s s' hexec
      exact ⟨by rw [h], by rw [h]⟩
  | host_call hc a auth hr hp hpre hexec =>
      -- step_affects_caps = is_cap_action
      -- h_not_affects means NOT (cap_invoke ∨ cap_delegate ∨ cap_accept ∨ cap_revoke)
      simp only [step_affects_caps, is_cap_action] at h_not_affects
      push_neg at h_not_affects
      obtain ⟨h1, h2, h3, h4⟩ := h_not_affects
      -- Non-cap syscalls don't change caps (by host_call frame axiom)
      have h := host_call_caps_frame hc a auth hr hexec h1 h2 h3 h4
      exact h
  | kernel_internal op hexec =>
      -- REFINED: kernelOp_affects_caps is always False for all ops
      -- So kernel ops never affect caps, use comprehensive frame theorems
      cases op with
      | time_tick =>
        have h := (time_tick_comprehensive_frame s s' hexec).1
        exact ⟨by rw [h], by rw [h]⟩
      | route_one dst =>
        have h := (route_one_comprehensive_frame dst s s' hexec).1
        exact ⟨by rw [h], by rw [h]⟩
      | workflow_tick wid =>
        have h := (workflow_tick_comprehensive_frame wid s s' hexec).1
        exact ⟨by rw [h], by rw [h]⟩
      | unblock_send dst =>
        have h := (unblock_send_comprehensive_frame dst s s' hexec).1
        exact ⟨by rw [h], by rw [h]⟩

end Lion
