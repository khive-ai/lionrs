/-
Lion/State/Workflow.lean
=========================

Workflow DAG and termination (Theorem 008).
-/

import Lion.Core.Identifiers
import Lion.Core.CountPLemmas
import Lion.Core.CountPGeneral

namespace Lion

/-! =========== WORKFLOWS (008) =========== -/

/-- Workflow execution status -/
inductive WorkflowStatus where
  | running
  | success
  | failure
deriving DecidableEq, Repr

/-- Node execution state -/
inductive NodeState where
  | pending
  | active
  | completed
  | failed
deriving DecidableEq, Repr

/-- DAG edge: (from, to) means 'from' must complete before 'to' starts -/
structure Edge where
  from_ : Nat
  to_ : Nat
deriving DecidableEq, Repr

/-- Workflow definition (static DAG structure) -/
structure WorkflowDef where
  nodes : List Nat
  edges : List Edge
deriving Repr

namespace WorkflowDef

/-- Check if node has no incoming edges (ready to start) -/
def is_source (wf : WorkflowDef) (n : Nat) : Bool :=
  wf.edges.all (·.to_ ≠ n)

/-- Check if node has no outgoing edges (terminal) -/
def is_sink (wf : WorkflowDef) (n : Nat) : Bool :=
  wf.edges.all (·.from_ ≠ n)

/-- Get dependencies of a node -/
def dependencies (wf : WorkflowDef) (n : Nat) : List Nat :=
  wf.edges.filterMap (fun e => if e.to_ = n then some e.from_ else none)

/-- Get dependents of a node -/
def dependents (wf : WorkflowDef) (n : Nat) : List Nat :=
  wf.edges.filterMap (fun e => if e.from_ = n then some e.to_ else none)

end WorkflowDef

/-- Workflow instance (runtime state) -/
structure WorkflowInstance where
  definition  : WorkflowDef
  status      : WorkflowStatus
  node_states : Nat → NodeState
  timeout_at  : Time
  retries     : Nat → Nat

namespace WorkflowInstance

/-- Bool predicate: is node in pending state? -/
def is_pending (wi : WorkflowInstance) (n : Nat) : Bool :=
  decide (wi.node_states n = .pending)

/-- Bool predicate: is node in active state? -/
def is_active (wi : WorkflowInstance) (n : Nat) : Bool :=
  decide (wi.node_states n = .active)

/-- Count pending nodes -/
def pending_count (wi : WorkflowInstance) : Nat :=
  wi.definition.nodes.countP wi.is_pending

/-- Count active nodes -/
def active_count (wi : WorkflowInstance) : Nat :=
  wi.definition.nodes.countP wi.is_active

/-- All nodes completed or failed -/
def is_terminal (wi : WorkflowInstance) : Bool :=
  wi.definition.nodes.all (fun n =>
    wi.node_states n = .completed ∨ wi.node_states n = .failed)

/-- At least one node failed -/
def has_failure (wi : WorkflowInstance) : Bool :=
  wi.definition.nodes.any (fun n => wi.node_states n = .failed)

end WorkflowInstance

/-! =========== TERMINATION MEASURE (008) =========== -/

/--
**Concrete Termination Measure**

A natural number measure that decreases on each workflow step.
Uses lexicographic ordering on (time_remaining, pending_nodes, active_nodes, retries_remaining).

Key insight: Every productive workflow step MUST either:
1. Advance time (decreasing time_remaining), OR
2. Complete a pending node (decreasing pending_count), OR
3. Finish an active node (decreasing active_count), OR
4. Consume a retry (decreasing total retries remaining)

If none of these decrease, the workflow is stuck (timeout/failure).

**Weight Analysis for Strict Decrease**:
- tick:          time_left↓ by 1                                    → -1 net
- start_node:    pending↓(-1000), active↑(+100)                     → -900 net
- complete_node: active↓(-100)                                      → -100 net
- fail_node:     active↓(-100)                                      → -100 net
- retry_node:    pending↑(+1000), active↓(-100), retries↓(-1000)   → -100 net
- timeout:       terminal state (no further steps)

The weight on retries_remaining (×1000) MUST exceed the net gain from
pending↑ - active↓ = 1000 - 100 = 900 to ensure retry_node decreases measure.
-/
def workflow_measure (now : Time) (wi : WorkflowInstance) : Nat :=
  let time_left := if now < wi.timeout_at then wi.timeout_at - now else 0
  let pending := wi.pending_count
  let active := wi.active_count
  let retries_remaining := wi.definition.nodes.foldl (fun acc n => acc + wi.retries n) 0
  -- Weighted sum ensures strict decrease on any component decrease
  -- Weights: time (×1), pending (×1000), active (×100), retries_remaining (×1000)
  -- retry_node: pending↑(+1000), active↓(-100), retries↓(-1000) = -100 net decrease
  time_left + pending * 1000 + active * 100 + retries_remaining * 1000

/-! =========== WORKFLOW STEP RELATION =========== -/

/--
**Workflow Step Relation**

Concrete definition of what constitutes a workflow transition.
Each case specifies exactly how state changes, enabling proofs.
-/
inductive WorkflowStep : Time → WorkflowInstance → Time → WorkflowInstance → Prop where
  /-- Time tick: clock advances by 1, nothing else changes -/
  | tick (now : Time) (wi : WorkflowInstance)
      (h_not_timeout : now < wi.timeout_at) :
      WorkflowStep now wi (now + 1) wi

  /-- Start node: pending → active (dependencies satisfied) -/
  | start_node (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
      (h_pending : wi.node_states n = .pending)
      (h_deps_done : ∀ d ∈ wi.definition.dependencies n,
        wi.node_states d = .completed)
      (h_result : wi' = { wi with
        node_states := fun x => if x = n then .active else wi.node_states x }) :
      WorkflowStep now wi now wi'

  /-- Complete node: active → completed -/
  | complete_node (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
      (h_active : wi.node_states n = .active)
      (h_result : wi' = { wi with
        node_states := fun x => if x = n then .completed else wi.node_states x }) :
      WorkflowStep now wi now wi'

  /-- Fail node: active → failed (no retries left) -/
  | fail_node (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
      (h_active : wi.node_states n = .active)
      (h_no_retry : wi.retries n = 0)
      (h_result : wi' = { wi with
        node_states := fun x => if x = n then .failed else wi.node_states x }) :
      WorkflowStep now wi now wi'

  /-- Retry node: active → pending (consume a retry) -/
  | retry_node (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
      (h_active : wi.node_states n = .active)
      (h_has_retry : wi.retries n > 0)
      (h_result : wi' = { wi with
        node_states := fun x => if x = n then .pending else wi.node_states x,
        retries := fun x => if x = n then wi.retries n - 1 else wi.retries x }) :
      WorkflowStep now wi now wi'

  /-- Timeout: clock reaches timeout_at, workflow fails -/
  | timeout (now : Time) (wi wi' : WorkflowInstance)
      (h_timeout : now ≥ wi.timeout_at)
      (h_result : wi' = { wi with status := .failure }) :
      WorkflowStep now wi now wi'

/-! =========== MEASURE DECREASE PROOFS =========== -/

/--
**Theorem (Tick Decreases Measure)**:
Time advancing strictly decreases time_left component.

The proof follows from:
1. When now < timeout_at, time_left = timeout_at - now > 0
2. After tick, time_left' = timeout_at - (now+1) < timeout_at - now
3. Other components (pending, active, retry) are unchanged
-/
theorem tick_decreases_measure (now : Time) (wi : WorkflowInstance)
    (h_before : now < wi.timeout_at) :
    workflow_measure (now + 1) wi < workflow_measure now wi := by
  -- Fully reduce workflow_measure to eliminate let bindings
  simp only [workflow_measure, WorkflowInstance.pending_count, WorkflowInstance.active_count]

  -- Since h_before: now < timeout, the old time_left = timeout - now
  simp only [h_before, ite_true]

  -- Case split on now + 1 < timeout
  by_cases h : now + 1 < wi.timeout_at
  · -- Case: now + 1 < timeout
    simp only [h, ite_true]
    -- Goal: (timeout-(now+1)) + rest < (timeout-now) + rest
    -- First prove the time component inequality
    have h1 : now + 1 ≤ wi.timeout_at := Nat.le_of_lt h
    have h_time : wi.timeout_at - (now + 1) < wi.timeout_at - now := Nat.sub_lt_sub_left h1 (Nat.lt_succ_self now)
    exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_right h_time _) _) _
  · -- Case: now + 1 >= timeout
    simp only [h, ite_false]
    -- Goal: 0 + rest < (timeout-now) + rest
    have h_pos : 0 < wi.timeout_at - now := Nat.sub_pos_of_lt h_before
    exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_right h_pos _) _) _

/-!
## Measure Decrease Lemmas

These lemmas prove that each workflow step case decreases the termination measure.
The proofs require counting properties on lists (countP behavior under updates).

We state these as axioms because:
1. The semantic claims are clear and correct by construction
2. Full proofs require extensive List.countP lemmas
3. The main theorem (workflow_step_decreases_measure) composes these

Key insight: pending*1000 + active*100 + retries_remaining*1000 ensures strict decrease:
- start_node:    pending↓(-1000), active↑(+100)                    → -900 net
- complete_node: active↓(-100)                                     → -100 net
- fail_node:     active↓(-100)                                     → -100 net
- retry_node:    pending↑(+1000), active↓(-100), retries↓(-1000)  → -100 net

The weight 1000 on retries_remaining is critical: it must exceed the +900 gain
from (pending↑ - active↓) to ensure retry_node decreases the measure.
-/

/--
**Theorem (Start Node Decreases Measure)**:
Moving pending → active decreases measure.
Net: -1000 (pending) + 100 (active) = -900 (minimum, more if n appears multiple times).

NO NODUP REQUIRED. Uses CountPGeneral lemmas.
-/
theorem start_node_decreases_measure (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
    (h_pending : wi.node_states n = .pending)
    (h_in : n ∈ wi.definition.nodes)
    (h_result : wi' = { wi with node_states := fun x => if x = n then .active else wi.node_states x }) :
    workflow_measure now wi' < workflow_measure now wi := by
  -- Unfold workflow_measure to work with components
  simp only [workflow_measure]
  -- Key facts about wi':
  -- 1. wi'.pending_count < wi.pending_count (n was pending, now not)
  -- 2. wi'.active_count > wi.active_count (n was not active, now is)
  -- 3. Other components unchanged

  -- Establish time_left unchanged
  have h_time_eq : (if now < wi'.timeout_at then wi'.timeout_at - now else 0) =
                   (if now < wi.timeout_at then wi.timeout_at - now else 0) := by
    simp only [h_result]

  -- Establish retries_remaining unchanged
  have h_retries_eq : wi'.definition.nodes.foldl (fun acc n => acc + wi'.retries n) 0 =
                      wi.definition.nodes.foldl (fun acc n => acc + wi.retries n) 0 := by
    simp only [h_result]

  -- Prove pending_count decreases
  have h_pend_dec : wi'.pending_count < wi.pending_count := by
    simp only [WorkflowInstance.pending_count, h_result]
    -- Old predicate: wi.is_pending = fun x => decide (wi.node_states x = .pending)
    -- New predicate: wi'.is_pending = fun x => decide ((if x = n then .active else wi.node_states x) = .pending)
    -- For n: old = true (h_pending), new = false (active ≠ pending)
    -- For x ≠ n: unchanged
    apply countP_update_decreases_general wi.definition.nodes n wi.is_pending
      (fun x => decide ((if x = n then NodeState.active else wi.node_states x) = NodeState.pending))
      h_in
    · -- h_old: wi.is_pending n = true
      simp only [WorkflowInstance.is_pending, h_pending, decide_eq_true_eq]
    · -- h_new: new predicate on n = false
      simp only [↓reduceIte, decide_eq_false_iff_not]
      decide
    · -- h_unchanged: for x ≠ n, predicates equal
      intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_pending]

  -- Prove active_count increases
  have h_act_inc : wi'.active_count > wi.active_count := by
    simp only [WorkflowInstance.active_count, h_result]
    apply countP_update_increases_general wi.definition.nodes n wi.is_active
      (fun x => decide ((if x = n then NodeState.active else wi.node_states x) = NodeState.active))
      h_in
    · -- h_old: wi.is_active n = false (since n was pending)
      simp only [WorkflowInstance.is_active, h_pending, decide_eq_false_iff_not]
      decide
    · -- h_new: new predicate on n = true
      simp only [↓reduceIte, decide_eq_true_eq]
    · -- h_unchanged
      intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_active]

  -- Now show measure decreases
  rw [h_time_eq, h_retries_eq]
  -- Goal: time + pending' * 1000 + active' * 100 + retries < time + pending * 1000 + active * 100 + retries
  -- Simplifies to: pending' * 1000 + active' * 100 < pending * 1000 + active * 100

  -- Prove balance: pending_drop = active_rise (both equal count(n))
  have h_balance : wi.pending_count - wi'.pending_count = wi'.active_count - wi.active_count := by
    -- Use countP_symmetric_change: both changes equal List.count n nodes
    simp only [WorkflowInstance.pending_count, WorkflowInstance.active_count, h_result]
    -- Define the old and new predicates
    let old_pend := wi.is_pending
    let new_pend := fun x => decide ((if x = n then NodeState.active else wi.node_states x) = NodeState.pending)
    let old_act := wi.is_active
    let new_act := fun x => decide ((if x = n then NodeState.active else wi.node_states x) = NodeState.active)
    -- Apply countP_symmetric_change
    apply countP_symmetric_change wi.definition.nodes n old_pend new_pend old_act new_act
    · -- h_f_old_a: old_pend n = true (n was pending)
      simp only [old_pend, WorkflowInstance.is_pending, h_pending, decide_eq_true_eq]
    · -- h_g_new_a: new_pend n = false (n is now active, not pending)
      simp only [new_pend, ↓reduceIte, decide_eq_false_iff_not]
      decide
    · -- h_f_other_a: old_act n = false (n was pending, not active)
      simp only [old_act, WorkflowInstance.is_active, h_pending, decide_eq_false_iff_not]
      decide
    · -- h_g_other_a: new_act n = true (n is now active)
      simp only [new_act, ↓reduceIte, decide_eq_true_eq]
    · -- h_f_unchanged: for x ≠ n, pending predicate unchanged
      intro x _ hne
      simp only [new_pend, old_pend, hne, ↓reduceIte, WorkflowInstance.is_pending]
    · -- h_g_unchanged: for x ≠ n, active predicate unchanged
      intro x _ hne
      simp only [new_act, old_act, hne, ↓reduceIte, WorkflowInstance.is_active]

  -- Now apply arithmetic: pending_drop = active_rise, so pending * 1000 - active * 100 decreases
  -- Using h_balance: pending_drop = active_rise
  -- Net change = -drop * 1000 + rise * 100 = -drop * 1000 + drop * 100 = -drop * 900 < 0
  have h_drop_pos : wi.pending_count - wi'.pending_count ≥ 1 := Nat.sub_pos_of_lt h_pend_dec
  -- From h_pend_dec: wi'.pending_count < wi.pending_count
  -- Goal: pending' * 1000 + active' * 100 < pending * 1000 + active * 100
  omega

/--
**Theorem (Complete Node Decreases Measure)**:
Moving active → completed decreases measure by at least 100.

Proof: Only active_count decreases; pending_count unchanged.
NO NODUP REQUIRED.
-/
theorem complete_node_decreases_measure (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
    (h_active : wi.node_states n = .active)
    (h_in : n ∈ wi.definition.nodes)
    (h_result : wi' = { wi with node_states := fun x => if x = n then .completed else wi.node_states x }) :
    workflow_measure now wi' < workflow_measure now wi := by
  simp only [workflow_measure]

  -- time_left unchanged
  have h_time_eq : (if now < wi'.timeout_at then wi'.timeout_at - now else 0) =
                   (if now < wi.timeout_at then wi.timeout_at - now else 0) := by
    simp only [h_result]

  -- retries unchanged
  have h_retries_eq : wi'.definition.nodes.foldl (fun acc m => acc + wi'.retries m) 0 =
                      wi.definition.nodes.foldl (fun acc m => acc + wi.retries m) 0 := by
    simp only [h_result]

  -- pending_count unchanged (n was active, not pending)
  have h_pend_eq : wi'.pending_count = wi.pending_count := by
    simp only [WorkflowInstance.pending_count, h_result]
    apply countP_update_preserved
    intro x _
    simp only [WorkflowInstance.is_pending]
    by_cases hx : x = n
    · -- x = n was active, so not pending; completed is also not pending
      subst hx
      simp only [↓reduceIte]
      have h_not_pend : wi.node_states x ≠ NodeState.pending := by
        rw [h_active]; decide
      have h_new_not_pend : NodeState.completed ≠ NodeState.pending := by decide
      simp only [h_not_pend, h_new_not_pend]
    · simp only [hx, ↓reduceIte]

  -- active_count decreases
  have h_act_dec : wi'.active_count < wi.active_count := by
    simp only [WorkflowInstance.active_count, h_result]
    apply countP_update_decreases_general wi.definition.nodes n wi.is_active
      (fun x => decide ((if x = n then NodeState.completed else wi.node_states x) = NodeState.active))
      h_in
    · simp only [WorkflowInstance.is_active, h_active, decide_eq_true_eq]
    · simp only [↓reduceIte, decide_eq_false_iff_not]; decide
    · intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_active]

  -- Measure decreases because active_count decreases and others unchanged
  rw [h_time_eq, h_retries_eq, h_pend_eq]
  have : wi'.active_count * 100 < wi.active_count * 100 := by
    exact Nat.mul_lt_mul_of_pos_right h_act_dec (by decide : 0 < 100)
  omega

/--
**Theorem (Fail Node Decreases Measure)**:
Moving active → failed decreases measure by at least 100.

Proof: Identical to complete_node - only active_count decreases.
NO NODUP REQUIRED.
-/
theorem fail_node_decreases_measure (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
    (h_active : wi.node_states n = .active)
    (h_in : n ∈ wi.definition.nodes)
    (h_result : wi' = { wi with node_states := fun x => if x = n then .failed else wi.node_states x }) :
    workflow_measure now wi' < workflow_measure now wi := by
  simp only [workflow_measure]

  -- time_left unchanged
  have h_time_eq : (if now < wi'.timeout_at then wi'.timeout_at - now else 0) =
                   (if now < wi.timeout_at then wi.timeout_at - now else 0) := by
    simp only [h_result]

  -- retries unchanged
  have h_retries_eq : wi'.definition.nodes.foldl (fun acc m => acc + wi'.retries m) 0 =
                      wi.definition.nodes.foldl (fun acc m => acc + wi.retries m) 0 := by
    simp only [h_result]

  -- pending_count unchanged (n was active, not pending)
  have h_pend_eq : wi'.pending_count = wi.pending_count := by
    simp only [WorkflowInstance.pending_count, h_result]
    apply countP_update_preserved
    intro x _
    simp only [WorkflowInstance.is_pending]
    by_cases hx : x = n
    · -- x = n was active, so not pending; failed is also not pending
      subst hx
      simp only [↓reduceIte]
      have h_not_pend : wi.node_states x ≠ NodeState.pending := by
        rw [h_active]; decide
      have h_new_not_pend : NodeState.failed ≠ NodeState.pending := by decide
      simp only [h_not_pend, h_new_not_pend]
    · simp only [hx, ↓reduceIte]

  -- active_count decreases
  have h_act_dec : wi'.active_count < wi.active_count := by
    simp only [WorkflowInstance.active_count, h_result]
    apply countP_update_decreases_general wi.definition.nodes n wi.is_active
      (fun x => decide ((if x = n then NodeState.failed else wi.node_states x) = NodeState.active))
      h_in
    · simp only [WorkflowInstance.is_active, h_active, decide_eq_true_eq]
    · simp only [↓reduceIte, decide_eq_false_iff_not]; decide
    · intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_active]

  -- Measure decreases because active_count decreases and others unchanged
  rw [h_time_eq, h_retries_eq, h_pend_eq]
  have : wi'.active_count * 100 < wi.active_count * 100 := by
    exact Nat.mul_lt_mul_of_pos_right h_act_dec (by decide : 0 < 100)
  omega

/--
**Theorem (Retry Decreases Measure)**:
Consuming a retry decreases measure.

Net change analysis:
- active→pending: pending↑(+1000), active↓(-100) = +900
- retries_remaining↓ by at least 1: -1 × 1000 = -1000
- Total: +900 - 1000 = -100 net decrease (at minimum)

The weight 1000 on retries_remaining ensures strict decrease despite state change.

Proof uses foldl_add_strict_decrease_of_single from CountPGeneral.
NO NODUP REQUIRED - if n appears multiple times, retries decreases by more.
-/
theorem retry_decreases_measure (now : Time) (wi wi' : WorkflowInstance) (n : Nat)
    (h_active : wi.node_states n = .active)
    (h_has_retry : wi.retries n > 0)
    (h_in : n ∈ wi.definition.nodes)
    (h_result : wi' = { wi with
      node_states := fun x => if x = n then .pending else wi.node_states x,
      retries := fun x => if x = n then wi.retries n - 1 else wi.retries x }) :
    workflow_measure now wi' < workflow_measure now wi := by
  simp only [workflow_measure]

  -- time_left unchanged
  have h_time_eq : (if now < wi'.timeout_at then wi'.timeout_at - now else 0) =
                   (if now < wi.timeout_at then wi.timeout_at - now else 0) := by
    simp only [h_result]

  -- pending_count increases (n transitions active → pending)
  have h_pend_inc : wi'.pending_count > wi.pending_count := by
    simp only [WorkflowInstance.pending_count, h_result]
    apply countP_update_increases_general wi.definition.nodes n wi.is_pending
      (fun x => decide ((if x = n then NodeState.pending else wi.node_states x) = NodeState.pending))
      h_in
    · -- h_old: wi.is_pending n = false (n was active, not pending)
      simp only [WorkflowInstance.is_pending, h_active, decide_eq_false_iff_not]
      decide
    · -- h_new: new predicate on n = true (n is now pending)
      simp only [↓reduceIte, decide_eq_true_eq]
    · -- h_unchanged: for x ≠ n, predicates equal
      intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_pending]

  -- active_count decreases (n transitions active → pending)
  have h_act_dec : wi'.active_count < wi.active_count := by
    simp only [WorkflowInstance.active_count, h_result]
    apply countP_update_decreases_general wi.definition.nodes n wi.is_active
      (fun x => decide ((if x = n then NodeState.pending else wi.node_states x) = NodeState.active))
      h_in
    · -- h_old: wi.is_active n = true (n was active)
      simp only [WorkflowInstance.is_active, h_active, decide_eq_true_eq]
    · -- h_new: new predicate on n = false (pending ≠ active)
      simp only [↓reduceIte, decide_eq_false_iff_not]
      decide
    · -- h_unchanged: for x ≠ n, predicates equal
      intro x _ hne
      simp only [hne, ↓reduceIte, WorkflowInstance.is_active]

  -- Key insight: all three changes equal count(n)
  -- pending_rise = active_drop = retries_drop = count(n)
  -- Net: count(n) * 1000 - count(n) * 100 - count(n) * 1000 = count(n) * (-100) < 0

  -- Establish pending_rise = count(n) using countP_change_eq_count
  have h_pend_change : wi'.pending_count = wi.pending_count + wi.definition.nodes.count n := by
    simp only [WorkflowInstance.pending_count, h_result]
    -- new_pend n = true, old_pend n = false
    -- countP new_pend = countP old_pend + count n
    have h := countP_change_eq_count wi.definition.nodes n
      (fun x => decide ((if x = n then NodeState.pending else wi.node_states x) = NodeState.pending))
      wi.is_pending
    apply h
    · -- h_old: new_pend n = true
      simp only [↓reduceIte, decide_eq_true_eq]
    · -- h_new: old_pend n = false (was active)
      simp only [WorkflowInstance.is_pending, h_active, decide_eq_false_iff_not]
      decide
    · -- h_unchanged
      intro x _ hne
      simp only [WorkflowInstance.is_pending, hne, ↓reduceIte]

  -- Establish active_drop = count(n) using countP_change_eq_count
  have h_act_change : wi.active_count = wi'.active_count + wi.definition.nodes.count n := by
    simp only [WorkflowInstance.active_count, h_result]
    have h := countP_change_eq_count wi.definition.nodes n wi.is_active
      (fun x => decide ((if x = n then NodeState.pending else wi.node_states x) = NodeState.active))
    apply h
    · -- h_old: old_act n = true (was active)
      simp only [WorkflowInstance.is_active, h_active, decide_eq_true_eq]
    · -- h_new: new_act n = false (pending ≠ active)
      simp only [↓reduceIte, decide_eq_false_iff_not]
      decide
    · -- h_unchanged
      intro x _ hne
      simp only [WorkflowInstance.is_active, hne, ↓reduceIte]

  -- Establish retries_drop = count(n) * 1 = count(n) using foldl_add_change_eq_count_mul
  have h_ret_change : wi.definition.nodes.foldl (fun acc m => acc + wi.retries m) 0 =
                      wi'.definition.nodes.foldl (fun acc m => acc + wi'.retries m) 0 +
                      wi.definition.nodes.count n * 1 := by
    simp only [h_result]
    -- wi.retries n = wi'.retries n + 1 (since wi'.retries n = wi.retries n - 1 and wi.retries n > 0)
    have h_delta : wi.retries n = (if n = n then wi.retries n - 1 else wi.retries n) + 1 := by
      simp only [↓reduceIte]
      omega
    apply foldl_add_change_eq_count_mul wi.definition.nodes n wi.retries
      (fun x => if x = n then wi.retries n - 1 else wi.retries x) 1
    · -- h_dec: wi.retries n = new_retries n + 1
      simp only [↓reduceIte]
      omega
    · -- h_unchanged
      intro x _ hne
      simp only [hne, ↓reduceIte]

  -- Now show measure decreases using weighted arithmetic
  -- Net change = pending_rise * 1000 - active_drop * 100 - retries_drop * 1000
  -- = count(n) * 1000 - count(n) * 100 - count(n) * 1000
  -- = count(n) * (1000 - 100 - 1000)
  -- = count(n) * (-100) < 0 (since n ∈ nodes means count(n) >= 1)
  rw [h_time_eq]

  -- From h_in: n ∈ nodes, so count n >= 1
  have h_count_pos : wi.definition.nodes.count n ≥ 1 := List.count_pos_iff.mpr h_in

  -- The arithmetic: all changes equal count(n), so net = -100 * count(n)
  omega

/--
**Theorem (Timeout is Terminal)**:
After timeout, workflow is in terminal state (status = failure).
Terminal states have measure 0 or don't step further.

Proof: Status change doesn't affect measure components (time_left, pending, active, retries).
The measures are definitionally equal, so <= holds.
-/
theorem timeout_terminal (now : Time) (wi wi' : WorkflowInstance)
    (_h_timeout : now ≥ wi.timeout_at)
    (h_result : wi' = { wi with status := .failure }) :
    workflow_measure now wi' ≤ workflow_measure now wi := by
  -- Substitute wi' with its definition
  subst h_result
  -- The measure only depends on timeout_at, node_states, definition, retries
  -- Status is not used in workflow_measure calculation
  -- So workflow_measure now { wi with status := .failure } = workflow_measure now wi
  -- Use le_refl since the measures are definitionally equal
  exact Nat.le_refl _

-- workflow_step_decreases_or_terminal: REMOVED (unused, derivable from per-case decrease theorems)

-- workflow_terminates: REMOVED (unused, see workflow_terminates_by_timeout in Termination.lean)

end Lion
