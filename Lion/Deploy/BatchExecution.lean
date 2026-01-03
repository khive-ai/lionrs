/-
Lion/Deploy/BatchExecution.lean
================================

Formal proofs for khive-deploy batch execution.
Proves termination and order preservation for batched operations.

Related ADRs:
- khive-deploy ADR-001: Service Abstraction
- khive-deploy ADR-002: WASM Support (Batched I/O Pattern)
- khive-deploy ADR-007: Batch Execution

NOTE: Two distinct batch size limits exist:
- ADR-002 MAX_BATCH_SIZE = 10,000 (WASM I/O boundary optimization)
- ADR-007 MAX_BATCH_SIZE = 100 (concurrent API request limiting)

This proof uses ADR-002's limit (10,000) for WASM batch semantics.
ADR-007's limit (100) is for runtime concurrency control, not proven here.

Properties:
1. Termination: Finite request list always completes
2. Order preservation: Results match request order exactly

STATUS: FIXED - Mathlib4 API compatibility (Dec 2025).
-/

import Mathlib.Data.List.Basic
import Lion.Core.SecurityLevel
import Lion.Core.Rights
import Lion.Deploy.ContextPropagation

namespace Lion.Deploy.Batch

open Lion

/-! =========== PART 1: TYPE DEFINITIONS =========== -/

/-- Maximum batch size (from ADR-002: MAX_BATCH_SIZE = 10_000) -/
def MAX_BATCH_SIZE : Nat := 10000

/-- Maximum item size in bytes (from ADR-002: MAX_ITEM_SIZE = 1MB) -/
def MAX_ITEM_SIZE : Nat := 1024 * 1024

/-- Operation identifier (service.operation format) -/
structure OperationId where
  service : String
  operation : String
deriving DecidableEq, Repr, Inhabited

/--
`xs[i]!` uses the `Inhabited` default when out-of-bounds, so we provide an
`Inhabited` instance for `OperationContext` (and later `OperationRequest`).
-/
instance : Inhabited OperationContext where
  default := ⟨default, default, default, "", none, default⟩

/-- Single operation request in a batch -/
structure OperationRequest where
  opId : OperationId
  input : String  -- JSON-encoded input
  context : OperationContext
deriving Inhabited

/-- Operation result variants -/
inductive OperationResult where
  | success (output : String)
  | validationError (msg : String)
  | serviceNotFound (service : String)
  | operationNotFound (op : String)
  | internalError (msg : String)
  | resourceLimit (msg : String)
  | permissionDenied (msg : String)
deriving DecidableEq, Repr, Inhabited

/-- Batch request containing multiple operations -/
structure BatchRequest where
  requests : List OperationRequest
  h_bounded : requests.length ≤ MAX_BATCH_SIZE

/-- Batch result containing results for each request -/
structure BatchResult where
  results : List OperationResult
deriving Repr

/-! =========== PART 2: BATCH EXECUTION MODEL =========== -/

/-- Execute a single operation (abstract model).
    In reality, this dispatches to ServiceGroup.execute. -/
def executeOperation (req : OperationRequest) : OperationResult :=
  -- This is an abstract model; actual implementation dispatches to handlers
  OperationResult.success "executed"

/-- Execute a batch of operations sequentially.
    PROPERTY: Processes each request in order, produces results in same order. -/
def batchExecute (batch : BatchRequest) : BatchResult :=
  ⟨batch.requests.map executeOperation⟩

/-! =========== PART 3: TERMINATION PROOFS =========== -/

/-- Batch execution on empty list produces empty results -/
theorem batch_empty_terminates :
    batchExecute ⟨[], Nat.zero_le _⟩ = ⟨[]⟩ := rfl

/-- Batch execution on singleton produces singleton result -/
theorem batch_singleton_terminates (req : OperationRequest)
    (h : [req].length ≤ MAX_BATCH_SIZE) :
    (batchExecute ⟨[req], h⟩).results.length = 1 := rfl

/-- Batch execution terminates for any finite list.
    PROOF: List.map is structurally recursive on a finite list,
    hence always terminates. The bound MAX_BATCH_SIZE ensures finiteness. -/
theorem batch_terminates (batch : BatchRequest) :
    ∃ result : BatchResult, result = batchExecute batch :=
  ⟨batchExecute batch, rfl⟩

/-- Stronger termination: execution produces exactly as many results as requests -/
theorem batch_terminates_with_count (batch : BatchRequest) :
    (batchExecute batch).results.length = batch.requests.length := by
  simp [batchExecute, List.length_map]

/-- Batch execution on bounded list terminates within bounds -/
theorem batch_bounded_termination (batch : BatchRequest) :
    (batchExecute batch).results.length ≤ MAX_BATCH_SIZE := by
  calc
    (batchExecute batch).results.length
        = batch.requests.length := batch_terminates_with_count batch
    _ ≤ MAX_BATCH_SIZE := batch.h_bounded

/-! =========== PART 4: ORDER PRESERVATION PROOFS =========== -/

/-- Results are in the same order as requests (index correspondence) -/
theorem batch_order_preserved (batch : BatchRequest) (i : Nat)
    (h : i < batch.requests.length) :
    (batchExecute batch).results[i]? =
    some (executeOperation batch.requests[i]!) := by
  -- `List.getElem?_map` rewrites indexing into a map,
  -- `List.getElem?_eq_getElem h` reduces `[i]?` to `some [i]` for in-bounds `h`,
  -- and `List.getElem!_eq_getElem?_getD` ties `!` to `getD` of the option form.
  simp [batchExecute, List.getElem?_map, List.getElem!_eq_getElem?_getD, h]

/-- Alternative formulation: nth result corresponds to nth request -/
theorem batch_nth_correspondence (batch : BatchRequest) (i : Nat)
    (h : i < batch.requests.length) :
    (batchExecute batch).results.get ⟨i, by
      rw [batch_terminates_with_count]; exact h⟩ =
    executeOperation (batch.requests.get ⟨i, h⟩) := by
  simp [batchExecute]

/-- Order preservation via list equality -/
theorem batch_results_eq_map (batch : BatchRequest) :
    (batchExecute batch).results = batch.requests.map executeOperation := rfl

/-- Prepending a request prepends its result (order preservation induction step) -/
theorem batch_cons_order (req : OperationRequest) (rest : List OperationRequest)
    (h : (req :: rest).length ≤ MAX_BATCH_SIZE) :
    (batchExecute ⟨req :: rest, h⟩).results =
    executeOperation req :: (batchExecute ⟨rest, Nat.le_of_succ_le h⟩).results := by
  simp [batchExecute, List.map_cons]

/-! =========== PART 5: BATCH SIZE VALIDATION =========== -/

/-- Attempt to create a bounded batch request -/
def BatchRequest.mk? (requests : List OperationRequest) : Option BatchRequest :=
  if h : requests.length ≤ MAX_BATCH_SIZE then
    some ⟨requests, h⟩
  else
    none

/-- Valid batch creation succeeds -/
theorem batch_valid_creation (requests : List OperationRequest)
    (h : requests.length ≤ MAX_BATCH_SIZE) :
    BatchRequest.mk? requests = some ⟨requests, h⟩ := by
  simp [BatchRequest.mk?, h]

/-- Invalid batch creation fails -/
theorem batch_invalid_creation (requests : List OperationRequest)
    (h : requests.length > MAX_BATCH_SIZE) :
    BatchRequest.mk? requests = none := by
  simp [BatchRequest.mk?, Nat.not_le.mpr h]

/-- Batch size validation is decidable -/
instance (requests : List OperationRequest) : Decidable (requests.length ≤ MAX_BATCH_SIZE) :=
  inferInstanceAs (Decidable _)

/-! =========== PART 6: COMPOSITION PROPERTIES =========== -/

/-- Concatenating batches preserves order -/
theorem batch_append_order (b1 b2 : List OperationRequest)
    (h : (b1 ++ b2).length ≤ MAX_BATCH_SIZE) :
    (batchExecute ⟨b1 ++ b2, h⟩).results =
    (b1.map executeOperation) ++ (b2.map executeOperation) := by
  simp [batchExecute, List.map_append]

/-- Splitting a batch and recombining preserves results -/
theorem batch_split_recombine (batch : BatchRequest) (n : Nat)
    (hn : n ≤ batch.requests.length) :
    (batchExecute batch).results =
    (batch.requests.take n).map executeOperation ++
    (batch.requests.drop n).map executeOperation := by
  simp [batchExecute, ← List.map_append, List.take_append_drop]

/-! =========== PART 7: IDEMPOTENCE AND DETERMINISM =========== -/

/-- Batch execution is deterministic -/
theorem batch_deterministic (batch : BatchRequest) :
    batchExecute batch = batchExecute batch := rfl

/-- Same inputs produce same outputs -/
theorem batch_same_input_same_output (b1 b2 : BatchRequest)
    (h : b1.requests = b2.requests) :
    (batchExecute b1).results = (batchExecute b2).results := by
  simp [batchExecute, h]

/-! =========== PART 8: ERROR HANDLING PROPERTIES =========== -/

/-- Partial failure model: each operation result is independent -/
def hasError (result : OperationResult) : Bool :=
  match result with
  | .success _ => false
  | _ => true

/-- Count errors in batch result -/
def errorCount (br : BatchResult) : Nat :=
  br.results.filter hasError |>.length

/-- Success count plus error count equals total -/
theorem success_plus_error_eq_total (br : BatchResult) :
    (br.results.filter (fun r => !hasError r)).length + errorCount br =
    br.results.length := by
  -- Expand `errorCount`
  simp [errorCount]
  -- Use Mathlib's filter partition length lemma:
  have h := List.length_eq_length_filter_add (l := br.results) (f := hasError)
  -- h : br.results.length =
  --       (filter hasError br.results).length + (filter (fun x => !hasError x) br.results).length
  calc
    (br.results.filter (fun r => !hasError r)).length + (br.results.filter hasError).length
        = (br.results.filter hasError).length + (br.results.filter (fun r => !hasError r)).length := by
            exact Nat.add_comm _ _
    _ = br.results.length := by
            simpa using h.symm

/-- No error propagation: error in one request doesn't affect others -/
theorem no_error_propagation (batch : BatchRequest) (i j : Nat)
    (hi : i < batch.requests.length) (hj : j < batch.requests.length)
    (hne : i ≠ j) :
    -- Result at index i depends only on request at index i
    (batchExecute batch).results.get ⟨i, by rw [batch_terminates_with_count]; exact hi⟩ =
    executeOperation (batch.requests.get ⟨i, hi⟩) := by
  exact batch_nth_correspondence batch i hi

/-! =========== PART 9: WASM BOUNDARY PROPERTIES =========== -/

/-- WASM batch operations respect memory limits (model) -/
structure WasmBatchConstraints where
  maxBatchSize : Nat := MAX_BATCH_SIZE
  maxItemSize : Nat := MAX_ITEM_SIZE
  maxOperationMemory : Nat := 100 * 1024 * 1024  -- 100MB

/-- Default WASM constraints from ADR-002 -/
def defaultWasmConstraints : WasmBatchConstraints := {}

/-- Batch respects WASM constraints -/
def respectsConstraints (batch : BatchRequest) (c : WasmBatchConstraints) : Prop :=
  batch.requests.length ≤ c.maxBatchSize

/-- Any valid BatchRequest respects default WASM constraints -/
theorem valid_batch_respects_wasm (batch : BatchRequest) :
    respectsConstraints batch defaultWasmConstraints := batch.h_bounded

end Lion.Deploy.Batch
