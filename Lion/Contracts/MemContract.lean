/-
Lion/Contracts/MemContract.lean
================================

Memory Isolation Contract (Theorem 002) - The Base Contract.

This is the FOUNDATION of the contract hierarchy:
- pre = True (no assumptions needed)
- inv = MemoryIsolated (plugins have disjoint memory)
- affects = step_affects_mem (memory-touching steps)

All other contracts depend on this one via their preconditions.

Design: WASM linear memory gives us structural isolation for free.
Each plugin has its own address space, so isolation holds trivially.
-/

import Lion.Contracts.Interface
import Lion.Contracts.StepAffects
import Lion.Composition.SystemInvariant

namespace Lion

/-! =========== MEMORY CONTRACT =========== -/

/--
Memory Isolation Contract (002).

This is the BASE contract in our assume-guarantee hierarchy.
It has no preconditions because memory isolation is a structural
property of the WASM execution model.

Key insight: WASM plugins have independent linear memories.
Address 0 in plugin1 is completely separate from address 0 in plugin2.
This gives us isolation by construction, not by dynamic checks.

The preservation proof uses step_preserves_memory_isolated theorem
which is proven from:
- plugin_internal: bounds axiom for executor, frame for others
- host_call: bounds axiom for caller, frame for others
- kernel_internal: plugins unchanged frame
-/
noncomputable def memContract : InterfaceContract State Step :=
  { pre := fun _ => True
    inv := MemoryIsolated
    affects := fun h => step_affects_mem h
    preserve := by
      intro s s' h hinv _hpre _ha
      -- Use the proven step_preserves_memory_isolated theorem
      exact step_preserves_memory_isolated h hinv
    frame := by
      intro s s' h hinv _hpre _hna
      -- Frame also uses step_preserves_memory_isolated
      -- (memory isolation is preserved regardless of affects predicate)
      exact step_preserves_memory_isolated h hinv
  }

/-! =========== DERIVED LEMMAS =========== -/

/-- Memory isolation is preserved by all steps. -/
theorem memory_isolation_preserved {s s' : State} (h : Step s s')
    (hinv : MemoryIsolated s) : MemoryIsolated s' :=
  step_preserves_memory_isolated h hinv

/-- Memory contract preservation via inv_step. -/
theorem mem_contract_inv_step {s s' : State} (h : Step s s')
    (hinv : memContract.inv s) : memContract.inv s' :=
  memContract.inv_step h hinv True.intro

/-- Memory isolation is the base of the dependency graph. -/
theorem mem_contract_satisfies_cap_pre (s : State) :
    memContract.inv s → memContract.inv s := id

/-! =========== COMPATIBILITY LEMMAS =========== -/

/-- Any state satisfies the precondition of memContract. -/
theorem mem_pre_trivial (s : State) : memContract.pre s := True.intro

/-- memContract's invariant provides memory isolation. -/
theorem mem_inv_provides_isolation (s : State) :
    memContract.inv s → MemoryIsolated s := by
  intro h
  exact h

/-! =========== STEP CLASSIFICATION FOR MEM =========== -/

/-- Plugin internal steps affect memory (they can write to linear memory). -/
lemma mem_plugin_internal_affects {s s' : State} (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s) (hexec : PluginExecInternal pid pi s s') :
    step_affects_mem (Step.plugin_internal pid pi hpre hexec) = True := rfl

/-- Host calls affect memory only for mem_alloc/mem_free. -/
lemma mem_host_call_affects_iff {s s' : State} (hc : HostCall)
    (a : Action) (auth : Authorized s a) (hr : HostResult)
    (hparse : hostcall_action hc = some a) (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    step_affects_mem (Step.host_call hc a auth hr hparse hpre hexec) ↔
    is_mem_action hc.function := by
  rfl

/-- Kernel internal steps do NOT affect memory (refined classification). -/
lemma mem_kernel_internal_not_affects {s s' : State} (op : KernelOp)
    (hexec : KernelExecInternal op s s') :
    ¬ step_affects_mem (Step.kernel_internal op hexec) := by
  simp only [step_affects_mem, kernelOp_affects_mem]
  cases op <;> simp

end Lion
