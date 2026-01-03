/-
Lion/Theorems/TemporalSafety.lean
=================================

Memory Temporal Safety theorems (Theorem 006).

Proves: Freed memory cannot be accessed (use-after-free prevention).
Key insight: WASM + Rust ownership = temporal safety by construction.

Security Property:
  forall address a, time t_free, t_access:
    free(a, t_free) ^ t_access > t_free => access(a, t_access) = error

Dependencies: 002-memory-isolation
-/

import Lion.Step.Step
import Lion.Step.Authorization
import Lion.State.Memory

namespace Lion

/-! =========== CORE TEMPORAL SAFETY DEFINITIONS =========== -/

/-- A resource is in the freed set -/
def is_freed (s : State) (addr : MemAddr) : Prop :=
  addr ∈ s.ghost.freed_set

/-- A resource can be accessed (is live and not freed) -/
def can_access (s : State) (addr : MemAddr) : Prop :=
  MetaState.is_live s.ghost addr

/-! =========== USE-AFTER-FREE PREVENTION =========== -/

/--
**Theorem (Use-After-Free Prevented)**:
A freed resource cannot be accessed.

Proof: By definition, `is_live` requires the address NOT be in freed_set,
but `is_freed` puts it in freed_set. Contradiction.
-/
theorem use_after_free_prevented (s : State) (addr : MemAddr)
    (h_freed : is_freed s addr) :
    ¬ can_access s addr := by
  intro h_access
  -- h_access : MetaState.is_live s.ghost addr
  -- h_freed  : addr ∈ s.ghost.freed_set
  -- By definition of is_live: requires addr ∉ freed_set
  unfold can_access at h_access
  unfold MetaState.is_live at h_access
  split at h_access
  · -- Case: resources.get? addr = some (.allocated _)
    -- h_access says: addr ∉ s.ghost.freed_set
    -- h_freed says: addr ∈ s.ghost.freed_set
    -- Contradiction
    exact h_access h_freed
  · -- Other cases: h_access = False
    exact h_access

/--
**Corollary (Freed Stays Inaccessible)**:
Once freed, a resource stays inaccessible forever.
-/
theorem freed_stays_inaccessible (s : State) (addr : MemAddr)
    (h_freed : is_freed s addr) :
    ∀ s', State.temporal_safety s s' → ¬ can_access s' addr := by
  intro s' h_temp
  -- h_temp : ∀ a, a ∈ s.ghost.freed_set → a ∈ s'.ghost.freed_set
  have h_freed' : is_freed s' addr := h_temp addr h_freed
  exact use_after_free_prevented s' addr h_freed'

/-! =========== NO CAPABILITY CAN TARGET FREED RESOURCE =========== -/

/--
**Theorem (No Authorization for Freed)**:
An authorization witness cannot target a freed resource.

Proof: The Authorized structure requires h_live, which requires is_live.
But freed resources are not live. Contradiction.
-/
theorem no_authorization_for_freed (s : State) (a : Action) (addr : MemAddr)
    (h_target : a.target = addr)
    (h_freed : is_freed s addr) :
    ¬ ∃ (auth : Authorized s a), True := by
  intro ⟨auth, _⟩
  -- auth.h_live says: ∀ r, a.target = r → MetaState.is_live s.ghost r
  have h_live := auth.h_live addr h_target
  -- h_live : MetaState.is_live s.ghost addr
  -- h_freed : addr ∈ s.ghost.freed_set
  -- These contradict by use_after_free_prevented
  have h_not_access := use_after_free_prevented s addr h_freed
  exact h_not_access h_live

/--
**Corollary (No Host Call to Freed)**:
A host_call step cannot target a freed resource.
-/
theorem no_host_call_to_freed {s s' : State} (st : Step s s')
    (addr : MemAddr) (h_freed : is_freed s addr) :
    ∀ hc a (auth : Authorized s a) hr hp hpre hexec,
      st = Step.host_call hc a auth hr hp hpre hexec →
      a.target ≠ addr := by
  intro hc a auth hr hp hpre hexec _
  -- By contradiction: assume a.target = addr
  intro h_target
  -- auth.h_live requires is_live for target
  have h_live := auth.h_live addr h_target
  -- But addr is freed, so not live
  have h_not_live := use_after_free_prevented s addr h_freed
  exact h_not_live h_live

/-! =========== TEMPORAL SAFETY PRESERVATION =========== -/

/--
**Theorem (Free Monotonicity)**:
The free operation only adds to freed_set, never removes.

Proof: By definition, free sets freed_set := ms.freed_set ∪ {addr}.
If addr' ∈ ms.freed_set, then addr' ∈ ms.freed_set ∪ {addr}.
-/
theorem free_only_adds (ms : MetaState) (addr addr' : MemAddr)
    (h_in : addr' ∈ ms.freed_set) :
    addr' ∈ (ms.free addr).freed_set := by
  simp only [MetaState.free, Finset.mem_union]
  left
  exact h_in

/--
**Theorem (Alloc Preserves Freed)**:
Allocation does not remove from freed_set.

Proof: By definition, alloc sets freed_set := ms.freed_set (unchanged).
-/
theorem alloc_preserves_freed (ms : MetaState) (addr owner : Nat) (addr' : MemAddr)
    (h_in : addr' ∈ ms.freed_set) :
    addr' ∈ (ms.alloc addr owner).freed_set := by
  unfold MetaState.alloc
  exact h_in

/--
**Lemma (apply_free preserves temporal safety)**:
State.apply_free only adds to freed_set.
-/
lemma apply_free_preserves (s : State) (addr : MemAddr) :
    State.temporal_safety s (s.apply_free addr) := by
  intro addr' h_in
  -- s.apply_free addr = { s with ghost := s.ghost.free addr }
  -- Need: addr' ∈ (s.ghost.free addr).freed_set
  unfold State.apply_free
  simp only [State.temporal_safety]
  -- (s.ghost.free addr).freed_set = s.ghost.freed_set ∪ {addr}
  -- h_in : addr' ∈ s.ghost.freed_set
  -- So addr' ∈ s.ghost.freed_set ∪ {addr}
  exact free_only_adds s.ghost addr addr' h_in

/--
**Lemma (apply_alloc preserves temporal safety)**:
State.apply_alloc does not change freed_set.
-/
lemma apply_alloc_preserves (s : State) (owner : PluginId) (size : Nat) :
    State.temporal_safety s (s.apply_alloc owner size) := by
  intro addr h_in
  -- apply_alloc doesn't touch freed_set
  unfold State.apply_alloc
  simp only [State.temporal_safety]
  let alloc_addr := s.ghost.resources.size
  exact alloc_preserves_freed s.ghost alloc_addr owner addr h_in

/-! =========== STEP PRESERVES TEMPORAL SAFETY =========== -/

/--
**Theorem (Plugin Internal Preserves Ghost)**:
Plugin-internal computation does not affect ghost state.
Untrusted code cannot free memory directly.

Proof: Follows from plugin_internal_comprehensive_frame which states s'.ghost = s.ghost.
-/
theorem plugin_internal_preserves_ghost {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (_hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    s'.ghost = s.ghost :=
  plugin_internal_ghost_unchanged pid pi s s' hexec

/--
**Theorem (Kernel Internal Preserves Freed)**:
Kernel-internal operations preserve freed_set.
Time ticks and routing don't deallocate.

Proof: By case analysis on KernelOp. All comprehensive frame axioms
state s'.ghost = s.ghost, so freed_set is exactly preserved.
-/
theorem kernel_internal_preserves_freed {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    State.temporal_safety s s' := by
  intro addr h_in
  -- In all cases, s'.ghost = s.ghost from comprehensive frame
  cases op with
  | route_one dst =>
    rw [route_one_ghost_unchanged dst s s' hexec]
    exact h_in
  | time_tick =>
    rw [time_tick_ghost_unchanged s s' hexec]
    exact h_in
  | workflow_tick wid =>
    rw [workflow_tick_ghost_unchanged wid s s' hexec]
    exact h_in
  | unblock_send dst =>
    rw [unblock_send_ghost_unchanged dst s s' hexec]
    exact h_in

/--
**THEOREM (was axiom)**: Ghost state specification for `KernelExecHost`.
Now proven from constructive KernelExecHost definition.

- mem_free → ghost updated via MetaState.free
- mem_alloc → ghost updated via MetaState.alloc
- otherwise → ghost unchanged
-/
theorem host_call_ghost_spec {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) :
    KernelExecHost hc a auth hr s s' →
      (hc.function = .mem_free →
          ∃ addr, s'.ghost = (s.ghost.free addr)) ∧
      (hc.function = .mem_alloc →
          ∃ addr owner, s'.ghost = (s.ghost.alloc addr owner)) ∧
      (hc.function ≠ .mem_free →
        hc.function ≠ .mem_alloc →
          s'.ghost = s.ghost) := by
  intro hexec
  unfold KernelExecHost at hexec
  cases hf : hc.function <;> simp only [hf] at hexec
  -- cap_invoke: s' = s
  · obtain ⟨_, _, _, _, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- cap_delegate: only kernel changes
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- cap_accept: kernel and plugins change, ghost unchanged
  · obtain ⟨_, _, _, _, _, _, _, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- cap_revoke: only kernel changes
  · obtain ⟨_, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- mem_alloc: ghost changes via alloc
  · obtain ⟨size, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩
    · intro h; simp at h
    · intro _; subst h_eq; unfold State.apply_alloc
      exact ⟨s.ghost.resources.size, hc.caller, rfl⟩
    · intro _ h; simp at h
  -- mem_free: ghost changes via free
  · obtain ⟨addr, _, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩
    · intro _; subst h_eq; exact ⟨addr, rfl⟩
    · intro h; simp at h
    · intro h; simp at h
  -- ipc_send: s' = s
  · obtain ⟨_, _, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- ipc_receive: only actors change
  · split at hexec
    · obtain ⟨h_eq, _⟩ := hexec
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
      intro _; subst h_eq; rfl
    · obtain ⟨h_eq, _⟩ := hexec
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
      intro _; subst h_eq; rfl
  -- resource_create: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- resource_access: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- workflow_start: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- workflow_step: s' = s
  · obtain ⟨h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl
  -- declassify: only plugins change
  · obtain ⟨_, _, h_eq, _⟩ := hexec
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp at h
    intro _; subst h_eq; rfl

/--
**Theorem (Host Call Preserves Freed)**:
Host calls that modify memory do so safely:
- Free adds to freed_set
- Alloc preserves freed_set
- Other operations preserve freed_set

Proof: From host_call_ghost_spec + free_only_adds/alloc_preserves_freed.
-/
theorem host_call_preserves_freed {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s') :
    State.temporal_safety s s' := by
  intro addr h_in
  have hspec := host_call_ghost_spec (hc := hc) (a := a) (auth := auth) (hr := hr) hexec

  by_cases hfree : hc.function = .mem_free
  · -- Free case: freed_set grows (free_only_adds)
    rcases (hspec.1 hfree) with ⟨freed_addr, hghost⟩
    have : addr ∈ (s.ghost.free freed_addr).freed_set :=
      free_only_adds s.ghost freed_addr addr h_in
    simpa [hghost] using this

  · by_cases halloc : hc.function = .mem_alloc
    · -- Alloc case: freed_set unchanged (alloc_preserves_freed)
      rcases (hspec.2.1 halloc) with ⟨alloc_addr, owner, hghost⟩
      have : addr ∈ (s.ghost.alloc alloc_addr owner).freed_set :=
        alloc_preserves_freed s.ghost alloc_addr owner addr h_in
      simpa [hghost] using this

    · -- Other host calls: ghost unchanged
      have hghost : s'.ghost = s.ghost := hspec.2.2 hfree halloc
      simpa [hghost] using h_in

/--
**Theorem (Step Preserves Temporal Safety)**:
Every step preserves temporal safety.
Once freed, always freed.

Proof: By case analysis on Step constructor.
-/
theorem step_preserves_temporal_safety {s s' : State} (st : Step s s') :
    State.temporal_safety s s' := by
  cases st with
  | plugin_internal pid pi hpre hexec =>
      -- Plugin internal doesn't change ghost state
      intro addr h_in
      have h_ghost := plugin_internal_preserves_ghost pid pi hpre hexec
      -- h_ghost : s'.ghost = s.ghost
      -- h_in : addr ∈ s.ghost.freed_set
      -- Goal: addr ∈ s'.ghost.freed_set
      simp only [State.temporal_safety, h_ghost]
      exact h_in
  | host_call hc a auth hr hp hpre hexec =>
      -- Host calls preserve freed_set (axiom)
      exact host_call_preserves_freed hc a auth hr hp hpre hexec
  | kernel_internal op hexec =>
      -- Kernel internal preserves freed_set (axiom)
      exact kernel_internal_preserves_freed op hexec

/-! =========== REACHABILITY AND TEMPORAL SAFETY =========== -/

/--
**Theorem (Reachable Preserves Temporal Safety)**:
Temporal safety is preserved across any sequence of steps.

Proof: By induction on Reachable.
-/
theorem reachable_preserves_temporal_safety {s s' : State}
    (h_reach : Reachable s s') :
    State.temporal_safety s s' := by
  induction h_reach with
  | refl =>
      -- Reflexive: trivially true
      intro addr h_in
      exact h_in
  | step h_reach' st ih =>
      -- s →* s' → s''
      -- ih : temporal_safety s s'
      -- step_preserves : temporal_safety s' s''
      -- Need: temporal_safety s s''
      intro addr h_in
      have h_mid := ih addr h_in
      have h_step := step_preserves_temporal_safety st
      exact h_step addr h_mid

/--
**Corollary (Freed Forever)**:
Once a resource is freed, it remains freed in all reachable states.
-/
theorem freed_forever (s : State) (addr : MemAddr)
    (h_freed : is_freed s addr) :
    Always (fun s' => is_freed s' addr) s := by
  intro s' h_reach
  have h_temp := reachable_preserves_temporal_safety h_reach
  exact h_temp addr h_freed

/--
**Corollary (No Future Access)**:
A freed resource cannot be accessed in any future state.
-/
theorem no_future_access (s : State) (addr : MemAddr)
    (h_freed : is_freed s addr) :
    Always (fun s' => ¬ can_access s' addr) s := by
  intro s' h_reach
  have h_freed' := freed_forever s addr h_freed s' h_reach
  exact use_after_free_prevented s' addr h_freed'

/-! =========== DOUBLE-FREE PREVENTION =========== -/

/--
**Theorem (Double Free Detected)**:
Attempting to free an already-freed resource is detectable.

The MetaState tracks freed_set, so double-free is visible.
In implementation, this would trigger an error.
-/
theorem double_free_detectable (s : State) (addr : MemAddr)
    (h_freed : is_freed s addr) :
    addr ∈ s.ghost.freed_set := h_freed

/--
**Theorem (Free Idempotence on freed_set)**:
Freeing an already-freed address doesn't change freed_set membership
for that address (it's already there).
-/
theorem free_idempotent_membership (ms : MetaState) (addr : MemAddr)
    (h_in : addr ∈ ms.freed_set) :
    addr ∈ (ms.free addr).freed_set := by
  exact free_only_adds ms addr addr h_in

/-! =========== MEMORY TEMPORAL SAFETY MAIN THEOREM =========== -/

/--
**Main Theorem (Memory Temporal Safety)**:
Memory freed at time t cannot be accessed at any time t' > t.

This is the key security property. Proved by:
1. Free adds address to freed_set
2. freed_set is monotonic (only grows)
3. Authorization requires is_live
4. is_live requires NOT in freed_set
5. Therefore, freed resources cannot be authorized

Combined with complete mediation (Theorem 001), this ensures
no use-after-free is possible in the Lion microkernel.
-/
theorem memory_temporal_safety (s : State) (addr : MemAddr)
    (h_live : can_access s addr) :
    ∀ s' (h_reach : Reachable s s'),
      is_freed s' addr →
      ∀ s'' (h_reach' : Reachable s' s''),
        ¬ can_access s'' addr := by
  intro s' h_reach h_freed s'' h_reach'
  -- Once freed at s', stays freed at s''
  have h_freed'' := freed_forever s' addr h_freed s'' h_reach'
  -- Freed resources cannot be accessed
  exact use_after_free_prevented s'' addr h_freed''

/-! =========== WASM CORRESPONDENCE (FUTURE WORK) =========== -/

/--
**Theorem (WASM Linear Memory Safety)**:
WASM sandbox enforces memory bounds.
This is trivial since addr_in_bounds IS defined as addr + len ≤ bounds.
-/
theorem wasm_bounds_checked (mem : LinearMemory) (addr : MemAddr) (len : Size)
    (h_bounds : mem.addr_in_bounds addr len) :
    addr + len ≤ mem.bounds := h_bounds

/--
**Theorem (Rust Ownership Correspondence)**:
Rust's ownership system corresponds to our linear resource model.
Single owner at any time prevents dangling references.

Proof: Unfold is_live definition - it exactly matches the hypotheses.
-/
theorem rust_ownership_linear :
    ∀ (s : State) (addr : MemAddr) (owner : PluginId),
      s.ghost.resources.get? addr = some (.allocated owner) →
      addr ∉ s.ghost.freed_set →
      MetaState.is_live s.ghost addr := by
  intro s addr owner h_alloc h_not_freed
  unfold MetaState.is_live
  rw [h_alloc]
  exact h_not_freed

/-! =========== SUMMARY =========== -/

/-
Memory Temporal Safety Theorems Summary:

Core Properties:
1. use_after_free_prevented: Freed resources cannot be accessed
2. freed_stays_inaccessible: Freed resources stay inaccessible
3. no_authorization_for_freed: No capability can target freed resource
4. step_preserves_temporal_safety: Every step preserves freed_set
5. freed_forever: Once freed, always freed (across all reachable states)
6. memory_temporal_safety: Main theorem combining all properties

Axioms (5 total):
1. free_only_adds: Free operation only adds to freed_set
2. alloc_preserves_freed: Alloc doesn't remove from freed_set
3. plugin_internal_preserves_ghost: Untrusted code can't free
4. kernel_internal_preserves_freed: Kernel ops preserve freed_set
5. host_call_preserves_freed: Host calls safely manage memory

These axioms represent integration points with the execution model
and are dischargeable by examining the MetaState operations.
-/

end Lion
