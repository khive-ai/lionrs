/-
Lion/Step/Step.lean
====================

The unified Step relation with 3 constructors.
Core of the formal verification architecture.
-/

import Lion.Step.Authorization
import Lion.Step.HostCall
import Lion.Step.PluginInternal
import Lion.Step.KernelOp

namespace Lion

/-! =========== UNIFIED STEP (3 CONSTRUCTORS) =========== -/

/--
The Step relation captures all state transitions.
Organized by trust level:
1. plugin_internal: Untrusted, sandboxed computation
2. host_call: Trust boundary, requires authorization
3. kernel_internal: Trusted TCB operations

Key design: Authorization proofs are BAKED INTO host_call constructor.
You cannot construct a host_call step without providing all the proofs.
This makes complete mediation trivially true by construction.
-/
inductive Step : State → State → Type where
  /-- Plugin-internal computation (untrusted, sandboxed) -/
  | plugin_internal
      (pid : PluginId)
      (pi : PluginInternal)
      (hpre : plugin_internal_pre pid pi s)
      (hexec : PluginExecInternal pid pi s s')
      : Step s s'

  /-- Host call (trust boundary, mediated) -/
  | host_call
      (hc : HostCall)
      (a : Action)
      (auth : Authorized s a)
      (hr : HostResult)
      (hparse : hostcall_action hc = some a)
      (hpre : host_call_pre hc s)
      (hexec : KernelExecHost hc a auth hr s s')
      : Step s s'

  /-- Kernel-internal operation (trusted TCB) -/
  | kernel_internal
      (op : KernelOp)
      (hexec : KernelExecInternal op s s')
      : Step s s'

/-! =========== STEP SUGAR =========== -/

/-- Syntactic sugar: time tick step -/
abbrev Step.tick (s s' : State) (h : KernelExecInternal .time_tick s s') :=
  Step.kernel_internal .time_tick h

/-- Syntactic sugar: message delivery step -/
abbrev Step.deliver (s s' : State) (dst : ActorId) (h : KernelExecInternal (.route_one dst) s s') :=
  Step.kernel_internal (.route_one dst) h

/-! =========== STEP CLASSIFICATION =========== -/

/-- Is this step effectful (crosses trust boundary)? -/
def Step.is_effectful {s s' : State} : Step s s' → Bool
  | .host_call _ _ _ _ _ _ _ => true
  | .plugin_internal _ _ _ _ => false
  | .kernel_internal _ _ => false

/-- Get subject (executing plugin) of step, if any -/
def Step.subject {s s' : State} : Step s s' → Option PluginId
  | .plugin_internal pid _ _ _ => some pid
  | .host_call hc _ _ _ _ _ _ => some hc.caller
  | .kernel_internal _ _ => none

/-- Get security level of step -/
def Step.level {s s' : State} (st : Step s s') : SecurityLevel :=
  match st.subject with
  | some pid => (s.plugins pid).level
  | none => .Secret  -- Kernel is trusted (max level)

/-- Is this a declassify operation? -/
def Step.is_declassify {s s' : State} : Step s s' → Bool
  | .host_call hc _ _ _ _ _ _ => hc.function = .declassify
  | _ => false

/-! =========== REACHABILITY =========== -/

/-- Reflexive transitive closure of Step -/
inductive Reachable : State → State → Prop where
  | refl (s : State) : Reachable s s
  | step {s s' s'' : State} : Reachable s s' → Step s' s'' → Reachable s s''

/-- Transitivity of reachability -/
theorem Reachable.trans {s1 s2 s3 : State} :
    Reachable s1 s2 → Reachable s2 s3 → Reachable s1 s3 := by
  intro h1 h2
  induction h2 with
  | refl => exact h1
  | step _ hstep ih => exact Reachable.step ih hstep

/-- Eventually P holds in some reachable state -/
def Eventually (P : State → Prop) (s : State) : Prop :=
  ∃ s', Reachable s s' ∧ P s'

/-- Always P holds in all reachable states -/
def Always (P : State → Prop) (s : State) : Prop :=
  ∀ s', Reachable s s' → P s'

/-- Step preserves an invariant -/
def Step.preserves {s s' : State} (st : Step s s') (P : State → Prop) : Prop :=
  P s → P s'

end Lion
