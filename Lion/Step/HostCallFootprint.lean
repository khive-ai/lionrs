/-
Lion/Step/HostCallFootprint.lean
================================

Fine-grained footprint for host calls, aligned with RuntimeCorrespondence fields.

This module provides systematic effect tracking to avoid the 13×9 explosion
(13 host functions × 9 correspondence fields). Instead:
1. Define footprint per host function (13 cases)
2. Prove ModifiesOnly master theorem (13 cases)
3. Write preservation lemma per field (9 lemmas)

Total: ~22 proofs instead of 117.

STATUS: DRAFT - Q13 consultation implementation.
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Lion.Core.Identifiers
import Lion.State.State
import Lion.Step.HostCall

namespace Lion.Step

open Lion

/-! ## HostCallFootprint Structure

Fine-grained effect tracking aligned with RuntimeCorrespondence fields.
-/

/--
**HostCallFootprint**: Fine-grained footprint for host calls.

Designed to match RuntimeCorrespondence fields exactly, enabling
systematic preservation proofs.
-/
structure HostCallFootprint where
  /-- Kernel revocation state may change -/
  kernel_revocation : Bool := false
  /-- Kernel policy may change -/
  kernel_policy     : Bool := false
  /-- Kernel hmacKey may change (should never be true) -/
  kernel_hmacKey    : Bool := false
  /-- Kernel.now may change -/
  kernel_now        : Bool := false
  /-- State.time may change -/
  time              : Bool := false

  /-- Resources mapping may change -/
  resources         : Bool := false
  /-- Workflows mapping may change -/
  workflows         : Bool := false
  /-- Ghost/MetaState may change -/
  ghost             : Bool := false

  /-- Plugin memory may change for these plugin IDs -/
  plugins_memory    : Finset PluginId := ∅
  /-- Plugin level may change for these plugin IDs -/
  plugins_level     : Finset PluginId := ∅
  /-- Plugin heldCaps may change for these plugin IDs -/
  plugins_heldCaps  : Finset PluginId := ∅
  /-- Plugin localState may change for these plugin IDs -/
  plugins_local     : Finset PluginId := ∅
  /-- Actors may change for these actor IDs -/
  actors            : Finset ActorId  := ∅
  deriving DecidableEq

/-- Empty footprint (no effects) -/
abbrev HostCallFootprint.empty : HostCallFootprint := {}

@[simp] theorem HostCallFootprint.empty_kernel_revocation :
    HostCallFootprint.empty.kernel_revocation = false := rfl

@[simp] theorem HostCallFootprint.empty_kernel_hmacKey :
    HostCallFootprint.empty.kernel_hmacKey = false := rfl

@[simp] theorem HostCallFootprint.empty_ghost :
    HostCallFootprint.empty.ghost = false := rfl

/-! ## Footprint Mapping

Maps each HostFunctionId to its precise footprint.
-/

/--
**hostCallFootprint**: Compute the footprint for a host call.

This determines exactly which State fields may change for each host function.
-/
@[simp] def hostCallFootprint (hc : HostCall) : HostCallFootprint :=
  match hc.function with
  -- Capability operations
  | .cap_invoke      => {}
  | .cap_delegate    => { kernel_revocation := true }
  | .cap_accept      => { kernel_revocation := true, plugins_heldCaps := {hc.caller} }
  | .cap_revoke      => { kernel_revocation := true }

  -- Memory operations (only affect ghost - allocation tracking)
  | .mem_alloc       => { ghost := true }
  | .mem_free        => { ghost := true }

  -- IPC operations
  | .ipc_send        => { actors := {hc.caller} }
  | .ipc_receive     => { actors := {hc.caller} }

  -- Resource operations
  | .resource_create => { resources := true }
  | .resource_access => {}

  -- Workflow operations
  | .workflow_start  => { workflows := true }
  | .workflow_step   => { workflows := true }

  -- Security operations
  | .declassify      => { plugins_level := {hc.caller} }

/-! ## ModifiesOnly Predicate

Captures: "s' differs from s only in fields permitted by the footprint".
-/

/--
**ModifiesOnly**: State s' differs from s only in footprint-permitted fields.

This is the key predicate for systematic preservation proofs.
-/
def ModifiesOnly (fp : HostCallFootprint) (s s' : State) : Prop :=
  -- Kernel fields
  (fp.kernel_revocation = false → s'.kernel.revocation = s.kernel.revocation) ∧
  (fp.kernel_policy     = false → s'.kernel.policy     = s.kernel.policy) ∧
  (fp.kernel_hmacKey    = false → s'.kernel.hmacKey    = s.kernel.hmacKey) ∧
  (fp.kernel_now        = false → s'.kernel.now        = s.kernel.now) ∧
  (fp.time              = false → s'.time              = s.time) ∧

  -- Indexed plugin fields: unchanged outside footprint sets
  (∀ pid, pid ∉ fp.plugins_memory   → (s'.plugins pid).memory     = (s.plugins pid).memory) ∧
  (∀ pid, pid ∉ fp.plugins_level    → (s'.plugins pid).level      = (s.plugins pid).level) ∧
  (∀ pid, pid ∉ fp.plugins_heldCaps → (s'.plugins pid).heldCaps   = (s.plugins pid).heldCaps) ∧
  (∀ pid, pid ∉ fp.plugins_local    → (s'.plugins pid).localState = (s.plugins pid).localState) ∧

  -- Indexed actors: unchanged outside footprint set
  (∀ aid, aid ∉ fp.actors → s'.actors aid = s.actors aid) ∧

  -- Global tables
  (fp.resources = false → s'.resources = s.resources) ∧
  (fp.workflows = false → s'.workflows = s.workflows) ∧
  (fp.ghost     = false → s'.ghost     = s.ghost)

/-! ## Preservation Helpers

One-liner lemmas for extracting "unchanged" facts from ModifiesOnly.
-/

/-- Plugin memory unchanged for PIDs not in footprint -/
theorem modifiesOnly_plugins_memory_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (pid : PluginId) (hpid : pid ∉ fp.plugins_memory) :
    (s'.plugins pid).memory = (s.plugins pid).memory :=
  hmod.2.2.2.2.2.1 pid hpid

/-- Plugin level unchanged for PIDs not in footprint -/
theorem modifiesOnly_plugins_level_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (pid : PluginId) (hpid : pid ∉ fp.plugins_level) :
    (s'.plugins pid).level = (s.plugins pid).level :=
  hmod.2.2.2.2.2.2.1 pid hpid

/-- Plugin heldCaps unchanged for PIDs not in footprint -/
theorem modifiesOnly_plugins_heldCaps_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (pid : PluginId) (hpid : pid ∉ fp.plugins_heldCaps) :
    (s'.plugins pid).heldCaps = (s.plugins pid).heldCaps :=
  hmod.2.2.2.2.2.2.2.1 pid hpid

/-- Actors unchanged for AIDs not in footprint -/
theorem modifiesOnly_actors_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (aid : ActorId) (haid : aid ∉ fp.actors) :
    s'.actors aid = s.actors aid :=
  hmod.2.2.2.2.2.2.2.2.2.1 aid haid

/-- Kernel revocation unchanged when not in footprint -/
theorem modifiesOnly_kernel_revocation_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.kernel_revocation = false) :
    s'.kernel.revocation = s.kernel.revocation :=
  hmod.1 hfp

/-- Kernel hmacKey unchanged when not in footprint -/
theorem modifiesOnly_kernel_hmacKey_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.kernel_hmacKey = false) :
    s'.kernel.hmacKey = s.kernel.hmacKey :=
  hmod.2.2.1 hfp

/-- Time unchanged when not in footprint -/
theorem modifiesOnly_time_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.time = false) :
    s'.time = s.time :=
  hmod.2.2.2.2.1 hfp

/-- Resources unchanged when not in footprint -/
theorem modifiesOnly_resources_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.resources = false) :
    s'.resources = s.resources :=
  hmod.2.2.2.2.2.2.2.2.2.2.1 hfp

/-- Workflows unchanged when not in footprint -/
theorem modifiesOnly_workflows_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.workflows = false) :
    s'.workflows = s.workflows :=
  hmod.2.2.2.2.2.2.2.2.2.2.2.1 hfp

/-- Ghost unchanged when not in footprint -/
theorem modifiesOnly_ghost_unchanged
    {fp : HostCallFootprint} {s s' : State} (hmod : ModifiesOnly fp s s')
    (hfp : fp.ghost = false) :
    s'.ghost = s.ghost :=
  hmod.2.2.2.2.2.2.2.2.2.2.2.2 hfp

/-! ## Reflexivity

Empty footprint means state is unchanged.
-/

/-- ModifiesOnly is reflexive (any state satisfies ModifiesOnly _ s s) -/
theorem ModifiesOnly_refl (fp : HostCallFootprint) (s : State) :
    ModifiesOnly fp s s :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## Summary

This module provides:

1. **HostCallFootprint**: Fine-grained effect tracking per host function
2. **hostCallFootprint**: Mapping from HostCall to its effects
3. **ModifiesOnly**: Predicate for "changes only permitted fields"
4. **Preservation helpers**: One-liner lemmas for each unchanged field

Usage pattern:
1. Prove `KernelExecHost_modifies_only` master theorem (13 cases)
2. Use preservation helpers for unchanged fields
3. Only discharge modified fields directly

This reduces 117 proofs to ~22 (13 + 9).
-/

end Lion.Step
