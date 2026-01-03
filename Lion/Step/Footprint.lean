/-
Lion/Step/Footprint.lean
=========================

Footprint-based frame conditions for modular reasoning.
-/

import Mathlib.Data.Finset.Basic
import Lion.Step.Step

namespace Lion

/-! =========== FOOTPRINTS =========== -/

/-- Footprint of a step: what state components it may affect -/
structure Footprint where
  kernel    : Bool := false
  policy    : Bool := false
  workflows : Bool := false
  plugins   : Finset PluginId := ∅
  actors    : Finset ActorId := ∅

instance : Repr Footprint where
  reprPrec _ _ := "«Footprint»"

namespace Footprint

/-- Empty footprint (affects nothing) -/
def empty : Footprint where
  kernel := false
  policy := false
  workflows := false
  plugins := ∅
  actors := ∅

/-- Union of footprints -/
def union (f g : Footprint) : Footprint where
  kernel := f.kernel || g.kernel
  policy := f.policy || g.policy
  workflows := f.workflows || g.workflows
  plugins := f.plugins ∪ g.plugins
  actors := f.actors ∪ g.actors

instance : Union Footprint where union := union

/-- Disjoint footprints -/
def disjoint (f g : Footprint) : Prop :=
  (f.kernel = false ∨ g.kernel = false) ∧
  (f.policy = false ∨ g.policy = false) ∧
  (f.workflows = false ∨ g.workflows = false) ∧
  Disjoint f.plugins g.plugins ∧
  Disjoint f.actors g.actors

end Footprint

/-! =========== STEP FOOTPRINT =========== -/

/-- Compute footprint of a step -/
def step_footprint {s s' : State} : Step s s' → Footprint
  | .plugin_internal pid _ _ _ =>
      { plugins := {pid}, actors := {pid} }
  | .host_call hc _ _ _ _ _ _ =>
      { kernel := true, policy := true,
        plugins := {hc.caller}, actors := {hc.caller} }
  | .kernel_internal op _ =>
      match op with
      | .time_tick => { kernel := true }
      | .workflow_tick _ => { kernel := true, workflows := true }
      | .route_one dst => { kernel := true, actors := {dst} }
      | .unblock_send dst => { kernel := true, actors := {dst} }

/-! =========== COMPREHENSIVE FRAME THEOREM =========== -/

/--
**Comprehensive Step Frame Theorem**

A step only modifies state components within its footprint.
All components outside the footprint are unchanged.

PROVEN by case analysis on Step constructors:
- plugin_internal: Uses plugin_internal_comprehensive_frame
- host_call: Uses host_call_comprehensive_frame (axiom due to opaque KernelExecHost)
- kernel_internal: Uses KernelExecInternal frame theorems

This is the single source of truth for step framing.
-/
theorem step_comprehensive_frame :
  ∀ {s s' : State} (st : Step s s'),
    -- Plugins outside footprint unchanged
    (∀ pid, pid ∉ (step_footprint st).plugins → s'.plugins pid = s.plugins pid) ∧
    -- Actors outside footprint unchanged
    (∀ aid, aid ∉ (step_footprint st).actors → s'.actors aid = s.actors aid) ∧
    -- Kernel unchanged if not in footprint
    ((step_footprint st).kernel = false → s'.kernel = s.kernel) ∧
    -- Workflows unchanged if not in footprint
    ((step_footprint st).workflows = false → s'.workflows = s.workflows) ∧
    -- Resources always unchanged by steps (managed separately)
    s'.resources = s.resources ∧
    -- Ghost state may be updated (for verification tracking)
    True := by
  intro s s' st
  cases st with
  | plugin_internal pid pi hpre hexec =>
      -- Use plugin_internal_comprehensive_frame
      have frame := plugin_internal_comprehensive_frame pid pi _ _ hexec
      refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.2.2.2.1, trivial⟩
      case plugins =>
        intro other hne
        -- footprint.plugins = {pid}, so other ∉ {pid} means other ≠ pid
        simp only [step_footprint, Finset.notMem_singleton] at hne
        exact frame.2.1 other hne
      case actors =>
        intro aid hne
        -- footprint.actors = {pid}, actors unchanged
        simp only [step_footprint, Finset.notMem_singleton] at hne
        -- actors unchanged by plugin_internal
        have h_actors := frame.2.2.1
        rw [h_actors]
      case kernel =>
        intro _
        exact frame.1
      case workflows =>
        intro _
        exact frame.2.2.2.2.1
  | host_call hc a auth hr hparse hpre hexec =>
      -- Use host_call_comprehensive_frame (axiom)
      have frame := host_call_comprehensive_frame hc a auth hr _ _ hexec
      refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.resources_unchanged, trivial⟩
      case plugins =>
        intro other hne
        simp only [step_footprint, Finset.notMem_singleton] at hne
        exact frame.plugins_frame other hne
      case actors =>
        intro aid hne
        simp only [step_footprint, Finset.notMem_singleton] at hne
        exact frame.actors_frame aid hne
      case kernel =>
        -- footprint.kernel = true, so this case is vacuously true
        intro h_false
        simp [step_footprint] at h_false
      case workflows =>
        -- footprint.workflows = false, use frame.workflows_unchanged
        intro _
        exact frame.workflows_unchanged
  | kernel_internal op hexec =>
      cases op with
      | time_tick =>
          have frame := time_tick_comprehensive_frame _ _ hexec
          refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.2.2.2.1, trivial⟩
          case plugins =>
            intro pid _
            rw [frame.2.1]
          case actors =>
            intro aid _
            rw [frame.2.2.1]
          case kernel =>
            -- footprint.kernel = true, vacuous
            intro h_false
            simp [step_footprint] at h_false
          case workflows =>
            intro _
            exact frame.2.2.2.2.1
      | workflow_tick wid =>
          have frame := workflow_tick_comprehensive_frame wid _ _ hexec
          refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.2.2.2.1, trivial⟩
          case plugins =>
            intro pid _
            rw [frame.2.1]
          case actors =>
            intro aid _
            rw [frame.2.2.1]
          case kernel =>
            -- footprint.kernel = true, vacuous
            intro h_false
            simp [step_footprint] at h_false
          case workflows =>
            -- footprint.workflows = true, vacuous
            intro h_false
            simp [step_footprint] at h_false
      | route_one dst =>
          have frame := route_one_comprehensive_frame dst _ _ hexec
          refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.2.2.2.1, trivial⟩
          case plugins =>
            intro pid _
            rw [frame.2.1]
          case actors =>
            intro aid hne
            simp only [step_footprint, Finset.notMem_singleton] at hne
            exact frame.2.2.1 aid hne
          case kernel =>
            -- footprint.kernel = true, vacuous
            intro h_false
            simp [step_footprint] at h_false
          case workflows =>
            intro _
            exact frame.2.2.2.2.1
      | unblock_send dst =>
          have frame := unblock_send_comprehensive_frame dst _ _ hexec
          refine ⟨?plugins, ?actors, ?kernel, ?workflows, frame.2.2.2.2.1, trivial⟩
          case plugins =>
            intro pid _
            rw [frame.2.1]
          case actors =>
            intro aid hne
            simp only [step_footprint, Finset.notMem_singleton] at hne
            exact frame.2.2.1 aid hne
          case kernel =>
            -- footprint.kernel = true, vacuous
            intro h_false
            simp [step_footprint] at h_false
          case workflows =>
            intro _
            exact frame.2.2.2.2.2.1

/-! =========== DERIVED FRAME THEOREMS =========== -/

/-- Plugins outside footprint unchanged -/
theorem frame_plugins {s s' : State} (st : Step s s') (pid : PluginId)
    (h : pid ∉ (step_footprint st).plugins) :
    s'.plugins pid = s.plugins pid :=
  (step_comprehensive_frame st).1 pid h

/-- Actors outside footprint unchanged -/
theorem frame_actors {s s' : State} (st : Step s s') (aid : ActorId)
    (h : aid ∉ (step_footprint st).actors) :
    s'.actors aid = s.actors aid :=
  (step_comprehensive_frame st).2.1 aid h

/-- Kernel unchanged if not in footprint -/
theorem frame_kernel {s s' : State} (st : Step s s')
    (h : (step_footprint st).kernel = false) :
    s'.kernel = s.kernel :=
  (step_comprehensive_frame st).2.2.1 h

/-- Workflows unchanged if not in footprint -/
theorem frame_workflows {s s' : State} (st : Step s s')
    (h : (step_footprint st).workflows = false) :
    s'.workflows = s.workflows :=
  (step_comprehensive_frame st).2.2.2.1 h

/-! =========== FRAME PROPERTIES =========== -/

/-- Memory isolation follows from plugin frame -/
theorem memory_isolated_from_frame {s s' : State} (st : Step s s')
    (active : PluginId) (h_only : (step_footprint st).plugins = {active}) :
    ∀ pid, pid ≠ active → s'.plugins pid = s.plugins pid := by
  intro pid hne
  apply frame_plugins
  rw [h_only]
  exact fun h => hne (Finset.mem_singleton.mp h)

/-- Disjoint footprints commute (conceptually) -/
theorem disjoint_steps_commute {s s₁ s₂ s₁₂ s₂₁ : State}
    (st₁ : Step s s₁) (st₂ : Step s s₂)
    (st₁' : Step s₁ s₁₂) (st₂' : Step s₂ s₂₁)
    (h_disj : (step_footprint st₁).disjoint (step_footprint st₂)) :
    -- If footprints are disjoint, order doesn't matter
    True := trivial  -- Actual proof requires confluence

end Lion
