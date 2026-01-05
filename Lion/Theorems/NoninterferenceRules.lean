/-
Lion/Theorems/NoninterferenceRules.lean
========================================

Step rules for noninterference property preservation.
Tagged with @[step_rule] for use with step_cases tactic.

This module provides wrapper lemmas for:
1. Confidentiality step_confinement: High steps preserve low-equivalence
2. Integrity confinement: Low-integrity steps preserve high-integrity state
3. Labels no-downgrade: Non-declassify steps preserve security labels

Usage with step_cases:
  step_cases st
  case plugin_internal pid pi hpre hexec => ...
  case host_call hc a auth hr hparse hpre hexec => ...
  case kernel_internal op hexec => ...

STATUS: Complete - step_rule lemmas for all noninterference properties
-/

import Lion.Theorems.Noninterference
import Lion.Theorems.IntegrityNoninterference
import Lion.Tactic.StepCases

namespace Lion.NoninterferenceRules

open Lion Lion.Noninterference Lion.IntegrityNoninterference Lion.Tactic.StepCases

/-! =========== PART 1: CONFIDENTIALITY STEP_CONFINEMENT RULES ===========

    These rules prove that high steps preserve low_equivalent_left.
    High step = step by a plugin with level > L (observer level).

    Pattern: If the executing plugin's level > L, then low-observable
    state (plugins/resources at level <= L) is unchanged.
-/

/--
Rule: plugin_internal preserves low-equivalence when plugin is high.
A high-security plugin's internal execution doesn't affect low-observable state.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_confinement_rule {s s' : State}
    (L : SecurityLevel)
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s')
    (h_high : (s.plugins pid).level > L) :
    low_equivalent_left L s s' := by
  constructor
  -- Low plugins unchanged
  · intro pid' h_low
    by_cases h_eq : pid' = pid
    · -- pid' = pid: level > L contradicts h_low (level <= L)
      subst h_eq
      exfalso
      exact absurd h_low (not_le_of_gt h_high)
    · -- pid' <> pid: frame condition
      have h_ne : pid' != pid := by simp [bne_iff_ne]; exact h_eq
      exact (plugin_internal_frame' pid pi s s' hpre hexec pid' h_ne).symm
  -- Low resources unchanged
  · intro rid _
    exact (congrFun (plugin_internal_resource_frame pid pi s s' hpre hexec) rid).symm

/--
Rule: host_call preserves low-equivalence when caller is high.
A high-security caller's host call doesn't affect low-observable state.
-/
@[step_rule Step.host_call]
theorem host_call_confinement_rule {s s' : State}
    (L : SecurityLevel)
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (hparse : hostcall_action hc = some a)
    (hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_high : (s.plugins hc.caller).level > L) :
    low_equivalent_left L s s' :=
  host_call_preserves_low_equiv L hc a auth hr hparse hpre hexec h_high

/--
Rule: kernel_internal preserves low-equivalence.
Kernel operations don't modify plugin or resource state visible to observers.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_confinement_rule {s s' : State}
    (L : SecurityLevel)
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    low_equivalent_left L s s' := by
  cases op with
  | time_tick =>
    obtain ⟨_, h_plugins, _⟩ := time_tick_only_time s s' hexec
    constructor
    · intro pid _
      exact (congrFun h_plugins pid).symm
    · intro rid _
      exact (congrFun (time_tick_comprehensive_frame s s' hexec).2.2.2.1 rid).symm
  | route_one dst =>
    constructor
    · intro pid _
      exact (congrFun (route_one_memory_unchanged dst s s' hexec) pid).symm
    · intro rid _
      exact (congrFun (route_one_resource_unchanged dst s s' hexec) rid).symm
  | workflow_tick wid =>
    constructor
    · intro pid _
      exact (congrFun (workflow_tick_plugins_unchanged wid s s' hexec) pid).symm
    · intro rid _
      exact (congrFun (workflow_tick_resources_unchanged wid s s' hexec) rid).symm
  | unblock_send dst =>
    constructor
    · intro pid _
      exact (congrFun (unblock_send_plugins_unchanged dst s s' hexec) pid).symm
    · intro rid _
      exact (congrFun (unblock_send_resources_unchanged dst s s' hexec) rid).symm

/-! =========== PART 2: INTEGRITY CONFINEMENT RULES ===========

    These rules prove that low-integrity steps preserve high_integrity_preserved.
    Low-integrity step = step by a plugin with level < H (integrity level).

    Pattern: If the executing plugin's level < H, then high-integrity
    state (plugins at level >= H, kernel security fields) is unchanged.
-/

/--
Rule: plugin_internal preserves high-integrity when plugin is low-integrity.
A low-integrity plugin's internal execution doesn't affect high-integrity state.
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_integrity_rule {s s' : State}
    (H : IntegrityLevel)
    (pid : PluginId) (pi : PluginInternal)
    (hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s')
    (h_low_int : (s.plugins pid).level < H) :
    high_integrity_preserved H s s' := by
  constructor
  -- High-integrity plugins unchanged
  · intro pid' h_high
    by_cases h_eq : pid' = pid
    · -- pid' = pid: level of pid < H contradicts h_high (level >= H)
      subst h_eq
      exfalso
      exact absurd h_high (not_le_of_gt h_low_int)
    · -- pid' <> pid: frame condition
      exact plugin_internal_frame pid pi s s' hexec pid' h_eq
  -- Kernel hmacKey and policy preserved
  · intro _
    have h_kernel := (plugin_internal_comprehensive_frame pid pi s s' hexec).1
    exact ⟨by rw [h_kernel], by rw [h_kernel]⟩

/--
Rule: host_call preserves high-integrity when caller is low-integrity.
A low-integrity caller's host call doesn't affect high-integrity state.
-/
@[step_rule Step.host_call]
theorem host_call_integrity_rule {s s' : State}
    (H : IntegrityLevel)
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (_hparse : hostcall_action hc = some a)
    (_hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_low_int : (s.plugins hc.caller).level < H) :
    high_integrity_preserved H s s' := by
  constructor
  -- High-integrity plugins unchanged
  · intro pid' h_high
    by_cases h_eq : pid' = hc.caller
    · -- pid' = caller: level < H contradicts h_high
      subst h_eq
      exfalso
      exact absurd h_high (not_le_of_gt h_low_int)
    · -- pid' <> caller: frame condition
      exact host_call_plugin_frame hc a auth hr s s' hexec pid' h_eq
  -- Kernel hmacKey and policy preserved
  · intro _
    exact ⟨host_call_hmacKey_unchanged hc a auth hr s s' hexec,
           host_call_policy_unchanged hc a auth hr s s' hexec⟩

/--
Rule: kernel_internal cannot be low-integrity (kernel is Secret level).
This rule is for completeness - kernel is at max level so this case
never applies for H <= Secret.
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_integrity_rule {s s' : State}
    (H : IntegrityLevel)
    (op : KernelOp) (_ : KernelExecInternal op s s')
    (h_low_int : SecurityLevel.Secret < H) :
    high_integrity_preserved H s s' := by
  -- Kernel is at Secret level (max), so Secret < H is impossible
  exfalso
  have h_max : H <= SecurityLevel.Secret := SecurityLevel.le_top H
  exact absurd h_low_int (not_lt_of_ge h_max)

/-! =========== PART 3: LABELS NO-DOWNGRADE RULES ===========

    These rules prove that non-declassify steps preserve labels_no_downgrade.
    This property is used in the TINI proof to show transitivity of low-equivalence.

    Pattern: For non-declassify steps, plugin and resource levels never decrease.
-/

/--
Rule: plugin_internal preserves labels (level unchanged).
-/
@[step_rule Step.plugin_internal]
theorem plugin_internal_labels_rule {s s' : State}
    (pid : PluginId) (pi : PluginInternal)
    (_hpre : plugin_internal_pre pid pi s)
    (hexec : PluginExecInternal pid pi s s') :
    labels_no_downgrade s s' := by
  constructor
  -- Plugin levels
  · intro pid'
    by_cases h_eq : pid' = pid
    · -- pid' = pid: level is preserved exactly
      rw [h_eq]
      exact le_of_eq (plugin_internal_level_preserved pid pi s s' hexec).symm
    · -- pid' <> pid: unchanged by frame
      have : s'.plugins pid' = s.plugins pid' :=
        plugin_internal_frame pid pi s s' hexec pid' h_eq
      simp only [this, le_refl]
  -- Resource levels
  · intro rid
    have : s'.resources = s.resources := plugin_internal_resources_unchanged pid pi s s' hexec
    simp only [this, le_refl]

/--
Rule: host_call (non-declassify) preserves labels.
-/
@[step_rule Step.host_call]
theorem host_call_labels_rule {s s' : State}
    (hc : HostCall) (a : Action) (auth : Authorized s a)
    (hr : HostResult) (_hparse : hostcall_action hc = some a)
    (_hpre : host_call_pre hc s)
    (hexec : KernelExecHost hc a auth hr s s')
    (h_not_declass : hc.function ≠ .declassify) :
    labels_no_downgrade s s' := by
  constructor
  -- Plugin levels
  · intro pid
    by_cases h_eq : pid = hc.caller
    · subst h_eq
      exact le_of_eq (host_call_caller_level_preserved hc a auth hr s s' h_not_declass hexec).symm
    · have : s'.plugins pid = s.plugins pid :=
        host_call_plugin_frame hc a auth hr s s' hexec pid h_eq
      simp only [this, le_refl]
  -- Resource levels
  · intro rid
    have : s'.resources = s.resources := host_call_resources_unchanged hc a auth hr s s' hexec
    simp only [this, le_refl]

/--
Rule: kernel_internal preserves labels (no changes to plugins/resources).
-/
@[step_rule Step.kernel_internal]
theorem kernel_internal_labels_rule {s s' : State}
    (op : KernelOp) (hexec : KernelExecInternal op s s') :
    labels_no_downgrade s s' := by
  cases op with
  | time_tick =>
    have ⟨_, h_plugins, _⟩ := time_tick_only_time s s' hexec
    constructor
    · intro pid; simp only [congrFun h_plugins pid, le_refl]
    · intro rid
      have := (time_tick_comprehensive_frame s s' hexec).2.2.2.1
      simp only [congrFun this rid, le_refl]
  | route_one dst =>
    constructor
    · intro pid
      simp only [congrFun (route_one_memory_unchanged dst s s' hexec) pid, le_refl]
    · intro rid
      simp only [congrFun (route_one_resource_unchanged dst s s' hexec) rid, le_refl]
  | workflow_tick wid =>
    constructor
    · intro pid
      simp only [congrFun (workflow_tick_plugins_unchanged wid s s' hexec) pid, le_refl]
    · intro rid
      simp only [congrFun (workflow_tick_resources_unchanged wid s s' hexec) rid, le_refl]
  | unblock_send dst =>
    constructor
    · intro pid
      simp only [congrFun (unblock_send_plugins_unchanged dst s s' hexec) pid, le_refl]
    · intro rid
      simp only [congrFun (unblock_send_resources_unchanged dst s s' hexec) rid, le_refl]

/-! =========== PART 4: COMBINED STEP PRESERVATION THEOREMS ===========

    These use step_cases to provide automated proofs.
-/

/--
Theorem: Any step preserves low-equivalence when high.
Combines all confinement rules using step_cases.
-/
theorem step_confinement_auto {s s' : State} (L : SecurityLevel) (st : Step s s')
    (h_high : is_high_step L st) :
    low_equivalent_left L s s' := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    have h_level : (s.plugins pid).level > L := by
      simp only [is_high_step, step_level, Step.level, Step.subject] at h_high
      exact h_high
    exact plugin_internal_confinement_rule L pid pi hpre hexec h_level
  case host_call hc a auth hr hparse hpre hexec =>
    have h_level : (s.plugins hc.caller).level > L := by
      simp only [is_high_step, step_level, Step.level, Step.subject] at h_high
      exact h_high
    exact host_call_confinement_rule L hc a auth hr hparse hpre hexec h_level
  case kernel_internal op hexec =>
    exact kernel_internal_confinement_rule L op hexec

/--
Theorem: Any non-declassify step preserves labels.
Combines all label rules using step_cases.
-/
theorem step_labels_no_downgrade_auto {s s' : State} (st : Step s s')
    (h_not_declass : st.is_declassify = false) :
    labels_no_downgrade s s' := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    exact plugin_internal_labels_rule pid pi hpre hexec
  case host_call hc a auth hr hparse hpre hexec =>
    have h_not_func : hc.function ≠ .declassify := by
      simp only [Step.is_declassify] at h_not_declass
      exact fun h => by simp [h] at h_not_declass
    exact host_call_labels_rule hc a auth hr hparse hpre hexec h_not_func
  case kernel_internal op hexec =>
    exact kernel_internal_labels_rule op hexec

/--
Theorem: Low-integrity steps preserve high-integrity state.
Combines all integrity rules using step_cases.
-/
theorem step_integrity_confinement_auto {s s' : State} (H : IntegrityLevel) (st : Step s s')
    (h_low_int : step_integrity st < H) :
    high_integrity_preserved H s s' := by
  step_cases st
  case plugin_internal pid pi hpre hexec =>
    have h_level : (s.plugins pid).level < H := by
      simp only [step_integrity, Step.level, Step.subject] at h_low_int
      exact h_low_int
    exact plugin_internal_integrity_rule H pid pi hpre hexec h_level
  case host_call hc a auth hr hparse hpre hexec =>
    have h_level : (s.plugins hc.caller).level < H := by
      simp only [step_integrity, Step.level, Step.subject] at h_low_int
      exact h_low_int
    exact host_call_integrity_rule H hc a auth hr hparse hpre hexec h_level
  case kernel_internal op hexec =>
    -- Kernel is at Secret level, so step_integrity = Secret < H is impossible
    simp only [step_integrity, Step.level, Step.subject] at h_low_int
    exfalso
    have h_max : H <= SecurityLevel.Secret := SecurityLevel.le_top H
    exact absurd h_low_int (not_lt_of_ge h_max)

/-! =========== SUMMARY ===========

STEP RULES PROVIDED:

Confidentiality (step_confinement):
- plugin_internal_confinement_rule: High plugin preserves low-equiv
- host_call_confinement_rule: High caller preserves low-equiv
- kernel_internal_confinement_rule: Kernel preserves low-equiv (always)

Integrity (integrity_confinement):
- plugin_internal_integrity_rule: Low-integrity plugin preserves high-integrity
- host_call_integrity_rule: Low-integrity caller preserves high-integrity
- kernel_internal_integrity_rule: Kernel is max level (vacuous case)

Labels (labels_no_downgrade):
- plugin_internal_labels_rule: Plugin internal preserves labels
- host_call_labels_rule: Non-declassify host call preserves labels
- kernel_internal_labels_rule: Kernel ops preserve labels

COMBINED THEOREMS:
- step_confinement_auto: Automated step_cases for confidentiality
- step_labels_no_downgrade_auto: Automated step_cases for labels
- step_integrity_confinement_auto: Automated step_cases for integrity

USAGE:
  step_cases st
  case plugin_internal pid pi hpre hexec => <apply relevant rule>
  case host_call hc a auth hr hparse hpre hexec => <apply relevant rule>
  case kernel_internal op hexec => <apply relevant rule>
-/

end Lion.NoninterferenceRules
