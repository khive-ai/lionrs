/-
Lion/Composition/AttackCoverage.lean
=====================================

Attack Coverage Theorem - Machine-checked traceability from attack classes
to mitigating properties in SystemInvariant.

This module provides:
1. Attack class taxonomy covering major attack categories
2. Mitigates function mapping attacks to required properties
3. Coverage theorem proving SystemInvariant mitigates all attack classes
4. Traceability matrix documentation

Out of scope (documented explicitly):
- Timing/power/cache side channels (requires microarchitectural model)
- Supply chain / malicious dependencies (requires build provenance)
- Social engineering (human factor)
- Hardware fault / physical tampering (fault model)
- Livelock/starvation (requires fairness model)
-/

import Lion.Composition.SystemInvariant

namespace Lion

/-! =========== ATTACK CLASS TAXONOMY =========== -/

/--
High-level attack classes used for security traceability.

Each class represents a category of attacks that share common mitigations.
The taxonomy is designed to map cleanly to SystemInvariant properties.
-/
inductive AttackClass where
  /-- Buffer overflow, use-after-free, cross-plugin memory corruption -/
  | memory_corruption
  /-- Capability forgery, rights amplification through delegation -/
  | privilege_escalation
  /-- Unauthorized access, revoked capability use, policy violations -/
  | policy_bypass
  /-- Mailbox overflow, workflow starvation, resource exhaustion -/
  | resource_exhaustion
  /-- Deadlock (within model), livelock (needs fairness - partial) -/
  | deadlock_livelock
  /-- Component isolation breach, covert channels, composition attacks -/
  | composition_attack
deriving DecidableEq, Repr

/-! =========== MITIGATES MAPPING =========== -/

/--
The properties required to mitigate each attack class.

This is a Prop-level mapping so we can prove it directly from SystemInvariant.
Each attack class maps to the conjunction of properties that prevent it.
-/
def Mitigates (attack : AttackClass) (s : State) : Prop :=
  match attack with
  | .memory_corruption =>
      -- Spatial safety (MemoryIsolated) + temporal safety (TemporalSafe)
      MemoryIsolated s ∧ TemporalSafe s
  | .privilege_escalation =>
      -- Caps can't be forged + caps stay within authority bounds
      CapUnforgeable s ∧ CapConfined s
  | .policy_bypass =>
      -- Policy decisions are sound + revocation is effective
      PolicySound s ∧ CapRevocable s
  | .resource_exhaustion =>
      -- Messages can be delivered + workflows have work + progress possible
      MessageDeliveryPossible s ∧ AllWorkflowsHaveWork s ∧ WorkflowProgressPossible s
  | .deadlock_livelock =>
      -- Deadlock freedom (livelock needs fairness model - not fully covered)
      DeadlockFree s
  | .composition_attack =>
      -- Step confinement (noninterference) + memory isolation
      StepConfinementHolds s ∧ MemoryIsolated s

/-! =========== ATTACK COVERAGE THEOREM =========== -/

/--
**Attack Coverage Theorem: Machine-checked traceability**

If SystemInvariant holds, then every attack class is mitigated.

This is the formal link between "we proved SystemInvariant" and
"we have mitigations for every major attack class in our threat model."

The theorem is intentionally simple - it just projects from the
SystemInvariant bundle. The value is in the machine-checked guarantee
that the mapping is complete and correct.
-/
theorem attack_coverage_of_systemInvariant (s : State)
    (h : SystemInvariant s) :
    ∀ attack : AttackClass, Mitigates attack s := by
  intro attack
  cases attack <;> simp only [Mitigates]
  · -- memory_corruption
    exact ⟨h.memory_isolated, h.temporal_safe⟩
  · -- privilege_escalation
    exact ⟨h.cap_unforgeable, h.cap_confined⟩
  · -- policy_bypass
    exact ⟨h.policy_sound, h.cap_revocable⟩
  · -- resource_exhaustion
    exact ⟨h.message_delivery, h.workflows_have_work, h.workflow_progress⟩
  · -- deadlock_livelock
    exact h.deadlock_free
  · -- composition_attack
    exact ⟨h.step_confinement, h.memory_isolated⟩

/-! =========== HUMAN-READABLE TRACEABILITY =========== -/

/--
Human-readable list of mitigating properties for each attack class.
Useful for documentation, reports, and audits.
-/
def mitigationNames : AttackClass → List String
  | .memory_corruption    => ["MemoryIsolated", "TemporalSafe"]
  | .privilege_escalation => ["CapUnforgeable", "CapConfined"]
  | .policy_bypass        => ["PolicySound", "CapRevocable"]
  | .resource_exhaustion  => ["MessageDeliveryPossible", "AllWorkflowsHaveWork", "WorkflowProgressPossible"]
  | .deadlock_livelock    => ["DeadlockFree (deadlock only; livelock needs fairness)"]
  | .composition_attack   => ["StepConfinementHolds", "MemoryIsolated"]

/--
Human-readable description of each attack class.
-/
def attackDescription : AttackClass → String
  | .memory_corruption    => "Buffer overflow, use-after-free, cross-plugin memory corruption"
  | .privilege_escalation => "Capability forgery, rights amplification through delegation"
  | .policy_bypass        => "Unauthorized access, revoked capability use, policy violations"
  | .resource_exhaustion  => "Mailbox overflow, workflow starvation, resource exhaustion"
  | .deadlock_livelock    => "Deadlock (within model), livelock (needs fairness model)"
  | .composition_attack   => "Component isolation breach, covert channels, composition attacks"

/-! =========== OUT OF SCOPE =========== -/

/--
Attack classes explicitly out of scope for the current formal model.

These require additional modeling that is beyond the current state-transition
proof infrastructure:

1. **Timing/power/cache side channels**: Requires constant-time analysis
   and microarchitectural model

2. **Supply chain attacks**: Requires build/provenance argument, not
   state-transition proof

3. **Social engineering**: Human factor, not formal model

4. **Hardware faults**: Requires fault model and physical security

5. **Livelock/starvation**: Requires fairness/liveness model with
   infinite traces (current proofs are safety properties only)
-/
inductive OutOfScopeAttack where
  | timing_side_channel
  | power_side_channel
  | cache_side_channel
  | supply_chain
  | social_engineering
  | hardware_fault
  | physical_tampering
  | livelock
  | starvation
deriving DecidableEq, Repr

end Lion
