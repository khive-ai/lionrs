/-
Lion/Theorems/RuntimeTrustBundle.lean
=====================================

Runtime Trust Bundle: Complete runtime assumptions in a single bundle.

This consolidates all scheduler/runtime assumptions:
1. WASM isolation (from RuntimeIsolation)
2. Low step determinism (scheduler picks unique step)
3. Message delivery fairness (scheduler routes messages)

Combined into a single conceptual trust: "the runtime behaves correctly."
-/

import Lion.Core.RuntimeIsolation
import Lion.Step.Step
import Lion.Theorems.MessageDelivery
import Lion.Theorems.NoninterferenceBase

namespace Lion

open Lion.Noninterference

/-! =========== LOW STEP DETERMINISM =========== -/

/--
**Low Step Determinism**

Low steps from the same source state with the same declassify type
lead to the same destination state.

This encodes deterministic execution of low-observable operations:
- WASM execution is deterministic (given same inputs → same outputs)
- Scheduler picks a unique enabled operation at each state

Trust justification:
- WASM is a deterministic execution model
- Single-threaded scheduler picks one operation at a time
- Low-observable state evolves deterministically

Previously axiom, now bundled into RuntimeTrustBundle.
-/
def LowStepDeterministic : Prop :=
  ∀ (L : SecurityLevel) {s s1 s2 : State} (st1 : Step s s1) (st2 : Step s s2),
    is_low_step L st1 → is_low_step L st2 →
    st1.is_declassify = st2.is_declassify →
    s1 = s2

/-! =========== RUNTIME TRUST BUNDLE =========== -/

/--
**Runtime Trust Bundle**

Complete runtime trust assumptions (conceptual bundle #2):

1. **WASM Isolation**: Plugin memory bounds, key protection
2. **Scheduler Determinism**: Low steps are deterministic
3. **Message Delivery**: Scheduler fairly routes messages

Trust justification:
- Wasmtime provides memory isolation and deterministic execution
- Single-threaded scheduler provides determinism and fairness
- These are all properties of the runtime environment, not the logic

This is one of the 3 true trust bundles:
- Crypto (CryptoTrustBundle)
- Runtime (RuntimeTrustBundle)  ← This bundle
- Correspondence (RuntimeBridge)
-/
structure RuntimeTrustBundle : Prop where
  /-- WASM isolation properties -/
  isolation : RuntimeIsolation
  /-- Low step determinism (scheduler picks unique step) -/
  determinism : LowStepDeterministic
  /-- Message delivery fairness (scheduler routes messages) -/
  delivery : MessageDeliveryAssumptions

/-! =========== LOW STEP DETERMINISM AXIOM =========== -/

/--
**Low Step Determinism Axiom**

This is the scheduler determinism assumption. Previously standalone axiom,
now part of the RuntimeTrustBundle.
-/
axiom low_step_determinism_axiom : LowStepDeterministic

/-! =========== BUNDLE THEOREM =========== -/

/--
**Runtime Trust Bundle (Derived)**

Bundles all runtime assumptions into a single structure.
This is derived from the component axioms (not a new axiom).

Mirrors the pattern used by CryptoTrustBundle.
-/
theorem runtime_trust_bundle : RuntimeTrustBundle where
  isolation := runtime_isolation
  determinism := low_step_determinism_axiom
  delivery := message_delivery_assumptions

/-! =========== RE-EXPORTED THEOREMS =========== -/

/-- Low step determinism (from bundle, main export) -/
theorem low_step_deterministic (L : SecurityLevel) :
    ∀ {s s1 s2 : State} (st1 : Step s s1) (st2 : Step s s2),
      is_low_step L st1 → is_low_step L st2 →
      st1.is_declassify = st2.is_declassify →
      s1 = s2 :=
  low_step_determinism_axiom L

end Lion
