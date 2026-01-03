/-
Lion/Core/RuntimeIsolation.lean
================================

Runtime Isolation Bundle: Single axiom for WASM sandbox + key protection.

This bundles two related trust assumptions:
1. WASM sandbox memory bounds enforcement
2. HMAC key protection in kernel memory

Combined into a single conceptual trust: "the runtime isolates plugins from kernel secrets."
-/

import Lion.State.State
import Lion.Step.PluginInternal

namespace Lion

/-! =========== RUNTIME ISOLATION (BUNDLED) =========== -/

/--
Memory region classification for isolation proofs.
-/
inductive MemRegion where
  | kernel                    -- Kernel's protected memory
  | plugin (pid : PluginId)   -- Plugin's linear memory
deriving DecidableEq, Repr

/-- Address belongs to a memory region -/
def addr_in_region (addr : MemAddr) : MemRegion → Prop
  | .kernel => addr < 0x1000000  -- First 16MB is kernel space
  | .plugin pid => addr ≥ 0x1000000 + pid * 0x100000

/-- The HMAC key is stored in kernel memory -/
opaque hmac_key_addr : MemAddr

/--
**Runtime Isolation Bundle**

Single trust assumption for the runtime environment:
1. WASM sandbox enforces memory bounds on all plugin operations
2. HMAC key is protected in kernel memory region

Trust justification:
- WASM linear memory model provides bounds checking on all load/store
- Wasmtime implements this correctly (audited, production-tested)
- Kernel memory region is inaccessible from plugin code (architectural)
-/
structure RuntimeIsolation : Prop where
  /-- WASM sandbox enforces memory bounds on all plugin operations -/
  wasm_bounds : ∀ pid pi s s' (_hpre : plugin_internal_pre pid pi s),
    PluginExecInternal pid pi s s' →
    ∀ addr, (s'.plugins pid).memory.bytes.contains addr →
      addr < (s'.plugins pid).memory.bounds
  /-- HMAC key is stored in kernel memory region -/
  key_in_kernel : addr_in_region hmac_key_addr .kernel

/-- Single runtime isolation axiom -/
axiom runtime_isolation : RuntimeIsolation

/-! =========== RE-EXPORTED THEOREMS =========== -/

/-- WASM bounds enforcement (re-export from bundle) -/
theorem plugin_internal_respects_bounds :
  ∀ pid pi s s' (_hpre : plugin_internal_pre pid pi s) (h : PluginExecInternal pid pi s s'),
    ∀ addr, (s'.plugins pid).memory.bytes.contains addr →
      addr < (s'.plugins pid).memory.bounds :=
  runtime_isolation.wasm_bounds

/-- HMAC key in kernel region (re-export from bundle) -/
theorem hmac_key_in_kernel : addr_in_region hmac_key_addr .kernel :=
  runtime_isolation.key_in_kernel

end Lion
