# 5.4 Implementation Roadmap

_[Previous: End-to-End Correctness](ch5-3-end-to-end-correctness.md) |
[Next: Future Research Directions](ch5-5-future-research.md)_

---

This section provides a comprehensive roadmap for translating the formal
specifications into a working Lion ecosystem implementation, ensuring tight
correspondence between theory and practice.

## 5.4.1 Theory-to-Practice Mapping

All formal components verified in previous chapters correspond directly to
implementation modules, maintaining traceability from mathematical proofs to
executable code.

### Formal Component Correspondence

| Formal Component             | Implementation Module   | Verification Method             |
| ---------------------------- | ----------------------- | ------------------------------- |
| Category Theory Model (Ch 1) | Rust trait hierarchy    | Type system correspondence      |
| Capability System (Ch 2)     | `lion_capability` crate | Cryptographic implementation    |
| Memory Isolation (Ch 3)      | `lion_isolation` crate  | WebAssembly runtime integration |
| Actor Concurrency (Ch 3)     | `lion_actor` crate      | Message-passing verification    |
| Policy Engine (Ch 4)         | `lion_policy` crate     | DSL implementation              |
| Workflow Manager (Ch 4/5)    | `lion_workflow` crate   | DAG execution engine            |

### Correspondence Maintenance Strategies

#### Formal Contracts in Code

```rust
// Example: Capability handle with formal correspondence
#[derive(Debug, Clone)]
pub struct CapabilityHandle {
    // Corresponds to Definition 4.3: (authority, permissions, constraints, delegation_depth)
    authority: ResourceId,
    permissions: PermissionSet,
    constraints: ConstraintSet,
    delegation_depth: u32,
    
    // Cryptographic binding (Implementation of Theorem 2.1 proof)
    cryptographic_binding: Hmac<Sha256>,
    plugin_binding: PluginId,
}

impl CapabilityHandle {
    // Corresponds to κ(c,a) from Definition 4.5
    pub fn authorizes(&self, action: &Action) -> bool {
        // Implementation matches formal verification proof steps
        self.permissions.contains(&action.required_permission()) &&
        self.constraints.evaluate(&action.context()) &&
        self.verify_cryptographic_binding()
    }
}
```

#### Type System Enforcement

```rust
// Rust types reflect formal invariants
use std::marker::PhantomData;

// Capability can only be created by Core (corresponds to Lemma 2.4.1)
pub struct Capability<State> {
    inner: CapabilityInner,
    _state: PhantomData<State>,
}

pub struct Granted;
pub struct Revoked;

// Type system prevents use of revoked capabilities
impl Capability<Granted> {
    pub fn use_capability(&self, action: Action) -> Result<Response> {
        // Safe to use
    }
}

// Revoked capabilities cannot be used (compile-time prevention)
impl Capability<Revoked> {
    // No use_capability method available
}
```

#### Runtime Assertions

```rust
// Runtime verification of formal properties
fn verify_capability_integrity(cap: &CapabilityHandle, plugin_id: PluginId) {
    // Corresponds to Step 2 of Theorem 3.1 proof
    let expected_binding = crypto::hmac(plugin_id.as_bytes(), cap.handle_bytes());
    assert_eq!(cap.cryptographic_binding, expected_binding, 
               "Capability integrity violation - formal property violated");
}
```

## 5.4.2 Rust Implementation Architecture

The Lion ecosystem is implemented as a multi-crate Rust project with clear
module boundaries corresponding to formal components.

### Core Crate Structure

```
lion/
├── lion_core/              # Central orchestration (Chapter 1 category)
│   ├── src/
│   │   ├── orchestrator.rs # Central coordinator
│   │   ├── types.rs        # Core type definitions
│   │   └── category.rs     # Category theory abstractions
│   └── Cargo.toml
├── lion_capability/        # Capability management (Chapter 2)
│   ├── src/
│   │   ├── manager.rs      # Grant/verify implementation
│   │   ├── handle.rs       # Cryptographic handles
│   │   └── attenuation.rs  # Delegation with constraints
│   └── Cargo.toml
├── lion_isolation/         # WebAssembly isolation (Chapter 3)
│   ├── src/
│   │   ├── enforcer.rs     # Memory isolation implementation
│   │   ├── wasm_runtime.rs # Wasmtime integration
│   │   └── resource.rs     # Resource limit enforcement
│   └── Cargo.toml
├── lion_actor/             # Actor concurrency (Chapter 3)
│   ├── src/
│   │   ├── system.rs       # Actor system implementation
│   │   ├── mailbox.rs      # Message passing
│   │   └── supervisor.rs   # Hierarchical supervision
│   └── Cargo.toml
├── lion_policy/            # Policy evaluation (Chapter 4)
│   ├── src/
│   │   ├── engine.rs       # Evaluation algorithm
│   │   ├── dsl.rs          # Policy language parser
│   │   └── composition.rs  # Algebraic operators
│   └── Cargo.toml
├── lion_workflow/          # Workflow orchestration (Chapter 4/5)
│   ├── src/
│   │   ├── dag.rs          # DAG representation
│   │   ├── executor.rs     # Execution engine
│   │   └── retry.rs        # Error handling policies
│   └── Cargo.toml
└── verification/           # Formal verification integration
    ├── lean/              # Lean4 proof files
    ├── tla/               # TLA+ specifications
    └── tests/             # Property-based tests
```

### Crate Dependency Graph

The dependency relationships mirror the formal composition hierarchy:

```
lion_core
├─→ lion_capability (uses capability management)
├─→ lion_isolation (uses memory isolation)
├─→ lion_actor (uses concurrency model)
├─→ lion_policy (uses authorization)
└─→ lion_workflow (uses orchestration)

lion_workflow
├─→ lion_actor (workflow steps as actors)
├─→ lion_policy (step authorization)
└─→ lion_capability (resource access)

lion_policy
└─→ lion_capability (capability-based conditions)

lion_isolation
└─→ lion_capability (resource access control)
```

### Critical Function Implementation

#### Capability Grant Function

```rust
// Implementation corresponds exactly to Theorem 2.1 proof
impl CapabilityManager {
    pub fn grant_capability(
        &self, 
        plugin_id: PluginId, 
        resource: ResourceId,
        permissions: PermissionSet
    ) -> Result<CapabilityHandle> {
        // Step 1: Policy authorization (Theorem 5.1)
        if !self.policy_engine.authorize(plugin_id, resource, Action::Grant) {
            return Err(CapabilityError::PolicyDenied);
        }
        
        // Step 2: Create cryptographically bound handle (Theorem 2.1 proof)
        let handle_id = self.allocate_handle_id();
        let binding = crypto::hmac(
            plugin_id.as_bytes(), 
            handle_id.to_bytes()
        );
        
        let handle = CapabilityHandle {
            authority: resource,
            permissions,
            constraints: ConstraintSet::default(),
            delegation_depth: 0,
            cryptographic_binding: binding,
            plugin_binding: plugin_id,
        };
        
        // Step 3: Store in capability table
        self.capability_table.insert((plugin_id, handle_id), handle.clone());
        
        Ok(handle)
    }
}
```

#### Policy Evaluation Engine

```rust
// Implementation corresponds to Chapter 4 evaluation semantics
impl PolicyEngine {
    pub fn evaluate(
        &self, 
        policy: &Policy, 
        action: &Action, 
        capability: &Option<CapabilityHandle>
    ) -> Decision {
        match policy {
            // Base cases (corresponds to Theorem 4.1 proof base cases)
            Policy::Atomic(condition) => self.evaluate_condition(condition, action),
            Policy::CapabilityRef(cap_req) => {
                capability.as_ref()
                    .map(|cap| if cap.authorizes(action) { 
                        Decision::Permit 
                    } else { 
                        Decision::Deny 
                    })
                    .unwrap_or(Decision::Deny)
            },
            Policy::Constant(decision) => *decision,
            
            // Inductive cases (corresponds to Theorem 4.1 inductive cases)
            Policy::Conjunction(p1, p2) => {
                let r1 = self.evaluate(p1, action, capability);
                let r2 = self.evaluate(p2, action, capability);
                self.combine_conjunction(r1, r2)
            },
            Policy::Disjunction(p1, p2) => {
                let r1 = self.evaluate(p1, action, capability);
                let r2 = self.evaluate(p2, action, capability);
                self.combine_disjunction(r1, r2)
            },
            // ... other operators following formal semantics
        }
    }
}
```

## 5.4.3 WebAssembly Integration Strategy

The isolation implementation leverages Wasmtime for verified memory isolation
corresponding to Theorem 3.1.

### Isolation Architecture

```rust
use wasmtime::*;

pub struct IsolationEnforcer {
    engine: Engine,
    instances: HashMap<PluginId, Instance>,
    capability_manager: Arc<CapabilityManager>,
}

impl IsolationEnforcer {
    pub fn load_plugin(
        &mut self, 
        plugin_id: PluginId, 
        wasm_bytes: &[u8]
    ) -> Result<()> {
        // Configure Wasmtime for isolation (implements Theorem 3.1)
        let mut config = Config::new();
        config.memory_init_cow(false);  // Prevent memory sharing
        config.max_wasm_stack(1024 * 1024);  // Stack limit
        
        let engine = Engine::new(&config)?;
        let module = Module::new(&engine, wasm_bytes)?;
        
        // Create isolated instance with capability-based imports
        let mut linker = Linker::new(&engine);
        self.register_capability_functions(&mut linker, plugin_id)?;
        
        let instance = linker.instantiate(&module)?;
        
        // Memory isolation invariant: instance.memory ∩ host.memory = ∅
        self.verify_memory_isolation(&instance)?;
        
        self.instances.insert(plugin_id, instance);
        Ok(())
    }
    
    fn register_capability_functions(
        &self, 
        linker: &mut Linker<()>, 
        plugin_id: PluginId
    ) -> Result<()> {
        // Import functions that require capability verification
        linker.func_wrap("env", "open_file", 
            move |handle: u64, path_ptr: u32, path_len: u32| -> u32 {
                // Capability verification before host call
                let cap_handle = CapabilityHandle::from_u64(handle);
                if !self.capability_manager.verify(plugin_id, &cap_handle) {
                    return ERROR_UNAUTHORIZED;
                }
                
                // Safe execution with verified capability
                self.host_open_file(path_ptr, path_len)
            }
        )?;
        
        Ok(())
    }
}
```

### Resource Bounds Implementation

```rust
// Implements resource bounds from Theorem 5.2
struct ResourceLimits {
    max_memory: usize,
    max_fuel: u64,        // CPU instruction limit
    max_duration: Duration,
}

impl IsolationEnforcer {
    fn execute_with_limits(
        &self,
        plugin_id: PluginId,
        function: &str,
        args: &[Val],
        limits: ResourceLimits
    ) -> Result<Vec<Val>> {
        let instance = self.instances.get(&plugin_id)
            .ok_or(IsolationError::PluginNotFound)?;
        
        // Set fuel limit (CPU bound)
        instance.add_fuel(limits.max_fuel)?;
        
        // Set memory limit
        let memory = instance.get_memory("memory")
            .ok_or(IsolationError::NoMemory)?;
        memory.set_max_size(limits.max_memory)?;
        
        // Execute with timeout (duration bound)
        let start_time = Instant::now();
        let result = instance.get_func(function)
            .ok_or(IsolationError::FunctionNotFound)?
            .call(args);
        
        if start_time.elapsed() > limits.max_duration {
            return Err(IsolationError::TimeoutExceeded);
        }
        
        result.map_err(|e| {
            match e {
                wasmtime::Error::FuelExhausted => IsolationError::CpuLimitExceeded,
                wasmtime::Error::MemoryOutOfBounds => IsolationError::MemoryLimitExceeded,
                _ => IsolationError::ExecutionError(e),
            }
        })
    }
}
```

## 5.4.4 Verification and Testing Framework

The implementation maintains correspondence with formal specifications through
multi-level verification.

### Property-Based Testing

```rust
use proptest::prelude::*;

// Test capability confinement (corresponds to Theorem 2.1)
proptest! {
    #[test]
    fn capability_confinement_property(
        plugin1_id: PluginId,
        plugin2_id: PluginId,
        resource: ResourceId
    ) {
        prop_assume!(plugin1_id != plugin2_id);
        
        let manager = CapabilityManager::new();
        
        // Grant capability to plugin1
        let cap = manager.grant_capability(plugin1_id, resource, 
                                         PermissionSet::all())?;
        
        // Verify plugin2 cannot use plugin1's capability
        let verification_result = manager.verify_capability(plugin2_id, &cap);
        
        prop_assert!(verification_result.is_err(), 
                    "Capability confinement violated: plugin2 used plugin1's capability");
    }
}

// Test memory isolation (corresponds to Theorem 3.1)
proptest! {
    #[test]
    fn memory_isolation_property(
        plugin1_code: Vec<u8>,
        plugin2_code: Vec<u8>
    ) {
        let mut enforcer = IsolationEnforcer::new();
        
        // Load two plugins
        enforcer.load_plugin(PluginId(1), &plugin1_code)?;
        enforcer.load_plugin(PluginId(2), &plugin2_code)?;
        
        // Execute both plugins and verify memory isolation
        let memory1 = enforcer.get_plugin_memory(PluginId(1));
        let memory2 = enforcer.get_plugin_memory(PluginId(2));
        
        // Memory spaces must be disjoint
        prop_assert!(memory1.address_range().is_disjoint(&memory2.address_range()),
                    "Memory isolation violated: overlapping address spaces");
    }
}
```

### Lean Integration Testing

```bash
#!/bin/bash
# CI script for continuous verification

# Run Lean proofs
echo "Verifying Lean proofs..."
lean --make verification/lean/
if [ $? -ne 0 ]; then
    echo "Lean verification failed"
    exit 1
fi

# Run TLA+ model checking
echo "Model checking TLA+ specifications..."
tla+ check verification/tla/LionSystem.tla
if [ $? -ne 0 ]; then
    echo "TLA+ verification failed"
    exit 1
fi

# Run property-based tests
echo "Running property-based tests..."
cargo test --features=proptest
if [ $? -ne 0 ]; then
    echo "Property tests failed"
    exit 1
fi

echo "All verification passed"
```

### Formal Correspondence Checks

```rust
// Automated checks that implementation matches formal specifications
#[cfg(test)]
mod formal_correspondence {
    use super::*;
    
    #[test]
    fn policy_evaluation_matches_formal_semantics() {
        // Test case derived from Theorem 4.1 proof
        let policy = Policy::Conjunction(
            Box::new(Policy::Atomic(Condition::SubjectEquals("alice".to_string()))),
            Box::new(Policy::Atomic(Condition::TimeInRange(9..17)))
        );
        
        let action = Action {
            subject: "alice".to_string(),
            resource: "file.txt".to_string(),
            operation: "read".to_string(),
            context: Context { hour: 10 },
        };
        
        let result = PolicyEngine::new().evaluate(&policy, &action, &None);
        
        // Should permit based on formal semantics
        assert_eq!(result, Decision::Permit, 
                  "Implementation deviates from formal semantics");
    }
    
    #[test]
    fn workflow_termination_matches_formal_bounds() {
        // Test case derived from Theorem 5.2
        let workflow = WorkflowBuilder::new()
            .add_step("validate", 3) // max 3 retries
            .add_step("transform", 1)
            .add_step("store", 2)
            .with_timeout(Duration::from_secs(60))
            .build();
        
        let start_time = Instant::now();
        let result = WorkflowExecutor::new().execute(workflow);
        let duration = start_time.elapsed();
        
        // Must complete within formal bounds
        assert!(duration < Duration::from_secs(60), 
               "Workflow exceeded formal termination bound");
        
        // Must reach definitive state
        assert!(matches!(result, WorkflowResult::Completed(_) | WorkflowResult::Failed(_)),
               "Workflow did not reach definitive termination state");
    }
}
```

### Continuous Integration Pipeline

```yaml
# .github/workflows/verification.yml
name: Lion Formal Verification

on: [push, pull_request]

jobs:
  formal-verification:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2

      - name: Install Lean 4
        run: |
          curl -sSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
          echo "$HOME/.elan/bin" >> $GITHUB_PATH

      - name: Install TLA+
        run: |
          wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
          sudo mv tla2tools.jar /usr/local/bin/

      - name: Verify Lean Proofs
        run: lean --make verification/lean/

      - name: Model Check TLA+ Specs
        run: java -jar /usr/local/bin/tla2tools.jar -config verification/tla/LionSystem.cfg verification/tla/LionSystem.tla

      - name: Build and Test Implementation
        run: |
          cargo build --all-features
          cargo test --all-features
          cargo test --features=proptest -- --ignored

      - name: Formal Correspondence Check
        run: cargo test formal_correspondence
```

This comprehensive implementation roadmap ensures that the Lion ecosystem can be
built with confidence that the running code corresponds to the formally verified
specifications, maintaining end-to-end correctness from mathematical proofs to
production deployment.

---

_Next: [Future Research Directions](ch5-5-future-research.md)_
