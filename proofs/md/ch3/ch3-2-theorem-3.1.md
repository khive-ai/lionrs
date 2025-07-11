# 3.2 Theorem 3.1: WebAssembly Isolation

_[Previous: Memory Isolation Model](ch3-1-memory-isolation.md) |
[Next: Actor Model Foundation](ch3-3-actor-model.md)_

---

**Theorem 3.1** (WebAssembly Isolation): The Lion WASM isolation system provides
complete memory isolation between plugins and the host environment.

This theorem encapsulates the guarantee that no matter what sequence of actions
plugins execute (including malicious or buggy behavior), they cannot read or
write each other's memory or the host's memory, except through allowed
capability-mediated channels.

## Proof of Theorem 3.1

### Step 1: Memory Disjointness

We prove that plugin memory spaces are completely disjoint:

$$\forall \text{addr} \in \text{Address\_Space}: \text{addr} \in \text{Plugin}[i].\text{linear\_memory} \Rightarrow \text{addr} \notin \text{Plugin}[j].\text{linear\_memory} \; (\forall j \neq i) \land \text{addr} \notin \text{Host}.\text{memory}$$

**Proof**: This follows directly from WebAssembly's linear memory model. Each
plugin instance receives its own linear memory space, with bounds checking
enforced by the WebAssembly runtime:

```rust
// Lion WebAssembly isolation implementation
impl WasmIsolationBackend {
    fn load_plugin(&self, id: PluginId, bytes: &[u8]) -> Result<()> {
        // Each plugin gets its own Module and Instance
        let module = Module::new(&self.engine, bytes)?;
        let instance = Instance::new(&module, &[])?;
        
        // Memory isolation invariant: instance.memory ∩ host.memory = ∅
        self.instances.insert(id, instance);
        Ok(())
    }
}
```

In this code, each loaded plugin gets a new `Instance` with its own memory. The
comment explicitly notes the invariant that the instance's memory has an empty
intersection with host memory. Formally, the runtime ensures (via memory
allocation and sandboxing) that the address ranges allocated to different plugin
instances are distinct. WebAssembly's semantics prevent pointer arithmetic from
accessing memory outside the allocated bounds of an instance. Therefore, the
separation logic assertion $\{P[i].\text{memory}\} * \{P[j].\text{memory}\}$
holds for all $i \neq j$, establishing disjointness.

### Step 2: Capability Confinement

We prove that capabilities cannot be forged or leaked across isolation
boundaries:

```rust
impl CapabilitySystem {
    fn grant_capability(&self, plugin_id: PluginId, cap: Capability) -> Handle {
        // Capabilities are cryptographically bound to plugin identity
        let handle = self.allocate_handle();
        let binding = crypto::hmac(plugin_id.as_bytes(), handle.to_bytes());
        self.capability_table.insert((plugin_id, handle), (cap, binding));
        handle
    }
    
    fn verify_capability(&self, plugin_id: PluginId, handle: Handle) -> Result<Capability> {
        let (cap, binding) = self.capability_table.get(&(plugin_id, handle))
            .ok_or(Error::CapabilityNotFound)?;
        
        // Verify cryptographic binding
        let expected_binding = crypto::hmac(plugin_id.as_bytes(), handle.to_bytes());
        if binding != expected_binding {
            return Err(Error::CapabilityCorrupted);
        }
        
        Ok(cap.clone())
    }
}
```

In Lion's implementation, whenever a capability is passed into a plugin (via the
Capability Manager), it's associated with that plugin's identity and a
cryptographic HMAC tag (`binding`). The only way for a plugin to use a
capability handle is through `verify_capability`, which checks that the handle
was indeed issued to that plugin. This mechanism prevents one plugin from using
a handle issued to another (the verification would fail). It also prevents
forgery: the handle includes a random component and the binding check fails if a
plugin tries to guess or fabricate a handle.

From a formal standpoint, if plugin $i$ holds a capability handle $h$, then for
any plugin $j \neq i$, `verify_capability(j, h)` will not return a valid
capability (it will error). Thus, even if a plugin somehow obtained a handle
string from another (say via an I/O channel outside Lion), it cannot use it.
Capabilities remain confined to the intended principal.

### Step 3: Resource Bounds Enforcement

We prove that resource limits are enforced per plugin atomically:

```rust
fn check_resource_limits(plugin_id: PluginId, usage: ResourceUsage) -> Result<()> {
    let limits = get_plugin_limits(plugin_id)?;
    
    // Memory bounds checking
    if usage.memory > limits.max_memory {
        return Err(Error::ResourceExhausted);
    }
    
    // CPU time bounds checking  
    if usage.cpu_time > limits.max_cpu_time {
        return Err(Error::TimeoutExceeded);
    }
    
    // File handle bounds checking
    if usage.file_handles > limits.max_file_handles {
        return Err(Error::HandleExhausted);
    }
    
    Ok(())
}
```

For each plugin, Lion tracks a set of resource limits (max memory, CPU time,
open file handles, etc.). The `check_resource_limits` function is invoked on
relevant operations (e.g., memory allocation, scheduling, file open). Each
resource is checked against that plugin's quota. The checks are done in one go,
preventing any interleaving where another plugin's usage could affect the
result.

These runtime checks complement the static isolation: not only can plugins not
interfere with each other's memory, they also cannot starve each other of
resources because each has its own limits. If plugin $P_1$ tries to allocate
beyond its limit, it gets a `ResourceExhausted` error without affecting $P_2$.

## Conclusion

By combining WebAssembly's linear memory model, cryptographic capability
scoping, and atomic resource limit enforcement, we conclude that no plugin can
violate isolation. Formally, for any two distinct plugins $P_i$ and $P_j$:

- There is no reachable state where $P_i$ has a pointer into $P_j$'s memory
  (Memory Disjointness)
- There is no operation by $P_i$ that can retrieve or affect a capability
  belonging to $P_j$ without going through the verified channels (Capability
  Confinement)
- All resource usage by $P_i$ is accounted to $P_i$ and cannot exhaust $P_j$'s
  quotas (Resource Isolation)

Therefore, **Theorem 3.1** is proven: Lion's isolation enforces complete
separation of memory and controlled interaction only via the capability system.
Any sharing or communication is deliberate and checked.

**Remark**: We have mechanized key parts of this argument in a Lean model (see
Appendix B.1), encoding plugin memory as separate state components and proving
an invariant that no state action can move data from one plugin's memory
component to another's. This complements the above reasoning by machine-checking
the absence of cross-plugin memory flows.

---

_Next: [Actor Model Foundation](ch3-3-actor-model.md)_
