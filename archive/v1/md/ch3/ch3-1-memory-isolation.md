# 3.1 Memory Isolation Model

_[Previous: Abstract](ch3-0-abstract.md) |
[Next: WebAssembly Isolation Theorem](ch3-2-theorem-3.1.md)_

---

## 3.1.1 WebAssembly Separation Logic Foundations

The Lion ecosystem employs WebAssembly's linear memory model as its isolation
foundation. We extend the formal model using Iris-Wasm (a WebAssembly-tailored
separation logic) to provide complete memory isolation between plugins.

**Definition 3.1** (Lion Isolation System): Let $\mathbf{L}$ be the Lion
isolation system with components:

- $\mathbf{W}$: WebAssembly runtime environment
- $\mathbf{P}$: Set of plugin sandboxes $\{P_1, P_2, \ldots, P_n\}$
- $\mathbf{H}$: Host environment with capability system
- $\mathbf{I}$: Controlled interface layer for inter-plugin communication
- $\mathbf{M}$: Memory management system with bounds checking

In this model, each plugin $P_i$ has its own linear memory and can interact with
others only through the interface layer $\mathbf{I}$, which in turn uses
capabilities in $\mathbf{H}$ to mediate actions.

### Separation Logic Invariants

Using Iris-Wasm separation logic, we define the core isolation invariant:

$$\forall i, j \in \text{Plugin\_IDs}, i \neq j: \{P[i].\text{memory}\} * \{P[j].\text{memory}\} * \{\text{Host}.\text{memory}\}$$

Where $*$ denotes separation (disjointness of memory regions). This invariant
ensures that:

1. Plugin memory spaces are completely disjoint
2. Host memory remains isolated from all plugins
3. Memory safety is preserved across all operations (no out-of-bounds or
   use-after-free concerning another's memory)

Informally, no plugin can read or write another plugin's memory, nor the host's,
and vice versa. We treat each memory as a resource in separation logic and
assert that resources for different plugins (and the host) are never aliased or
overlapping.

### Robust Safety Property

**Definition 3.2** (Robust Safety): A plugin $P$ exhibits robust safety if
unknown adversarial code can only affect $P$ through explicitly exported
functions.

**Formal Statement**:

$$\forall P \in \text{Plugins}, \forall A \in \text{Adversarial\_Code}: \text{Effect}(A, P) \Rightarrow \exists f \in P.\text{exports}: \text{Calls}(A, f)$$

This means any effect an adversarial module $A$ has on plugin $P$ must occur via
calling one of $P$'s exposed entry points. There is no hidden channel or side
effect by which $A$ can tamper with $P$'s state — it must go through the
official interface of $P$. This property is crucial for reasoning about
untrusted code running in a plugin: the plugin can be analyzed as if those are
the only ways it can be influenced.

**Proof Sketch**: We prove robust safety by induction on the structure of $A$'s
program, using the WebAssembly semantics: since $A$ can only call $P$ via
imports (which correspond to $P$'s exports), any influence is accounted for. No
direct memory writes across sandboxes are possible due to the isolation
invariant.

---

_Next: [WebAssembly Isolation Theorem](ch3-2-theorem-3.1.md)_
