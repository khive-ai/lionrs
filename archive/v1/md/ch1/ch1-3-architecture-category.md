# 1.3 Lion Architecture as a Category

## 1.3.1 The LionComp Category

**Definition 1.9** (LionComp Category): The Lion ecosystem forms a category
$\mathbf{LionComp}$ where:

1. **Objects**: System components with typed interfaces
   $$\mathrm{Obj}(\mathbf{LionComp}) = \{\text{Core}, \text{CapMgr}, \text{IsoEnf}, \text{PolEng}, \text{MemMgr}, \text{WorkMgr}\} \cup \text{Plugins}$$

2. **Morphisms**: Capability-mediated interactions between components
   $$f: A \to B \text{ is a 5-tuple } (A, B, c, \text{pre}, \text{post})$$

   where:
   - $c \in \text{Capabilities}$ is the required capability
   - $\text{pre}: \text{SystemState} \to \mathbb{B}$ is the precondition
   - $\text{post}: \text{SystemState} \to \mathbb{B}$ is the postcondition

3. **Composition**: For morphisms $f: A \to B$ and $g: B \to C$:
   $$g \circ f = (A, C, c_g \sqcup c_f, \text{pre}_f, \text{post}_g)$$

   where $\sqcup$ is capability combination

4. **Identity**: For each component $A$:
   $$\mathrm{id}_A = (A, A, \mathbf{1}_A, \lambda s.\text{true}, \lambda s.\text{true})$$

**Lemma 1.1** (LionComp is a Category): The structure
$(\mathrm{Obj}(\mathbf{LionComp}), \mathrm{Hom}, \circ, \mathrm{id})$ satisfies
the category axioms.

**Proof**: We verify each axiom:

1. **Associativity**: Proven in Theorem 1.4
2. **Identity**: Proven in Theorem 1.5
3. **Composition closure**: Given $f: A \to B$ and $g: B \to C$, the composition
   $g \circ f: A \to C$ is well-defined by capability combination closure.

## 1.3.2 Component Types

**Definition 1.10** (Component Classification): Objects in LionComp are
classified by trust level:

**Trusted Computing Base (TCB)**:

- **Core**: `Core = (State, Orchestrator, EventLoop)`
- **CapabilityManager**:
  `CapMgr = (CapabilityTable, AuthorityGraph, Attenuation)`
- **IsolationEnforcer**: `IsoEnf = (WASMSandbox, MemoryBounds, BoundaryCheck)`

**System Components**:

- **PolicyEngine**:
  `PolEng = (PolicyTree, DecisionFunction, CompositionAlgebra)`
- **MemoryManager**: `MemMgr = (HeapAllocator, IsolationBoundaries, GCRoot)`
- **WorkflowManager**: `WorkMgr = (DAG, Scheduler, TerminationProof)`

**Application Components**:

- **Plugin**: `Plugin = (WASMModule, CapabilitySet, MemoryRegion)`

## 1.3.3 Morphism Structure

**Definition 1.11** (Capability-Mediated Morphism): A morphism $f: A \to B$ in
$\mathbf{LionComp}$ is a 5-tuple:

$$f = (A, B, c, \text{pre}, \text{post})$$

where:

- $A, B \in \mathrm{Obj}(\mathbf{LionComp})$ are the source and target
  components
- $c \in \text{Capabilities}$ is an unforgeable reference authorizing the
  interaction
- $\text{pre}: \text{SystemState} \to \mathbb{B}$ is the required precondition
- $\text{post}: \text{SystemState} \to \mathbb{B}$ is the guaranteed
  postcondition

The morphism is _valid_ if and only if:

$$\begin{align}
\text{authorized}(c, A, B) &= \text{true} \\
\text{unforgeable}(c) &= \text{true} \\
\forall s \in \text{SystemState}: \text{pre}(s) &\Rightarrow \text{valid\_transition}(s, f)
\end{align}$$

**Example 1.6**: File access morphism

```
file_read: Plugin₁ → FileSystem
  capability = FileReadCap("/path/to/file")
  precondition = file_exists("/path/to/file") ∧ plugin_authorized(Plugin₁)
  postcondition = file_content_returned ∧ no_side_effects
```

## 1.3.4 Composition Rules

**Theorem 1.4** (LionComp Category Axiom: Associativity): For morphisms
$f: A \to B$, $g: B \to C$, $h: C \to D$ in $\mathbf{LionComp}$:

$$h \circ (g \circ f) = (h \circ g) \circ f$$

**Proof**: Let $f = (A, B, c_f, \text{pre}_f, \text{post}_f)$,
$g = (B, C, c_g, \text{pre}_g, \text{post}_g)$, and
$h = (C, D, c_h, \text{pre}_h, \text{post}_h)$ be capability-mediated morphisms.

The composition $g \circ f$ is defined as:
$$g \circ f = (A, C, c_g \sqcup c_f, \text{pre}_f, \text{post}_g)$$

Similarly, $h \circ g = (B, D, c_h \sqcup c_g, \text{pre}_g, \text{post}_h)$.

By the capability transitivity property:
$$h \circ (g \circ f) = (A, D, c_h \sqcup (c_g \sqcup c_f), \text{pre}_f, \text{post}_h)$$

$$(h \circ g) \circ f = (A, D, (c_h \sqcup c_g) \sqcup c_f, \text{pre}_f, \text{post}_h)$$

Since capability combination is associative:
$$c_h \sqcup (c_g \sqcup c_f) = (c_h \sqcup c_g) \sqcup c_f$$

Therefore, $h \circ (g \circ f) = (h \circ g) \circ f$. $\square$

**Theorem 1.5** (LionComp Category Axiom: Identity Laws): For any object
$A \in \mathrm{Obj}(\mathbf{LionComp})$ and morphism $f: A \to B$:

$$\mathrm{id}_B \circ f = f = f \circ \mathrm{id}_A$$

**Proof**: Let $f = (A, B, c_f, \text{pre}_f, \text{post}_f)$ be a
capability-mediated morphism.

The identity morphism $\mathrm{id}_A$ is defined as:
$$\mathrm{id}_A = (A, A, \mathbf{1}_A, \text{true}, \text{true})$$

where $\mathbf{1}_A$ is the unit capability for component $A$.

**Left identity**: $$\begin{align}
\mathrm{id}_B \circ f &= (A, B, \mathbf{1}_B \sqcup c_f, \text{pre}_f, \text{post}_f) \\
&= (A, B, c_f, \text{pre}_f, \text{post}_f) \quad \text{(by unit law of $\sqcup$)} \\
&= f
\end{align}$$

**Right identity**: $$\begin{align}
f \circ \mathrm{id}_A &= (A, B, c_f \sqcup \mathbf{1}_A, \text{true}, \text{post}_f) \\
&= (A, B, c_f, \text{pre}_f, \text{post}_f) \quad \text{(by unit law and precondition propagation)} \\
&= f
\end{align}$$

Therefore, the identity laws hold. $\square$

## 1.3.5 Security Properties

**Definition 1.12** (Security-Preserving Morphism): A morphism $f: A \to B$ is
security-preserving if:

$$\text{secure}(A) \land \text{authorized}(f) \Rightarrow \text{secure}(B)$$

**Theorem 1.6** (Security Composition): The composition of security-preserving
morphisms is security-preserving.

**Proof**: By transitivity of security properties and capability authority
preservation.

## 1.3.6 Monoidal Structure

**Definition 1.13** (LionComp Monoidal Structure): LionComp forms a symmetric
monoidal category with:

- **Tensor Product**: $\otimes$ represents parallel composition of components
  (e.g., running two components side by side in isolation)
- **Unit Object**: $I$ represents an empty no-component (no-operation context)
- **Symmetry**: The braiding $\gamma_{A,B}: A \otimes B \to B \otimes A$ swaps
  parallel components A and B

**Definition 1.14** (Parallel Composition): For components $A$ and $B$, their
parallel composition $A \otimes B$ is defined as a new composite component whose
behavior consists of A and B operating independently (with no direct
interactions unless mediated by capabilities).

## 1.3.7 System Functors

**Definition 1.15** (Capability Functor):
$\text{Cap}: \mathbf{LionComp}^{\text{op}} \to \mathbf{Set}$ defined by:

- $\text{Cap}(A) = \{\text{capabilities available to component } A\}$
- $\text{Cap}(f: A \to B) = \{\text{capability transformations induced by } f\}$

This contravariant functor assigns each component the set of capabilities it
holds, and each morphism the effect it has on capabilities.

**Definition 1.16** (Isolation Functor):
$\text{Iso}: \mathbf{LionComp} \to \mathbf{WASMSandbox}$ defined by:

- $\text{Iso}(A) = \{\text{WebAssembly sandbox for component } A\}$
- $\text{Iso}(f: A \to B) = \{\text{isolation boundary crossing for } f\}$

**Definition 1.17** (Policy Functor):
$\text{Pol}: \mathbf{LionComp} \times \text{Actions} \to \text{Decisions}$
defined by:

- $\text{Pol}(A, \text{action}) = \{\text{policy decision for component } A \text{ performing action}\}$

## 1.3.8 Design Impact

The category-theoretic perspective directly informs the system design:

- **Type System Design**: Categorical structure guides Rust type definitions
  (objects correspond to types, morphisms to functions), ensuring that only
  well-typed (authorized) interactions are possible
- **API Design**: Functor and natural transformation concepts inform interface
  design, making security and isolation properties explicit in function
  signatures and module boundaries
- **Composability**: The monoidal structure and functors ensure that adding new
  components or interactions preserves existing guarantees (security and
  correctness compose), a crucial property for incremental development
