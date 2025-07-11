# 1.5 Functors and Natural Transformations

## 1.5.1 System Functors

The Lion ecosystem defines several functors that connect different aspects of
the system:

**Definition 1.19** (Capability Functor):
$\text{Cap}: \mathbf{LionComp}^{\text{op}} \to \mathbf{Set}$

- $\text{Cap}(A) = \{\text{capabilities available to component } A\}$
- $\text{Cap}(f: A \to B) = \{\text{capability transformations induced by } f\}$

**Definition 1.20** (Isolation Functor):
$\text{Iso}: \mathbf{LionComp} \to \mathbf{WASMSandbox}$

- $\text{Iso}(A) = \{\text{WebAssembly sandbox for component } A\}$
- $\text{Iso}(f: A \to B) = \{\text{isolation boundary crossing for } f\}$

**Definition 1.21** (Policy Functor):
$\text{Pol}: \mathbf{LionComp} \times \text{Actions} \to \text{Decisions}$

- $\text{Pol}(A, \text{action}) = \{\text{policy decision for component } A \text{ performing action}\}$

## 1.5.2 Natural Transformations

**Definition 1.22** (Security Preservation Natural Transformation):
$\text{SecPres}: F \Rightarrow G$ where $F$ and $G$ are security-preserving
functors.

For each component $A$, we have a morphism $\alpha_A: F(A) \to G(A)$ such that:

$$\alpha_B \circ F(f) = G(f) \circ \alpha_A$$

This ensures that security properties are preserved across functor
transformations.

## 1.5.3 Adjunctions

**Definition 1.23** (Capability-Memory Adjunction):
$\text{Cap} \dashv \text{Mem}$

The capability functor is left adjoint to the memory functor, establishing a
correspondence:

$$\text{Hom}(\text{Cap}(A), B) \cong \text{Hom}(A, \text{Mem}(B))$$

This adjunction formalizes the relationship between capability grants and memory
access rights.
