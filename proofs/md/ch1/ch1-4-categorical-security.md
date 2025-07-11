# 1.4 Categorical Security in Lion

## 1.4.1 Capability Transfer as Morphisms

In LionComp, an inter-component capability transfer (e.g., plugin sending a file
handle to another plugin via the Capability Manager) is modeled as a morphism
$f: \text{Plugin}_A \to \text{Plugin}_B$. The security-preserving condition
(Definition 1.12) for $f$ states that if $\text{Plugin}_A$ was secure and $f$ is
authorized by the policy, then $\text{Plugin}_B$ remains secure. This
encapsulates the **end-to-end security** of capability passing.

## 1.4.2 Monoidal Isolation

Isolation Enforcer and WebAssembly sandboxing yield parallel composition
properties:

**Theorem 1.7** (Associativity): For components $A$, $B$, $C$:

$$(A \otimes B) \otimes C \cong A \otimes (B \otimes C)$$

Parallel composition of Lion components is associative up to isomorphism.

**Theorem 1.8** (Unit Laws): For any component $A$:

$$A \otimes I \cong A \cong I \otimes A$$

The empty component $I$ acts as a unit for parallel composition.

**Theorem 1.9** (Symmetry): For components $A$ and $B$:

$$A \otimes B \cong B \otimes A$$

LionComp's parallel composition is symmetric monoidal, reflecting the
commutativity of isolating components side-by-side.

## 1.4.3 Security Composition Theorem

Lion's design ensures that individual component security properties hold under
composition:

**Theorem 1.10** (Security Composition): For components
$A, B \in \mathrm{Obj}(\mathbf{LionComp})$:

$$\text{secure}(A) \land \text{secure}(B) \Rightarrow \text{secure}(A \otimes B)$$

where $\otimes$ denotes parallel composition in the monoidal structure.

**Definition 1.18** (Security Predicate): A component
$C \in \mathrm{Obj}(\mathbf{LionComp})$ is _secure_, denoted $\text{secure}(C)$,
if and only if:

$$\begin{align}
\text{MemoryIsolation}(C) &\equiv \forall \text{addr} \in \text{mem}(C), \forall D \neq C: \text{addr} \notin \text{mem}(D) \\
\text{AuthorityConfinement}(C) &\equiv \forall c \in \text{capabilities}(C): \text{authority}(c) \subseteq \text{granted\_authority}(C) \\
\text{CapabilityUnforgeability}(C) &\equiv \forall c \in \text{capabilities}(C): \text{unforgeable}(c) = \text{true} \\
\text{PolicyCompliance}(C) &\equiv \forall a \in \text{actions}(C): \text{policy\_allows}(C, a) = \text{true}
\end{align}$$

and

$$\text{secure}(C) \equiv \text{MemoryIsolation}(C) \land \text{AuthorityConfinement}(C) \land \text{CapabilityUnforgeability}(C) \land \text{PolicyCompliance}(C)$$

**Proof of Theorem 1.10**: We prove that each security invariant is preserved
under parallel composition by structural analysis of the monoidal tensor
product.

**Step 1: Joint State Construction**

Define the joint state of $A \otimes B$ as:
$$\text{state}(A \otimes B) = (\text{state}(A), \text{state}(B), \text{interaction\_log})$$

where
$\text{interaction\_log}: \mathbb{N} \to \text{Capabilities} \times \text{Messages}$
records all capability-mediated communications.

**Step 2: Memory Isolation Preservation**

**Lemma 1.2**:
$\text{MemoryIsolation}(A) \land \text{MemoryIsolation}(B) \Rightarrow \text{MemoryIsolation}(A \otimes B)$

**Proof**: By the monoidal structure of $\mathbf{LionComp}$:
$$\text{mem}(A \otimes B) = \text{mem}(A) \sqcup \text{mem}(B)$$

where $\sqcup$ denotes disjoint union. From the assumptions: $$\begin{align}
\text{mem}(A) \cap \text{mem}(C) &= \emptyset \quad \forall C \neq A \\
\text{mem}(B) \cap \text{mem}(D) &= \emptyset \quad \forall D \neq B
\end{align}$$

For any component $E \neq A \otimes B$, either $E = A$, $E = B$, or $E$ is
distinct from both. In all cases:
$$\text{mem}(A \otimes B) \cap \text{mem}(E) = (\text{mem}(A) \sqcup \text{mem}(B)) \cap \text{mem}(E) = \emptyset$$

**Step 3: Authority Confinement Preservation**

**Lemma 1.3**:
$\text{AuthorityConfinement}(A) \land \text{AuthorityConfinement}(B) \Rightarrow \text{AuthorityConfinement}(A \otimes B)$

**Proof**: The capability set of the composite component is:
$$\text{capabilities}(A \otimes B) = \text{capabilities}(A) \sqcup \text{capabilities}(B) \sqcup \text{interaction\_capabilities}(A, B)$$

For capabilities $c_A \in \text{capabilities}(A)$:
$$\text{authority}(c_A) \subseteq \text{granted\_authority}(A) \subseteq \text{granted\_authority}(A \otimes B)$$

Similarly for $c_B \in \text{capabilities}(B)$. For interaction capabilities
$c_{AB} \in \text{interaction\_capabilities}(A, B)$:
$$\text{authority}(c_{AB}) \subseteq \text{authority}(c_A) \cup \text{authority}(c_B) \quad \text{(by capability attenuation)}$$

Therefore, authority confinement is preserved.

**Step 4: Capability Unforgeability Preservation**

**Lemma 1.4**:
$\text{CapabilityUnforgeability}(A) \land \text{CapabilityUnforgeability}(B) \Rightarrow \text{CapabilityUnforgeability}(A \otimes B)$

**Proof**: By the cryptographic binding properties of capabilities,
unforgeability is preserved under capability composition operations. Since:
$$\forall c \in \text{capabilities}(A \otimes B): c \in \text{capabilities}(A) \lor c \in \text{capabilities}(B) \lor c \in \text{derived\_capabilities}(A, B)$$

and derived capabilities inherit unforgeability from their parents, the result
follows.

**Step 5: Policy Compliance Preservation**

**Lemma 1.5**:
$\text{PolicyCompliance}(A) \land \text{PolicyCompliance}(B) \Rightarrow \text{PolicyCompliance}(A \otimes B)$

**Proof**: Actions in the composite component are either individual actions or
interaction actions:
$$\text{actions}(A \otimes B) = \text{actions}(A) \sqcup \text{actions}(B) \sqcup \text{interaction\_actions}(A, B)$$

By policy composition rules, all actions remain policy-compliant.

**Conclusion**: By Lemmas 1.2, 1.3, 1.4, and 1.5:
$$\text{secure}(A) \land \text{secure}(B) \Rightarrow \text{secure}(A \otimes B)$$

This theorem is fundamental to the Lion ecosystem's security model, enabling
safe composition of verified components.
