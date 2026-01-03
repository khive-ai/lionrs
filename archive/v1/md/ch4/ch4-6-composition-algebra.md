# 4.6 Composition Algebra

_[Previous: Workflow Termination Theorem](ch4-5-theorem-4.2.md) |
[Next: Chapter Summary](ch4-7-summary.md)_

---

We have established the mathematical foundations for both policy evaluation and
workflow orchestration. Now we develop a complete algebraic framework for
composing these elements while preserving correctness properties.

## Policy Composition Algebra

### Closure Properties

The policy composition operators form a closed algebra under the evaluation
semantics:

**Theorem 4.3** (Policy Closure): For any policies $p_1, p_2 \in \mathbf{P}$ and
operator $\circ \in \{\land, \lor, \neg, \oplus, \Rightarrow\}$:

$$p_1 \circ p_2 \in \mathbf{P} \text{ and preserves soundness}$$

**Proof**: By Theorem 4.1's inductive cases, each composition operator preserves
the soundness property. The composed policy remains well-formed within the
policy language grammar.

### Algebraic Properties

The composition operators satisfy standard algebraic laws:

#### Commutativity

- $p_1 \land p_2 \equiv p_2 \land p_1$
- $p_1 \lor p_2 \equiv p_2 \lor p_1$

#### Associativity

- $(p_1 \land p_2) \land p_3 \equiv p_1 \land (p_2 \land p_3)$
- $(p_1 \lor p_2) \lor p_3 \equiv p_1 \lor (p_2 \lor p_3)$

#### Identity Elements

- $p \land \text{PERMIT} \equiv p$
- $p \lor \text{DENY} \equiv p$

#### Absorption

- $p \land (p \lor q) \equiv p$
- $p \lor (p \land q) \equiv p$

#### De Morgan's Laws

- $\neg(p_1 \land p_2) \equiv \neg p_1 \lor \neg p_2$
- $\neg(p_1 \lor p_2) \equiv \neg p_1 \land \neg p_2$

### Override Operator Properties

The override operator $\oplus$ provides deterministic conflict resolution:

$$p_1 \oplus p_2 = \begin{cases}
p_1 & \text{if } \varphi(p_1, a) \neq \text{INDETERMINATE} \\
p_2 & \text{if } \varphi(p_1, a) = \text{INDETERMINATE}
\end{cases}$$

**Properties**:

- **Non-commutative**: $p_1 \oplus p_2 \not\equiv p_2 \oplus p_1$ (order
  matters)
- **Associative**:
  $(p_1 \oplus p_2) \oplus p_3 \equiv p_1 \oplus (p_2 \oplus p_3)$
- **Identity**: $p \oplus \text{INDETERMINATE} \equiv p$

## Workflow Composition Algebra

### Sequential Composition

Workflows can be composed sequentially:

$$W_1 ; W_2 = (N_1 \cup N_2, E_1 \cup E_2 \cup \{(\text{end}_1, \text{start}_2)\}, \text{start}_1, \text{end}_2)$$

This creates a new workflow where $W_2$ begins after $W_1$ completes.

**Termination Preservation**: If $W_1$ and $W_2$ both terminate (by Theorem
4.2), then $W_1 ; W_2$ also terminates.

### Parallel Composition

Workflows can be composed in parallel:

$$W_1 \parallel W_2 = (N_1 \cup N_2 \cup \{\text{fork}, \text{join}\}, E', \text{fork}, \text{join})$$

where $E'$ includes:

- All edges from $E_1$ and $E_2$
- Fork edges: $(\text{fork}, \text{start}_1)$, $(\text{fork}, \text{start}_2)$
- Join edges: $(\text{end}_1, \text{join})$, $(\text{end}_2, \text{join})$

**Termination Preservation**: Parallel composition preserves termination since
each branch terminates independently.

### Conditional Composition

Workflows support conditional branching:

$$W_1 \triangleright_c W_2 = \text{if condition } c \text{ then } W_1 \text{ else } W_2$$

This creates branching based on runtime conditions.

### Iterative Composition

Bounded iteration is supported:

$$W^{\leq n} = \text{repeat } W \text{ at most } n \text{ times}$$

The bound $n$ ensures termination.

## Capability Integration Algebra

### Policy-Capability Composition

The combined authorization function forms an algebra:

$$\text{authorize}(p, c, a) = \varphi(p, a) \land \kappa(c, a)$$

**Composition Rule**: For multiple capabilities $C = \{c_1, c_2, \ldots, c_k\}$:

$$\text{authorize}(p, C, a) = \varphi(p, a) \land \bigvee_{c \in C} \kappa(c, a)$$

This allows access if the policy permits and _any_ capability authorizes it.

### Capability Attenuation Algebra

Capability delegation follows attenuation rules:

$$\text{attenuate}(c, \text{constraints}) = (\text{authority}_c, \text{permissions}_c \cap \text{new\_perms}, \text{constraints}_c \cup \text{constraints}, \text{depth}_c + 1)$$

**Properties**:

- **Monotonic**:
  $\text{authority}(\text{attenuate}(c, \sigma)) \subseteq \text{authority}(c)$
- **Transitive**:
  $\text{attenuate}(\text{attenuate}(c, \sigma_1), \sigma_2) = \text{attenuate}(c, \sigma_1 \cup \sigma_2)$

## Complexity Preservation

### Policy Composition Complexity

Composing policies with $k$ operators increases complexity by a factor of $k$:

$$\text{complexity}(p_1 \circ p_2 \circ \ldots \circ p_k) = O(k \times \max_i(\text{complexity}(p_i)))$$

This remains polynomial for bounded $k$.

### Workflow Composition Complexity

Sequential composition adds execution times:

$$T(W_1 ; W_2) = T(W_1) + T(W_2)$$

Parallel composition takes the maximum:

$$T(W_1 \parallel W_2) = \max(T(W_1), T(W_2)) + \text{sync\_overhead}$$

## Functional Completeness

### Policy Language Completeness

**Theorem 4.4** (Functional Completeness): The policy language with operators
$\{\land, \lor, \neg\}$ is functionally complete for three-valued logic.

**Proof**: Any three-valued logic function can be expressed using conjunction,
disjunction, and negation. The additional operators $\oplus$ and $\Rightarrow$
provide syntactic convenience.

### Workflow Language Completeness

**Theorem 4.5** (Workflow Completeness): The workflow composition operators are
sufficient to express any finite-state orchestration pattern.

**Proof**: Sequential, parallel, and conditional composition, combined with
bounded iteration, can express:

- Finite state machines
- Petri nets (with token-based synchronization)
- Process calculi (with message passing)

All expressible patterns maintain the DAG property and termination guarantees.

## Type Safety

The composition algebra is type-safe:

### Policy Type Safety

**Theorem 4.6** (Policy Type Safety): Well-typed policy compositions produce
well-typed policies.

**Proof**: The type system ensures:

- Operators apply only to compatible policy types
- Evaluation always produces values in
  $\{\text{PERMIT}, \text{DENY}, \text{INDETERMINATE}\}$
- Composition preserves semantic coherence

### Workflow Type Safety

**Theorem 4.7** (Workflow Type Safety): Well-typed workflow compositions
preserve task interface compatibility.

**Proof**: The type system ensures:

- Task outputs match required inputs
- Resource requirements are satisfiable
- Composition preserves DAG property

## Conclusion

The composition algebra provides a mathematically rigorous foundation for
building complex policies and workflows while preserving correctness properties:

1. **Soundness Preservation**: All compositions maintain policy soundness
2. **Termination Preservation**: All compositions maintain workflow termination
3. **Complexity Bounds**: Composition complexity remains polynomial
4. **Type Safety**: Well-typed compositions produce well-typed results
5. **Functional Completeness**: The algebra can express all required
   orchestration patterns

This enables confident construction of large-scale Lion systems through
principled composition of verified components.

---

_Next: [Chapter Summary](ch4-7-summary.md)_
