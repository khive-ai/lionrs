# 5.1 Policy Correctness

_[Previous: Abstract](ch5-0-abstract.md) |
[Next: Workflow Termination](ch5-2-workflow-termination.md)_

---

## 5.1.1 Theorem 5.1: Evaluation Soundness and Completeness

**Theorem 5.1** (Policy Evaluation Correctness): The Lion policy evaluation
system is sound, complete, and decidable with polynomial-time complexity.

### Formal Statement

$$\forall p \in \text{Policies}, \forall a \in \text{Actions}, \forall c \in \text{Capabilities}:$$

1. **Soundness**:
   $\varphi(p,a,c) = \text{PERMIT} \Rightarrow \text{safe}(p,a,c)$
2. **Completeness**:
   $\text{safe}(p,a,c) \Rightarrow \varphi(p,a,c) \neq \text{DENY}$
3. **Decidability**: $\exists$ algorithm with time complexity $O(d \times b)$
   where $d = $ policy depth, $b = $ branching factor

Here $\varphi(p,a,c)$ is an extended evaluation function that considers both
policy $p$ and capability $c$ in making a decision (corresponding to the
$\text{authorize}(p,c,a)$ function from Chapter 4).

**Interpretation**:

- **Soundness**: No unsafe permissions are ever granted
- **Completeness**: If something is safe, the policy won't erroneously deny it
  (may permit or return indeterminate, but not firm denial)
- **Decidability**: There exists a terminating decision procedure with
  polynomial time complexity

### Proof Strategy

The proof proceeds by structural induction on policy composition, leveraging the
safety definitions from Chapter 4.

#### Soundness Proof

**Soundness** extends Theorem 4.1 for policies to include capability checking:

$$\varphi(p,a,c) = \text{PERMIT} \Rightarrow \text{safe}(p,a,c)$$

**Proof**: Already proven as Theorem 4.1 for policies. Integration with
capability $c$ only strengthens the condition since:

$$\text{authorize}(p,c,a) = \varphi(p,a) \land \kappa(c,a)$$

If either policy or capability would make the access unsafe, $\varphi$ would not
return PERMIT. The capability check $\kappa(c,a)$ provides an additional safety
conjunct, strengthening the overall safety guarantee.

#### Completeness Proof

**Completeness** ensures that safe accesses are not inappropriately denied:

$$\text{safe}(p,a,c) \Rightarrow \varphi(p,a,c) \neq \text{DENY}$$

**Proof by Structural Induction**:

**Base Cases**:

- **Atomic Condition**: If $\text{safe}(p_{\text{atomic}}, a, c)$ holds for a
  condition-based policy, then the condition is satisfied and the atomic rule
  yields PERMIT (or at worst INDETERMINATE), never DENY
- **Capability Policy**: If safe, then $\kappa(c,a) = \text{TRUE}$ and the
  policy permits the access
- **Constant Policy**: Constant PERMIT policies trivially don't deny safe
  accesses

**Inductive Cases** (assuming completeness for sub-policies):

- **Conjunction**: If $\text{safe}(p_1 \land p_2, a, c)$, then both
  $\text{safe}(p_1, a, c)$ and $\text{safe}(p_2, a, c)$. By inductive
  hypothesis, neither sub-policy denies, so the conjunction doesn't deny
- **Disjunction**: If safe, at least one branch finds it safe. By inductive
  hypothesis, that branch doesn't deny, so the disjunction permits
- **Override ($\oplus$)**: If safe, either the first policy handles it correctly
  or defers to the second. Well-formed override policies don't deny safe
  accesses
- **Implication ($\Rightarrow$)**: If safe, either the antecedent is false
  (trivially safe) or the consequent is true (explicitly safe)

#### Decidability and Complexity Proof

**Decidability**: The evaluation function $\varphi$ is total and terminates
because:

1. Finite policy depth (no infinite recursion)
2. Finite action space (each request processed individually)
3. Finite capability space (bounded at any given time)
4. Terminating operators (all composition operators compute results in finite
   steps)

**Complexity Analysis**:

- Policy representation as tree with $\leq b^d$ nodes (balanced worst-case)
- Evaluation per node is $O(1)$ (condition evaluation or result combination)
- Total complexity: $O(b^d)$ which is polynomial for fixed $d$ and $b$
- Practical complexity: $O(d \times b)$ due to typical policy structures and
  short-circuit evaluation

## 5.1.2 Policy Evaluation Framework

### Extended Evaluation Function

The evaluation function integrates policy and capability checking:

$$\varphi: \text{Policies} \times \text{Actions} \times \text{Capabilities} \to \{\text{PERMIT}, \text{DENY}, \text{INDETERMINATE}\}$$

**Implementation**:

```
φ(p, a, c) = match p with
  | AtomicPolicy(rule) → evaluate_rule(rule, a, c)
  | CompositePolicy(p₁, p₂, op) → combine_evaluations(φ(p₁,a,c), φ(p₂,a,c), op)
  | ConditionalPolicy(condition, then_p, else_p) → 
      if evaluate_condition(condition, a, c) 
      then φ(then_p, a, c) 
      else φ(else_p, a, c)
```

### Capability Integration

The evaluation function integrates capability checking through the authorization
predicate:

$$\text{authorize}(p, c, a) = \varphi(p, a, c) \land \kappa(c, a)$$

In practice, capability requirements can be embedded within policy $p$ (via
CapabilityRef atomic policies) or checked separately, with the same net effect:
final authorization requires both policy permission and capability
authorization.

### Safety Predicate Definition

We extend the safety predicate to consider full system state:

$$\text{safe}(p, a, c) = \forall \text{system\_state } s: \text{execute}(s, a, c) \Rightarrow \text{system\_invariants}(s) \land \text{security\_properties}(s) \land \text{resource\_bounds}(s)$$

This holistic definition captures that granting request $a$ with capability $c$
preserves:

- System invariants (no policy violations)
- Security properties (no capability misuse)
- Resource bounds (no resource exhaustion)

## 5.1.3 Composition Algebra for Policies

### Policy Composition Operators

The composition operators maintain their three-valued logic semantics:

#### Conjunction ($\land$)

$$\varphi(p_1 \land p_2, a, c) = \varphi(p_1, a, c) \land \varphi(p_2, a, c)$$

Both policies must permit for the conjunction to permit.

#### Disjunction ($\lor$)

$$\varphi(p_1 \lor p_2, a, c) = \varphi(p_1, a, c) \lor \varphi(p_2, a, c)$$

Either policy may permit for the disjunction to permit.

#### Override ($\oplus$)

$$\varphi(p_1 \oplus p_2, a, c) = \begin{cases}
\varphi(p_1, a, c) & \text{if } \varphi(p_1, a, c) \neq \text{INDETERMINATE} \\
\varphi(p_2, a, c) & \text{if } \varphi(p_1, a, c) = \text{INDETERMINATE}
\end{cases}$$

First policy takes precedence unless indeterminate.

#### Consensus ($\otimes$)

$$\varphi(p_1 \otimes p_2, a, c) = \text{consensus\_function}(\varphi(p_1, a, c), \varphi(p_2, a, c))$$

Majority decision with conflict resolution (implementation-defined semantics).

### Algebraic Properties

The composition operators satisfy standard algebraic laws extended to
three-valued logic:

- **Associativity**:
  $(p_1 \otimes p_2) \otimes p_3 = p_1 \otimes (p_2 \otimes p_3)$ for
  well-behaved operators
- **Commutativity**: $p_1 \land p_2 = p_2 \land p_1$,
  $p_1 \lor p_2 = p_2 \lor p_1$
- **Identity**: $p \land \text{PERMIT} = p$, $p \lor \text{DENY} = p$
- **Absorption**: $p \land (p \lor q) = p$, $p \lor (p \land q) = p$

These laws enable policy simplification and algebraic reasoning while preserving
correctness.

## 5.1.4 Complexity Analysis and Decidability

### Time Complexity Analysis

**Single Policy Evaluation**: $O(r)$ where $r$ is the number of atomic rules

**Composite Policy Evaluation**: $O(d \times b)$ where:

- $d$ = maximum policy nesting depth
- $b$ = maximum branching factor

**Total Complexity**: For a policy tree with $n$ nodes, evaluation is $O(n)$
since each node is visited once with constant-time processing.

### Space Complexity

- **Policy Storage**: $O(|P|)$ proportional to policy size
- **Evaluation Stack**: $O(d)$ for recursion depth
- **Memoization Cache**: Optional
  $O(|\text{Actions}| \times |\text{Capabilities}|)$ for repeated evaluations

### Decidability Proof

Every policy evaluation terminates because:

1. **Finite Policy Depth**: No infinite recursion or self-reference
2. **Finite Action Space**: Each request is processed individually in finite
   time
3. **Finite Capability Space**: Bounded capability sets at any given time
4. **Terminating Operators**: All composition operators yield decisions in
   finite steps

Therefore, $\varphi$ is a total computable function, establishing decidability.

---

_Next: [Workflow Termination](ch5-2-workflow-termination.md)_
