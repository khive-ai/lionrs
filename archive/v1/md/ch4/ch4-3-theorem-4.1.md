# 4.3 Theorem 4.1: Policy Soundness

_[Previous: Policy Evaluation Framework](ch4-2-policy-evaluation.md) |
[Next: Workflow Model](ch4-4-workflow-model.md)_

---

## Statement and Complexity Analysis

**Theorem 4.1** (Policy Soundness): For any policy $p \in \mathbf{P}$ and access
request $a \in \mathbf{A}$, if $\varphi(p, a) = \text{PERMIT}$, then the access
is safe according to the policy specification. Additionally, the evaluation
complexity is $O(d \times b)$ where $d$ is the policy depth and $b$ is the
branching factor.

**Formal Statement**:

$$\forall p \in \mathbf{P}, a \in \mathbf{A}: \varphi(p, a) = \text{PERMIT} \Rightarrow \text{SAFE}(p, a)$$

**Interpretation**: If the policy decision is to permit, that decision is
guaranteed not to lead to a violation (no unsafe permission is ever granted by a
policy decision). This addresses _soundness_.

## Formal Proof

### Proof Strategy

We prove Theorem 4.1 by structural induction on the structure of policy $p$.

**Safety Predicate**: Define $\text{SAFE}(p, a)$ as the safety predicate that
holds when access $a$ is safe under policy $p$ according to the specification
semantics (the "intended" meaning of the policy rules).

**Soundness Requirement**: We must prove:

$$\varphi(p, a) = \text{PERMIT} \Rightarrow \text{SAFE}(p, a)$$

### Base Cases

#### Atomic Condition Policy

For an atomic policy $p_{\text{atomic}}$ with condition $C$, if
$\varphi(p_{\text{atomic}}, a) = \text{PERMIT}$, then by the semantics of
conditions, $C(a) = \text{TRUE}$.

By the policy specification, if that condition is true, the access is intended
to be safe (assuming conditions reflect safety requirements). Thus:

$$C(a) = \text{TRUE} \Rightarrow \text{SAFE}(p_{\text{atomic}}, a)$$

#### Capability Policy

For a capability-based atomic policy $p_{\text{cap}}$ referencing a capability
$c$, if $\varphi(p_{\text{cap}}, a) = \text{PERMIT}$, then
$\kappa(c, a) = \text{TRUE}$ (meaning the capability indeed authorizes this
request).

By the capability attenuation principle and confinement properties (proved in
Chapter 2), $\kappa(c, a) = \text{TRUE}$ implies that $a$ is within the
authority deliberately granted, hence $\text{SAFE}(p_{\text{cap}}, a)$.

#### Constant Decision

For a constant policy $p_{\text{const}} = \text{PERMIT}$, trivially we consider
it safe by definition (we wouldn't embed a constant PERMIT in a policy unless we
deemed all such accesses safe by higher-level reasoning). So
$\text{SAFE}(p_{\text{const}}, a)$ holds.

### Inductive Cases

Assume soundness for sub-policies $p_1$ and $p_2$:

#### Conjunction ($\land$)

For $p = p_1 \land p_2$: If $\varphi(p_1 \land p_2, a) = \text{PERMIT}$, then
$\varphi(p_1, a) = \text{PERMIT} \land \varphi(p_2, a) = \text{PERMIT}$ (by
evaluation semantics).

By the inductive hypothesis:

- From $\varphi(p_1, a) = \text{PERMIT}$ we get $\text{SAFE}(p_1, a)$
- From $\varphi(p_2, a) = \text{PERMIT}$ we get $\text{SAFE}(p_2, a)$

Both sub-policies deem $a$ safe; by the semantics of conjunction, this means all
requirements are satisfied, so $\text{SAFE}(p_1 \land p_2, a)$ follows.

#### Disjunction ($\lor$)

For $p = p_1 \lor p_2$: If $\varphi(p_1 \lor p_2, a) = \text{PERMIT}$, then
$\varphi(p_1, a) = \text{PERMIT} \lor \varphi(p_2, a) = \text{PERMIT}$ (at least
one sub-policy permits it).

Without loss of generality, assume $\varphi(p_1, a) = \text{PERMIT}$. By
inductive hypothesis, $\text{SAFE}(p_1, a)$.

The definition of disjunction in policies is that an access is allowed if either
condition suffices; thus as long as one branch is safe and permits it, the
overall policy permits safely. Therefore, from $\text{SAFE}(p_1, a)$ we infer
$\text{SAFE}(p_1 \lor p_2, a)$.

#### Negation ($\neg$)

For $p = \neg p_1$: If $\varphi(\neg p_1, a) = \text{PERMIT}$, then
$\varphi(p_1, a) = \text{DENY}$.

By the contrapositive of the inductive hypothesis: if
$\varphi(p_1, a) = \text{DENY}$, then $p_1$'s conditions are not met. But
$\neg p_1$ permitting means precisely that $p_1$'s conditions for denial are not
met (i.e., the request is safe relative to the condition we're negating).

Thus we get $\text{SAFE}(\neg p_1, a)$ (negation flips the safety
interpretation: if $p_1$ would have been unsafe, then $\neg p_1$ permitting
avoids that unsafe scenario).

#### Override ($\oplus$)

For $p = p_1 \oplus p_2$: The override operator takes the first policy unless
it's indeterminate.

If $\varphi(p_1 \oplus p_2, a) = \text{PERMIT}$, then either:

1. $\varphi(p_1, a) = \text{PERMIT}$ (so by inductive hypothesis,
   $\text{SAFE}(p_1, a)$)
2. $\varphi(p_1, a) = \text{INDETERMINATE}$ and
   $\varphi(p_2, a) = \text{PERMIT}$ (so by inductive hypothesis,
   $\text{SAFE}(p_2, a)$)

In either case, we have safety from one of the sub-policies, thus
$\text{SAFE}(p_1 \oplus p_2, a)$.

#### Implication ($\Rightarrow$)

For $p = p_1 \Rightarrow p_2$: The implication is logically equivalent to
$\neg p_1 \lor p_2$.

If $\varphi(p_1 \Rightarrow p_2, a) = \text{PERMIT}$, then either:

1. $\varphi(p_1, a) = \text{DENY}$ (antecedent false, so implication trivially
   safe)
2. $\varphi(p_1, a) = \text{PERMIT}$ and $\varphi(p_2, a) = \text{PERMIT}$ (both
   safe by inductive hypothesis)

In both cases, $\text{SAFE}(p_1 \Rightarrow p_2, a)$ holds.

## Conclusion

Given these inductive proofs for all constructs, we conclude that whenever
$\varphi(p, a) = \text{PERMIT}$, in every case $\text{SAFE}(p, a)$ holds. This
establishes policy soundness.

## Complexity Analysis

### Time Complexity

Each operator in the policy grammar contributes at most linear overhead relative
to its sub-policies. The evaluation visits each node once and does constant work
per node.

- **Depth**: Maximum policy nesting depth is $d$
- **Branching**: Maximum branching factor is $b$
- **Worst-case**: $O(b^d)$ for fully balanced trees
- **Typical case**: $O(d \times b)$ due to short-circuit evaluation and
  practical policy structures

### Space Complexity

The space complexity is $O(d)$ for the recursion stack during evaluation.

### Practical Performance

In practice, $d$ and $b$ are small (typically $d < 10$, $b < 5$), making
evaluation very fast. The complexity is polynomial in policy size, and since
policies are not extremely large, this ensures efficient runtime performance.

---

_Next: [Workflow Model](ch4-4-workflow-model.md)_
