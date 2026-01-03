# 4.2 Policy Evaluation Framework

_[Previous: Mathematical Foundations](ch4-1-mathematical-foundations.md) |
[Next: Policy Soundness Theorem](ch4-3-theorem-4.1.md)_

---

## Sound and Complete Decision Making

The Lion ecosystem implements a policy evaluation framework that ensures both
soundness (no unsafe permissions granted) and completeness (all safe permissions
are granted).

### Definition 4.4: Policy Evaluation Function

A policy evaluation function
$\varphi: \mathbf{P} \times \mathbf{A} \to \text{Decisions}$ determines the
access decision for a policy $p \in \mathbf{P}$ and access request
$a \in \mathbf{A}$.

$$\varphi(p, a) \in \{\text{PERMIT}, \text{DENY}, \text{INDETERMINATE}\}$$

The function yields PERMIT, DENY, or INDETERMINATE based on the rules in policy
$p$.

### Definition 4.5: Capability Check Function

A capability check function
$\kappa: \mathbf{C} \times \mathbf{A} \to \{\text{TRUE}, \text{FALSE}\}$
determines whether capability $c \in \mathbf{C}$ permits access request
$a \in \mathbf{A}$.

$$\kappa(c,a) = \text{TRUE} \iff \text{the resource and action in } a \text{ are covered by } c\text{'s permissions and constraints}$$

Essentially, $\kappa(c,a) = \text{TRUE}$ if and only if the resource and action
in $a$ are covered by $c$'s permissions and constraints (and $c$ is not
expired/revoked).

### Definition 4.6: Combined Authorization Function

The combined authorization function integrates policy and capability decisions:

$$\text{authorize}(p, c, a) = \varphi(p, a) \land \kappa(c, a)$$

Here $\text{authorize}(p,c,a)$ returns PERMIT if _both_ the policy $p$ allows
$a$ and the capability $c$ allows $a$; it returns DENY if either forbids $a$ (or
both), and INDETERMINATE in cases where $p$ yields INDETERMINATE but $c$ would
allow.

**Note**: We treat INDETERMINATE as logically False for the $\land$ conjunction,
meaning if the policy is indeterminate, the result isn't fully PERMIT.

## Policy Evaluation Semantics

The evaluation semantics for compound policies follow standard logical
operations:

### Conjunction ($\land$)

$$\varphi(p_1 \land p_2, a) = \begin{cases}
\text{PERMIT} & \text{if } \varphi(p_1, a) = \text{PERMIT} \text{ and } \varphi(p_2, a) = \text{PERMIT} \\
\text{DENY} & \text{if } \varphi(p_1, a) = \text{DENY} \text{ or } \varphi(p_2, a) = \text{DENY} \\
\text{INDETERMINATE} & \text{otherwise}
\end{cases}$$

### Disjunction ($\lor$)

$$\varphi(p_1 \lor p_2, a) = \begin{cases}
\text{PERMIT} & \text{if } \varphi(p_1, a) = \text{PERMIT} \text{ or } \varphi(p_2, a) = \text{PERMIT} \\
\text{DENY} & \text{if } \varphi(p_1, a) = \text{DENY} \text{ and } \varphi(p_2, a) = \text{DENY} \\
\text{INDETERMINATE} & \text{otherwise}
\end{cases}$$

### Negation ($\neg$)

$$\varphi(\neg p, a) = \begin{cases}
\text{PERMIT} & \text{if } \varphi(p, a) = \text{DENY} \\
\text{DENY} & \text{if } \varphi(p, a) = \text{PERMIT} \\
\text{INDETERMINATE} & \text{if } \varphi(p, a) = \text{INDETERMINATE}
\end{cases}$$

### Override ($\oplus$)

The override operator provides deterministic conflict resolution:

$$\varphi(p_1 \oplus p_2, a) = \begin{cases}
\varphi(p_1, a) & \text{if } \varphi(p_1, a) \neq \text{INDETERMINATE} \\
\varphi(p_2, a) & \text{if } \varphi(p_1, a) = \text{INDETERMINATE}
\end{cases}$$

### Implication ($\Rightarrow$)

The implication operator captures conditional policies:

$$\varphi(p_1 \Rightarrow p_2, a) = \begin{cases}
\varphi(p_2, a) & \text{if } \varphi(p_1, a) = \text{PERMIT} \\
\text{PERMIT} & \text{if } \varphi(p_1, a) = \text{DENY} \\
\text{INDETERMINATE} & \text{if } \varphi(p_1, a) = \text{INDETERMINATE}
\end{cases}$$

## Complexity Considerations

The evaluation complexity depends on two key parameters:

- **Depth ($d$)**: Maximum policy nesting depth (layers of $\land/\lor/\oplus$,
  etc.)
- **Branching ($b$)**: Maximum branching factor (e.g., many-armed policy
  operators)

The evaluation complexity is $O(d \times b)$ in typical cases, though worst-case
can be $O(b^d)$ for fully balanced trees. However, short-circuit evaluation and
practical policy structures keep complexity manageable.

---

_Next: [Policy Soundness Theorem](ch4-3-theorem-4.1.md)_
