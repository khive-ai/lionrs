# 4.1 Mathematical Foundations

_[Previous: Abstract](ch4-0-abstract.md) |
[Next: Policy Evaluation Framework](ch4-2-policy-evaluation.md)_

---

## Core Domains and Notation

Let $\mathbf{P}$ be the set of all policies, $\mathbf{A}$ be the set of all
access requests, $\mathbf{C}$ be the set of all capabilities, and $\mathbf{W}$
be the set of all workflows in the Lion ecosystem.

### Definition 4.1: Policy Evaluation Domain

The policy evaluation domain is a three-valued logic system:

$$\text{Decisions} = \{\text{PERMIT}, \text{DENY}, \text{INDETERMINATE}\}$$

This set represents the possible outcomes of a policy decision: permission
granted, permission denied, or no definitive decision (e.g., due to missing
information).

### Definition 4.2: Access Request Structure

An access request $a \in \mathbf{A}$ is a tuple:

$$a = (\text{subject}, \text{resource}, \text{action}, \text{context})$$

where:

- $\text{subject}$ is the requesting entity's identifier (e.g., a plugin or
  user)
- $\text{resource}$ is the target resource identifier (e.g., file or capability
  ID)
- $\text{action}$ is the requested operation (e.g., read, write)
- $\text{context}$ contains environmental attributes (time, location, etc.)

### Definition 4.3: Capability Structure

A capability $c \in \mathbf{C}$ is a tuple:

$$c = (\text{authority}, \text{permissions}, \text{constraints}, \text{delegation\_depth})$$

This encodes the _authority_ (the actual object or resource reference, such as a
file handle or object ID), the set of _permissions_ or rights it grants, any
_constraints_ (conditions or attenuations on usage), and a _delegation_depth_
counter if the system limits how many times it can be delegated.

This structure follows the principle of least privilege and capability
attenuation: each time a capability is delegated, it can only lose permissions
or gain constraints, never gain permissions.

## Policy Language Structure

The Lion policy language supports hierarchical composition with the following
grammar:

$$\begin{align}
\text{Policy} &::= \text{AtomicPolicy} \mid \text{CompoundPolicy} \\
\text{AtomicPolicy} &::= \text{Condition} \mid \text{CapabilityRef} \mid \text{ConstantDecision} \\
\text{CompoundPolicy} &::= \text{Policy} \land \text{Policy} \mid \text{Policy} \lor \text{Policy} \mid \neg \text{Policy} \\
&\quad \mid \text{Policy} \oplus \text{Policy} \mid \text{Policy} \Rightarrow \text{Policy} \\
\text{Condition} &::= \text{Subject} \mid \text{Resource} \mid \text{Action} \mid \text{Context} \mid \text{Temporal}
\end{align}$$

This BNF describes that a $\text{Policy}$ can be either atomic or compound.
Atomic policies include:

- Simple conditions (predicates on the request's subject, resource, etc.)
- References to capability checks
- Constants (like "always permit")

Compound policies allow combining simpler policies with logical connectives:

- $\land$ (conjunction)
- $\lor$ (disjunction)
- $\neg$ (negation)
- $\oplus$ (override operator - first policy takes precedence unless
  INDETERMINATE)
- $\Rightarrow$ (implication or conditional policy)

The exact semantics of these operators are defined in evaluation, mostly
matching logical counterparts, with $\oplus$ providing deterministic resolution
of conflicts and $\Rightarrow$ capturing hierarchical conditions.

This expressive policy language allows encoding rules such as:

- Role-based access (via conditions on subject roles)
- Context-based constraints (via context conditions)
- Temporal constraints (time windows)

---

_Next: [Policy Evaluation Framework](ch4-2-policy-evaluation.md)_
