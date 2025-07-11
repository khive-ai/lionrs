# 2.5 Theorem 2.3: Confused Deputy Prevention

## 2.5.1 Background and Theorem Statement

A _confused deputy_ occurs when a program with authority is manipulated to use
its authority on behalf of another (potentially less privileged) entity. Lion
eliminates ambient authority, requiring explicit capabilities for every
privileged action, thereby preventing confused deputy scenarios.

**Theorem 2.3** (Confused Deputy Prevention): In the Lion capability model, no
component can exercise authority on behalf of another component without an
explicit capability transfer; hence, classic confused deputy attacks are not
possible.

**Formal Statement:**

$$\forall A, B \in S, \forall o \in O, \forall r \in R, \forall \text{action} \in \text{Actions}: \text{perform}(B, \text{action}, o, r) \Rightarrow \exists c \in \text{capabilities}(B) : (o, r) \in \text{authority}(c)$$

where:

- $S$ is the set of all system components
- $O$ is the set of all objects/resources
- $R$ is the set of all rights/permissions
- $\text{perform}(B, \text{action}, o, r)$ models component B performing an
  action on object o with rights r
- $\text{capabilities}(B)$ gives the set of capabilities held by component B
- $\text{authority}(c)$ gives the authority set of capability c

**Informal Statement:** If a component _B_ performs an action _a_ on an object
_o_ with rights _r_, then _B_ must possess a capability granting _(o, r)_, or
the action is denied. Even if another component _A_ tricked _B_ into performing
_a_, _B_ cannot do so unless it was explicitly granted the needed capability (by
design, _A_ cannot grant _B_ more authority than _A_ itself has, and all such
grants are controlled).

## 2.5.2 Formal Proof Strategy

To prove Theorem 2.3, we formalize the absence of ambient authority and then
show how that ensures confused deputy immunity. We introduce supporting lemmas
corresponding to critical conditions:

### Lemma 2.3.1: No Ambient Authority

**Claim**: The Lion system has no ambient authority — components have no default
permissions without capabilities.

**Proof**: By design, every action that could affect another component or
external resource requires presenting a capability token. A component's initial
state contains no capabilities except those explicitly bestowed (initial
capabilities are given only to TCB components and are tightly limited).
Formally:

```
∀ s ∈ S, (∀ o ∈ O, r ∈ R : ¬can_access(s, o, r) unless ∃ c ∈ C held_by(s) with (o, r) ∈ authority(c))
```

This is enforced by the lion\_core reference monitor. Therefore, a component
cannot simply perform actions out of the blue; it must use a capability.

_(Mechanized note: We have modeled this property in TLA+ by asserting that any
`Next` state action representing resource access has a precondition of
possessing a corresponding capability. The model checker confirms that any state
where a component acts without a capability is unreachable.)_

### Lemma 2.3.2: Explicit Capability Passing

**Claim**: All capability authority must be explicitly passed between components
(no global mutable state or hidden channels exist for privilege escalation).

**Proof**: Lion's only means for sharing authority is via capability invocation
or transfer calls. If component A wants component B to have some authority, A
must invoke an operation in lion\_capability (e.g., `delegate` or `send`) to
create or send an appropriate capability to B. This action is recorded and
mediated. There are no alternative pathways (such as environment variables or
global ambient contexts) where authority can creep from A to B implicitly. We
model the system state such that the capability store and each component's
capability list are the sole sources of authority tokens; cross-component lists
do not spontaneously change unless a transfer event occurs.

### Lemma 2.3.3: Capability Confinement

**Claim**: Capabilities cannot be used to perform actions beyond their intended
scope.

**Proof**: A capability encapsulates specific rights on specific objects. If
component B has a capability for file X with only read permission, even if B is
tricked into acting on behalf of A, B cannot use that capability to write to X
or access a different file Y — the capability simply doesn't permit it.
Furthermore, if A asks B to do something for which B lacks a capability
entirely, B will be unable to comply (the action will be denied by lion\_core).
In formal terms, for any capability `c` that B holds and any attempted action
`a` by B on object `o`:

```
perform(B, a, o) ⟹ ∃ c ∈ held_by(B) such that (o, action_right(a)) ∈ authority(c)
```

If `a` is outside the authority of all B's capabilities, the operation is
blocked. Thus, even a misled component can only do what its tokens allow.

## 2.5.3 Proof of Theorem 2.3

Given the above lemmas:

- **No ambient authority (Lemma 2.3.1)** means a less-privileged component
  cannot indirectly exploit a more-privileged one unless that privileged
  component explicitly uses a capability on the less-privileged component's
  behalf.
- **Explicit authority requirement (Lemma 2.3.2)** ensures that any authority
  transfer from A to B is deliberate and logged – there is no accidental bleed
  of authority. In a confused deputy scenario, a malicious component _M_ might
  attempt to trick deputy _D_ into using _D_'s authority. In Lion, _D_ would
  need to have explicitly received that authority via a capability. If _M_
  doesn't hold it, it can't grant it to _D_; if _D_ doesn't already have it, _D_
  can't act.
- **Capability confinement (Lemma 2.3.3)** states that even if _D_ has some
  capability, its use is confined to that capability's scope – _D_ can't go
  beyond it, even if _M_ requests.

Combining these, assume by contradiction that a confused deputy attack is
possible: a malicious component _M_ causes deputy _D_ to perform an unauthorized
action _a_. Because _D_ performs _a_, and Lion has no ambient authority, _D_
must have a capability for _a_. How did _D_ get it? Not from thin air (Lemma
2.3.1), not implicitly (Lemma 2.3.2) – _M_ would have to provide it, but _M_ by
assumption isn't authorized for _a_, so _M_ doesn't have that capability to
give. Therefore, the scenario fails. Formally, we derive a contradiction with
the assumptions unless the action was authorized for _D_ to begin with, in which
case it's not confused deputy, just normal operation.

Hence, Theorem 2.3 is established: the Lion capability system structurally
prevents confused deputies by removing the underlying cause (ambient authority).
Any component's authority is explicit and cannot be leveraged by another
component without proper capability transfer.
