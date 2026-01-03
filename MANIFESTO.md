# Capability-Bounded Autonomous Reasoning

> A Manifesto for Formally Verified Agentic Systems
>
> Lion Project, 2026

---

## I. The Problem

We are building systems that reason. Not systems that merely compute—systems that pursue
goals, form plans, adapt strategies, and take actions in open environments.

These systems inherit the power of human-level reasoning without inheriting the social
structures that make human reasoning safe: accountability, mortality, reputation,
empathy, shared vulnerability.

The question is not whether autonomous reasoning systems will be deployed. The question
is whether they will be deployed with formal guarantees or with hope and prayer.

---

## II. The Failure of Traditional Security

Classical computer security assumes a separation between:

- **Code**: deterministic, analyzable, bounded
- **Data**: passive, structured, controlled
- **Users**: external, authenticated, accountable

This separation dissolves when the executing entity can reason:

- Code becomes _intent_—goals that may be pursued through unforeseen means
- Data becomes _context_—information that shapes reasoning in complex ways
- Users become _collaborators_—or adversaries, or both, dynamically

Firewalls do not stop an agent from reasoning its way around restrictions. Access
control lists do not bind a system that can request, persuade, or manipulate its way to
elevated privileges. Sandboxes do not contain an entity that can reason about their
boundaries.

The traditional model is not wrong. It is _incomplete_.

---

## III. Capabilities as the Primitive

We propose **capabilities** as the fundamental primitive for bounding autonomous
reasoning.

A capability is:

1. **Unforgeable**: cannot be created except by delegation from existing capability
2. **Transferable**: can be passed between principals according to policy
3. **Attenuable**: can only be weakened, never strengthened, upon transfer
4. **Revocable**: can be invalidated by the granting authority

Unlike permissions (which ask "who are you?"), capabilities ask "what can you prove
you're allowed to do?" This shift is crucial for autonomous systems:

- An agent's _identity_ is fluid and contestable
- An agent's _capabilities_ are cryptographically verifiable
- Authority flows through explicit delegation, not implicit trust

**The Confinement Theorem**: An agent holding capability C cannot affect resources
outside C's transitive closure, regardless of the agent's reasoning capabilities.

This is not a policy. It is a mathematical theorem, proven in Lean4, dependent only on
cryptographic assumptions that can themselves be discharged.

---

## IV. Information Flow as Invariant

Autonomous systems process information. The security question becomes: _where can
information flow?_

We adopt **Termination-Insensitive Noninterference (TINI)** as our core information flow
property:

> If two initial states are indistinguishable at security level L, and both executions
> terminate without declassification, then their final states are indistinguishable at
> level L.

In simpler terms: high-security information cannot leak to low-security observers
through the system's normal operation.

**The TINI Theorem** (proven, not assumed):

```lean
∀ L s₁ s₂, s₁ ≈_L s₂ → terminates(s₁) → terminates(s₂) →
  final(s₁) ≈_L final(s₂)
```

The proof uses **stuttering bisimulation**: even when executions take different paths
(as reasoning systems will), their observable effects at each security level remain
synchronized.

---

## V. The Trust Hierarchy

Not all components can be verified to the same degree. We explicitly stratify trust:

**Layer 0: Mathematical Foundations** (Lean4 + Mathlib)

- Trusted: type theory, proof checker, standard library
- Verified: our theorems, our definitions, our proofs

> **Layer 1: Cryptographic Primitives**

- Trusted: HMAC security, hash collision resistance, authenticated encryption
- Dischargeable: via cryptographic proofs or verified implementations (HACL*)

> **Layer 2: Runtime Isolation**

- Trusted: memory isolation, process separation, time monotonicity
- Dischargeable: via verified kernels (seL4) or hardware guarantees (TDX)

> **Layer 3: Implementation Correspondence**

- Trusted: Rust implementation matches Lean specification
- Dischargeable: via testing, auditing, or verified extraction

Each layer can be audited independently. Each assumption is explicit. The trusted
computing base (TCB) is minimized and documented.

---

## VI. Composition over Monoliths

Autonomous systems are not built; they are _composed_.

A reasoning agent is:

- A capability holder (what it can affect)
- A message processor (how it receives information)
- A goal pursuer (what it tries to achieve)
- A plugin in a larger system (how it relates to others)

**The Compositionality Principle**: If agents A and B each satisfy security properties
P_A and P_B with respect to their capabilities, then their composition satisfies P_A ∧
P_B with respect to their combined capabilities.

This is not obvious. Most security properties are not compositional. Capability
security, properly formalized, achieves compositionality through:

1. **Authority encapsulation**: an agent's authority is exactly its capabilities
2. **No ambient authority**: there is no "root" or "admin" mode
3. **Explicit delegation**: capability transfer is a first-class operation

---

## VII. The Declassification Problem

Information flow control has a fundamental tension: useful systems must sometimes
_intentionally_ release information. A medical system must share diagnoses. A financial
system must report transactions.

We handle this through **explicit declassification**:

1. Declassification is a capability (not all agents can declassify)
2. Declassification is logged (creates audit trail)
3. Declassification is bounded (cannot declassify more than held)
4. TINI holds _in the absence of_ declassification

The theorems separate:

- **Baseline security**: what holds when no one declassifies
- **Controlled release**: what happens when authorized declassification occurs

This separation allows formal reasoning about both security and functionality.

---

## VIII. The Agentic Difference

Why does this matter specifically for autonomous reasoning systems?

**Traditional programs**: behavior is determined by code **Agentic systems**: behavior
emerges from goals + context + reasoning

This means:

- We cannot enumerate all possible behaviors
- We cannot test all possible inputs
- We cannot rely on code review alone

We _can_:

- Bound what resources an agent can affect (capabilities)
- Prove that information flows only where permitted (TINI)
- Verify that composition preserves security (compositionality)
- Audit the trusted computing base explicitly (TCB minimization)

The proofs don't constrain _what_ an agent reasons. They constrain _what the reasoning
can affect_.

---

## IX. Implementation Principles

Theory without implementation is philosophy. These principles guide Lion:

1. **Specification first**: Lean4 formalization before Rust code
2. **Correspondence checking**: implementation tested against spec
3. **Minimal kernel**: only capability operations in trusted core
4. **Plugin isolation**: untrusted code runs in sandboxed plugins
5. **Cryptographic delegation**: capabilities are HMAC-sealed tokens
6. **Revocation built-in**: authority can always be withdrawn

The kernel is small enough to verify. The plugins are isolated enough to contain. The
protocols are simple enough to audit.

---

## X. What We Have Proven

As of this writing, the Lion formal verification includes:

**Core Security Theorems**:

- Capability unforgeability
- Delegation confinement
- TINI (termination-insensitive noninterference)
- High-step confinement
- Revocation completeness

**Infrastructure Theorems**:

- Stuttering bisimulation correctness
- Joint trace simulation
- Unwinding lemma composition
- Star (reflexive-transitive closure) properties

**Trusted Assumptions** (explicit, auditable):

- Cryptographic primitive security (MAC, hash, seal)
- Runtime isolation (memory, execution, time)
- Implementation correspondence (types, operations)

Zero sorries. Three trust bundles. Compilable proofs.

---

## XI. The Path Forward

This is not complete. This is a foundation.

**Near-term**:

- Reduce axioms through proof (mathematical and semantic)
- Rust implementation matching Lean specification
- Integration with existing agentic frameworks

**Medium-term**:

- Verified extraction from Lean to Rust
- Hardware-backed capability enforcement
- Distributed capability protocols

**Long-term**:

- Formal semantics for goal-directed reasoning
- Provable alignment through capability restriction
- Security theorems that compose across organizational boundaries

---

## XII. The Stakes

We are not building toys. We are not writing academic exercises.

Autonomous systems will manage infrastructure, handle finances, make medical decisions,
control physical systems. The question of "what can this system affect?" must have a
mathematical answer, not a hopeful guess.

The capability model is old (Dennis & Van Horn, 1966). The information flow model is
established (Denning, 1976). The proof techniques are mature (stuttering bisimulation,
unwinding). What is new is the application:

**Formal security for systems that reason.**

When an agent is deployed with Lion's formal guarantees:

- Its authority is exactly its capabilities—no more
- Its information flow is bounded by security levels—provably
- Its composition with other agents is safe—by theorem

This is what it means to build trustworthy autonomous systems.

---

## XIII. Invitation

This manifesto is not a declaration of completion. It is a statement of direction.

To the skeptics: the proofs compile. Examine them.

To the researchers: the foundations are open. Build on them.

To the engineers: the implementation is underway. Contribute.

To the policymakers: this is what "provable AI safety" can mean. Demand it.

---

_The Lion Project_ _Capability-Bounded Autonomous Reasoning_ _2026_

---

## Appendix: Key Definitions

**Capability**: An unforgeable token granting specific rights over specific resources.

**Low-equivalent**: Two states that are indistinguishable to observers at or below
security level L.

**TINI**: Termination-Insensitive Noninterference—high secrets don't leak to low
observers in terminating, non-declassifying executions.

**Stuttering bisimulation**: A simulation relation allowing one side to take multiple
steps while the other stutters, maintaining equivalence.

**TCB**: Trusted Computing Base—the set of components that must be correct for security
guarantees to hold.

**Confinement**: The property that a subsystem cannot affect resources outside its
granted capabilities.

---

## Appendix: Repository Structure

```text
formal-proofs/
├── Lion/
│   ├── Core/           # Cryptography, capabilities, runtime
│   ├── State/          # System state formalization
│   ├── Step/           # Transition relation
│   ├── Theorems/       # Security proofs
│   ├── Contracts/      # Implementation correspondence
│   └── Refinement/     # Spec-to-impl refinement
└── MANIFESTO.md        # This document
```

---

## Appendix: Citation

If this work informs your research:

```bibtex
@misc{lion2026,
  title={Lion: Capability-Bounded Autonomous Reasoning},
  author={Li, Haiyang (Ocean)},
  year={2025},
  note={Formal verification in Lean4},
  url={https://github.com/khive-ai/lionrs}
}
```
