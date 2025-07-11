# 2.1 Introduction

The Lion ecosystem represents a novel approach to distributed component security
through mathematically verified capability-based access control. Unlike
traditional access control models that rely on identity-based permissions,
capabilities provide unforgeable tokens that combine authority with the means to
exercise that authority.

## 2.1.1 Motivation

Traditional security models face fundamental challenges in distributed systems:

- **Ambient Authority**: Components inherit excessive privileges from their
  execution context
- **Confused Deputy Attacks**: Privileged components can be tricked into
  performing unauthorized actions
- **Composition Complexity**: Combining secure components may produce insecure
  systems
- **Privilege Escalation**: Manual permission management leads to
  over-privileging

The Lion capability system addresses these challenges through formal
mathematical guarantees rather than implementation-specific mitigations.

## 2.1.2 Contribution Overview

This chapter presents four main theoretical contributions:

1. **Theorem 2.1** (Cross-Component Capability Flow): Formal proof that
   capability authority is preserved across component boundaries with
   unforgeable references
2. **Theorem 2.2** (Security Composition): Mathematical proof that component
   composition preserves individual security properties through categorical
   composition
3. **Theorem 2.3** (Confused Deputy Prevention): Formal proof that eliminating
   ambient authority prevents confused deputy attacks through explicit
   capability passing
4. **Theorem 2.4** (Automatic POLA Enforcement): Proof that Lion's type system
   constraints automatically enforce the Principle of Least Authority (POLA),
   granting only minimal required privileges

Each theorem is supported by formal definitions and lemmas establishing the
required security invariants. We also outline how these proofs integrate with
mechanized models (TLA+ and Lean) and inform the implementation in Rust.
