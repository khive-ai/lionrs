# 2.2 System Model and Formal Definitions

## 2.2.1 Lion Ecosystem Architecture

The Lion ecosystem consists of four primary components operating in a
distributed capability-based security model:

- **lion\_core**: Core capability system providing unforgeable reference
  management
- **lion\_capability**: Capability derivation and attenuation logic
- **lion\_isolation**: WebAssembly-based isolation enforcement
- **lion\_policy**: Distributed policy evaluation and decision engine

These components interact to mediate all access to resources via capabilities,
enforce isolation between plugins, and check policies on-the-fly.

## 2.2.2 Formal System Definition

**Definition 2.1** (Lion Capability System): The Lion capability system $L$ is
defined as a 7-tuple:

$$L = (C, R, O, S, P, I, F)$$

Where:

- **C**: Set of all capabilities (unforgeable authority tokens)
- **R**: Set of all rights/permissions (e.g., read, write, execute)
- **O**: Set of all objects/resources (files, network connections, etc.)
- **S**: Set of all subjects (components, plugins, modules)
- **P**: Set of all policies (access control rules)
- **I**: Set of all isolation contexts (WebAssembly instances)
- **F**: Set of inter-component communication functions (the channels through
  which capabilities are transferred)

Lion's formal model thus encompasses the space of all possible capabilities and
the structural elements needed to reason about their propagation and checks.

**Definition 2.2** (Cross-Component Capability): A cross-component capability is
a 5-tuple:

$$c \in C := (\text{object}: O, \text{rights}: \mathcal{P}(R), \text{source}: S, \text{target}: S, \text{context}: I)$$

Where $\mathcal{P}(R)$ denotes the power set of rights, representing all
possible subsets of permissions. This definition captures a specific capability
instance granting a set of rights on an object, issued by a source component to
a target component, possibly scoped within an isolation context.

**Definition 2.3** (Capability Authority): The authority of a capability is the
set of object-right pairs it grants:

$$\text{authority}(c) = \{(o, r) \mid o \in \text{objects}(c), r \in \text{rights}(c)\}$$

For a given capability token $c$, $\text{authority}(c)$ formalizes exactly what
operations on which objects are permitted by possessing $c$.

**Definition 2.4** (Component Composition): Two components can be composed if
their capability interfaces are compatible:

$$\text{compatible}(s_1, s_2) \iff \exists c_1 \in \text{exports}(s_1), c_2 \in \text{imports}(s_2) : \text{match}(c_1, c_2)$$

In other words, component $s_1$ can connect to $s_2$ if $s_1$ exports a
capability that $s_2$ expects (imports), and the objects/rights match
appropriately. This lays the groundwork for secure composition—components only
interact via known capability contracts.

**Definition 2.5** (Security Properties): A component is secure if it satisfies
all capability security invariants:

$$\text{secure}(s) \iff \text{unforgeable\_refs}(s) \land \text{authority\_confinement}(s) \land \text{least\_privilege}(s) \land \text{policy\_compliance}(s)$$

Where each predicate represents a key property (capability references cannot be
forged, the component cannot obtain authority beyond what it's explicitly given,
it operates with minimal privileges, and it respects all policy rules). Only if
all hold do we consider component _s_ secure.

These definitions enable precise statements of the theorems to follow. In
particular, we will prove that if the system starts in a state where every
component satisfies these properties, and all interactions are via compatible
capabilities, then these properties continue to hold.
