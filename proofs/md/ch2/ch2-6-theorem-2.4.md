# 2.6 Theorem 2.4: Automatic POLA Enforcement

## 2.6.1 Principle of Least Authority (POLA) in Lion

The Principle of Least Authority dictates that each component should operate
with the minimum privileges necessary. Lion's design automates POLA via its type
system and capability distribution: components are by default given no authority
beyond what is passed to them as capabilities.

**Theorem 2.4** (Automatic POLA Enforcement): The Lion system's static and
dynamic mechanisms ensure that each component's accessible authority is
minimized automatically, without requiring manual configuration. In particular,
the type system and capability derivation logic guarantee that components can
only exercise the specific privileges that have been intentionally delegated to
them.

## 2.6.2 Key Mechanisms and Lemmas

To prove Theorem 2.4, we highlight and formalize the mechanisms that enforce
POLA:

### Lemma 2.4.1: Type System Enforces Minimal Authority

**Claim**: The Lion Rust-based type system prevents granting excessive authority
by construction. If a capability is not in a component's type-defined interface,
that component cannot receive or use it.

**Proof (Outline)**: Each component's interface (capabilities it can consume or
produce) is encoded as Rust trait bounds or phantom types in the Lion codebase.
For example, if component _X_ is only supposed to read files, it might implement
a trait `FileReader` that provides a method requiring a `ReadCapability<File>`
type. It will not even compile code that attempts to use a `WriteCapability`.
Thus, by static analysis, any attempt to give _X_ more authority (like a write
capability) results in a type error. This is an enforcement of POLA at compile
time: the component's code literally cannot handle capabilities outside its
declared scope.

### Lemma 2.4.2: Capability Derivation Implements Attenuation

**Claim**: All capability derivation operations can only reduce authority (never
increase it).

**Proof**: Lion's capability manager provides functions to derive new
capabilities (for delegation or attenuation). For example, an operation
`derive(c, new_rights, constraints)` will produce a child capability `c_child`
such that:

$$\text{authority}(c_{\text{child}}) \subseteq \text{authority}(c)$$

and possibly with additional restrictions (constraints, shorter expiry, etc.).
The code and formal spec reflect this: any `new_authority` chosen for a
derivative capability must be a subset of the original, and any added
constraints only narrow its usage. Thus, no derivation yields a more powerful
capability than the original.

### Lemma 2.4.3: Automatic Minimal Capability Derivation

**Claim**: The system automatically provides minimal capabilities for
operations, i.e., whenever a component requests an operation, Lion grants a
capability scoped strictly to that operation's needs, no more.

**Proof**: When a component performs an operation like opening a file or sending
a network message, the runtime (capability manager and core) often synthesizes
ephemeral capabilities narrowly scoped to that operation. For example,
`open_file(path, mode)` might internally result in a capability token granting
just _mode_ access to _path_, returned to the component. This token cannot be
used for any other file or extended privileges. Because the capability manager
always chooses the minimal rights required (and because of Lemma 2.4.2, it could
derive such a token from a broader one but not vice versa), the component ends
up with only that minimal token. In formal terms, if `op` is an operation
requiring authority `α`, the system ensures `c` it provides satisfies
$\text{authority}(c) = \alpha$ and by Lemma 2.4.2 `c` is minimal for performing
`op`.

_(Example)_: If a component has a capability to a directory, and it requests
access to a file within, the system might create a new capability for that file
alone (attenuating the directory capability). That new capability `c_file` is
minimal: it has no rights beyond the file and operations requested. This is done
automatically by the framework.

## 2.6.3 Proof of Theorem 2.4

By combining these lemmas:

- **Minimal types (Lemma 2.4.1)**: The design-time privileges of components are
  limited to what their interface allows. No component can even _express_ code
  that uses more authority than granted.
- **Attenuation (Lemma 2.4.2)**: At runtime, when capabilities are delegated,
  they are always <= the original authority. So a chain of delegations cannot
  accumulate into more authority; it can only maintain or diminish.
- **Automatic minimization (Lemma 2.4.3)**: The system proactively attenuates
  capabilities for each operation. Components end up handling tokens that are
  just sufficient.

Therefore, each component in Lion naturally operates with the least authority.
Even if a developer inadvertently tries to use more, the system's compile-time
and runtime checks prevent it. There is no way to step outside this confinement
without explicitly modifying the system's trusted core, which we consider out of
scope (and which is verified separately).

From a formal perspective: For any component _s_ and any operation _op_ that _s_
performs involving a resource _o_, there exists a capability _c_ held by _s_
such that $(o, \text{required\_rights}(op)) \in \text{authority}(c)$, and for
all c' held by s, $\text{authority}(c') \not\subset \text{authority}(c)$ (no
strictly larger authority is held). This captures that _c_ is minimal and _s_
has nothing excessive beyond _c_. Theorem 2.4 follows, completing our proof that
POLA is automatically enforced by Lion.
