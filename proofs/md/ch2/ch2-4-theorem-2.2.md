# 2.4 Theorem 2.2: Security Composition

## 2.4.1 Theorem Statement

**Theorem 2.2** (Component Composition Security Preservation): When Lion
components are composed, the security properties of individual components are
preserved in the composite system.

**Formal Statement:**

$$\forall A, B \in \text{Components}: \text{secure}(A) \land \text{secure}(B) \land \text{compatible}(A, B) \Rightarrow \text{secure}(A \oplus B)$$

where:

- $\oplus$ denotes component composition
- $\text{compatible}(A, B)$ ensures interface compatibility
- $\text{secure}(\cdot)$ is the security predicate from Definition 2.5

In other words, if each component is secure in isolation and they interact only
via authorized capabilities, then the combined system is also secure.

## 2.4.2 Proof Outline

The proof of Theorem 2.2 relies on showing that each constituent security
property from Definition 2.5 is preserved under composition. We break the proof
into supporting lemmas:

### Lemma 2.2.1: Compositional Security Properties

**Claim**: All base security invariants hold after composition: if components
$A$ and $B$ separately ensure the security properties, then $A \oplus B$ also
ensures them.

**Proof**: We prove each security property is preserved under composition:

1. **Unforgeable References**: Given
   $\text{unforgeable\_refs}(A) \land \text{unforgeable\_refs}(B)$, we show
   $\text{unforgeable\_refs}(A \oplus B)$.

   Since capabilities in the composite are either from $A$, from $B$, or
   interaction capabilities derived from both, and capability derivation
   preserves unforgeability, unforgeability is maintained.

2. **Authority Confinement**: Given individual authority confinement,
   composition preserves it because:
   $$\text{authority}(A \oplus B) = \text{authority}(A) \cup \text{authority}(B) \subseteq \text{granted\_authority}(A) \cup \text{granted\_authority}(B) = \text{granted\_authority}(A \oplus B)$$

3. **Least Privilege**: Composition does not grant additional privileges beyond
   what each component individually possesses.

4. **Policy Compliance**: All actions in the composite remain policy-compliant
   by policy composition rules.

**QED**

**Detailed reasoning**:

- _Unforgeable references_: A and B cannot forge capabilities on their own. When
  composed, any reference one might try to forge would still need to be
  validated by lion\_core, which remains global and unchanged. So,
  unforgeability holds globally if it held locally.
- _Authority confinement_: A cannot gain rights it wasn't granted, B cannot gain
  rights it wasn't granted. If A and B communicate, they can only exchange
  existing capabilities, which by Theorem 2.1 do not increase authority; thus
  neither ends up with more authority than originally allowed.
- _Least privilege_: Composition does not add new rights to either component;
  each still only has the minimum it needs (capabilities are not duplicated or
  expanded, they are merely transferred or shared).
- _Policy compliance_: Each action by A or B was policy-checked; interactions
  between them are also subject to policy checks, so all actions in the
  composite are still policy-compliant.

### Lemma 2.2.2: Interface Compatibility Preserves Security

Compatible interfaces (Definition 2.4) ensure no insecure interactions: if
components connect only through matching capability interfaces, then any action
one performs at the behest of another is one that was anticipated and
authorized.

**Proof Idea**: If `s₁` and `s₂` are composed via a matching pair of
capabilities `(c_export, c_import)`, then by definition those capabilities refer
to the same object and rights. `s₂` cannot trick `s₁` into doing more than `s₁`
explicitly offered, and `s₁` cannot misuse `s₂` beyond what `s₂` agreed to
import. This alignment means all cross-component calls respect the intended
security constraints of each component, preserving invariants like authority
confinement.

## 2.4.3 Proof of Theorem 2.2

Using the above lemmas:

- **All security properties preserved (Lemma 2.2.1)**: Each security predicate
  in `secure(s)` remains true for each component after composition. Thus, for
  composite system S = A⊕B (some composition of A and B), `unforgeable_refs(S)`,
  `authority_confinement(S)`, etc., all hold true because no new capability
  flows or authority leaks were introduced by simply co-locating the components
  or enabling their communication.

- **Interface security (Lemma 2.2.2)**: Because A and B only interact via
  compatible interfaces, there is no undefined or unexpected behavior at the
  interface. They cannot, for instance, bypass the capability system to call
  internal functions; everything is mediated by known capabilities. This ensures
  that the assumptions under which A and B were proved secure in isolation
  (namely, that any request from the outside is authorized) continue to hold
  when they talk to each other.

Given these points, we can argue: ∀ components A, B, if secure(A) ∧ secure(B)
and A, B are composed only through capabilities where `compatible(A, B)` holds,
then secure(A ⊕ B). This line of reasoning can be extended inductively to any
number of components composed into a larger system (pairwise composition
generalizes to an n-ary composition by induction).

**Conclusion**: Theorem 2.2 is proven by composition of the above lemmas: all
individual security invariants are preserved (so no property is broken), and no
new vulnerabilities are introduced at interfaces (so no new risk). Therefore,
the overall security condition (Definition 2.5) holds for the composite as well.

_(Mechanization note: A proof of compositional security is encoded in Lean,
where we represent components as state machines with invariants and show that if
invariants hold for each machine, they hold for their product. This mechanized
proof in Lean complements the high-level proof here by checking the logical
details algorithmically.)_
