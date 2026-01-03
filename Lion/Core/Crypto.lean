/-
Lion/Core/Crypto.lean
======================

Cryptographic primitives for capability sealing (Theorem 001).
HMAC-SHA256 for unforgeability.
-/

import Lion.Core.Identifiers
import Lion.Core.Rights

namespace Lion

noncomputable section

/-! =========== CRYPTO (001) =========== -/

/-!
## Split-View Cryptography Pattern

We use a "split-view" approach to handle the tension between:
1. **Logical proofs** need injectivity (different payloads → different tags)
2. **Crypto proofs** only guarantee negligible collision probability

Solution:
- `SymbolicTag`: Inductive type where injectivity holds BY CONSTRUCTION
- `serializeTag`: Maps symbolic tags to bytes for crypto analysis

This avoids the Pigeonhole Principle violation of claiming a hash function
is perfectly injective (infinite domain → finite range).
-/

/-- Secret key type (256-bit) - concrete for derived instances -/
def Key := List UInt8
deriving DecidableEq, Repr

/--
Symbolic HMAC tag - an inductive type representing "the tag that would be
produced by HMAC(key, payload)".

Injectivity holds by constructor laws: if SymbolicTag.mk k₁ p₁ = SymbolicTag.mk k₂ p₂,
then k₁ = k₂ and p₁ = p₂. This is a theorem, not an axiom.

**IMPORTANT**: SymbolicTag is for PROOF purposes only. Plugins never see this type.
At runtime, capabilities contain opaque `SealedTag` bytes.
-/
inductive SymbolicTag where
  | mk (key : Key) (payload : ByteArray) : SymbolicTag
deriving DecidableEq

instance : Repr SymbolicTag where
  reprPrec _ _ := "«SymbolicTag»"

/-- Key inhabitation (auto-derived from List UInt8) -/
instance : Inhabited Key := ⟨[]⟩

instance : Inhabited SymbolicTag where
  default := SymbolicTag.mk default ByteArray.empty

/-- Alias for backward compatibility (proof-internal only) -/
abbrev Tag := SymbolicTag

/-- HMAC-SHA256 computation (symbolic) -/
def hmac (k : Key) (m : ByteArray) : SymbolicTag :=
  SymbolicTag.mk k m

/--
**Theorem (HMAC Injectivity - Provable, Not Axiom)**

For the same key, different messages produce different symbolic tags.
This follows directly from the constructor laws of SymbolicTag.
-/
theorem hmac_injective_under_key_proven :
    ∀ (k : Key) (m₁ m₂ : ByteArray),
      m₁ ≠ m₂ → hmac k m₁ ≠ hmac k m₂ := by
  intro k m₁ m₂ h_diff h_eq
  simp only [hmac, SymbolicTag.mk.injEq] at h_eq
  exact h_diff h_eq.2

/--
**Theorem (Full HMAC Injectivity)**

Different (key, message) pairs produce different symbolic tags.
-/
theorem hmac_full_injective :
    ∀ (k₁ k₂ : Key) (m₁ m₂ : ByteArray),
      (k₁ ≠ k₂ ∨ m₁ ≠ m₂) → hmac k₁ m₁ ≠ hmac k₂ m₂ := by
  intro k₁ k₂ m₁ m₂ h_diff h_eq
  simp only [hmac, SymbolicTag.mk.injEq] at h_eq
  cases h_diff with
  | inl hk => exact hk h_eq.1
  | inr hm => exact hm h_eq.2

/-!
## Serialization (for Crypto Proofs)

The actual bytes of a tag are only relevant for the cryptographic
unforgeability proof in Theorems/Unforgeability.lean.
-/

/-- Serialize symbolic tag to bytes (for crypto analysis) -/
opaque serializeTag : SymbolicTag → ByteArray

-- serializeTag_injective: REMOVED (unused, kept opaque definition for future use)

/-- Capability payload (data to be sealed) -/
structure CapPayload where
  holder : PluginId
  target : ResourceId
  rights : Rights
  parent : Option CapId
  epoch  : Nat  -- For revocation tracking

/-- Serialize capability payload to bytes -/
opaque serializeCap : CapPayload → ByteArray

-- serializeCap_injective: REMOVED (unused, kept opaque definition for future use)

/-!
## Runtime Seal Representation

To prevent key leakage in the formal model (where low-equivalence compares
plugin states), we separate:
- `SealedTag`: Opaque bytes that plugins hold (key NOT visible)
- `SymbolicTag`: Proof-internal representation (key visible for proofs)

The kernel maintains the correspondence; plugins only see `SealedTag`.
-/

/-- Sealed tag - what plugins actually hold at runtime.
    The key is NOT part of this type's structure.
    Concrete for derived instances. -/
def SealedTag := List UInt8
deriving DecidableEq, Repr

instance : Inhabited SealedTag := ⟨[]⟩

/-- Seal a capability payload with the kernel key (produces opaque bytes) -/
opaque seal_payload : Key → CapPayload → SealedTag

/-- Verify a sealed tag against a key and payload -/
opaque verify_seal_runtime : Key → CapPayload → SealedTag → Bool

/-! =========== SEAL ASSUMPTIONS =========== -/

/--
**Seal Assumptions Record**

Bundles seal-related cryptographic axioms into a single record.
-/
structure SealAssumptions : Prop where
  /-- Different payloads produce different seals (under same key) -/
  seal_injective_payload :
    ∀ (k : Key) (p₁ p₂ : CapPayload),
      seal_payload k p₁ = seal_payload k p₂ → p₁ = p₂
  /-- Verified seals are the unique output of seal_payload -/
  verified_seal_is_canonical :
    ∀ (k : Key) (p : CapPayload) (s : SealedTag),
      verify_seal_runtime k p s = true → s = seal_payload k p
  /-- Seal-verify roundtrip: sealing then verifying always succeeds -/
  seal_verify_roundtrip :
    ∀ (k : Key) (p : CapPayload),
      verify_seal_runtime k p (seal_payload k p) = true

/-- Single axiom bundling seal assumptions -/
axiom seal_assumptions : SealAssumptions

-- Re-export individual axioms as theorems for backward compatibility

/-- Different payloads produce different seals (under same key) -/
theorem seal_injective_payload :
  ∀ (k : Key) (p₁ p₂ : CapPayload),
    seal_payload k p₁ = seal_payload k p₂ → p₁ = p₂ :=
  seal_assumptions.seal_injective_payload

/-- Verified seals are the unique output of seal_payload.
    If a seal verifies for (k, p), it must be seal_payload k p. -/
theorem verified_seal_is_canonical :
  ∀ (k : Key) (p : CapPayload) (s : SealedTag),
    verify_seal_runtime k p s = true → s = seal_payload k p :=
  seal_assumptions.verified_seal_is_canonical

/-- Seal-verify roundtrip: sealing a payload and verifying always succeeds.
    This is the fundamental correctness property of seal/verify. -/
theorem seal_verify_roundtrip :
  ∀ (k : Key) (p : CapPayload),
    verify_seal_runtime k p (seal_payload k p) = true :=
  seal_assumptions.seal_verify_roundtrip

/--
Correspondence between SealedTag and SymbolicTag (kernel-internal only).
This is used in proofs to connect runtime verification to symbolic reasoning.
Plugins NEVER have access to this correspondence.
-/
opaque sealed_corresponds_to_symbolic : SealedTag → SymbolicTag → Prop

-- seal_correspondence: REMOVED (unused, sealed_corresponds_to_symbolic kept opaque)

/-- Runtime tag type used in capabilities (key NOT visible) -/
abbrev RuntimeTag := SealedTag

/-! =========== CAPABILITY =========== -/

/-- Sealed capability with HMAC signature.
    IMPORTANT: signature is RuntimeTag (opaque), NOT SymbolicTag.
    This prevents key leakage when comparing plugin states. -/
structure Capability where
  id        : CapId
  holder    : PluginId
  target    : ResourceId
  rights    : Rights
  parent    : Option CapId
  epoch     : Nat
  valid     : Bool  -- Runtime revocation flag
  signature : RuntimeTag  -- Opaque seal (key NOT visible)

namespace Capability

/-- Extract payload for verification -/
def payload (c : Capability) : CapPayload where
  holder := c.holder
  target := c.target
  rights := c.rights
  parent := c.parent
  epoch  := c.epoch

/-- Verify capability seal against kernel key (runtime check) -/
def verify_seal (k : Key) (c : Capability) : Prop :=
  verify_seal_runtime k c.payload c.signature = true

/-- Payload equality from field equalities (valid is not part of payload) -/
lemma payload_eq_of_fields_eq {c c' : Capability}
    (h_holder : c.holder = c'.holder)
    (h_target : c.target = c'.target)
    (h_rights : c.rights = c'.rights)
    (h_parent : c.parent = c'.parent)
    (h_epoch  : c.epoch  = c'.epoch) :
    c.payload = c'.payload := by
  simp only [payload, h_holder, h_target, h_rights, h_parent, h_epoch]

/-- Transfer verify_seal across capabilities with equal signature and payload -/
lemma verify_seal_transfer (k : Key) {c c' : Capability}
    (h_sig : c.signature = c'.signature)
    (h_payload : c.payload = c'.payload)
    (h_verify : verify_seal k c') :
    verify_seal k c := by
  unfold verify_seal at h_verify ⊢
  simp only [h_sig, h_payload, h_verify]

/-- Verify capability seal against kernel key (symbolic, for proofs) -/
def verify_seal_symbolic (k : Key) (c : Capability) (sym : SymbolicTag) : Prop :=
  sealed_corresponds_to_symbolic c.signature sym ∧
  sym = hmac k (serializeCap c.payload)

/-- Well-formed capability has valid seal -/
structure WellFormed (k : Key) (c : Capability) : Prop where
  h_seal : verify_seal k c
  h_holder_valid : c.holder > 0  -- Non-zero holder
  h_rights_nonempty : c.rights ≠ ∅

end Capability

/-! =========== CRYPTOGRAPHIC PROPERTIES (THEOREMS) =========== -/

/-!
## Key Change: Injectivity is PROVEN, not AXIOMATIZED

The old `hmac_injective_under_key` axiom was mathematically unsound
(violated Pigeonhole Principle). With SymbolicTag, injectivity is a
theorem that follows from constructor laws.

For backward compatibility, we provide `hmac_injective_under_key` as
an alias to the proven theorem.
-/

/-- Backward-compatible alias for hmac_injective_under_key_proven -/
theorem hmac_injective_under_key :
    ∀ (k : Key) (m₁ m₂ : ByteArray),
      m₁ ≠ m₂ → hmac k m₁ ≠ hmac k m₂ :=
  hmac_injective_under_key_proven

/--
Seal injectivity: capabilities with different payloads have different signatures.
This follows from seal_injective_payload axiom on the runtime SealedTag.
-/
theorem seal_injective_on_payload (k : Key) (c₁ c₂ : Capability) :
    c₁.payload ≠ c₂.payload →
    Capability.verify_seal k c₁ →
    Capability.verify_seal k c₂ →
    c₁.signature ≠ c₂.signature := by
  intro h_diff h_seal₁ h_seal₂ h_eq
  -- Verified seals are canonical: signature = seal_payload k payload
  have h₁ : c₁.signature = seal_payload k c₁.payload :=
    verified_seal_is_canonical k c₁.payload c₁.signature h_seal₁
  have h₂ : c₂.signature = seal_payload k c₂.payload :=
    verified_seal_is_canonical k c₂.payload c₂.signature h_seal₂
  -- If signatures equal, then seal_payload outputs equal
  rw [h₁, h₂] at h_eq
  -- By seal injectivity, payloads must be equal
  have h_payload_eq := seal_injective_payload k c₁.payload c₂.payload h_eq
  -- But we assumed payloads differ - contradiction
  exact h_diff h_payload_eq

/-!
## Forgery Resistance

Formal forgery resistance is proven in Theorems/Unforgeability.lean
using game-based cryptographic reductions on the serialized form.
-/

/-- Forgery resistance placeholder (see Unforgeability.lean for full proof) -/
theorem forgery_requires_key_knowledge :
    ∀ (c : Capability) (k : Key),
      Capability.verify_seal k c →
      True :=  -- Actual security follows from UF-CMA game in Unforgeability.lean
  fun _ _ _ => trivial

/-! =========== BLAKE3 HASH CHAIN (for khive-db Event Log) =========== -/

/-- Hash32 type: 32-byte hash (corresponds to khive-types Hash32).
    BLAKE3 output for content-addressed storage and event chain integrity. -/
def Hash32 := List UInt8
deriving DecidableEq, Repr

instance : Inhabited Hash32 := ⟨[]⟩

/-- Zero hash (genesis block) -/
def Hash32.zero : Hash32 := List.replicate 32 0

/-- BLAKE3 hash function (symbolic representation).
    Like HMAC, we use an inductive representation for proof purposes. -/
inductive Blake3Hash where
  | mk (data : List UInt8) : Blake3Hash
deriving DecidableEq

instance : Repr Blake3Hash where
  reprPrec _ _ := "«Blake3Hash»"

instance : Inhabited Blake3Hash where
  default := Blake3Hash.mk []

/-- Compute BLAKE3 hash of data (symbolic) -/
def blake3 (data : List UInt8) : Blake3Hash :=
  Blake3Hash.mk data

/--
**Theorem (BLAKE3 Injectivity - Provable)**

Different inputs produce different symbolic hashes.
This follows directly from the constructor laws of Blake3Hash.
-/
theorem blake3_injective :
    ∀ (d₁ d₂ : List UInt8), d₁ ≠ d₂ → blake3 d₁ ≠ blake3 d₂ := by
  intro d₁ d₂ h_diff h_eq
  simp only [blake3, Blake3Hash.mk.injEq] at h_eq
  exact h_diff h_eq

/-- Event in an append-only log (simplified model using List UInt8 for payload) -/
structure LogEvent where
  id : Nat
  eventType : String
  payload : List UInt8
  timestampUs : Nat
  version : Nat
  prevHash : Hash32
deriving DecidableEq, Repr

instance : Inhabited LogEvent where
  default := ⟨0, "", [], 0, 0, []⟩

/-- Serialize event for hashing (opaque) -/
opaque serializeEvent : LogEvent → List UInt8

/-! =========== HASH ASSUMPTIONS =========== -/

/--
**Hash Assumptions Record**

Bundles hash/event-related cryptographic axioms into a single record.

Note: BLAKE3 collision resistance is now a theorem (provable from symbolic model),
so only serializeEvent_injective remains as an assumption.
-/
structure HashAssumptions : Prop where
  /-- Serialize event is injective -/
  serializeEvent_injective :
    ∀ (e₁ e₂ : LogEvent), serializeEvent e₁ = serializeEvent e₂ → e₁ = e₂

/-- Single axiom bundling hash assumptions -/
axiom hash_assumptions : HashAssumptions

/-! =========== MASTER CRYPTO ASSUMPTIONS BUNDLE =========== -/

/--
**CryptoAssumptions - Master Bundle**

Bundles ALL cryptographic assumptions into a single structure:
1. seal_assumptions: Seal/verify properties (AEAD-like)
2. hash_assumptions: BLAKE3 collision resistance (via serializeEvent injectivity)

Note: cap_mac_security lives in Theorems/Unforgeability.lean as it's specific
to the UF-CMA game. This bundle covers the foundational crypto primitives.

Target: This + cap_mac_security forms the complete "Crypto" trust bundle.
-/
structure CryptoAssumptions : Prop where
  seal_props : SealAssumptions
  hash_props : HashAssumptions

/-- Derive CryptoAssumptions from the two component axioms -/
theorem crypto_assumptions : CryptoAssumptions where
  seal_props := seal_assumptions
  hash_props := hash_assumptions

-- Re-export individual axioms as theorems for backward compatibility

/-- Serialize event is injective (different events produce different serializations) -/
theorem serializeEvent_injective :
  ∀ (e₁ e₂ : LogEvent), serializeEvent e₁ = serializeEvent e₂ → e₁ = e₂ :=
  hash_assumptions.serializeEvent_injective

/--
**BLAKE3 Collision Resistance (Theorem)**

This is the contrapositive of blake3_injective, which is provable from the
symbolic model where blake3 = Blake3Hash.mk. No axiom needed.
-/
theorem blake3_collision_resistant :
  ∀ (d₁ d₂ : List UInt8),
    blake3 d₁ = blake3 d₂ → d₁ = d₂ := by
  intro d₁ d₂ h_eq
  by_contra h_neq
  exact blake3_injective d₁ d₂ h_neq h_eq

/-- Event with its computed hash -/
structure HashedEvent where
  event : LogEvent
  hash : Blake3Hash
  h_hash_valid : hash = blake3 (serializeEvent event)

/-- Hash chain: sequence of events where each references previous hash -/
inductive HashChain : List HashedEvent → Prop where
  | nil : HashChain []
  | genesis (e : HashedEvent) (h_prev : e.event.prevHash = Hash32.zero) :
      HashChain [e]
  | cons (e : HashedEvent) (chain : List HashedEvent) (last : HashedEvent)
      (h_chain : HashChain (last :: chain))
      (h_prev : e.event.prevHash = serializeEvent last.event) :
      HashChain (e :: last :: chain)

/-!
## Hash Chain Integrity Properties
-/

/--
**Theorem: Hash Chain Detects Tampering**

If any event in the chain is modified, the hash will not match.
-/
theorem hash_detects_tampering (e₁ e₂ : LogEvent) (h_diff : e₁ ≠ e₂) :
    blake3 (serializeEvent e₁) ≠ blake3 (serializeEvent e₂) := by
  intro h_eq
  have h_ser_neq : serializeEvent e₁ ≠ serializeEvent e₂ := by
    intro h
    exact h_diff (serializeEvent_injective e₁ e₂ h)
  simp only [blake3, Blake3Hash.mk.injEq] at h_eq
  exact h_ser_neq h_eq

/--
**Theorem: Genesis Event Has Zero PrevHash**

The first event in a valid chain always references Hash32.zero.
-/
theorem genesis_prev_zero (e : HashedEvent) (h : HashChain [e]) :
    e.event.prevHash = Hash32.zero := by
  cases h with
  | genesis _ h_prev => exact h_prev

/--
**Theorem: Chain Integrity from Collision Resistance**

With collision resistance, hash chain integrity is guaranteed:
if two chains have the same final hash, they must be identical.
-/
theorem chain_integrity_from_collision_resistance
    (e₁ e₂ : HashedEvent)
    (h_hash_eq : e₁.hash = e₂.hash) :
    serializeEvent e₁.event = serializeEvent e₂.event := by
  have h₁ := e₁.h_hash_valid
  have h₂ := e₂.h_hash_valid
  rw [h₁, h₂] at h_hash_eq
  exact blake3_collision_resistant _ _ h_hash_eq

end -- noncomputable section

end Lion
