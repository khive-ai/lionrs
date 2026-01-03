# 2.8 Mechanized Verification and Models

We have created mechanized models for the capability framework to bolster
confidence in these proofs:

- A **TLA+ specification** of the capability system (Appendix A.2) models
  components, capabilities, and transfers. We used TLC model checking to
  simulate cross-component interactions and verify invariants like
  unforgeability and authority preservation under all possible send/receive
  sequences.
- A **Lean** (Lean4) mechanization encodes a simplified version of the
  capability semantics and proves properties analogous to Theorems 2.1–2.4. The
  Lean proof (part of Appendix B) ensures there are no hidden logical errors in
  our pen-and-paper reasoning for capability flow and composition.
- These mechanized artifacts provide a machine-checked foundation that
  complements the manual proofs, giving additional assurance that the Lion
  capability security framework is sound.
