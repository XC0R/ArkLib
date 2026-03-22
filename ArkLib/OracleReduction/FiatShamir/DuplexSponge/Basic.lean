/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.Security.Basic

/-!
# Duplex Sponge Fiat-Shamir Substrate

This module packages the paper-facing Section 3 and Section 4 substrate for the CO25
duplex-sponge Fiat-Shamir formalization:

- Section 3.2: `DuplexSpongeFS.lemma_3_2`
- Section 3.3: the duplex-sponge API from `ArkLib.Data.Hash.DuplexSponge`
- Section 3.4: paper-facing aliases for the NARG security definitions already present in
  `ArkLib.OracleReduction.Security.Basic`
- Section 4: the duplex-sponge Fiat-Shamir transformation from
  `ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs`

Zero-knowledge definitions are intentionally not included here, because ArkLib does not yet provide
the generic Section 7 substrate needed for the CO25 ZK development.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace DuplexSpongeFS

/-! ## Section 3.3 -/

/-- Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3. -/
abbrev SpongeState (U : Type) [SpongeUnit U] [SpongeSize] := CanonicalSpongeState U

/-- Paper-facing alias for the canonical duplex sponge used in CO25 Section 3.3. -/
abbrev Sponge (U : Type) [SpongeUnit U] [SpongeSize] := CanonicalDuplexSponge U

/-! ## Section 3.4 -/

namespace NARG

variable {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Paper-facing alias for CO25 Section 3.4 completeness. -/
abbrev completeness
    (relation : Set (Statement × Witness))
    (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Proof.completeness init impl relation completenessError proof

/-- Paper-facing alias for CO25 Section 3.4 perfect completeness. -/
abbrev perfectCompleteness
    (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Proof.perfectCompleteness init impl relation proof

/-- Paper-facing alias for CO25 Section 3.4 soundness. -/
abbrev soundness
    (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  Proof.soundness init impl langIn verifier soundnessError

/-- Paper-facing alias for CO25 Section 3.4 straightline knowledge soundness. -/
abbrev straightlineKnowledgeSoundness
    (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  Proof.knowledgeSoundness init impl relation verifier knowledgeError

/-- Paper-facing alias for the straightline extractor interface used in Section 3.4. -/
abbrev StraightlineExtractor := Extractor.Straightline oSpec Statement Witness Bool pSpec

end NARG

/-! ## Section 4 -/

/-- Paper-facing alias for CO25 Definition 4.1 codecs. -/
abbrev Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) := ProtocolSpec.Codec pSpec U

section Section4

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Paper-facing alias for the hybrid oracle from CO25 Equation 16. -/
abbrev HybridOracle : OracleSpec
    ((i : pSpec.ChallengeIdx) × StmtIn ×
      ((j : pSpec.MessageIdx) → (j.1 < i.1) → Vector U (pSpec.Lₚᵢ j))) :=
  ProtocolSpec.duplexSpongeHybridOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- Paper-facing alias for the random-oracle / ideal-permutation oracle from CO25 Definition 4.2.
-/
abbrev ChallengeOracle : OracleSpec (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  OracleSpec.duplexSpongeChallengeOracle StmtIn U

end Section4

section Transforms

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Paper-facing alias for the unsalted DSFS transform from Section 4. -/
abbrev duplexSpongeFiatShamir
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :=
  Reduction.duplexSpongeFiatShamir (U := U) R

/-- Paper-facing alias for the salted DSFS transform from CO25 Construction 4.3. -/
abbrev duplexSpongeFiatShamirSalted {δ : Nat}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :=
  Reduction.duplexSpongeFiatShamirSalted (U := U) sampleSalt R

end Transforms

end DuplexSpongeFS
