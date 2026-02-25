/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.StateFunction

/-!
# Composition of Security Properties

Theorems about how completeness, soundness, and round-by-round (RBR) soundness
compose under `Reduction.comp` and `Reduction.compNth`.

## Main results

### Completeness
- `Reduction.completeness_comp` — completeness composes with error addition
- `Reduction.perfectCompleteness_comp` — perfect completeness composes
- `Reduction.completeness_compNth` — `n`-fold completeness with error `n * ε`
- `Reduction.perfectCompleteness_compNth` — `n`-fold perfect completeness

### Soundness
- `rbrSoundness_implies_soundness` — RBR soundness implies overall soundness
- `Verifier.soundness_compNth` — soundness of `n`-fold composition

### Knowledge Soundness
- `rbrKnowledgeSoundness_implies_knowledgeSoundness` — RBR k.s. implies overall k.s.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

/-! ## Completeness Composition -/

section Completeness

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Completeness composes: if `r₁` has completeness error `ε₁` (relIn → relMid) and
`r₂` has completeness error `ε₂` (relMid → relOut), then `r₁.comp r₂` has
completeness error at most `ε₁ + ε₂` (relIn → relOut). -/
theorem Reduction.completeness_comp
    {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {relIn : Set (S₁ × W₁)} {relMid : Set (S₂ × W₂)} {relOut : Set (S₃ × W₃)}
    {r₁ : Reduction (OracleComp oSpec) S₁ W₁ S₂ W₂ pSpec₁}
    {r₂ : Reduction (OracleComp oSpec) S₂ W₂ S₃ W₃ pSpec₂}
    {Inv : σ → Prop}
    {ε₁ ε₂ : ℝ≥0}
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h₁ : r₁.completeness impl Inv relIn relMid ε₁)
    (h₂ : r₂.completeness impl Inv relMid relOut ε₂) :
    letI := ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (r₁.comp r₂).completeness impl Inv relIn relOut (ε₁ + ε₂) := by
  sorry

/-- Perfect completeness composes. -/
theorem Reduction.perfectCompleteness_comp
    {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂]
    {relIn : Set (S₁ × W₁)} {relMid : Set (S₂ × W₂)} {relOut : Set (S₃ × W₃)}
    {r₁ : Reduction (OracleComp oSpec) S₁ W₁ S₂ W₂ pSpec₁}
    {r₂ : Reduction (OracleComp oSpec) S₂ W₂ S₃ W₃ pSpec₂}
    {Inv : σ → Prop}
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h₁ : r₁.perfectCompleteness impl Inv relIn relMid)
    (h₂ : r₂.perfectCompleteness impl Inv relMid relOut) :
    letI := ChallengesSampleable.ofAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (r₁.comp r₂).perfectCompleteness impl Inv relIn relOut := by
  sorry

/-- Perfect completeness of `n`-fold composition: if one round is perfectly complete,
then `n` rounds are perfectly complete. -/
theorem Reduction.perfectCompleteness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    {Inv : σ → Prop}
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : r.perfectCompleteness impl Inv rel rel) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (r.compNth n).perfectCompleteness impl Inv rel rel := by
  sorry

/-- Completeness of `n`-fold composition with error `n * ε`. -/
theorem Reduction.completeness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {r : Reduction (OracleComp oSpec) S W S W pSpec}
    {Inv : σ → Prop}
    {ε : ℝ≥0}
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : r.completeness impl Inv rel rel ε) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (r.compNth n).completeness impl Inv rel rel (n * ε) := by
  sorry

end Completeness

/-! ## RBR Soundness → Soundness -/

section Soundness

variable {StmtIn StmtOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- RBR soundness implies overall soundness. The total soundness error is bounded by
the sum of per-round RBR errors over all challenge rounds. -/
theorem rbrSoundness_implies_soundness
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : ProtocolSpec.InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl langIn langOut verifier Inv rbrError) :
    verifier.soundness init impl langIn langOut
      (Finset.sum Finset.univ rbrError) := by
  sorry

/-- Soundness of `n`-fold composition: if each copy has RBR soundness error `rbrError`,
the composed protocol has total soundness error at most `n * Σᵢ rbrError(i)`. -/
theorem Verifier.soundness_compNth
    {S : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {lang : Set S}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : ProtocolSpec.InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrSoundness impl lang lang v Inv rbrError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).soundness init impl lang lang
      (n * Finset.sum Finset.univ rbrError) := by
  sorry

end Soundness

/-! ## RBR Knowledge Soundness → Knowledge Soundness -/

section KnowledgeSoundness

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- RBR knowledge soundness implies overall knowledge soundness. The total knowledge
error is bounded by the sum of per-round RBR knowledge errors. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound StmtIn WitIn WitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv relIn relOut verifier extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : ProtocolSpec.InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) :
    verifier.knowledgeSoundness init impl relIn relOut
      (Finset.sum Finset.univ rbrKnowledgeError) := by
  sorry

/-- Knowledge soundness of `n`-fold composition: if each copy has RBR knowledge
soundness error `rbrKnowledgeError`, the composed protocol has total knowledge
soundness error at most `n * Σᵢ rbrKnowledgeError(i)`. -/
theorem Verifier.knowledgeSoundness_compNth
    {S W : Type}
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
    {rel : Set (S × W)}
    {v : Verifier (OracleComp oSpec) S S pSpec}
    {Inv : σ → Prop}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound S W W pSpec WitMid}
    {ksf : KnowledgeStateFunction impl Inv rel rel v extractor}
    {rbrKnowledgeError : ChallengeIndex pSpec → ℝ≥0}
    (hInit : ProtocolSpec.InitSatisfiesInv init Inv)
    (hPres : QueryImpl.PreservesInv impl Inv)
    (h : rbrKnowledgeSoundness impl Inv extractor ksf rbrKnowledgeError) (n : Nat) :
    letI := ChallengesSampleable.ofReplicate (pSpec := pSpec) n
    (v.compNth n).knowledgeSoundness init impl rel rel
      (n * Finset.sum Finset.univ rbrKnowledgeError) := by
  sorry

end KnowledgeSoundness

end ProtocolSpec
