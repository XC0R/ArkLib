/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.LiftContext.Reduction

/-!
# Lift-Context for Oracle Reductions

Oracle lifting wrappers and preservation theorem surface.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

variable {pSpec : ProtocolSpec}
  {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]

/-! ## Lifting definitions -/

def OracleProver.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
      InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  HonestProver.liftContext lens.toContext P

def OracleVerifier.liftContext
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) :
    OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  verify := by
    intro _outerStmt _challenges
    sorry
  simulate := by
    intro _q
    sorry
  reify := fun outerOStmtIn msgs => do
    let innerOStmtIn := lens.reifyIn outerOStmtIn
    let innerOStmtOut ← V.reify innerOStmtIn msgs
    pure (lens.reifyOut outerOStmtIn innerOStmtOut)

def OracleReduction.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
      InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

/-! ## Commutation lemmas with plain conversion -/

namespace OracleVerifier

theorem liftContext_toVerifier_comm
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (oStmtInData : ∀ i, OuterOStmtIn i) :
    (V.liftContext lens).toVerifier oStmtInData =
      (V.toVerifier (lens.reifyIn oStmtInData)).liftContext
        ({ proj := lens.projStmt, lift := lens.liftStmt } :
          Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) := by
  -- Full definitional commutation with oracle simulation/reification routing.
  sorry

end OracleVerifier

namespace OracleReduction

theorem liftContext_toReduction_comm
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
      InnerStmtOut InnerOStmtOut InnerWitOut pSpec)
    (oStmtInData : ∀ i, OuterOStmtIn i) :
    ((R.liftContext lens).toReduction oStmtInData).verifier =
      ((R.toReduction (lens.stmt.reifyIn oStmtInData)).verifier).liftContext
        ({ proj := lens.stmt.projStmt, lift := lens.stmt.liftStmt } :
          Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) := by
  simpa [OracleReduction.liftContext, OracleReduction.toReduction] using
    (OracleVerifier.liftContext_toVerifier_comm (lens := lens.stmt) (V := R.verifier)
      (oStmtInData := oStmtInData))

end OracleReduction

/-! ## Preservation theorem surface -/

namespace OracleReduction

variable {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)} {Inv : σ → Prop}
  [ChallengesSampleable pSpec]
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
  {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
  {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
  (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
  (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
    InnerStmtOut InnerOStmtOut InnerWitOut pSpec)
  (oStmtInData : ∀ i, OuterOStmtIn i)

theorem liftContext_completeness
    (ε : ℝ≥0)
    (h : (R.toReduction (lens.stmt.reifyIn oStmtInData)).completeness
      impl Inv innerRelIn innerRelOut ε) :
    ((R.liftContext lens).toReduction oStmtInData).completeness
      impl Inv outerRelIn outerRelOut ε := by
  sorry

theorem liftContext_perfectCompleteness
    (h : (R.toReduction (lens.stmt.reifyIn oStmtInData)).perfectCompleteness
      impl Inv innerRelIn innerRelOut) :
    ((R.liftContext lens).toReduction oStmtInData).perfectCompleteness
      impl Inv outerRelIn outerRelOut := by
  exact liftContext_completeness (lens := lens) (R := R) (oStmtInData := oStmtInData) (ε := 0) h

end OracleReduction

namespace OracleVerifier

variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {Inv : σ → Prop}
  [ChallengesSampleable pSpec]
  {outerLangIn : Set OuterStmtIn}
  {outerLangOut : Set OuterStmtOut}
  {innerLangIn : Set InnerStmtIn}
  {innerLangOut : Set InnerStmtOut}
  (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
  (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
  (oStmtInData : ∀ i, OuterOStmtIn i)

theorem liftContext_soundness
    (ε : ℝ≥0)
    (h : (V.toVerifier (lens.reifyIn oStmtInData)).soundness init impl innerLangIn innerLangOut ε) :
    ((V.liftContext lens).toVerifier oStmtInData).soundness
      init impl outerLangIn outerLangOut ε := by
  -- Delegates to plain lifting after conversion.
  sorry

theorem liftContext_knowledgeSoundness
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
    {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
    {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {witLens : Witness.InvLens OuterStmtIn
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (ε : ℝ≥0)
    (h : (V.toVerifier (lens.reifyIn oStmtInData)).knowledgeSoundness
      init impl innerRelIn innerRelOut ε) :
    ((V.liftContext lens).toVerifier oStmtInData).knowledgeSoundness
      init impl outerRelIn outerRelOut ε := by
  sorry

theorem liftContext_rbrSoundness
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrSoundness (impl := impl) (langIn := innerLangIn) (langOut := innerLangOut)
      (verifier := V.toVerifier (lens.reifyIn oStmtInData)) (Inv := Inv) rbrError) :
    rbrSoundness (impl := impl) (langIn := outerLangIn) (langOut := outerLangOut)
      (verifier := (V.liftContext lens).toVerifier oStmtInData) (Inv := Inv) rbrError := by
  sorry

theorem liftContext_rbrKnowledgeSoundness
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
    {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
    {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound
      InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction (impl := impl) (Inv := Inv) innerRelIn innerRelOut
      (V.toVerifier (lens.reifyIn oStmtInData)) extractor}
    (h : rbrKnowledgeSoundness (impl := impl) (Inv := Inv) extractor ksf rbrError) :
    ∃ (WitMid' : Fin (pSpec.length + 1) → Type)
      (extractor' : Extractor.RoundByRound
        OuterStmtIn OuterWitIn OuterWitOut pSpec WitMid')
      (ksf' : KnowledgeStateFunction (impl := impl) (Inv := Inv) outerRelIn outerRelOut
        ((V.liftContext lens).toVerifier oStmtInData) extractor'),
      rbrKnowledgeSoundness (impl := impl) (Inv := Inv) extractor' ksf' rbrError := by
  sorry

end OracleVerifier

end ProtocolSpec
