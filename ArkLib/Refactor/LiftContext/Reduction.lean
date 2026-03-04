/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.LiftContext.Lens
import ArkLib.Refactor.Security.StateFunction
import ArkLib.Refactor.Security.Composition.Soundness
import ArkLib.Refactor.Security.Composition.KnowledgeSoundness

/-!
# Lift-Context for Plain Reductions

Lifting operations and preservation theorem surface for plain
`HonestProver`/`Verifier`/`Reduction` in the refactored framework.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

variable {pSpec : ProtocolSpec}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

/-! ## Lifting definitions -/

def HonestProver.liftContext {m : Type → Type} [Monad m]
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : HonestProver m InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
    HonestProver m OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec :=
  fun (outerStmtIn, outerWitIn) => do
    let pInner ← P (lens.stmt.proj outerStmtIn, lens.wit.proj (outerStmtIn, outerWitIn))
    pure <|
      Prover.mapOutput
        (fun (innerStmtOut, innerWitOut) =>
          lens.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut))
        pSpec pInner

def Verifier.liftContext {m : Type → Type} [Monad m]
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier m InnerStmtIn InnerStmtOut pSpec) :
    Verifier m OuterStmtIn OuterStmtOut pSpec :=
  fun outerStmtIn tr => do
    let innerStmtOut ← V (lens.proj outerStmtIn) tr
    pure (lens.lift outerStmtIn innerStmtOut)

def Reduction.liftContext {m : Type → Type} [Monad m]
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction m InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
    Reduction m OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

open Verifier in
def Extractor.Straightline.liftContext
    {ι : Type} {oSpec : OracleSpec ι}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
    Extractor.Straightline oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec :=
  fun outerStmtIn outerWitOut tr => do
    let innerStmtIn := lens.stmt.proj outerStmtIn
    let innerWitOut := lens.wit.proj (outerStmtIn, outerWitOut)
    let innerWitIn ← E innerStmtIn innerWitOut tr
    pure (lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn)

def Verifier.compatStatement
    {ι : Type} {oSpec : OracleSpec ι}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier (OracleComp oSpec) InnerStmtIn InnerStmtOut pSpec) :
    OuterStmtIn → InnerStmtOut → Prop :=
  fun _ _ => True

def Reduction.compatContext
    {ι : Type} {oSpec : OracleSpec ι}
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction (OracleComp oSpec) InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
    (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop :=
  fun _ _ => True

/-! ## Intertwining theorem surface -/

namespace HonestProver

theorem liftContext_run
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : HonestProver m InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec)
    (outerStmtIn : OuterStmtIn) (outerWitIn : OuterWitIn)
    (ch : Challenges pSpec) :
    (do
      let p ← (P.liftContext lens) (outerStmtIn, outerWitIn)
      Prover.run pSpec p ch)
      =
    (do
      let p ← P (lens.stmt.proj outerStmtIn, lens.wit.proj (outerStmtIn, outerWitIn))
      let (tr, innerOut) ← Prover.run pSpec p ch
      pure (tr, lens.lift (outerStmtIn, outerWitIn) innerOut)) := by
  simp [HonestProver.liftContext, Prover.run_mapOutput]

end HonestProver

namespace Reduction

theorem liftContext_run
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction m InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec)
    (outerStmtIn : OuterStmtIn) (outerWitIn : OuterWitIn) (ch : Challenges pSpec) :
    (R.liftContext lens).run outerStmtIn outerWitIn ch =
      (do
        let (verResult, innerCtxOut) ←
          R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)) ch
        let liftedCtx := lens.lift (outerStmtIn, outerWitIn) innerCtxOut
        let liftedVer := verResult.map (lens.stmt.lift outerStmtIn)
        pure (liftedVer, liftedCtx)) := by
  sorry

end Reduction

/-! ## State-function lifting helper (used by RBR theorems) -/

namespace StateFunction

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {Inv : σ → Prop}
  {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
  {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
  (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
  (V : Verifier (OracleComp oSpec) InnerStmtIn InnerStmtOut pSpec)
  [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
    (Verifier.compatStatement (pSpec := pSpec) lens V)]
  (sf : StateFunction impl Inv innerLangIn innerLangOut V)

def liftContext :
    StateFunction impl Inv outerLangIn outerLangOut (V.liftContext lens) := by
  sorry

end StateFunction

/-! ## Preservation theorem surface -/

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {Inv : σ → Prop}
  [ChallengesSampleable pSpec]
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
  (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
  (R : Reduction (OracleComp oSpec) InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec)
  [lensComplete : lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
    (Reduction.compatContext (pSpec := pSpec) lens R)]

theorem liftContext_completeness
    (ε : ℝ≥0)
    (h : R.completeness impl Inv innerRelIn innerRelOut ε) :
    (R.liftContext lens).completeness impl Inv outerRelIn outerRelOut ε := by
  sorry

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness impl Inv innerRelIn innerRelOut) :
    (R.liftContext lens).perfectCompleteness impl Inv outerRelIn outerRelOut := by
  exact liftContext_completeness (lens := lens) (R := R) (ε := 0) h

end Reduction

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {Inv : σ → Prop}
  [ChallengesSampleable pSpec]
  {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
  {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
  (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
  (V : Verifier (OracleComp oSpec) InnerStmtIn InnerStmtOut pSpec)
  [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
    (Verifier.compatStatement (pSpec := pSpec) lens V)]

theorem liftContext_soundness
    (ε : ℝ≥0)
    (h : V.soundness init impl innerLangIn innerLangOut ε) :
    (V.liftContext lens).soundness init impl outerLangIn outerLangOut ε := by
  sorry

variable
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
  {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
    (Verifier.compatStatement (pSpec := pSpec) lens V) (fun _ _ => True) ⟨lens, witLens⟩]

theorem liftContext_knowledgeSoundness
    (ε : ℝ≥0)
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut ε) :
    (V.liftContext lens).knowledgeSoundness init impl outerRelIn outerRelOut ε := by
  sorry

theorem liftContext_rbrSoundness
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    (h : rbrSoundness (impl := impl) (langIn := innerLangIn) (langOut := innerLangOut)
      (verifier := V) (Inv := Inv) rbrError) :
    rbrSoundness (impl := impl) (langIn := outerLangIn) (langOut := outerLangOut)
      (verifier := V.liftContext lens) (Inv := Inv) rbrError := by
  sorry

theorem liftContext_rbrKnowledgeSoundness
    {rbrError : ChallengeIndex pSpec → ℝ≥0}
    {WitMid : Fin (pSpec.length + 1) → Type}
    {extractor : Extractor.RoundByRound InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid}
    {ksf : KnowledgeStateFunction (impl := impl) (Inv := Inv) innerRelIn innerRelOut V extractor}
    (h : rbrKnowledgeSoundness (impl := impl) (Inv := Inv) extractor ksf rbrError) :
    ∃ (WitMid' : Fin (pSpec.length + 1) → Type)
      (extractor' : Extractor.RoundByRound OuterStmtIn OuterWitIn OuterWitOut pSpec WitMid')
      (ksf' : KnowledgeStateFunction (impl := impl) (Inv := Inv)
        outerRelIn outerRelOut (V.liftContext lens) extractor'),
      rbrKnowledgeSoundness (impl := impl) (Inv := Inv) extractor' ksf' rbrError := by
  sorry

end Verifier

end ProtocolSpec
