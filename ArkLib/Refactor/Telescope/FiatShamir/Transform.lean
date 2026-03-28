/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Telescope.FiatShamir.Basic
import ArkLib.Refactor.Telescope.Reduction
import ArkLib.Refactor.Telescope.Syntax.Verifier

/-!
# Telescope Fiat-Shamir Transform

Basic messages-only Fiat-Shamir surfaces on top of the telescope oracle core.
-/

open OracleComp OracleSpec

namespace ProtocolCtx
namespace FiatShamir

/-- Concrete input carried by the basic FS transform: the original input oracle together
with a replay oracle for the corresponding interactive context. The wrapper itself is
only a carrier; operational oracle access still goes through the stored fields. -/
structure ReplayInput
    (Statement : Type)
    (InputOracle : Statement → Type)
    (BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (statement : Statement) where
  inputOracle : InputOracle statement
  replayOracle : ReplayOracle (BaseContext statement inputOracle)

namespace ReplayInput

instance
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {statement : Statement} :
    OracleInterface (ReplayInput Statement InputOracle BaseContext statement) :=
  OracleInterface.instDefault

/-- The non-interactive one-message context induced by a replay oracle. -/
def context
    {Statement : Type}
    {InputOracle : Statement → Type}
    (BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx) :
    (statement : Statement) →
    ReplayInput Statement InputOracle BaseContext statement → ProtocolCtx
  | statement, input =>
      .P_to_V
        (MessagesOnly (BaseContext statement input.inputOracle) input.replayOracle)
        (MessagesOnly.trivialOracleInterface _ _)
        (fun _ => .nil)

/-- Recover the bundled messages-only proof from the one-message FS transcript. -/
def proof
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    (statement : Statement)
    (input : ReplayInput Statement InputOracle BaseContext statement)
    (tr : Transcript (context BaseContext statement input)) :
    MessagesOnly (BaseContext statement input.inputOracle) input.replayOracle :=
  tr.1

/-- Reconstruct the original interactive transcript from an FS transcript. -/
def fullTranscript
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    (statement : Statement)
    (input : ReplayInput Statement InputOracle BaseContext statement)
    (tr : Transcript (context BaseContext statement input)) :
    Transcript (BaseContext statement input.inputOracle) :=
  MessagesOnly.deriveTranscript input.replayOracle (proof statement input tr)

/-- Statement output family transported through the basic FS wrapper. -/
def statementOut
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    (BaseStatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type) :
    (statement : Statement) →
    (input : ReplayInput Statement InputOracle BaseContext statement) →
    Transcript (context BaseContext statement input) → Type
  | statement, input, tr =>
      BaseStatementOut statement input.inputOracle (fullTranscript statement input tr)

/-- Output oracle family transported through the basic FS wrapper. -/
def outputOracle
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    (BaseOutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type) :
    (statement : Statement) →
    (input : ReplayInput Statement InputOracle BaseContext statement) →
    Transcript (context BaseContext statement input) → Type
  | statement, input, tr =>
      BaseOutputOracle statement input.inputOracle (fullTranscript statement input tr)

/-- Witness output family transported through the basic FS wrapper. -/
def witnessOut
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    (BaseWitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type) :
    (statement : Statement) →
    (input : ReplayInput Statement InputOracle BaseContext statement) →
    Transcript (context BaseContext statement input) → Type
  | statement, input, tr =>
      BaseWitnessOut statement input.inputOracle (fullTranscript statement input tr)

instance instOutputOracle
    {Statement : Type}
    {InputOracle : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {BaseOutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (BaseOutputOracle statement inputOracle tr)] :
    ∀ statement, ∀ input, ∀ tr,
      OracleInterface (outputOracle BaseOutputOracle statement input tr)
  | _, _, _ => by
      dsimp [outputOracle]
      infer_instance

end ReplayInput

namespace Prover

/-- Execute a prover against a replay oracle, storing only prover messages while using
the replay oracle to supply verifier challenges. -/
def runMessagesOnly {m : Type → Type} [Monad m] :
    {ctx : ProtocolCtx} → {Output : Transcript ctx → Type} →
    (rho : ReplayOracle ctx) → Prover m ctx Output →
    m ((proof : MessagesOnly ctx rho) × Output (MessagesOnly.deriveTranscript rho proof))
  | .nil, _, _, output => pure ⟨PUnit.unit, output⟩
  | .P_to_V _ _ _, _, rho, ⟨msg, cont⟩ => do
      let next ← cont
      let ⟨proof, out⟩ ← runMessagesOnly (rho.afterMessage msg) next
      pure ⟨⟨msg, proof⟩, out⟩
  | .V_to_P T _, _, rho, receiveCont => do
      let chal : T := rho.head
      let next ← receiveCont chal
      runMessagesOnly (rho.afterChallenge chal) next

end Prover

namespace OracleProver

/-- Basic messages-only Fiat-Shamir transform of an oracle prover. -/
def fiatShamir
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {BaseStatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    {BaseOutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    {BaseWitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    (prover : OracleProver oSpec Statement InputOracle WitnessIn BaseContext
      BaseStatementOut BaseOutputOracle BaseWitnessOut) :
    OracleProver oSpec Statement
      (ReplayInput Statement InputOracle BaseContext)
      WitnessIn
      (ReplayInput.context BaseContext)
      (ReplayInput.statementOut BaseStatementOut)
      (ReplayInput.outputOracle BaseOutputOracle)
      (ReplayInput.witnessOut BaseWitnessOut) :=
  fun statement input wit => do
    let p ← prover statement input.inputOracle wit
    let ⟨proof, out⟩ ← Prover.runMessagesOnly input.replayOracle p
    pure ⟨proof, pure out⟩

end OracleProver

namespace OracleVerifier

open scoped TelescopeSyntax

/-- Basic messages-only Fiat-Shamir transform of an oracle verifier. -/
def fiatShamir
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {BaseStatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    {BaseOutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (BaseOutputOracle statement inputOracle tr)]
    (verifier : OracleVerifier oSpec Statement InputOracle BaseContext
      BaseStatementOut BaseOutputOracle) :
    OracleVerifier oSpec Statement
      (ReplayInput Statement InputOracle BaseContext)
      (ReplayInput.context BaseContext)
      (ReplayInput.statementOut BaseStatementOut)
      (ReplayInput.outputOracle BaseOutputOracle) where
  verify := verifier!{ statement, input, proof => do
    let fullTr := ReplayInput.fullTranscript statement input proof
    OptionT.mk do
      let result ←
        (OracleVerifier.toVerifier verifier statement input.inputOracle fullTr).run
      pure result
  }
  simulate := fun statement input tr q => do
    let fullTr := ReplayInput.fullTranscript statement input tr
    pure <|
      simulateQ
        (OracleVerifier.simOracleSingle (Transcript.messageData fullTr))
        (verifier.simulate statement input.inputOracle fullTr q)
  realize := fun statement input tr =>
    let fullTr := ReplayInput.fullTranscript statement input tr
    verifier.realize statement input.inputOracle fullTr

end OracleVerifier

namespace OracleReduction

/-- Basic messages-only Fiat-Shamir transform of an oracle reduction. -/
def fiatShamir
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {BaseContext : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {BaseStatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    {BaseOutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    {BaseWitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (BaseContext statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (BaseOutputOracle statement inputOracle tr)]
    (red : OracleReduction oSpec Statement InputOracle WitnessIn BaseContext
      BaseStatementOut BaseOutputOracle BaseWitnessOut) :
    OracleReduction oSpec Statement
      (ReplayInput Statement InputOracle BaseContext)
      WitnessIn
      (ReplayInput.context BaseContext)
      (ReplayInput.statementOut BaseStatementOut)
      (ReplayInput.outputOracle BaseOutputOracle)
      (ReplayInput.witnessOut BaseWitnessOut) where
  prover := OracleProver.fiatShamir red.prover
  verifier := OracleVerifier.fiatShamir red.verifier

end OracleReduction

end FiatShamir
end ProtocolCtx
