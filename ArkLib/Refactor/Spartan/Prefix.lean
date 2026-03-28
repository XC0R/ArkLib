/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Refactor.Spartan.Defs
import ArkLib.Refactor.Migration.SendAndRetain

/-!
# Refactor Spartan Prefix

The Spartan stages before the first sumcheck, expressed directly on the refactor
substrate:

- send the witness and retain it as oracle data
- receive the first verifier challenge while preserving the oracle context
-/

open MvPolynomial Matrix OracleComp OracleSpec ProtocolSpec

namespace Spartan.Refactor

noncomputable section

section Prefix

variable {ι : Type} {oSpec : OracleSpec ι}
variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- After the first message, the public statement is unchanged. -/
@[simp] abbrev AfterFirstMessageStmt : Type := Statement R pp

/-- The first message retains the witness as an extra oracle. -/
@[simp] abbrev AfterFirstMessageOStmt : Sum R1CS.MatrixIdx Unit → Type :=
  ProtocolSpec.SendAndRetain.OStmtOut
    (OStmtIn := OracleStatement R pp) (Msg := Witness R pp)

/-- After the first message, there is no remaining witness. -/
@[simp] abbrev AfterFirstMessageWit : Type := Unit

/-- Refactor-native Stage 1: send the witness MLE and retain it as oracle data. -/
def firstMessage :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (AfterFirstMessageStmt R pp) (AfterFirstMessageOStmt R pp) AfterFirstMessageWit
      (ProtocolSpec.SendAndRetain.pSpec (Msg := Witness R pp)) :=
  ProtocolSpec.SendAndRetain.oracleReduction (oSpec := oSpec)
    (StmtIn := Statement R pp) (StmtOut := AfterFirstMessageStmt R pp)
    (OStmtIn := OracleStatement R pp) (WitIn := Witness R pp)
    (WitOut := AfterFirstMessageWit) (Msg := Witness R pp)
    (sendMsg := fun ctx => pure ctx.2)
    (mapStmt := id)
    (mapWit := fun _ => ())

/-- The first virtual polynomial whose claimed sum should be zero. -/
def zeroCheckVirtualPolynomial (stmt : AfterFirstMessageStmt R pp)
    (oStmt : ∀ i, AfterFirstMessageOStmt R pp i) :
      MvPolynomial (Fin pp.ℓ_m) R :=
  letI 𝕫 := R1CS.𝕫 stmt (oStmt (.inr ()))
  ∑ x : Fin (2 ^ pp.ℓ_m),
    (eqPolynomial (finFunctionFinEquiv.symm x : Fin pp.ℓ_m → R)) *
      C ((oStmt (.inl .A) *ᵥ 𝕫) x * (oStmt (.inl .B) *ᵥ 𝕫) x - (oStmt (.inl .C) *ᵥ 𝕫) x)

/-- The verifier's first random challenge `τ`. -/
@[simp] abbrev FirstChallenge : Type := Fin pp.ℓ_m → R

/-- Statement after receiving the first verifier challenge. -/
structure AfterFirstChallenge where
  tau : FirstChallenge R pp
  stmt : Statement R pp

/-- Oracle data is unchanged across the first challenge round. -/
@[simp] abbrev AfterFirstChallengeOStmt : Sum R1CS.MatrixIdx Unit → Type :=
  AfterFirstMessageOStmt R pp

/-- No witness remains after the first challenge round. -/
@[simp] abbrev AfterFirstChallengeWit : Type := Unit

/-- Protocol spec for Stage 2's verifier challenge. -/
@[reducible] def firstChallengePSpec : ProtocolSpec :=
  [ProtocolSpec.chal (FirstChallenge R pp)]

/-- Refactor-native Stage 2: sample the first verifier challenge while preserving
the retained witness and input matrices as oracle context. -/
def firstChallenge :
    OracleReduction oSpec
      (AfterFirstMessageStmt R pp) (AfterFirstMessageOStmt R pp) AfterFirstMessageWit
      (AfterFirstChallenge R pp) (AfterFirstChallengeOStmt R pp) AfterFirstChallengeWit
      (firstChallengePSpec R pp) where
  prover := fun ⟨⟨stmt, oStmtData⟩, ()⟩ =>
    pure (fun tau => pure (({ tau := tau, stmt := stmt }, oStmtData), ()))
  verifier := OracleVerifier.keepInputOracle (oSpec := oSpec)
    (StmtIn := AfterFirstMessageStmt R pp) (StmtOut := AfterFirstChallenge R pp)
    (OStmt := AfterFirstMessageOStmt R pp) (pSpec := firstChallengePSpec R pp)
    (fun stmt challenges => pure { tau := challenges.head, stmt := stmt })

end Prefix

end

end Spartan.Refactor
