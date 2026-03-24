/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.Security.Basic

/-!
# Theorem about completeness

This file contains the theorem that duplex sponge Fiat-Shamir is complete, assuming the underlying
interactive protocol is complete.

(do we even have to go through basic Fiat-Shamir? any complication with handling completeness
error?)
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The transcript type of the one-message non-interactive proof produced by the unsalted DSFS
transform. -/
abbrev DuplexSpongeProofTranscript :=
  FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩

/-- The transcript type of the one-message non-interactive proof produced by the salted DSFS
transform. -/
abbrev DuplexSpongeSaltedProofTranscript (δ : Nat) :=
  FullTranscript
    ⟨!v[Direction.P_to_V],
      !v[ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ]⟩

/-- Expanding the DSFS verifier shows that it verifies by re-deriving the transcript from the proof
messages via the duplex sponge. -/
@[simp]
theorem duplexSpongeFiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DuplexSpongeProofTranscript (pSpec := pSpec)) :
    (V.duplexSpongeFiatShamir (U := U)).verify stmtIn proof =
      (do
      let messages : pSpec.Messages := proof 0
      let ⟨_, transcript⟩ ← messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

/-- The salted DSFS verifier is the same verifier-side computation, with an initial salt-absorb
step before transcript derivation. -/
@[simp]
theorem duplexSpongeFiatShamirSalted_verify_eq {δ : Nat}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (proof : DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ) :
    (V.duplexSpongeFiatShamirSalted (U := U)).verify stmtIn proof =
      (do
      let ⟨salt, messages⟩ :
          ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ := proof 0
      let ⟨_, transcript⟩ ←
        messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U) stmtIn salt
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

end Execution

end Verifier

namespace Reduction

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The explicit honest execution underlying the unsalted DSFS transform. This packages the honest
prover's DSFS-generated proof together with the verifier's acceptance check on that proof. -/
def duplexSpongeFiatShamirHonestRun
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← R.prover.runToRoundDSFS (U := U) (Fin.last n) stmtIn state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamir (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

/-- The explicit honest execution underlying the salted DSFS transform. -/
def duplexSpongeFiatShamirSaltedHonestRun {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    -- TODO: how to restrict that this is uniform salts sampling?
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let salt ← sampleSalt.liftComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ←
    R.prover.runToRoundDSFSSalted (U := U) (i := Fin.last n) stmtIn salt state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ := fun
    | ⟨0, _⟩ => (salt, messages)
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamirSalted (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

end Execution

section Completeness

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The unsalted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
        StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirHonestRun (U := U) stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The salted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirSaltedHonestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
          StmtOut × WitOut) × StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirSaltedHonestRun (U := U) sampleSalt stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The transformed unsalted DSFS run is the lifted explicit honest execution. -/
theorem duplexSpongeFiatShamir_run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    (R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn =
      liftM (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn) := by
  sorry

/-- The transformed salted DSFS run is the lifted explicit honest execution. -/
theorem duplexSpongeFiatShamirSalted_run_eq_honestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn =
      liftM (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt stmtIn witIn) := by
  sorry

/-- Completeness of the unsalted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirHonestExecution`. -/
theorem duplexSpongeFiatShamir_completeness_unroll
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (R.duplexSpongeFiatShamir (U := U)).completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirHonestExecution (U := U)) completenessError := by
  sorry

/-- Completeness of the salted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirSaltedHonestExecution`. -/
theorem duplexSpongeFiatShamirSalted_completeness_unroll {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).completeness
      init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt)
        completenessError := by
  sorry

end Completeness

end Reduction
