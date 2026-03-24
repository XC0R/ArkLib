/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # The Basic Fiat-Shamir Transformation

  This file defines the basic Fiat-Shamir transformation. This transformation takes in a
  (public-coin) interactive reduction (IR) `R` and transforms it into a non-interactive reduction in
  the following way:
  - Each verifier's challenge, instead of being sent from the verifier, will be obtained from a
    Fiat-Shamir oracle, which for the `i`-th challenge requires the input statement and all messages
    up to round `i`

  This is the _basic_ (or slow) version to be distinguished from the more efficient version based on
  duplex sponge (see `DuplexSponge` folder).

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  Our formalization mostly follows the treatment in the Chiesa-Yogev textbook.
-/

universe u v

section find_home

variable {n : ℕ} {σ τ : Type u} {m : Type u → Type v} [Monad m]

/-- Traverse a dependent function indexed by `Fin n` in any monad. -/
def Fin.traverseM {β : Fin n → Type u}
    (f : (i : Fin n) → m (β i)) : m ((i : Fin n) → β i) :=
  let rec aux (k : ℕ) (h : k ≤ n) : m ((i : Fin k) → β (Fin.castLE h i)) :=
    match k with
    | 0 => pure (fun i => i.elim0)
    | k' + 1 => do
      let tail ← aux k' (Nat.le_of_succ_le h)
      let head ← f (Fin.castLE h (Fin.last k'))
      return (Fin.snoc tail head)
  aux n (le_refl n)

instance : MonadLift (StateT σ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.1; return (y.1, y.2, st.2)

instance : MonadLift (StateT τ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.2; return (y.1, st.1, y.2)

end find_home

open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

-- In order to define the Fiat-Shamir transformation for the prover, we need to define
-- a slightly altered execution for the prover

/--
Prover's function for processing the next round, given the current result of the previous round.

  This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
        (pSpec.MessagesUpTo j.succ × StmtIn × prover.PrvState j.succ) := do
  let ⟨messages, stmtIn, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsChallengeOracle StmtIn pSpec) ⟨⟨j, hDir⟩, ⟨stmtIn, messages⟩⟩
    return ⟨messages.extend hDir, stmtIn, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, stmtIn, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          (pSpec.MessagesUpTo i × StmtIn × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, stmt, state⟩)
    prover.processRoundFS
    i

/-- The (slow) Fiat-Shamir transformation for the prover. -/
def Prover.fiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.fiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← (messages.deriveTranscriptFS (oSpec := oSpec) stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamir
  verifier := R.verifier.fiatShamir

section Execution

-- Show that the Fiat-Shamir prover's run gives the same output as the original prover's run

namespace Verifier

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Expanding the basic Fiat-Shamir verifier shows that it re-derives the transcript from the proof
messages via the Fiat-Shamir oracle and then runs the original verifier. -/
@[simp]
theorem fiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

end Verifier



end Execution

section Security

noncomputable section

open scoped NNReal

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

namespace Reduction

section Completeness

local instance fiatShamirProverOnly : ProtocolSpec.ProverOnly
    ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ where
  prover_first' := by simp

abbrev FiatShamirProtocolSpec : ProtocolSpec 1 :=
  ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩

local instance fiatShamirChallengeOracleInterface :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      OracleInterface ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) :=
  challengeOracleInterface (pSpec := FiatShamirProtocolSpec (pSpec := pSpec))

/-- The one-message proof transcript produced by the basic Fiat-Shamir transform. -/
abbrev FiatShamirProofTranscript :=
  FullTranscript (FiatShamirProtocolSpec (pSpec := pSpec))

/-- The explicit honest execution underlying the basic Fiat-Shamir transform. -/
def fiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      ((FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← liftM <|
    R.prover.runToRoundFS (Fin.last n) stmtIn state
  let ctxOut ← liftM <|
    (R.prover.output state).liftComp (oSpec + fsChallengeOracle StmtIn pSpec)
  let proof : FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← (R.verifier.fiatShamir).run stmtIn proof
  return ⟨⟨proof, ctxOut⟩, stmtOut⟩

/-- Completeness of the transformed one-message reduction is equivalent to the explicit honest
Fiat-Shamir execution packaged via `Reduction.fiatShamirHonestExecution`. -/
theorem fiatShamir_completeness_unroll
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    R.fiatShamir.completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.fiatShamirHonestExecution) completenessError := by
  sorry

-- TODO: discharge `fiatShamir_completeness_unroll`.
-- `Reduction.run_of_prover_first` is now available, and `simulateQ_add_run_liftM_left` in
-- `Execution.lean` collapses the unused outer challenge oracle on lifted `OptionT` runs. The
-- remaining gap is the final file-local normalization between the elaborated run of
-- `R.fiatShamir` and `liftM (R.fiatShamirHonestExecution ...)`, where Lean still chooses multiple
-- coercion paths for the same lifted computation.

end Completeness

end Reduction

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
