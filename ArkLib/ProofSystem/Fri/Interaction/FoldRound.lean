/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.Core

/-!
# Interaction-Native FRI: Single Non-final Fold Round

This module packages one non-final FRI round as an oracle continuation.

The continuation carries:
- the verifier challenges seen so far, as a plain local statement;
- the previously produced folded codewords, as an oracle family;
- the current honest computable polynomial, as prover witness.

The round itself remains the standard receiver-then-sender interaction:
the verifier samples `α`, and the prover replies with the next folded codeword.
-/

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

namespace Fri

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- Append one more verifier challenge to the existing fold-round challenge
prefix. -/
private def snocChallengePrefix {i : ℕ}
    (prev : FoldChallengePrefix (F := F) i) (α : F) :
    FoldChallengePrefix (F := F) i.succ :=
  fun j =>
    by
      cases j using Fin.lastCases with
      | last => exact α
      | cast j => exact prev j

/-- Append the current round's codeword to the previously produced fold-codeword
oracle family. -/
private def snocCodewordPrefix {i : ℕ}
    (prev : OracleStatement (FoldCodewordPrefix (F := F) (n := n) D x s i))
    (next : Codeword (F := F) s n i.succ) :
    OracleStatement (FoldCodewordPrefix (F := F) (n := n) D x s i.succ) :=
  fun j =>
    by
      cases j using Fin.lastCases with
      | last => exact next
      | cast j => exact prev j

/-- Oracle continuation for the `i`-th non-final FRI fold round. -/
def foldRoundContinuation {SharedIn : Type} {ι : Type} {oSpec : OracleSpec ι}
    (i : Fin k)
    (sampleChallenge : SharedIn → OracleComp oSpec F) :
    OracleReduction.Continuation (ι := ι) oSpec SharedIn
      (fun _ => foldRoundSpec (F := F) (n := n) D x s i)
      (fun _ => foldRoundRoles (F := F) (n := n) D x s i)
      (fun _ => foldRoundOD (F := F) (n := n) D x s i)
      (fun _ => FoldChallengePrefix (F := F) i.1)
      (ιₛᵢ := fun _ => Fin (i.1 + 1))
      (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1)
      (fun _ => HonestPoly (F := F) s d i.1)
      (fun _ _ => FoldChallengePrefix (F := F) i.1.succ)
      (ιₛₒ := fun _ _ => Fin (i.1.succ + 1))
      (fun _ _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
      (fun _ _ => HonestPoly (F := F) s d i.1.succ) where
  prover _ sWithOracles witness := do
    pure <| fun α => do
      let nextPoly := honestFoldPoly (F := F) (s := s) (d := d) witness α
      let nextCodeword :=
        honestCodeword (F := F) (D := D) (x := x) (s := s) (d := d) i.1.succ nextPoly
      let nextChallenges :=
        snocChallengePrefix (F := F) sWithOracles.stmt α
      let nextCodewords :=
        snocCodewordPrefix (D := D) (x := x) (s := s) (n := n)
          sWithOracles.oracleStmt nextCodeword
      pure ⟨nextCodeword, pure ⟨⟨nextChallenges, nextCodewords⟩, nextPoly⟩⟩
  verifier shared {_} _accSpec prevChallenges := do
    let α ← sampleChallenge shared
    pure ⟨α, fun _ => snocChallengePrefix (F := F) prevChallenges α⟩
  simulate _ tr := fun q =>
    by
      rcases q with ⟨j, q⟩
      cases j using Fin.lastCases with
      | last =>
          exact pure <|
            foldRoundCodeword
              (F := F) (n := n) (_D := D) (_x := x) (_s := s) (i := i) tr q
      | cast j =>
          exact liftM <|
            query
              (spec := [FoldCodewordPrefix (F := F) (n := n) D x s i.1]ₒ)
              ⟨j, q⟩

end

end Fri
