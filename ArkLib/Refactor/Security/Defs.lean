/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Reduction
import ArkLib.Refactor.Security.Invariant

/-!
# Security Definitions for Reductions

Basic security notions for the refactored IOP model:
- Challenge sampling infrastructure (outside sampling)
- Completeness and perfect completeness
- Soundness
- Knowledge soundness (straightline extractor)

## Challenge Sampling

With "outside" challenge sampling, challenges are pre-sampled from `SampleableType`
instances and passed to the reduction. The `ChallengesSampleable` class provides
a `sampleChallenges` function for a given protocol spec.

## Probability Formulation

All security definitions use a single `Pr[...]` over the joint distribution of:
- Challenge randomness (from `sampleChallenges`)
- Shared oracle randomness (from `init` and `impl`)

This replaces the old model's `challengeQueryImpl` combination.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

/-! ## Challenge Sampling -/

/-- Class providing challenge sampling for a protocol spec. Instances are synthesized
recursively: `P_to_V` rounds are skipped, `V_to_P` rounds use `SampleableType`. -/
class ChallengesSampleable (pSpec : ProtocolSpec) where
  sampleChallenges : ProbComp (Challenges pSpec)

noncomputable instance : ChallengesSampleable ([] : ProtocolSpec) where
  sampleChallenges := pure HVector.nil

noncomputable instance {T : Type} {oi : OracleInterface T} {tl : ProtocolSpec}
    [ChallengesSampleable tl] : ChallengesSampleable ((.P_to_V T oi) :: tl) where
  sampleChallenges := ChallengesSampleable.sampleChallenges (pSpec := tl)

noncomputable instance {T : Type} {tl : ProtocolSpec}
    [SampleableType T] [ChallengesSampleable tl] :
    ChallengesSampleable ((.V_to_P T) :: tl) where
  sampleChallenges := do
    let chal ← $ᵗ T
    let rest ← ChallengesSampleable.sampleChallenges (pSpec := tl)
    return chal ::ₕ rest

def sampleChallenges (pSpec : ProtocolSpec) [ChallengesSampleable pSpec] :
    ProbComp (Challenges pSpec) :=
  ChallengesSampleable.sampleChallenges

/-- Challenge sampling for appended protocol specs. -/
noncomputable def ChallengesSampleable.ofAppend
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [ChallengesSampleable pSpec₁] [ChallengesSampleable pSpec₂] :
    ChallengesSampleable (pSpec₁ ++ pSpec₂) where
  sampleChallenges := do
    let ch₁ ← ChallengesSampleable.sampleChallenges (pSpec := pSpec₁)
    let ch₂ ← ChallengesSampleable.sampleChallenges (pSpec := pSpec₂)
    return Challenges.join pSpec₁ pSpec₂ ch₁ ch₂

/-- Challenge sampling for replicated protocol specs. -/
noncomputable def ChallengesSampleable.ofReplicate
    {pSpec : ProtocolSpec} [ChallengesSampleable pSpec] :
    (n : Nat) → ChallengesSampleable (pSpec.replicate n)
  | 0 => inferInstanceAs (ChallengesSampleable ([] : ProtocolSpec))
  | n + 1 => @ofAppend _ _ ‹_› (ofReplicate n)

/-! ## Completeness -/

variable {StmtIn WitIn StmtOut WitOut : Type}
  {ι : Type} {oSpec : OracleSpec ι}
  {pSpec : ProtocolSpec} [ChallengesSampleable pSpec]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A reduction satisfies **completeness** if for all valid input `(stmtIn, witIn) ∈ relIn`,
the execution with pre-sampled challenges yields a valid output with probability at least
`1 - completenessError`.

The probability is over the joint distribution of challenge sampling and shared oracle
randomness. -/
def Reduction.completeness (Inv : σ → Prop) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
  ∀ σ0 : σ,
  (Inv σ0) →
    Pr[fun (verResult, (prvStmtOut, witOut)) =>
        verResult = some prvStmtOut ∧ (prvStmtOut, witOut) ∈ relOut
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (reduction.run stmtIn witIn challenges)).run' σ0
    ] ≥ 1 - completenessError

/-- Perfect completeness: completeness with error `0`. -/
def Reduction.perfectCompleteness (Inv : σ → Prop) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  Reduction.completeness impl Inv relIn relOut reduction 0

class Reduction.IsComplete (Inv : σ → Prop) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec) where
  completenessError : ℝ≥0
  is_complete : reduction.completeness impl Inv relIn relOut completenessError

class Reduction.IsPerfectComplete (Inv : σ → Prop) (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec) where
  is_perfect_complete : reduction.perfectCompleteness impl Inv relIn relOut

instance {Inv : σ → Prop} {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction (OracleComp oSpec) StmtIn WitIn StmtOut WitOut pSpec}
    [Reduction.IsPerfectComplete impl Inv relIn relOut reduction] :
    Reduction.IsComplete impl Inv relIn relOut reduction where
  completenessError := 0
  is_complete := Reduction.IsPerfectComplete.is_perfect_complete

/-! ## Soundness -/

/-- A verifier satisfies **soundness** if for any adversarial prover and any input statement
`stmtIn ∉ langIn`, the probability that the verifier outputs a statement in `langOut`
is at most `soundnessError`. -/
def Verifier.soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ (Output : Type),
  ∀ prover : Prover (OracleComp oSpec) Output pSpec,
  ∀ stmtIn ∉ langIn,
    Pr[fun (verResult, _) => ∃ s ∈ langOut, verResult = some s
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (do
          let (tr, out) ← Prover.run pSpec prover challenges
          let verResult ← (verifier stmtIn tr).run
          return (verResult, out))).run' (← init)
    ] ≤ soundnessError

class Verifier.IsSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) where
  soundnessError : ℝ≥0
  is_sound : verifier.soundness init impl langIn langOut soundnessError

/-! ## Knowledge Soundness -/

/-- A straightline extractor: given the transcript and an output witness, attempts to
extract an input witness. Does not have rewinding capability. -/
def Extractor.Straightline (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type)
    (pSpec : ProtocolSpec) :=
  StmtIn → WitOut → Transcript pSpec →
  OptionT (OracleComp oSpec) WitIn

/-- A verifier satisfies **knowledge soundness** if there exists a straightline extractor
such that for any prover, the probability that the verifier accepts but the extractor
fails to produce a valid witness is at most `knowledgeError`. -/
def Verifier.knowledgeSoundness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ prover : Prover (OracleComp oSpec) (StmtOut × WitOut) pSpec,
    Pr[fun (verResult, (stmtOut, witOut), extractedWit) =>
        (verResult = some stmtOut ∧ (stmtOut, witOut) ∈ relOut) ∧
          (extractedWit.isNone ∨ ∃ w, extractedWit = some w ∧ (stmtIn, w) ∉ relIn)
      | do
        let challenges ← sampleChallenges pSpec
        (simulateQ impl (do
          let (tr, proverOut) ← Prover.run pSpec prover challenges
          let verResult ← (verifier stmtIn tr).run
          let extractedWit ← (extractor stmtIn proverOut.2 tr).run
          return (verResult, proverOut, extractedWit))).run' (← init)
    ] ≤ knowledgeError

class Verifier.IsKnowledgeSound (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier (OracleComp oSpec) StmtIn StmtOut pSpec) where
  knowledgeError : ℝ≥0
  is_knowledge_sound : verifier.knowledgeSoundness init impl relIn relOut knowledgeError

/-! ## Proof Specializations -/

/-- Completeness for a `Proof` (output is `Bool`, trivial witness). -/
def Proof.completeness (Inv : σ → Prop) (langIn : Set (StmtIn × WitIn))
    (proof : Proof (OracleComp oSpec) StmtIn WitIn pSpec)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness impl Inv langIn ({(true, ())} : Set (Bool × Unit))
    proof completenessError

/-- Soundness for a `Proof`. -/
def Proof.soundness (langIn : Set StmtIn)
    (proof : Proof (OracleComp oSpec) StmtIn WitIn pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  Verifier.soundness init impl langIn ({true} : Set Bool) proof.verifier soundnessError

end ProtocolSpec
