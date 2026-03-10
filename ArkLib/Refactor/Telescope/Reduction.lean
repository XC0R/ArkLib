import ArkLib.Refactor.Telescope.OracleVerifier

/-!
# Telescope Reductions

Native reduction layer for `ProtocolCtx`. Execution is challenger-driven rather than
`Challenges`-driven: dependent protocols cannot pre-sample a static challenge vector.

The primary surfaces in this file are statement-indexed and transcript-indexed:

- the protocol context is supplied as `Context : Statement → ProtocolCtx`,
- prover and verifier outputs may vary with the concrete transcript,
- sequential composition is staged over dependent continuations rather than constant
  append or self-composition helpers.
-/

open OracleComp OracleSpec

namespace ProtocolCtx

/-- A statement-indexed honest prover. The protocol context and final output types may
depend on the public statement and on the final transcript. -/
def HonestProver (m : Type → Type)
    (Statement : Type)
    (WitnessIn : Statement → Type)
    (Context : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Context statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Context statement) → Type) :=
  (statement : Statement) → (wit : WitnessIn statement) →
    m (Prover m (Context statement)
      (fun tr => StatementOut statement tr × WitnessOut statement tr))

namespace HonestProver

/-- Sequential composition of honest provers over a statement-indexed dependent append.
The second stage may depend on the first transcript, but the second-stage context is
still public: it cannot depend on the first prover output. -/
def comp {m : Type → Type} [Monad m]
    {Statement : Type}
    {WitnessIn : Statement → Type}
    {Context₁ : Statement → ProtocolCtx}
    {StatementMid : (statement : Statement) → Transcript (Context₁ statement) → Type}
    {WitnessMid : (statement : Statement) → Transcript (Context₁ statement) → Type}
    {Context₂ : (statement : Statement) → Transcript (Context₁ statement) → ProtocolCtx}
    {StatementOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type}
    {WitnessOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type}
    (p₁ : HonestProver m Statement WitnessIn Context₁ StatementMid WitnessMid)
    (p₂ : (statement : Statement) → (tr₁ : Transcript (Context₁ statement)) →
      HonestProver m (StatementMid statement tr₁) (fun _ => WitnessMid statement tr₁)
        (fun _ => Context₂ statement tr₁)
        (fun _ tr₂ => StatementOut statement tr₁ tr₂)
        (fun _ tr₂ => WitnessOut statement tr₁ tr₂)) :
    HonestProver m Statement WitnessIn
      (fun statement => (Context₁ statement).append (Context₂ statement))
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        StatementOut statement parts.1 parts.2)
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        WitnessOut statement parts.1 parts.2) :=
  fun statement wit => do
    let prv₁ ← p₁ statement wit
    Prover.comp (Context₁ statement) (Context₂ statement) prv₁
      (fun tr₁ mid => by
        rcases mid with ⟨stmtMid, witMid⟩
        let outFamily :
            Transcript ((Context₁ statement).append (Context₂ statement)) → Type :=
          fun tr =>
            let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
            StatementOut statement parts.1 parts.2 × WitnessOut statement parts.1 parts.2
        let joinedFamily :
            Transcript (Context₂ statement tr₁) → Type :=
          fun tr₂ => outFamily (Transcript.join (Context₁ statement) (Context₂ statement) tr₁ tr₂)
        let transport :
            ∀ tr₂,
              (StatementOut statement tr₁ tr₂ × WitnessOut statement tr₁ tr₂) →
                joinedFamily tr₂ := by
          intro tr₂ out
          have hType :
              joinedFamily tr₂ =
                (StatementOut statement tr₁ tr₂ × WitnessOut statement tr₁ tr₂) := by
            unfold joinedFamily outFamily
            exact congrArg
              (fun parts =>
                StatementOut statement parts.1 parts.2 × WitnessOut statement parts.1 parts.2)
              (Transcript.split_join (Context₁ statement) (Context₂ statement) tr₁ tr₂)
          exact Eq.mp hType.symm out
        let p₂' := Prover.mapOutput transport <$> p₂ statement tr₁ stmtMid witMid
        exact p₂')

end HonestProver

/-- A plain telescope reduction: statement-indexed honest prover plus statement-indexed
plain verifier family. -/
structure Reduction (m : Type → Type)
    (Statement : Type)
    (WitnessIn : Statement → Type)
    (Context : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Context statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Context statement) → Type) where
  prover : HonestProver m Statement WitnessIn Context StatementOut WitnessOut
  verifier : (statement : Statement) → (tr : Transcript (Context statement)) →
    OptionT m (StatementOut statement tr)

/-- Oracle prover specialisation: the prover receives concrete input-oracle data and
produces concrete output-oracle data alongside the public statement/witness output. -/
def OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type)
    (InputOracle : Statement → Type)
    (WitnessIn : Statement → Type)
    (Context : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Context statement) → Type)
    (OutputOracle : (statement : Statement) → Transcript (Context statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Context statement) → Type) :=
  (statement : Statement) → InputOracle statement → WitnessIn statement →
    OracleComp oSpec (Prover (OracleComp oSpec) (Context statement)
      (fun tr => (StatementOut statement tr × OutputOracle statement tr) × WitnessOut statement tr))

/-- A telescope oracle reduction: oracle prover plus statement-indexed,
transcript-dependent oracle verifier. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type)
    (InputOracle : Statement → Type) [∀ statement, OracleInterface (InputOracle statement)]
    (WitnessIn : Statement → Type)
    (Context : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Context statement) → Type)
    (OutputOracle : (statement : Statement) → Transcript (Context statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Context statement) → Type) where
  prover :
    OracleProver oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut
  verifier : OracleVerifier oSpec Statement InputOracle Context StatementOut

namespace Reduction

/-- Execute a reduction against an explicit challenger. Returns the transcript,
verifier output, and prover output statement/witness. -/
def runWithTranscript {m : Type → Type} [Monad m]
    {Statement : Type}
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : Reduction m Statement WitnessIn Context StatementOut WitnessOut)
    (statement : Statement) (wit : WitnessIn statement)
    (challenger : Challenger m (Context statement)) :
    m ((tr : Transcript (Context statement)) ×
      Option (StatementOut statement tr) ×
      (StatementOut statement tr × WitnessOut statement tr)) := do
  let prover ← red.prover statement wit
  let ⟨tr, proverOut⟩ ← Prover.run (Context statement) prover challenger
  let verResult ← (red.verifier statement tr).run
  pure ⟨tr, verResult, proverOut⟩

/-- Execute a reduction while packaging the transcript existentially. When outputs are
transcript-indexed there is no transcript-free return type. -/
def run {m : Type → Type} [Monad m]
    {Statement : Type}
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : Reduction m Statement WitnessIn Context StatementOut WitnessOut)
    (statement : Statement) (wit : WitnessIn statement)
    (challenger : Challenger m (Context statement)) :
    m ((tr : Transcript (Context statement)) ×
      (Option (StatementOut statement tr) ×
        (StatementOut statement tr × WitnessOut statement tr))) := do
  let ⟨tr, verResult, proverOut⟩ ← runWithTranscript red statement wit challenger
  pure ⟨tr, (verResult, proverOut)⟩

/-- Identity reduction over the empty protocol. -/
def id {m : Type → Type} [Monad m]
    {Statement : Type} {Witness : Statement → Type} :
    Reduction m Statement Witness
      (fun _ => .nil)
      (fun _ _ => Statement)
      (fun statement _ => Witness statement) where
  prover := fun statement wit => pure (statement, wit)
  verifier := fun statement _ => pure statement

/-- Sequential composition of reductions over a statement-indexed dependent append. -/
def comp {m : Type → Type} [Monad m]
    {Statement : Type}
    {WitnessIn : Statement → Type}
    {Context₁ : Statement → ProtocolCtx}
    {StatementMid : (statement : Statement) → Transcript (Context₁ statement) → Type}
    {WitnessMid : (statement : Statement) → Transcript (Context₁ statement) → Type}
    {Context₂ : (statement : Statement) → Transcript (Context₁ statement) → ProtocolCtx}
    {StatementOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type}
    {WitnessOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type}
    (r₁ : Reduction m Statement WitnessIn Context₁ StatementMid WitnessMid)
    (r₂ : (statement : Statement) → (tr₁ : Transcript (Context₁ statement)) →
      Reduction m (StatementMid statement tr₁) (fun _ => WitnessMid statement tr₁)
        (fun _ => Context₂ statement tr₁)
        (fun _ tr₂ => StatementOut statement tr₁ tr₂)
        (fun _ tr₂ => WitnessOut statement tr₁ tr₂)) :
    Reduction m Statement WitnessIn
      (fun statement => (Context₁ statement).append (Context₂ statement))
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        StatementOut statement parts.1 parts.2)
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        WitnessOut statement parts.1 parts.2) where
  prover := HonestProver.comp r₁.prover (fun statement tr₁ => (r₂ statement tr₁).prover)
  verifier := fun statement tr => do
    let ⟨tr₁, tr₂⟩ := Transcript.split (Context₁ statement) (Context₂ statement) tr
    let mid ← r₁.verifier statement tr₁
    (r₂ statement tr₁).verifier mid tr₂

end Reduction

namespace OracleReduction

/-- Convert a telescope oracle reduction to a plain telescope reduction whose public
statement explicitly carries the concrete input-oracle value. This avoids freezing the
oracle input at construction time. -/
def toReduction
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {OutputOracle : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut) :
    Reduction (OracleComp oSpec)
      ((statement : Statement) × InputOracle statement)
      (fun statement => WitnessIn statement.1)
      (fun statement => Context statement.1)
      (fun statement tr => StatementOut statement.1 tr)
      (fun statement tr => WitnessOut statement.1 tr) where
  prover := fun statement wit => do
    let p ← red.prover statement.1 statement.2 wit
    pure <| Prover.mapOutput (fun _ ((stmtOut, _), witOut) => (stmtOut, witOut)) p
  verifier := fun statement tr =>
    OracleVerifier.toVerifier red.verifier statement.1 statement.2 tr

/-- Execute an oracle reduction against an explicit oracle challenger. -/
def runWithTranscript
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {OutputOracle : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement)) :
    OracleComp oSpec
      ((tr : Transcript (Context statement)) ×
        Option (StatementOut statement tr) ×
        ((StatementOut statement tr × OutputOracle statement tr) × WitnessOut statement tr)) := do
  let prover ← red.prover statement inputOracle wit
  let ⟨tr, proverOut⟩ ← Prover.run (Context statement) prover challenger
  let verResult ← (OracleVerifier.toVerifier red.verifier statement inputOracle tr).run
  pure ⟨tr, verResult, proverOut⟩

/-- Execute an oracle reduction while packaging the transcript existentially. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {OutputOracle : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement)) :
    OracleComp oSpec
      ((tr : Transcript (Context statement)) ×
        (Option (StatementOut statement tr) ×
          ((StatementOut statement tr × OutputOracle statement tr) ×
            WitnessOut statement tr))) := do
  let ⟨tr, verResult, proverOut⟩ ← runWithTranscript red statement inputOracle wit challenger
  pure ⟨tr, (verResult, proverOut)⟩

/-- Log the prover-side oracle queries performed during execution. Because the
challenger is part of the prover execution, its oracle activity is logged together
with the prover's. -/
def runWithLog
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : Statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → Transcript (Context statement) → Type}
    {OutputOracle : (statement : Statement) → Transcript (Context statement) → Type}
    {WitnessOut : (statement : Statement) → Transcript (Context statement) → Type}
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement)) :
    OracleComp oSpec
      ((((tr : Transcript (Context statement)) ×
          Option (StatementOut statement tr) ×
          ((StatementOut statement tr × OutputOracle statement tr) × WitnessOut statement tr)) ×
        QueryLog oSpec × QueryLog oSpec)) := do
  let prover ← red.prover statement inputOracle wit
  let ⟨⟨tr, proverOut⟩, proveLog⟩ ←
    (simulateQ loggingOracle (Prover.run (Context statement) prover challenger)).run
  let ⟨verResult, verifyLog⟩ ←
    (simulateQ loggingOracle
      ((OracleVerifier.toVerifier red.verifier statement inputOracle) tr).run).run
  pure ⟨⟨tr, verResult, proverOut⟩, proveLog, verifyLog⟩

end OracleReduction

end ProtocolCtx
