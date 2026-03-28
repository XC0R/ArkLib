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

For oracle reductions, the concrete public input oracle is explicit and may also index
the protocol family.
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

/-- Iterate an indexed honest-prover family whose local protocol shape depends on a
public stage state. The stage witness family is also indexed by that public state,
but future contexts remain determined solely by the realized stage transcript. -/
def compFrom {m : Type → Type} [Monad m]
    {Stage : Nat → Type}
    (Context : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Context i stage) → Stage (i + 1))
    (Statement : (i : Nat) → Stage i → Type)
    (Witness : (i : Nat) → Stage i → Type)
    (step : (i : Nat) → (stage : Stage i) →
      HonestProver m (Statement i stage) (fun _ => Witness i stage)
        (fun _ => Context i stage)
        (fun _ tr => Statement (i + 1) (advance i stage tr))
        (fun _ tr => Witness (i + 1) (advance i stage tr))) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    HonestProver m (Statement i stage) (fun _ => Witness i stage)
      (fun _ => ProtocolCtx.chain Context advance n i stage)
      (fun _ tr => ProtocolCtx.chainFamily Context advance Statement n i stage tr)
      (fun _ tr => ProtocolCtx.chainFamily Context advance Witness n i stage tr)
  | 0, _, _ => fun statement witness => pure (statement, witness)
  | n + 1, i, stage => fun statement witness => do
      let prover₁ ← step i stage statement witness
      Prover.comp (Context i stage)
        (fun tr₁ => ProtocolCtx.chain Context advance n (i + 1) (advance i stage tr₁))
        prover₁
        (fun tr₁ mid => by
          rcases mid with ⟨stmtNext, witNext⟩
          let outFamily :
              Transcript (ProtocolCtx.chain Context advance (n + 1) i stage) → Type :=
            fun tr =>
              ProtocolCtx.chainFamily Context advance Statement (n + 1) i stage tr ×
                ProtocolCtx.chainFamily Context advance Witness (n + 1) i stage tr
          let joinedFamily :
              Transcript
                (ProtocolCtx.chain Context advance n (i + 1) (advance i stage tr₁)) → Type :=
            fun tr₂ =>
              outFamily (Transcript.join (Context i stage)
                (fun trRest => ProtocolCtx.chain Context advance n (i + 1)
                  (advance i stage trRest)) tr₁ tr₂)
          let transport :
              ∀ tr₂,
                (ProtocolCtx.chainFamily Context advance Statement n (i + 1)
                  (advance i stage tr₁) tr₂ ×
                  ProtocolCtx.chainFamily Context advance Witness n (i + 1)
                    (advance i stage tr₁) tr₂) →
                  joinedFamily tr₂ := by
            intro tr₂ out
            have hType :
                joinedFamily tr₂ =
                  (ProtocolCtx.chainFamily Context advance Statement n (i + 1)
                    (advance i stage tr₁) tr₂ ×
                    ProtocolCtx.chainFamily Context advance Witness n (i + 1)
                      (advance i stage tr₁) tr₂) := by
              unfold joinedFamily outFamily
              simpa [ProtocolCtx.chainFamily] using
                congrArg
                  (fun parts =>
                    ProtocolCtx.chainFamily Context advance Statement n (i + 1)
                      (advance i stage parts.1) parts.2 ×
                      ProtocolCtx.chainFamily Context advance Witness n (i + 1)
                        (advance i stage parts.1) parts.2)
                  (Transcript.split_join (Context i stage)
                    (fun trRest => ProtocolCtx.chain Context advance n (i + 1)
                      (advance i stage trRest)) tr₁ tr₂)
            exact Eq.mp hType.symm out
          let p₂' :=
            Prover.mapOutput transport <$>
              compFrom Context advance Statement Witness step n (i + 1)
                (advance i stage tr₁) stmtNext witNext
          exact p₂')

/-- Constant-statement/witness specialization of `compFrom`. The local protocol may
still vary by public stage state, but each stage consumes and returns the same public
statement/witness pair. -/
def compFromConst {m : Type → Type} [Monad m] {Stage : Nat → Type} {S W : Type}
    (Context : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Context i stage) → Stage (i + 1))
    (step : (i : Nat) → (stage : Stage i) →
      HonestProver m S (fun _ => W) (fun _ => Context i stage) (fun _ _ => S) (fun _ _ => W)) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    HonestProver m S (fun _ => W)
      (fun _ => ProtocolCtx.chain Context advance n i stage)
      (fun _ _ => S) (fun _ _ => W)
  | 0, _, _ => fun statement witness => pure (statement, witness)
  | n + 1, i, stage => fun statement witness => do
      let prover₁ ← step i stage statement witness
      Prover.comp (Context i stage)
        (fun tr₁ => ProtocolCtx.chain Context advance n (i + 1) (advance i stage tr₁))
        prover₁
        (fun tr₁ mid => by
          rcases mid with ⟨stmtNext, witNext⟩
          exact compFromConst Context advance step n (i + 1)
            (advance i stage tr₁) stmtNext witNext)

/-- Constant-state specialization of `compFrom` for repeatedly composing the same
honest prover over `ctx.replicate n`. -/
def compNth {m : Type → Type} [Monad m] {S W : Type}
    {ctx : ProtocolCtx} : (n : Nat) →
    HonestProver m S (fun _ => W) (fun _ => ctx) (fun _ _ => S) (fun _ _ => W) →
    HonestProver m S (fun _ => W) (fun _ => ctx.replicate n) (fun _ _ => S) (fun _ _ => W)
  | n, step =>
      compFromConst
        (Stage := fun _ => PUnit)
        (Context := fun _ _ => ctx)
        (advance := fun _ _ _ => PUnit.unit)
        (step := fun _ _ => step)
        n 0 PUnit.unit

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
    (Context : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    (WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type) :=
  (statement : Statement) → (inputOracle : InputOracle statement) → WitnessIn statement →
    OracleComp oSpec (Prover (OracleComp oSpec) (Context statement inputOracle)
      (fun tr =>
        (StatementOut statement inputOracle tr × OutputOracle statement inputOracle tr) ×
          WitnessOut statement inputOracle tr))

/-- A telescope oracle reduction: oracle prover plus statement-indexed,
input-oracle-indexed oracle verifier. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type)
    (InputOracle : Statement → Type) [∀ statement, OracleInterface (InputOracle statement)]
    (WitnessIn : Statement → Type)
    (Context : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    (WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)] where
  prover :
    OracleProver oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut
  verifier : OracleVerifier oSpec Statement InputOracle Context StatementOut OutputOracle

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

/-- Iterate an indexed reduction family whose local protocol shape depends on a public
stage state. The live public statement may vary by stage, while the stage witness
family remains indexed only by the public state. -/
def compFrom {m : Type → Type} [Monad m]
    {Stage : Nat → Type}
    (Context : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Context i stage) → Stage (i + 1))
    (Statement : (i : Nat) → Stage i → Type)
    (Witness : (i : Nat) → Stage i → Type)
    (step : (i : Nat) → (stage : Stage i) →
      Reduction m (Statement i stage) (fun _ => Witness i stage)
        (fun _ => Context i stage)
        (fun _ tr => Statement (i + 1) (advance i stage tr))
        (fun _ tr => Witness (i + 1) (advance i stage tr))) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Reduction m (Statement i stage) (fun _ => Witness i stage)
      (fun _ => ProtocolCtx.chain Context advance n i stage)
      (fun _ tr => ProtocolCtx.chainFamily Context advance Statement n i stage tr)
      (fun _ tr => ProtocolCtx.chainFamily Context advance Witness n i stage tr)
  | n, i, stage => {
      prover := HonestProver.compFrom Context advance Statement Witness
        (fun j stage' => (step j stage').prover) n i stage
      verifier := Verifier.compFrom Context advance Statement
        (fun j stage' => (step j stage').verifier) n i stage
    }

/-- Constant-statement/witness specialization of `compFrom`. The local protocol may
still vary by public stage state, but each stage preserves the same public
statement/witness types. -/
def compFromConst {m : Type → Type} [Monad m] {Stage : Nat → Type} {S W : Type}
    (Context : (i : Nat) → Stage i → ProtocolCtx)
    (advance : (i : Nat) → (stage : Stage i) → Transcript (Context i stage) → Stage (i + 1))
    (step : (i : Nat) → (stage : Stage i) →
      Reduction m S (fun _ => W) (fun _ => Context i stage) (fun _ _ => S) (fun _ _ => W)) :
    (n : Nat) → (i : Nat) → (stage : Stage i) →
    Reduction m S (fun _ => W)
      (fun _ => ProtocolCtx.chain Context advance n i stage)
      (fun _ _ => S) (fun _ _ => W)
  | n, i, stage => {
      prover := HonestProver.compFromConst Context advance
        (fun j stage' => (step j stage').prover) n i stage
      verifier := Verifier.compFromConst Context advance
        (fun j stage' => (step j stage').verifier) n i stage
    }

/-- Constant-state specialization of `compFrom` for repeatedly composing the same
reduction over `ctx.replicate n`. -/
def compNth {m : Type → Type} [Monad m] {S W : Type}
    {ctx : ProtocolCtx} : (n : Nat) →
    Reduction m S (fun _ => W) (fun _ => ctx) (fun _ _ => S) (fun _ _ => W) →
    Reduction m S (fun _ => W) (fun _ => ctx.replicate n) (fun _ _ => S) (fun _ _ => W)
  | n, step =>
      compFromConst
        (Stage := fun _ => PUnit)
        (Context := fun _ _ => ctx)
        (advance := fun _ _ _ => PUnit.unit)
        (step := fun _ _ => step)
        n 0 PUnit.unit

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
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut) :
    Reduction (OracleComp oSpec)
      ((statement : Statement) × InputOracle statement)
      (fun statement => WitnessIn statement.1)
      (fun statement => Context statement.1 statement.2)
      (fun statement tr => StatementOut statement.1 statement.2 tr)
      (fun statement tr => WitnessOut statement.1 statement.2 tr) where
  prover := fun statement wit => do
    let p ← red.prover statement.1 statement.2 wit
    let mapOut :
        ∀ tr,
          ((StatementOut statement.1 statement.2 tr × OutputOracle statement.1 statement.2 tr) ×
            WitnessOut statement.1 statement.2 tr) →
          (StatementOut statement.1 statement.2 tr × WitnessOut statement.1 statement.2 tr) :=
      fun _ out => (out.1.1, out.2)
    pure <| Prover.mapOutput mapOut p
  verifier := fun statement tr =>
    OracleVerifier.toVerifier red.verifier statement.1 statement.2 tr

/-- Execute an oracle reduction against an explicit oracle challenger. -/
def runWithTranscript
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement inputOracle)) :
    OracleComp oSpec
      ((tr : Transcript (Context statement inputOracle)) ×
        Option (StatementOut statement inputOracle tr) ×
        ((StatementOut statement inputOracle tr × OutputOracle statement inputOracle tr) ×
          WitnessOut statement inputOracle tr)) := do
  let prover ← red.prover statement inputOracle wit
  let ⟨tr, proverOut⟩ ← Prover.run (Context statement inputOracle) prover challenger
  let verResult ← (OracleVerifier.toVerifier red.verifier statement inputOracle tr).run
  pure ⟨tr, verResult, proverOut⟩

/-- Execute an oracle reduction while packaging the transcript existentially. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {WitnessIn : Statement → Type}
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement inputOracle)) :
    OracleComp oSpec
      ((tr : Transcript (Context statement inputOracle)) ×
        (Option (StatementOut statement inputOracle tr) ×
          ((StatementOut statement inputOracle tr × OutputOracle statement inputOracle tr) ×
            WitnessOut statement inputOracle tr))) := do
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
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (red : OracleReduction oSpec Statement InputOracle WitnessIn Context
      StatementOut OutputOracle WitnessOut)
    (statement : Statement) (inputOracle : InputOracle statement) (wit : WitnessIn statement)
    (challenger : Challenger (OracleComp oSpec) (Context statement inputOracle)) :
    OracleComp oSpec
      ((((tr : Transcript (Context statement inputOracle)) ×
          Option (StatementOut statement inputOracle tr) ×
          ((StatementOut statement inputOracle tr × OutputOracle statement inputOracle tr) ×
            WitnessOut statement inputOracle tr)) ×
        QueryLog oSpec × QueryLog oSpec)) := do
  let prover ← red.prover statement inputOracle wit
  let ⟨⟨tr, proverOut⟩, proveLog⟩ ←
    (simulateQ loggingOracle (Prover.run (Context statement inputOracle) prover challenger)).run
  let ⟨verResult, verifyLog⟩ ←
    (simulateQ loggingOracle
      ((OracleVerifier.toVerifier red.verifier statement inputOracle) tr).run).run
  pure ⟨⟨tr, verResult, proverOut⟩, proveLog, verifyLog⟩

end OracleReduction

end ProtocolCtx
