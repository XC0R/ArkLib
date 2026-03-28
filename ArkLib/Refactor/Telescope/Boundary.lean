/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Telescope.Reduction
import ArkLib.Refactor.Telescope.Syntax.Verifier
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Telescope Boundaries

Prototype lifting substrate for the telescope-native refactor.

The old `LiftContext.Lens` layer bundled two different roles:

1. root reindexing of statement and witness interfaces;
2. transcript-indexed continuation composition.

In the telescope setting these roles should stay separate.

* `RootBoundary.*` packages root-only reindexing data. The outer output families may
  still depend on the full realized transcript.
* `StageBoundary` is a public name for the continuation shape already used by
  `Reduction.comp`; it is not a second foundational optic.
-/

namespace ProtocolCtx

open OracleComp OracleSpec

namespace RootBoundary

@[ext]
structure Statement
    (OuterStatement InnerStatement : Type)
    (InnerContext : InnerStatement → ProtocolCtx)
    (InnerOutput : (statement : InnerStatement) → Transcript (InnerContext statement) → Type) where
  proj : OuterStatement → InnerStatement
  output : (outer : OuterStatement) → Transcript (InnerContext (proj outer)) → Type
  lift :
    (outer : OuterStatement) →
    (tr : Transcript (InnerContext (proj outer))) →
    InnerOutput (proj outer) tr → output outer tr

namespace Statement

@[inline, reducible] protected def id
    (Statement : Type)
    (Ctx : Statement → ProtocolCtx)
    (Output : (statement : Statement) → Transcript (Ctx statement) → Type) :
    RootBoundary.Statement Statement Statement Ctx Output where
  proj := id
  output := Output
  lift := fun _ _ out => out

@[inline] def ofInputOnly
    {OuterStatement InnerStatement : Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerOutput : (statement : InnerStatement) → Transcript (InnerContext statement) → Type}
    (proj : OuterStatement → InnerStatement) :
    RootBoundary.Statement OuterStatement InnerStatement InnerContext InnerOutput where
  proj := proj
  output := fun outer tr => InnerOutput (proj outer) tr
  lift := fun _ _ out => out

@[inline] def ofOutputOnly
    {Statement : Type}
    {Ctx : Statement → ProtocolCtx}
    {InnerOutput : (statement : Statement) → Transcript (Ctx statement) → Type}
    (output : (statement : Statement) → Transcript (Ctx statement) → Type)
    (lift :
      (statement : Statement) → (tr : Transcript (Ctx statement)) →
      InnerOutput statement tr → output statement tr) :
    RootBoundary.Statement Statement Statement Ctx InnerOutput where
  proj := id
  output := output
  lift := lift

end Statement

@[ext]
structure Witness
    {OuterStatement InnerStatement : Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    (OuterWitnessIn : OuterStatement → Type)
    (InnerWitnessIn : InnerStatement → Type)
    (stmt : Statement OuterStatement InnerStatement InnerContext InnerStatementOut)
    (InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type) where
  proj : (outer : OuterStatement) → OuterWitnessIn outer → InnerWitnessIn (stmt.proj outer)
  output : (outer : OuterStatement) → Transcript (InnerContext (stmt.proj outer)) → Type
  lift :
    (outer : OuterStatement) →
    (wit : OuterWitnessIn outer) →
    (tr : Transcript (InnerContext (stmt.proj outer))) →
    InnerStatementOut (stmt.proj outer) tr →
    InnerWitnessOut (stmt.proj outer) tr →
    output outer tr

namespace Witness

@[inline, reducible] protected def id
    (Statement : Type)
    (Witness : Statement → Type)
    (Ctx : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Ctx statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Ctx statement) → Type) :
    RootBoundary.Witness Witness Witness
      (RootBoundary.Statement.id Statement Ctx StatementOut)
      WitnessOut where
  proj := fun _ wit => wit
  output := WitnessOut
  lift := fun _ _ _ _ witOut => witOut

end Witness

@[ext]
structure Context
    (OuterStatement InnerStatement : Type)
    (OuterWitnessIn : OuterStatement → Type)
    (InnerWitnessIn : InnerStatement → Type)
    (InnerContext : InnerStatement → ProtocolCtx)
    (InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type)
    (InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type) where
  stmt : Statement OuterStatement InnerStatement InnerContext InnerStatementOut
  wit : Witness OuterWitnessIn InnerWitnessIn stmt InnerWitnessOut

namespace Context

variable
    {OuterStatement InnerStatement : Type}
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    {InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}

@[inline] def proj
    (boundary : Context OuterStatement InnerStatement
      OuterWitnessIn InnerWitnessIn InnerContext InnerStatementOut InnerWitnessOut)
    (outer : OuterStatement) (wit : OuterWitnessIn outer) :
    Σ inner : InnerStatement, InnerWitnessIn inner :=
  ⟨boundary.stmt.proj outer, boundary.wit.proj outer wit⟩

@[inline] def lift
    (boundary : Context OuterStatement InnerStatement
      OuterWitnessIn InnerWitnessIn InnerContext InnerStatementOut InnerWitnessOut)
    (outer : OuterStatement) (wit : OuterWitnessIn outer)
    (tr : Transcript (InnerContext (boundary.stmt.proj outer)))
    (stmtOut : InnerStatementOut (boundary.stmt.proj outer) tr)
    (witOut : InnerWitnessOut (boundary.stmt.proj outer) tr) :
    boundary.stmt.output outer tr × boundary.wit.output outer tr :=
  ⟨boundary.stmt.lift outer tr stmtOut, boundary.wit.lift outer wit tr stmtOut witOut⟩

@[inline, reducible] protected def id
    (Statement : Type)
    (Witness : Statement → Type)
    (Ctx : Statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → Transcript (Ctx statement) → Type)
    (WitnessOut : (statement : Statement) → Transcript (Ctx statement) → Type) :
    RootBoundary.Context Statement Statement Witness Witness Ctx StatementOut WitnessOut where
  stmt := RootBoundary.Statement.id Statement Ctx StatementOut
  wit := RootBoundary.Witness.id Statement Witness Ctx StatementOut WitnessOut

@[inline] def ofInputOnly
    {OuterStatement InnerStatement : Type}
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    {InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    (stmtProj : OuterStatement → InnerStatement)
    (witProj : (outer : OuterStatement) →
      OuterWitnessIn outer → InnerWitnessIn (stmtProj outer)) :
    RootBoundary.Context OuterStatement InnerStatement
      OuterWitnessIn InnerWitnessIn InnerContext InnerStatementOut InnerWitnessOut where
  stmt := RootBoundary.Statement.ofInputOnly
    (InnerContext := InnerContext) (InnerOutput := InnerStatementOut) stmtProj
  wit := {
    proj := witProj
    output := fun outer tr => InnerWitnessOut (stmtProj outer) tr
    lift := fun _ _ _ _ witOut => witOut
  }

end Context

@[ext]
structure InputOracle
    {OuterStatement InnerStatement : Type}
    (OuterInputOracle : OuterStatement → Type) [∀ outer, OracleInterface (OuterInputOracle outer)]
    (InnerInputOracle : InnerStatement → Type) [∀ inner, OracleInterface (InnerInputOracle inner)]
    (projStmt : OuterStatement → InnerStatement) where
  realize : (outer : OuterStatement) →
    OuterInputOracle outer → InnerInputOracle (projStmt outer)

namespace InputOracle

@[inline, reducible] protected def id
    (Statement : Type)
    (InputOracle : Statement → Type)
    [∀ statement, OracleInterface (InputOracle statement)] :
    RootBoundary.InputOracle InputOracle InputOracle id where
  realize := fun _ inputOracle => inputOracle

end InputOracle

@[ext]
structure OracleStatement
    (OuterStatement InnerStatement : Type)
    (OuterInputOracle : OuterStatement → Type) [∀ outer, OracleInterface (OuterInputOracle outer)]
    (InnerInputOracle : InnerStatement → Type) [∀ inner, OracleInterface (InnerInputOracle inner)]
    (InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx)
    (InnerOutput : (statement : InnerStatement) → (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type)
    (InnerOutputOracle : (statement : InnerStatement) → (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)] where
  proj : OuterStatement → InnerStatement
  input : InputOracle OuterInputOracle InnerInputOracle proj
  output : (outer : OuterStatement) → (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) → Type
  lift :
    (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) →
    InnerOutput (proj outer) (input.realize outer inputOracle) tr →
    output outer inputOracle tr
  outputOracle : (outer : OuterStatement) → (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) → Type
  instOutputOracle :
    (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) →
      OracleInterface (outputOracle outer inputOracle tr)
  simulate :
    (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) →
      QueryImpl
        (OracleInterface.spec (Message := outputOracle outer inputOracle tr))
        (OracleComp
          (OracleInterface.spec (Message :=
            InnerOutputOracle (proj outer) (input.realize outer inputOracle) tr)))
  realize :
    (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (proj outer) (input.realize outer inputOracle))) →
    InnerOutputOracle (proj outer) (input.realize outer inputOracle) tr →
    outputOracle outer inputOracle tr

attribute [instance] RootBoundary.OracleStatement.instOutputOracle

namespace OracleStatement

@[inline, reducible] protected def id
    (Statement : Type)
    (InputOracle : Statement → Type)
    [∀ statement, OracleInterface (InputOracle statement)]
    (Ctx : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (Output : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Ctx statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Ctx statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)] :
    RootBoundary.OracleStatement Statement Statement
      InputOracle InputOracle Ctx Output OutputOracle where
  proj := id
  input := RootBoundary.InputOracle.id Statement InputOracle
  output := Output
  lift := fun _ _ _ out => out
  outputOracle := OutputOracle
  instOutputOracle := fun _ _ _ => inferInstance
  simulate := fun statement inputOracle tr q =>
    liftM (query
      (spec := OracleInterface.spec (Message := OutputOracle statement inputOracle tr)) q)
  realize := fun _ _ _ outputOracle => outputOracle

@[inline] def ofInputOnly
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerOutput : (statement : InnerStatement) → (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (stmtProj : OuterStatement → InnerStatement)
    (inputRealize : (outer : OuterStatement) →
      OuterInputOracle outer → InnerInputOracle (stmtProj outer)) :
    RootBoundary.OracleStatement OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle InnerContext InnerOutput InnerOutputOracle where
  proj := stmtProj
  input := { realize := inputRealize }
  output := fun outer inputOracle tr =>
    InnerOutput (stmtProj outer) (inputRealize outer inputOracle) tr
  lift := fun _ _ _ out => out
  outputOracle := fun outer inputOracle tr =>
    InnerOutputOracle (stmtProj outer) (inputRealize outer inputOracle) tr
  instOutputOracle := fun _ _ _ => inferInstance
  simulate := fun outer inputOracle tr q =>
    liftM (query
      (spec := OracleInterface.spec
        (Message := InnerOutputOracle (stmtProj outer) (inputRealize outer inputOracle) tr)) q)
  realize := fun _ _ _ outputOracle => outputOracle

end OracleStatement

@[ext]
structure OracleWitness
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (OuterWitnessIn : OuterStatement → Type)
    (InnerWitnessIn : InnerStatement → Type)
    (stmt : OracleStatement OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle InnerContext InnerStatementOut InnerOutputOracle)
    (InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type) where
  proj : (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    OuterWitnessIn outer → InnerWitnessIn (stmt.proj outer)
  output : (outer : OuterStatement) → (inputOracle : OuterInputOracle outer) →
    (tr : Transcript (InnerContext (stmt.proj outer) (stmt.input.realize outer inputOracle))) → Type
  lift :
    (outer : OuterStatement) →
    (inputOracle : OuterInputOracle outer) →
    (wit : OuterWitnessIn outer) →
    (tr : Transcript (InnerContext (stmt.proj outer) (stmt.input.realize outer inputOracle))) →
    InnerStatementOut (stmt.proj outer) (stmt.input.realize outer inputOracle) tr →
    InnerOutputOracle (stmt.proj outer) (stmt.input.realize outer inputOracle) tr →
    InnerWitnessOut (stmt.proj outer) (stmt.input.realize outer inputOracle) tr →
    output outer inputOracle tr

namespace OracleWitness

@[inline, reducible] protected def id
    (Statement : Type)
    (InputOracle : Statement → Type)
    [∀ statement, OracleInterface (InputOracle statement)]
    (Witness : Statement → Type)
    (Ctx : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Ctx statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Ctx statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Ctx statement inputOracle)) → Type) :
    RootBoundary.OracleWitness (OuterInputOracle := InputOracle)
      (InnerInputOracle := InputOracle) Witness Witness
      (RootBoundary.OracleStatement.id Statement InputOracle Ctx StatementOut OutputOracle)
      WitnessOut where
  proj := fun _ _ wit => wit
  output := WitnessOut
  lift := fun _ _ _ _ _ _ witOut => witOut

end OracleWitness

@[ext]
structure OracleContext
    (OuterStatement InnerStatement : Type)
    (OuterInputOracle : OuterStatement → Type) [∀ outer, OracleInterface (OuterInputOracle outer)]
    (InnerInputOracle : InnerStatement → Type) [∀ inner, OracleInterface (InnerInputOracle inner)]
    (OuterWitnessIn : OuterStatement → Type)
    (InnerWitnessIn : InnerStatement → Type)
    (InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx)
    (InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type)
    (InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type) where
  stmt : OracleStatement OuterStatement InnerStatement
    OuterInputOracle InnerInputOracle InnerContext InnerStatementOut InnerOutputOracle
  wit : OracleWitness (OuterInputOracle := OuterInputOracle)
    (InnerInputOracle := InnerInputOracle)
    OuterWitnessIn InnerWitnessIn stmt InnerWitnessOut

namespace OracleContext

@[inline, reducible] protected def id
    (Statement : Type)
    (InputOracle : Statement → Type)
    [∀ statement, OracleInterface (InputOracle statement)]
    (Witness : Statement → Type)
    (Ctx : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Ctx statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Ctx statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (WitnessOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Ctx statement inputOracle)) → Type) :
    RootBoundary.OracleContext Statement Statement
      InputOracle InputOracle Witness Witness
      Ctx StatementOut OutputOracle WitnessOut where
  stmt := RootBoundary.OracleStatement.id
    Statement InputOracle Ctx StatementOut OutputOracle
  wit := RootBoundary.OracleWitness.id
    Statement InputOracle Witness Ctx StatementOut OutputOracle WitnessOut

/-- Telescope-native input-only oracle pullback. This is the direct analogue of the
old `OracleContext.Lens.ofInputOnly` pattern used by root wrappers such as Batched FRI:
the outer root interface projects to the inner statement/input/witness, while all
output families are inherited definitionally from the inner reduction. -/
@[inline] def ofInputOnly
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    {InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    (stmtProj : OuterStatement → InnerStatement)
    (inputRealize : (outer : OuterStatement) →
      OuterInputOracle outer → InnerInputOracle (stmtProj outer))
    (witProj : (outer : OuterStatement) →
      OuterInputOracle outer → OuterWitnessIn outer → InnerWitnessIn (stmtProj outer)) :
    RootBoundary.OracleContext OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle OuterWitnessIn InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut where
  stmt := RootBoundary.OracleStatement.ofInputOnly
    (InnerContext := InnerContext)
    (InnerOutput := InnerStatementOut)
    (InnerOutputOracle := InnerOutputOracle)
    stmtProj inputRealize
  wit := {
    proj := witProj
    output := fun outer inputOracle tr =>
      InnerWitnessOut (stmtProj outer) (inputRealize outer inputOracle) tr
    lift := fun _ _ _ _ _ _ witOut => witOut
  }

end OracleContext

namespace OracleStatement

/-- Freeze the outer input oracle into the public statement, yielding the root-only
plain statement boundary seen by `toVerifier` / `toReduction`. -/
@[inline] def toStatement
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerOutput : (statement : InnerStatement) → (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) → (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (boundary : RootBoundary.OracleStatement OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle InnerContext InnerOutput InnerOutputOracle) :
    RootBoundary.Statement
      ((outer : OuterStatement) × OuterInputOracle outer)
      ((inner : InnerStatement) × InnerInputOracle inner)
      (fun inner => InnerContext inner.1 inner.2)
      (fun inner tr => InnerOutput inner.1 inner.2 tr) where
  proj := fun ⟨outer, inputOracle⟩ =>
    ⟨boundary.proj outer, boundary.input.realize outer inputOracle⟩
  output := fun outer tr => boundary.output outer.1 outer.2 tr
  lift := fun outer tr out => boundary.lift outer.1 outer.2 tr out

end OracleStatement

end RootBoundary

namespace Verifier

def pullback {m : Type → Type} [Monad m]
    {OuterStatement InnerStatement : Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerOutput : (statement : InnerStatement) → Transcript (InnerContext statement) → Type}
    (boundary : RootBoundary.Statement OuterStatement InnerStatement InnerContext InnerOutput)
    (verifier : (statement : InnerStatement) →
      (tr : Transcript (InnerContext statement)) → OptionT m (InnerOutput statement tr)) :
    (outer : OuterStatement) →
      (tr : Transcript (InnerContext (boundary.proj outer))) →
      OptionT m (boundary.output outer tr) :=
  open scoped TelescopeSyntax in
  verifier!{ outer, tr => do
    let out ← verifier (boundary.proj outer) tr
    pure (boundary.lift outer tr out)
  }

end Verifier

namespace HonestProver

def pullback {m : Type → Type} [Monad m]
    {OuterStatement InnerStatement : Type}
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    {InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    (boundary : RootBoundary.Context OuterStatement InnerStatement
      OuterWitnessIn InnerWitnessIn InnerContext InnerStatementOut InnerWitnessOut)
    (prover : HonestProver m InnerStatement InnerWitnessIn
      InnerContext InnerStatementOut InnerWitnessOut) :
    HonestProver m OuterStatement OuterWitnessIn
      (fun outer => InnerContext (boundary.stmt.proj outer))
      (fun outer tr => boundary.stmt.output outer tr)
      (fun outer tr => boundary.wit.output outer tr) :=
  fun outer wit => do
    let inner ← prover (boundary.stmt.proj outer) (boundary.wit.proj outer wit)
    pure <| Prover.mapOutput
      (fun tr out => boundary.lift outer wit tr out.1 out.2)
      inner

end HonestProver

namespace Reduction

def pullback {m : Type → Type} [Monad m]
    {OuterStatement InnerStatement : Type}
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    {InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    (boundary : RootBoundary.Context OuterStatement InnerStatement
      OuterWitnessIn InnerWitnessIn InnerContext InnerStatementOut InnerWitnessOut)
    (red : Reduction m InnerStatement InnerWitnessIn
      InnerContext InnerStatementOut InnerWitnessOut) :
    Reduction m OuterStatement OuterWitnessIn
      (fun outer => InnerContext (boundary.stmt.proj outer))
      (fun outer tr => boundary.stmt.output outer tr)
      (fun outer tr => boundary.wit.output outer tr) where
  prover := HonestProver.pullback boundary red.prover
  verifier := Verifier.pullback boundary.stmt red.verifier

/-- Telescope-native input-only root lift for plain reductions. This packages the
common old `Context.Lens.ofInputOnly` pattern into a direct call to `pullback`. -/
@[inline] def pullbackInputOnly {m : Type → Type} [Monad m]
    {OuterStatement InnerStatement : Type}
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : InnerStatement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    {InnerWitnessOut : (statement : InnerStatement) →
      Transcript (InnerContext statement) → Type}
    (stmtProj : OuterStatement → InnerStatement)
    (witProj : (outer : OuterStatement) →
      OuterWitnessIn outer → InnerWitnessIn (stmtProj outer))
    (red : Reduction m InnerStatement InnerWitnessIn
      InnerContext InnerStatementOut InnerWitnessOut) :
    Reduction m OuterStatement OuterWitnessIn
      (fun outer => InnerContext (stmtProj outer))
      (fun outer tr => InnerStatementOut (stmtProj outer) tr)
      (fun outer tr => InnerWitnessOut (stmtProj outer) tr) :=
  pullback
    (RootBoundary.Context.ofInputOnly
      (InnerContext := InnerContext)
      (InnerStatementOut := InnerStatementOut)
      (InnerWitnessOut := InnerWitnessOut)
      stmtProj witProj)
    red

end Reduction

namespace OracleVerifier

def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (boundary : RootBoundary.OracleStatement OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle InnerContext InnerStatementOut InnerOutputOracle)
    (verifier : ProtocolCtx.OracleVerifier oSpec InnerStatement InnerInputOracle
      InnerContext InnerStatementOut InnerOutputOracle) :
    ProtocolCtx.OracleVerifier oSpec OuterStatement OuterInputOracle
      (fun outer inputOracle =>
        InnerContext (boundary.proj outer) (boundary.input.realize outer inputOracle))
      (fun outer inputOracle tr => boundary.output outer inputOracle tr)
      (fun outer inputOracle tr => boundary.outputOracle outer inputOracle tr) where
    verify := open scoped TelescopeSyntax in
      verifier!{ outer, inputOracle, tr => do
        let out ← verifier.verify
          (boundary.proj outer) (boundary.input.realize outer inputOracle) tr
        pure (boundary.lift outer inputOracle tr out)
      }
    simulate := fun outer inputOracle tr =>
      QueryImpl.compose
        (verifier.simulate
          (boundary.proj outer) (boundary.input.realize outer inputOracle) tr)
        (boundary.simulate outer inputOracle tr)
    realize := fun outer inputOracle tr =>
      Option.map (boundary.realize outer inputOracle tr)
        (verifier.realize
          (boundary.proj outer) (boundary.input.realize outer inputOracle) tr)

theorem pullback_toVerifier_comm
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    (boundary : RootBoundary.OracleStatement OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle InnerContext InnerStatementOut InnerOutputOracle)
    (verifier : ProtocolCtx.OracleVerifier oSpec InnerStatement InnerInputOracle
      InnerContext InnerStatementOut InnerOutputOracle)
    (outer : OuterStatement) (inputOracle : OuterInputOracle outer) :
    ProtocolCtx.OracleVerifier.toVerifier (pullback boundary verifier) outer inputOracle =
      fun tr =>
        (Verifier.pullback (RootBoundary.OracleStatement.toStatement boundary)
          (fun inner tr =>
            ProtocolCtx.OracleVerifier.toVerifier verifier inner.1 inner.2 tr)
          ⟨outer, inputOracle⟩) tr := by
  funext tr
  apply OptionT.ext
  simp only [toVerifier, Verifier.pullback, RootBoundary.OracleStatement.toStatement,
    bind_pure_comp, OptionT.run_map]
  change
    simulateQ (ProtocolCtx.OracleVerifier.oracleImpl (oSpec := oSpec) tr)
      (OptionT.run
        (boundary.lift outer inputOracle tr <$>
          verifier.verify (boundary.proj outer) (boundary.input.realize outer inputOracle) tr)) =
      Option.map (boundary.lift outer inputOracle tr) <$>
        simulateQ (ProtocolCtx.OracleVerifier.oracleImpl (oSpec := oSpec) tr)
          (OptionT.run
            (verifier.verify
              (boundary.proj outer) (boundary.input.realize outer inputOracle) tr))
  rw [OptionT.run_map, simulateQ_map]

end OracleVerifier

namespace OracleProver

def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    {InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    (boundary : RootBoundary.OracleContext OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle OuterWitnessIn InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut)
    (prover : OracleProver oSpec InnerStatement InnerInputOracle InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut) :
    OracleProver oSpec OuterStatement OuterInputOracle OuterWitnessIn
      (fun outer inputOracle =>
        InnerContext (boundary.stmt.proj outer) (boundary.stmt.input.realize outer inputOracle))
      (fun outer inputOracle tr => boundary.stmt.output outer inputOracle tr)
      (fun outer inputOracle tr => boundary.stmt.outputOracle outer inputOracle tr)
      (fun outer inputOracle tr => boundary.wit.output outer inputOracle tr) :=
  fun outer inputOracle wit => do
    let inner ← prover (boundary.stmt.proj outer)
      (boundary.stmt.input.realize outer inputOracle)
      (boundary.wit.proj outer inputOracle wit)
    pure <| Prover.mapOutput
      (fun tr out =>
        let stmtOut := out.1.1
        let outputOracle := out.1.2
        let witOut := out.2
        ((boundary.stmt.lift outer inputOracle tr stmtOut,
            boundary.stmt.realize outer inputOracle tr outputOracle),
          boundary.wit.lift outer inputOracle wit tr stmtOut outputOracle witOut))
      inner

end OracleProver

namespace OracleReduction

def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    {InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    (boundary : RootBoundary.OracleContext OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle OuterWitnessIn InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut)
    (red : OracleReduction oSpec InnerStatement InnerInputOracle InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut) :
    OracleReduction oSpec OuterStatement OuterInputOracle OuterWitnessIn
      (fun outer inputOracle =>
        InnerContext (boundary.stmt.proj outer) (boundary.stmt.input.realize outer inputOracle))
      (fun outer inputOracle tr => boundary.stmt.output outer inputOracle tr)
      (fun outer inputOracle tr => boundary.stmt.outputOracle outer inputOracle tr)
      (fun outer inputOracle tr => boundary.wit.output outer inputOracle tr) where
    prover := OracleProver.pullback boundary red.prover
    verifier := OracleVerifier.pullback boundary.stmt red.verifier

theorem pullback_toReduction_verifier_comm
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    {InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    (boundary : RootBoundary.OracleContext OuterStatement InnerStatement
      OuterInputOracle InnerInputOracle OuterWitnessIn InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut)
    (red : OracleReduction oSpec InnerStatement InnerInputOracle InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut) :
    (ProtocolCtx.OracleReduction.toReduction (pullback boundary red)).verifier =
      fun statement tr =>
        (Verifier.pullback (RootBoundary.OracleStatement.toStatement boundary.stmt)
          (ProtocolCtx.OracleReduction.toReduction red).verifier statement) tr := by
  funext statement
  cases statement with
  | mk outer inputOracle =>
      simpa [OracleReduction.pullback, ProtocolCtx.OracleReduction.toReduction] using
        (OracleVerifier.pullback_toVerifier_comm
          (boundary := boundary.stmt) (verifier := red.verifier)
          (outer := outer) (inputOracle := inputOracle))

/-- Telescope-native input-only oracle root lift. This is the direct replacement for
old `liftContext` call sites that only change the root statement/input-oracle surface
while inheriting all output families from the inner reduction. -/
@[inline] def pullbackInputOnly
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStatement InnerStatement : Type}
    {OuterInputOracle : OuterStatement → Type}
    [∀ outer, OracleInterface (OuterInputOracle outer)]
    {InnerInputOracle : InnerStatement → Type}
    [∀ inner, OracleInterface (InnerInputOracle inner)]
    {OuterWitnessIn : OuterStatement → Type}
    {InnerWitnessIn : InnerStatement → Type}
    {InnerContext : (statement : InnerStatement) → InnerInputOracle statement → ProtocolCtx}
    {InnerStatementOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      Transcript (InnerContext statement inputOracle) → Type}
    {InnerOutputOracle : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (InnerOutputOracle statement inputOracle tr)]
    {InnerWitnessOut : (statement : InnerStatement) →
      (inputOracle : InnerInputOracle statement) →
      (tr : Transcript (InnerContext statement inputOracle)) → Type}
    (stmtProj : OuterStatement → InnerStatement)
    (inputRealize : (outer : OuterStatement) →
      OuterInputOracle outer → InnerInputOracle (stmtProj outer))
    (witProj : (outer : OuterStatement) →
      OuterInputOracle outer → OuterWitnessIn outer → InnerWitnessIn (stmtProj outer))
    (red : OracleReduction oSpec InnerStatement InnerInputOracle InnerWitnessIn
      InnerContext InnerStatementOut InnerOutputOracle InnerWitnessOut) :
    let OuterOutputOracle :=
      fun (outer : OuterStatement) (inputOracle : OuterInputOracle outer)
        (tr : Transcript (InnerContext (stmtProj outer) (inputRealize outer inputOracle))) =>
        InnerOutputOracle (stmtProj outer) (inputRealize outer inputOracle) tr
    OracleReduction oSpec OuterStatement OuterInputOracle OuterWitnessIn
      (fun outer inputOracle => InnerContext (stmtProj outer) (inputRealize outer inputOracle))
      (fun outer inputOracle tr =>
        InnerStatementOut (stmtProj outer) (inputRealize outer inputOracle) tr)
      OuterOutputOracle
      (fun outer inputOracle tr =>
        InnerWitnessOut (stmtProj outer) (inputRealize outer inputOracle) tr) :=
  pullback
    (RootBoundary.OracleContext.ofInputOnly
      (InnerContext := InnerContext)
      (InnerStatementOut := InnerStatementOut)
      (InnerOutputOracle := InnerOutputOracle)
      (InnerWitnessOut := InnerWitnessOut)
      stmtProj inputRealize witProj)
    red

end OracleReduction

/-- Transcript-indexed continuation boundary for staged composition. This is a public
name for the second argument of `Reduction.comp`; unlike `RootBoundary`, it does not
introduce a new foundational transport primitive. -/
abbrev StageBoundary (m : Type → Type)
    (Statement : Type)
    (Context₁ : Statement → ProtocolCtx)
    (StatementMid : (statement : Statement) → Transcript (Context₁ statement) → Type)
    (WitnessMid : (statement : Statement) → Transcript (Context₁ statement) → Type)
    (Context₂ : (statement : Statement) → Transcript (Context₁ statement) → ProtocolCtx)
    (StatementOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type)
    (WitnessOut : (statement : Statement) →
      (tr₁ : Transcript (Context₁ statement)) → Transcript (Context₂ statement tr₁) → Type) :=
  (statement : Statement) → (tr₁ : Transcript (Context₁ statement)) →
    Reduction m (StatementMid statement tr₁) (fun _ => WitnessMid statement tr₁)
      (fun _ => Context₂ statement tr₁)
      (fun _ tr₂ => StatementOut statement tr₁ tr₂)
      (fun _ tr₂ => WitnessOut statement tr₁ tr₂)

namespace StageBoundary

@[inline] def comp {m : Type → Type} [Monad m]
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
    (boundary₂ : StageBoundary m Statement Context₁ StatementMid WitnessMid
      Context₂ StatementOut WitnessOut) :
    Reduction m Statement WitnessIn
      (fun statement => (Context₁ statement).append (Context₂ statement))
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        StatementOut statement parts.1 parts.2)
      (fun statement tr =>
        let parts := Transcript.split (Context₁ statement) (Context₂ statement) tr
        WitnessOut statement parts.1 parts.2) :=
  Reduction.comp r₁ boundary₂

end StageBoundary

end ProtocolCtx
