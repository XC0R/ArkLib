import ArkLib.Interaction.Boundary.Oracle
import ArkLib.Interaction.OracleReification

/-!
# Interaction-Native Boundaries: Reification Layer

This layer adds *concrete oracle materialization* on top of the oracle access
layer.  Where the access layer translates oracle queries (sufficient for the
verifier), the reification layer maps concrete oracle data directly (needed by
the prover and for validation against real executions).

## Two complementary views

For any oracle boundary there are two views of the same transport:

- **Simulation** (`OracleStatementAccess`): answer oracle queries by issuing
  other oracle queries.  This is all the verifier ever needs.
- **Materialization** (`OracleStatementReification`): given concrete oracle data,
  produce concrete oracle data.  This is what the prover needs.

`OracleStatementReification.Realizes` is the coherence predicate asserting that
these two views agree on every query answer.

## Bundled structures

`OracleStatement` and `OracleContext` bundle the plain boundary, oracle access,
oracle reification, and the coherence proof into a single record.  These are the
primary objects passed to `OracleDecoration.OracleReduction.pullback`.
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-- Concrete oracle materialization for a statement boundary.

`materializeIn` maps a concrete outer input oracle family to a concrete inner
input oracle family, given the outer statement.

`materializeOut` maps a concrete inner output oracle family (plus the outer
input oracle and transcript as context) to a concrete outer output oracle
family.  The outer input oracle is provided because the outer output oracle may
depend on it (e.g., when derived from the input). -/
structure OracleStatementReification
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toStatement : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  materializeIn :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      OracleStatement InnerOStmtIn
  materializeOut :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
      OracleStatement (InnerOStmtOut (toStatement.proj outer) tr) →
      OracleStatement (OuterOStmtOut outer tr)

/-- Oracle reification bundled with a plain witness boundary.  Witness transport
does not affect oracle reification; this structure groups them for
convenience. -/
structure OracleContextReification
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  stmt : OracleStatementReification toContext.stmt
    OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut

namespace OracleStatementReification

/-- Coherence between the simulation view (`access`) and the materialization
view (`reification`): for every concrete oracle data, simulating a query and
materializing the oracle give the same answer.

Two clauses:
1. **Input**: `simulateIn` against the outer input oracle agrees with
   materializing the inner input oracle and answering directly.
2. **Output**: `simulateOut` against the outer input and inner output oracles
   agrees with materializing the outer output oracle and answering directly.

This is the key hypothesis for future security transport theorems. -/
def Realizes
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {toStatement : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      OracleStatementAccess toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) : Prop :=
  (∀ outer oStmtIn i q,
      simulateQ
        (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
        (access.simulateIn ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              (reification.materializeIn outer oStmtIn i)
              q)) ∧
    ∀ outer oStmtIn tr innerOStmtOut i q,
      simulateQ
        (QueryImpl.add
          (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
          (OracleInterface.simOracle0
            (InnerOStmtOut (toStatement.proj outer) tr)
            innerOStmtOut))
        (access.simulateOut outer tr ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              ((reification.materializeOut
                outer
                oStmtIn
                tr
                innerOStmtOut) i)
              q)

end OracleStatementReification

/-- A fully bundled oracle statement boundary: plain statement boundary + oracle
access (simulation) + oracle reification (materialization) + coherence proof.

`toStatement` is an explicit type parameter so that the oracle families
`OuterOStmtOut` / `InnerOStmtOut` can depend on `toStatement.proj`.

Use this to drive `OracleDecoration.OracleReduction.pullback`. -/
structure OracleStatement
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toStatement : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  access :
    OracleStatementAccess toStatement
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut
  reification :
    OracleStatementReification toStatement
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut
  coherent :
    OracleStatementReification.Realizes access reification

/-- A fully bundled oracle context boundary: plain context boundary + oracle
access + oracle reification + coherence proof.

`toContext` is an explicit type parameter so that the oracle families can depend
on `toContext.stmt.proj`.  The coherence law lives at the statement level
(`access.stmt` / `reification.stmt`); the witness transport is independent of
oracle simulation.

Use this to drive `OracleDecoration.OracleReduction.pullback`. -/
structure OracleContext
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  access :
    OracleContextAccess toContext
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut
  reification :
    OracleContextReification toContext
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut
  coherent :
    OracleStatementReification.Realizes
      access.stmt
      reification.stmt

end Boundary

namespace OracleDecoration
namespace OracleReduction

/-- Reinterpret an inner oracle reduction through a full oracle context boundary.

- **Prover**: materializes the inner input oracle via `materializeIn`; runs the
  inner prover; materializes the outer output oracle via `materializeOut`;
  lifts all outputs through the plain context boundary.
- **Verifier**: rewired through `OracleReduction.pullbackVerifier` (access layer).
- **Output simulation**: rewired through `OracleStatementAccess.pullbackSimulate`. -/
def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (toContext :
      Boundary.Context OuterStmtIn InnerStmtIn
        OuterWitIn InnerWitIn
        InnerContext InnerStmtOut InnerWitOut)
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerContext s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
        InnerContext InnerRoles InnerOD InnerStmtOut InnerOStmtOut InnerWitOut) :
    OracleReduction oSpec
      OuterStmtIn
      OuterOStmtIn
      OuterWitIn
      (fun outer => InnerContext (toContext.stmt.proj outer))
      (fun outer => InnerRoles (toContext.stmt.proj outer))
      (fun outer => InnerOD (toContext.stmt.proj outer))
      toContext.StmtOut
      (fun outer tr => OuterOStmtOut outer tr)
      toContext.WitOut where
  prover sWithOracles outerWit := do
    let outerStmt := sWithOracles.stmt
    let outerOStmtIn := sWithOracles.oracleStmt
    let innerStmt := toContext.stmt.proj outerStmt
    let innerOStmtIn :=
      boundary.reification.stmt.materializeIn outerStmt outerOStmtIn
    let innerWit :=
      toContext.wit.proj outerStmt outerWit
    let strat ← reduction.prover ⟨innerStmt, innerOStmtIn⟩ innerWit
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        let innerStmtOut := out.stmt.stmt
        let innerOStmtOut := out.stmt.oracleStmt
        let outerStmtOut :=
          toContext.stmt.lift outerStmt tr innerStmtOut
        let outerOStmtOut :=
          boundary.reification.stmt.materializeOut
            outerStmt
            outerOStmtIn
            tr
            innerOStmtOut
        let outerWitOut :=
          toContext.wit.lift
            outerStmt
            outerWit
            tr
            innerStmtOut
            out.wit
        ⟨⟨outerStmtOut, outerOStmtOut⟩, outerWitOut⟩)
      strat
  verifier :=
    OracleReduction.pullbackVerifier
      toContext.stmt
      boundary.access.stmt
      reduction.verifier
  simulate outerStmt tr :=
    Boundary.OracleStatementAccess.pullbackSimulate
      (access := boundary.access.stmt)
      outerStmt
      tr
      (toOracleSpec
        (InnerContext (toContext.stmt.proj outerStmt))
        (InnerRoles (toContext.stmt.proj outerStmt))
        (InnerOD (toContext.stmt.proj outerStmt))
        tr)
      (reduction.simulate (toContext.stmt.proj outerStmt) tr)

end OracleReduction
end OracleDecoration
end Interaction
