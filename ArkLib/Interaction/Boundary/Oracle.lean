import ArkLib.Interaction.Boundary.Core
import ArkLib.Interaction.Oracle

/-!
# Interaction-Native Boundaries: Oracle Access Layer

This layer extends plain boundaries with verifier-side oracle simulation.
It does **not** deal with concrete oracle data; that belongs to the reification
layer (`Boundary.Reification`).

## The two simulation obligations

`OracleStatementAccess` carries exactly two fields:

- `simulateIn`: translate a query to an *inner* input oracle into a computation
  over *outer* input oracles.  Statement-independent: applies at every round
  uniformly, because the input oracle is fixed before the interaction begins.

- `simulateOut`: translate a query to an *outer* output oracle into a
  computation that may read both outer input oracles and inner output oracles.
  Statement-dependent because the outer output oracle type may depend on the
  outer statement and transcript.

## pullbackCounterpart

The key combinator walks a `Spec.Counterpart.withMonads` tree and rewires every
receiver-node oracle query through `simulateIn` via `simulateQ`.  This is an
instance of interpreter lifting: the inner oracle calls are handled by an outer
oracle handler.

## Usage

`OracleStatementAccess` is sufficient for verifier pullbacks and for the
verifier half of a reduction pullback.  To pull back the prover (which holds
concrete oracle data), you also need the reification layer.
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-- Verifier-side oracle simulation data for a statement boundary.

`simulateIn` routes a single inner input-oracle query to outer input-oracle
computations; it is statement-independent because input oracles are fixed
before the interaction starts.

`simulateOut` routes a single outer output-oracle query to computations that
may read *both* the outer input oracles and the inner output oracles.  It is
parameterized by the outer statement and transcript because the outer output
oracle type may depend on them. -/
structure OracleStatementAccess
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
  simulateIn :
    QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  simulateOut :
    (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
      QueryImpl [OuterOStmtOut outer tr]ₒ
        (OracleComp
          ([OuterOStmtIn]ₒ +
            [InnerOStmtOut (toStatement.proj outer) tr]ₒ))

/-- Oracle access bundled with a plain witness boundary.  Witness transport does
not affect oracle simulation; this structure groups them for convenience. -/
structure OracleContextAccess
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
  stmt : OracleStatementAccess toContext.stmt
    OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut

namespace OracleStatementAccess

/-- Route inner input oracle queries through `simulateIn`, passing base oracles
(`oSpec`) and the accumulator (`accSpec`) through unchanged.  Used at receiver
nodes of `pullbackCounterpart`. -/
def routeInputQueries
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (accSpec : OracleSpec ιₐ) :
    QueryImpl
      ((oSpec + [InnerOStmtIn]ₒ) + accSpec)
      (OracleComp ((oSpec + [OuterOStmtIn]ₒ) + accSpec))
  | .inl (.inl q) =>
      liftM <| query (spec := oSpec) q
  | .inl (.inr q) =>
      OracleComp.liftComp
        (superSpec := (oSpec + [OuterOStmtIn]ₒ) + accSpec)
        (simulateIn q)
  | .inr q =>
      liftM <| query (spec := accSpec) q

/-- Given a simulation of an inner output oracle that issues inner input oracle
queries, compose it with `simulateIn` to produce a simulation that issues outer
input oracle queries instead.  Used inside `pullbackSimulate`. -/
def routeInnerOutputQueries
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {toStatement : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    {outer : OuterStmtIn}
    {tr : Spec.Transcript (InnerContext (toStatement.proj outer))}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut (toStatement.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [InnerOStmtOut (toStatement.proj outer) tr]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl ([InnerOStmtIn]ₒ + msgSpec)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          OracleComp.liftComp
            (superSpec := [OuterOStmtIn]ₒ + msgSpec)
            (access.simulateIn qIn)
      | .inr qMsg =>
          liftM <| query (spec := msgSpec) qMsg
    simulateQ route (simulateInner q)

/-- Rewire a verifier's output oracle simulation through a statement boundary.
An outer output oracle query is passed to `simulateOut`, which may in turn
issue inner output oracle sub-queries; those are routed to the outer input
oracle via `routeInnerOutputQueries`. -/
def pullbackSimulate
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {toStatement : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    (outer : OuterStmtIn)
    (tr : Spec.Transcript (InnerContext (toStatement.proj outer)))
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut (toStatement.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [OuterOStmtOut outer tr]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl
          ([OuterOStmtIn]ₒ + [InnerOStmtOut (toStatement.proj outer) tr]ₒ)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          liftM <| query (spec := [OuterOStmtIn]ₒ) qIn
      | .inr qOut =>
          routeInnerOutputQueries
            (access := access)
            (outer := outer)
            (tr := tr)
            msgSpec
            simulateInner
            qOut
    simulateQ route (access.simulateOut outer tr q)

end OracleStatementAccess

/-- Rewire every receiver-node oracle query in a `Spec.Counterpart.withMonads`
tree through `simulateIn`, mapping inner input oracle queries to outer input
oracle computations, while also applying an output map `f`.

This is the core interpreter-lifting operation: the inner oracle signature is
handled by an outer oracle handler at every round. -/
def pullbackCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (spec : Spec)
    (roles : RoleDecoration spec)
    (od : OracleDecoration spec roles)
    {Output₁ Output₂ : Spec.Transcript spec → Type}
    (f : ∀ tr, Output₁ tr → Output₂ tr)
    {ιₐ : Type}
    (accSpec : OracleSpec ιₐ)
    (cpt :
      Spec.Counterpart.withMonads spec roles
        (OracleDecoration.toMonadDecoration
          oSpec InnerOStmtIn spec roles od accSpec)
        Output₁) :
    Spec.Counterpart.withMonads spec roles
      (OracleDecoration.toMonadDecoration
        oSpec OuterOStmtIn spec roles od accSpec)
      Output₂ :=
  match spec, roles, od with
  | .done, _, _ =>
      f ⟨⟩ cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      fun x =>
        pullbackCounterpart
          (simulateIn := simulateIn)
          (rest x)
          (rRest x)
          (odRest x)
          (fun tr out => f ⟨x, tr⟩ out)
          (accSpec + @OracleInterface.spec _ oi)
          (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      simulateQ
        (OracleStatementAccess.routeInputQueries
          (oSpec := oSpec)
          simulateIn
          accSpec) <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x,
          pullbackCounterpart
            (simulateIn := simulateIn)
            (rest x)
            (rRest x)
            (odFn x)
            (fun tr out => f ⟨x, tr⟩ out)
            accSpec
            cptRest⟩

end Boundary

namespace OracleDecoration
namespace OracleVerifier

/-- Reinterpret an inner oracle verifier through a statement boundary and oracle
access layer.  Input oracle queries are rerouted via `access.simulateIn`;
output oracle simulation is rerouted via `access.simulateOut`. -/
def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {od : OracleDecoration pSpec roles}
    {OuterStmtIn InnerStmtIn : Type}
    {InnerStmtOut : InnerStmtIn → Spec.Transcript pSpec → Type}
    (stmt :
      Boundary.Statement OuterStmtIn InnerStmtIn (fun _ => pSpec) InnerStmtOut)
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ : Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript pSpec) →
      Innerιₛₒ → Type}
    {Outerιₛₒ : Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript pSpec) →
      Outerιₛₒ → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      Boundary.OracleStatementAccess stmt
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      OracleVerifier oSpec pSpec roles od
        InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut) :
    OracleVerifier oSpec pSpec roles od
      OuterStmtIn OuterOStmtIn stmt.StmtOut OuterOStmtOut where
  iov :=
    Boundary.pullbackCounterpart access.simulateIn
      pSpec
      roles
      od
      (fun tr verifyInner outerStmt => do
        let stmtOut ← simulateQ
          (Boundary.OracleStatementAccess.routeInputQueries
            (oSpec := oSpec)
            access.simulateIn
            (toOracleSpec pSpec roles od tr))
          (verifyInner (stmt.proj outerStmt))
        pure (stmt.lift outerStmt tr stmtOut))
      (ιₐ := PEmpty)
      []ₒ
      verifier.iov
  simulate outerStmt tr :=
    Boundary.OracleStatementAccess.pullbackSimulate
      (access := access)
      outerStmt
      tr
      (toOracleSpec pSpec roles od tr)
      (verifier.simulate (stmt.proj outerStmt) tr)

end OracleVerifier

namespace OracleReduction

/-- Rewire the verifier side of an oracle reduction through a statement boundary
and oracle access layer.  Used by `OracleDecoration.OracleReduction.pullback`
(reification layer) to wire the verifier; separated here so it can be called
without concrete oracle data. -/
def pullbackVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerContext s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (stmt :
      Boundary.Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerContext s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      Boundary.OracleStatementAccess stmt
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      (s : InnerStmtIn) →
        {ιₐ : Type} →
        (accSpec : OracleSpec ιₐ) →
        Spec.Counterpart.withMonads
          (InnerContext s)
          (InnerRoles s)
          (toMonadDecoration oSpec InnerOStmtIn
            (InnerContext s) (InnerRoles s) (InnerOD s) accSpec)
          (fun tr => InnerStmtOut s tr)) :
    (outer : OuterStmtIn) →
      {ιₐ : Type} →
      (accSpec : OracleSpec ιₐ) →
      Spec.Counterpart.withMonads
        (InnerContext (stmt.proj outer))
        (InnerRoles (stmt.proj outer))
        (toMonadDecoration oSpec OuterOStmtIn
          (InnerContext (stmt.proj outer))
          (InnerRoles (stmt.proj outer))
          (InnerOD (stmt.proj outer))
          accSpec)
        (fun tr => stmt.StmtOut outer tr) :=
  fun outer {_} accSpec =>
    Boundary.pullbackCounterpart access.simulateIn
      (InnerContext (stmt.proj outer))
      (InnerRoles (stmt.proj outer))
      (InnerOD (stmt.proj outer))
      (fun tr stmtOut => stmt.lift outer tr stmtOut)
      accSpec
      (verifier (stmt.proj outer) accSpec)

end OracleReduction
end OracleDecoration
end Interaction
