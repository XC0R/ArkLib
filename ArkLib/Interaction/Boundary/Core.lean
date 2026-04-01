import ArkLib.Interaction.Reduction

/-!
# Interaction-Native Boundaries: Core Layer

A *boundary* reinterprets an existing interaction through a different outer
statement/witness interface without changing the underlying transcript or round
structure.  This is distinct from sequential composition, which extends a
protocol by appending new rounds.

## Three structures, one idea

`Statement` carries the statement-level boundary data:
- project the outer input statement to the inner one (`proj`);
- define what the outer output statement is (`StmtOut`);
- lift an inner output statement back to an outer one (`lift`).

`Witness` adds honest-prover witness transport over a fixed `Statement` boundary:
- project the outer witness to the inner one (`proj`);
- lift the inner output witness back to the outer one (`lift`).

`Context` bundles both into a single record.

## pullback

Given a boundary `b` and an inner protocol participant (verifier, prover, or
reduction), `pullback b` produces an outer participant that:
1. projects its input through `b`,
2. runs the inner participant on the projected input,
3. lifts the inner output back through `b`.

The transcript is unchanged throughout.
-/

namespace Interaction
namespace Boundary

/-- The statement-level half of a boundary.

`proj` maps the outer input statement to the inner one used by the protocol.
`StmtOut` specifies the *outer* output statement type after the interaction; it
may be strictly larger than the inner output statement type pushed through
`proj`.  `lift` produces an outer output statement from the inner one, given the
outer input and the shared transcript. -/
structure Statement
    (OuterStmtIn InnerStmtIn : Type)
    (InnerContext : InnerStmtIn → Spec)
    (InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type) where
  proj : OuterStmtIn → InnerStmtIn
  StmtOut :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerContext (proj outer)) → Type
  lift :
    (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerContext (proj outer))) →
      InnerStmtOut (proj outer) tr →
      StmtOut outer tr

namespace Statement

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}

/-- The outer protocol spec, computed by composing `proj` with the inner context
family.  The transcript type is unchanged: both inner and outer participants run
the same interaction. -/
@[inline] abbrev context
    (boundary : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut) :
    OuterStmtIn → Spec :=
  fun outer => InnerContext (boundary.proj outer)

/-- Identity boundary: the inner and outer statement interfaces coincide. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (context : StmtIn → Spec)
    (StmtOut : (s : StmtIn) → Spec.Transcript (context s) → Type) :
    Statement StmtIn StmtIn context StmtOut where
  proj := fun stmt => stmt
  StmtOut := StmtOut
  lift := fun _ _ stmtOut => stmtOut

/-- Boundary that only changes the input statement; the output is passed through
unchanged.  Use this when you need to project the input but the inner and outer
output statement types are definitionally equal. -/
@[inline] def ofInputOnly
    (proj : OuterStmtIn → InnerStmtIn) :
    Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut where
  proj := proj
  StmtOut := fun outer tr => InnerStmtOut (proj outer) tr
  lift := fun _ _ stmtOut => stmtOut

/-- Boundary that only changes the output statement; the input is passed through
unchanged.  Use this when the outer and inner input types coincide but you want
to map the output statement to a richer outer type. -/
@[inline] def ofOutputOnly
    (StmtIn : Type)
    (Context : StmtIn → Spec)
    (InnerStmtOut OuterStmtOut :
      (s : StmtIn) → Spec.Transcript (Context s) → Type)
    (lift :
      (s : StmtIn) →
      (tr : Spec.Transcript (Context s)) →
      InnerStmtOut s tr →
      OuterStmtOut s tr) :
    Statement StmtIn StmtIn Context InnerStmtOut where
  proj := fun stmt => stmt
  StmtOut := OuterStmtOut
  lift := lift

end Statement

/-- The witness-level half of a boundary, paired with a fixed `Statement`
boundary.

`proj` maps the outer prover witness to the inner witness expected by the inner
protocol.  `lift` reconstructs the outer output witness after the inner prover
finishes, given the outer input statement and witness, the transcript, the inner
output statement, and the inner output witness. -/
structure Witness
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (OuterWitIn InnerWitIn : Type)
    (stmt : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    (InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type) where
  WitOut :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerContext (stmt.proj outer)) → Type
  proj : (outer : OuterStmtIn) → OuterWitIn → InnerWitIn
  lift :
    (outer : OuterStmtIn) →
      OuterWitIn →
      (tr : Spec.Transcript (InnerContext (stmt.proj outer))) →
      InnerStmtOut (stmt.proj outer) tr →
      InnerWitOut (stmt.proj outer) tr →
      WitOut outer tr

namespace Witness

variable
    {StmtIn : Type}
    {Context : StmtIn → Spec}
    {StmtOut : (s : StmtIn) → Spec.Transcript (Context s) → Type}
    {WitIn : Type}
    {WitOut : (s : StmtIn) → Spec.Transcript (Context s) → Type}

/-- Identity witness boundary over the identity statement boundary. -/
@[inline, reducible] def id :
    Witness WitIn WitIn
      (Statement.id StmtIn Context StmtOut)
      WitOut where
  WitOut := fun stmt tr => WitOut stmt tr
  proj := fun _ wit => wit
  lift := fun _ _ _ _ witOut => witOut

/-- Witness boundary that only changes the input witness; the output witness is
passed through unchanged. -/
@[inline] def ofInputOnly
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {OuterWitIn InnerWitIn : Type}
    {stmt : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (proj :
      (outer : OuterStmtIn) →
      OuterWitIn →
      InnerWitIn) :
    Witness OuterWitIn InnerWitIn stmt InnerWitOut where
  WitOut := fun outer tr => InnerWitOut (stmt.proj outer) tr
  proj := proj
  lift := fun _ _ _ _ witOut => witOut

end Witness

/-- A full plain boundary bundling statement and witness transport.

Use `Context` when constructing a prover or full reduction pullback.
For verifier-only pullbacks, a `Statement` boundary suffices. -/
structure Context
    (OuterStmtIn InnerStmtIn : Type)
    (OuterWitIn InnerWitIn : Type)
    (InnerContext : InnerStmtIn → Spec)
    (InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type)
    (InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type) where
  stmt : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut
  wit : Witness OuterWitIn InnerWitIn stmt InnerWitOut

namespace Context

variable
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}

/-- The outer output statement type, delegated to the statement boundary. -/
@[inline] abbrev StmtOut
    (boundary : Context OuterStmtIn InnerStmtIn OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerContext (boundary.stmt.proj outer)) → Type :=
  boundary.stmt.StmtOut

/-- The outer output witness type, delegated to the witness boundary. -/
@[inline] abbrev WitOut
    (boundary : Context OuterStmtIn InnerStmtIn OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerContext (boundary.stmt.proj outer)) → Type :=
  boundary.wit.WitOut

/-- Project an outer `(stmt, wit)` pair to an inner `(stmt, wit)` pair. -/
@[inline] def proj
    (boundary : Context OuterStmtIn InnerStmtIn OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ⟨outerStmt, outerWit⟩ =>
    ⟨boundary.stmt.proj outerStmt, boundary.wit.proj outerStmt outerWit⟩

/-- Lift inner outputs back to outer outputs, returning both statement and witness
components. -/
@[inline] def lift
    (boundary : Context OuterStmtIn InnerStmtIn OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut)
    (outerStmt : OuterStmtIn) (outerWit : OuterWitIn)
    (tr : Spec.Transcript (InnerContext (boundary.stmt.proj outerStmt)))
    (stmtOut : InnerStmtOut (boundary.stmt.proj outerStmt) tr)
    (witOut : InnerWitOut (boundary.stmt.proj outerStmt) tr) :
    boundary.StmtOut outerStmt tr × boundary.WitOut outerStmt tr :=
  ⟨boundary.stmt.lift outerStmt tr stmtOut,
    boundary.wit.lift outerStmt outerWit tr stmtOut witOut⟩

/-- Identity context boundary. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (WitIn : Type)
    (context : StmtIn → Spec)
    (StmtOut WitOut :
      (s : StmtIn) → Spec.Transcript (context s) → Type) :
    Context StmtIn StmtIn WitIn WitIn context StmtOut WitOut where
  stmt := Statement.id StmtIn context StmtOut
  wit := Witness.id

/-- Context boundary that only changes the input statement and witness. -/
@[inline] def ofInputOnly
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (stmtProj : OuterStmtIn → InnerStmtIn)
    (witProj :
      (outer : OuterStmtIn) →
      OuterWitIn →
      InnerWitIn) :
    Context OuterStmtIn InnerStmtIn
      OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut where
  stmt := Statement.ofInputOnly stmtProj
  wit := Witness.ofInputOnly witProj

end Context

namespace Verifier

/-- Reinterpret an inner verifier through an outer statement boundary.

Projects the outer input statement, runs the inner verifier, and lifts the
inner output statement back to the outer interface.  The transcript and
round structure are unchanged. -/
def pullback {m : Type _ → Type _} [Functor m]
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary : Statement OuterStmtIn InnerStmtIn InnerContext InnerStmtOut)
    (verifier : Verifier m InnerStmtIn InnerContext InnerRoles InnerStmtOut) :
    Verifier m OuterStmtIn
      (fun outer => InnerContext (boundary.proj outer))
      (fun outer => InnerRoles (boundary.proj outer))
      boundary.StmtOut :=
  fun outer =>
    Spec.Counterpart.mapOutput
      (fun tr stmtOut => boundary.lift outer tr stmtOut)
      (verifier (boundary.proj outer))

end Verifier

namespace Prover

/-- Reinterpret an inner prover through a full context boundary.

Projects the outer `(stmt, wit)` pair, runs the inner prover strategy, and
lifts the inner `(stmtOut, witOut)` pair back to the outer interface. -/
def pullback {m : Type _ → Type _} [Monad m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary : Context OuterStmtIn InnerStmtIn
      OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut)
    (prover : Prover m InnerStmtIn InnerWitIn
      InnerContext InnerRoles InnerStmtOut InnerWitOut) :
    Prover m OuterStmtIn OuterWitIn
      (fun outer => InnerContext (boundary.stmt.proj outer))
      (fun outer => InnerRoles (boundary.stmt.proj outer))
      boundary.StmtOut
      boundary.WitOut :=
  fun outerStmt outerWit => do
    let strat ← prover
      (boundary.stmt.proj outerStmt)
      (boundary.wit.proj outerStmt outerWit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        boundary.lift outerStmt outerWit tr out.stmt out.wit)
      strat

end Prover

namespace Reduction

/-- Reinterpret an inner reduction through a full context boundary. -/
def pullback {m : Type _ → Type _} [Monad m] [Functor m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Spec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerContext s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type}
    (boundary : Context OuterStmtIn InnerStmtIn
      OuterWitIn InnerWitIn
      InnerContext InnerStmtOut InnerWitOut)
    (reduction : Reduction m InnerStmtIn InnerWitIn
      InnerContext InnerRoles InnerStmtOut InnerWitOut) :
    Reduction m OuterStmtIn OuterWitIn
      (fun outer => InnerContext (boundary.stmt.proj outer))
      (fun outer => InnerRoles (boundary.stmt.proj outer))
      boundary.StmtOut
      boundary.WitOut where
  prover := Prover.pullback boundary reduction.prover
  verifier := Verifier.pullback boundary.stmt reduction.verifier

end Reduction

end Boundary
end Interaction
