/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.TwoParty.Refine
import ArkLib.OracleReduction.OracleInterface

/-!
# Oracle Decoration, Oracle Verifiers, and Oracle Reductions

This module bridges the generic `Interaction.Spec` layer with VCVio's oracle
computation model. It introduces:

- `OracleDecoration` — per-node attachment of `OracleInterface` instances at
  sender nodes, specifying how prover messages can be queried as oracles.
- `OracleDecoration.QueryHandle` — an index type for oracle queries, parameterized
  by a transcript (the transcript determines the path through the interaction tree,
  and hence which oracle interfaces are available).
- `OracleDecoration.toOracleSpec` — the VCVio `OracleSpec` for querying sender
  messages along a given transcript path.

- `OracleDecoration.toMonadDecoration` — bridge from oracle decoration to per-node
  `MonadDecoration`: sender nodes get `Id`, receiver nodes get `OracleComp`.
- `OracleDecoration.liftOutput` — converts oracle-spec-indexed output to
  transcript-indexed output by threading the accumulated spec.
- `OracleCounterpart` — round-by-round challenger with growing oracle access,
  unified as `Counterpart.withMonads` via `toMonadDecoration`.
- `InteractiveOracleVerifier` — a transcript-indexed challenger whose terminal
  output is a verification function.
- `OracleVerifier` — batch structure with transcript-dependent `iov` and
  statement/transcript-dependent oracle simulation.
- `OracleProver` / `OracleReduction` — prover and reduction with oracle statements,
  using the full dependency chain.

## Path-dependent oracle access

In a W-type interaction spec, move types at each node depend on prior moves.
Consequently, the oracle interfaces available to the verifier depend on the
actual transcript. This is reflected in the type of `toOracleSpec`: it takes a
`Transcript` and produces an `OracleSpec` over `QueryHandle` for that specific
path.

## Unification with `Counterpart.withMonads`

`OracleCounterpart` is defined as `Counterpart.withMonads` with a
`MonadDecoration` computed from the oracle decoration via `toMonadDecoration`.
Sender nodes use `Id` (pure observation, `Id α = α` definitionally) and receiver
nodes use `OracleComp` with the current accumulated oracle access. This means all
generic `Counterpart.withMonads` composition combinators automatically apply to
oracle counterparts.

## Universe constraints

The oracle decoration layer (`OracleDecoration`, `QueryHandle`,
`toOracleSpec`, `answerQuery`) is universe-polymorphic in its statement and
oracle families. The downstream verifier and reduction interfaces are also
polymorphic in their statement, witness, and oracle-family universes where the
underlying `Spec`, `Counterpart.withMonads`, and `OracleComp` interfaces permit
it.
-/

universe u v w

open OracleComp OracleSpec

namespace Interaction

/-! ## Oracle decoration

`OracleDecoration` is a `Role.Refine` specialized to `OracleInterface`:
it carries an `OracleInterface X` at each sender node and recurses directly
at receiver nodes (no junk data). -/

/-- An `OracleDecoration` assigns an `OracleInterface` instance (as data, not a
typeclass) to each sender node. Defined as `Role.Refine OracleInterface`. -/
abbrev OracleDecoration (spec : Spec) (roles : RoleDecoration spec) :=
  Interaction.Role.Refine OracleInterface spec roles

/-- Oracle-statement data for an indexed oracle-statement family. -/
abbrev OracleStatement {ιₛ : Type v} (OStmt : ιₛ → Type w) :=
  ∀ i, OStmt i

/-- A plain statement bundled with its oracle-statement data. Used for both oracle
inputs and oracle outputs. -/
abbrev StatementWithOracles
    (Statement : Type u) {ιₛ : Type v} (OStmt : ιₛ → Type w) :=
  Statement × OracleStatement OStmt

namespace StatementWithOracles

/-- Plain-statement component of a bundled statement/input. -/
abbrev stmt {Statement : Type u} {ιₛ : Type v} {OStmt : ιₛ → Type w}
    (s : StatementWithOracles Statement OStmt) : Statement :=
  s.1

/-- Oracle-statement component of a bundled statement/input. -/
abbrev oracleStmt {Statement : Type u} {ιₛ : Type v} {OStmt : ιₛ → Type w}
    (s : StatementWithOracles Statement OStmt) : OracleStatement OStmt :=
  s.2

end StatementWithOracles

/-! ## Query handles and oracle spec -/

/-- Index type for oracle queries given a specific transcript path. At each
sender node, the verifier can either:
- query the current node's oracle interface (`.inl q`), or
- recurse into the subtree determined by the transcript move (`.inr h`).

At receiver nodes, there is no oracle to query, so we recurse immediately.

The transcript parameter ensures that the index type is well-typed: it
determines which subtree (and hence which oracle interfaces) are reachable. -/
def OracleDecoration.QueryHandle :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    Spec.Transcript spec → Type
  | .done, _, _, _ => Empty
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
      oi.Query ⊕ QueryHandle (rest x) (rRest x) (odRest x) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (odFn x) trRest

/-- The oracle specification for querying sender-node messages along a given
transcript path. Maps each `QueryHandle` to its response type. -/
def OracleDecoration.toOracleSpec :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    (tr : Spec.Transcript spec) → OracleSpec (QueryHandle spec roles od tr)
  | .done, _, _, _ => Empty.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec (rest x) (rRest x) (odRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (odFn x) trRest

/-- Answer oracle queries using the message values from a transcript. At each
sender node, the transcript provides the actual move `x : X`, which is used as
the message argument to `OracleInterface`'s implementation. -/
def OracleDecoration.answerQuery :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    (tr : Spec.Transcript spec) →
    QueryImpl (toOracleSpec spec roles od tr) Id
  | .done, _, _, _ => fun q => q.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery (rest x) (rRest x) (odRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (odFn x) trRest

/-- Answer queries to the combined oracle context consisting of the input oracle
statements and the sender-message oracles available along a transcript. -/
def OracleDecoration.oracleContextImpl
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, u} (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → (od : OracleDecoration.{0, 0} spec roles) →
    OracleStatement OStmtIn → (tr : Spec.Transcript spec) →
    QueryImpl ([OStmtIn]ₒ + toOracleSpec spec roles od tr) Id
  | spec, roles, od, oStmtIn, tr =>
      QueryImpl.add (OracleInterface.simOracle0 OStmtIn oStmtIn)
        (answerQuery spec roles od tr)

namespace OracleDecoration.QueryHandle

/-- Embed a first-phase query handle into the combined query-handle type for
`Spec.append`. -/
def appendLeft :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    QueryHandle spec₁ roles₁ od₁ tr₁ →
    QueryHandle (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q =>
      match q with
      | .inl q0 => .inl q0
      | .inr qRest =>
          .inr <| appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q =>
      appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

/-- Embed a second-phase query handle into the combined query-handle type for
`Spec.append`. -/
def appendRight :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ →
    QueryHandle (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
  | .done, _, _, _, _, _, ⟨⟩, _, q => q
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q =>
      .inr <| appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q =>
      appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem appendLeft_range :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle spec₁ roles₁ od₁ tr₁) →
    OracleDecoration.toOracleSpec (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      (appendLeft spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
    OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      cases q with
      | inl q0 => rfl
      | inr qRest =>
          simpa using appendLeft_range (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendLeft_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem appendRight_range :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂) →
    OracleDecoration.toOracleSpec (spec₁.append spec₂) (Spec.Decoration.append roles₁ roles₂)
      (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
      (appendRight spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
    OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q
  | .done, _, _, _, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendRight_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using appendRight_range (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem answerQuery_appendLeft :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle spec₁ roles₁ od₁ tr₁) →
    cast (appendLeft_range spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
      (OracleDecoration.answerQuery (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
        (appendLeft spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
    OracleDecoration.answerQuery spec₁ roles₁ od₁ tr₁ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => q.elim
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      cases q with
      | inl q0 =>
          rfl
      | inr qRest =>
          simpa using answerQuery_appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
            (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
            tr₁Rest tr₂ qRest
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendLeft (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

theorem answerQuery_appendRight :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (q : QueryHandle (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂) →
    cast (appendRight_range spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
      (OracleDecoration.answerQuery (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
        (appendRight spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) =
    OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q
  | .done, _, _, _, _, _, ⟨⟩, _, q => by
      rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨_, odRest⟩, od₂,
      ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, ⟨x, tr₁Rest⟩, tr₂, q => by
      simpa using answerQuery_appendRight (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩)
        tr₁Rest tr₂ q

end OracleDecoration.QueryHandle

section QueryRouting

variable {spec₁ : Spec} {spec₂ : Spec.Transcript spec₁ → Spec}
variable {roles₁ : RoleDecoration spec₁}
variable {roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)}
variable {od₁ : OracleDecoration spec₁ roles₁}
variable {od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)}
variable (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))

/-- Lift first-phase transcript-message queries into the appended transcript's
query context. -/
def liftAppendLeftQueries :
    QueryImpl (OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁)
      (OracleComp
        (OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun q =>
    cast (congrArg
      (OracleComp <| OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
      (OracleDecoration.QueryHandle.appendLeft_range
        spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) <|
      liftM <| query (spec := OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (OracleDecoration.QueryHandle.appendLeft spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)

/-- Lift second-phase transcript-message queries into the appended transcript's
query context. -/
def liftAppendRightQueries :
    QueryImpl (OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)
      (OracleComp
        (OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))) :=
  fun q =>
    cast (congrArg
      (OracleComp <| OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
      (OracleDecoration.QueryHandle.appendRight_range
        spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) <|
      liftM <| query (spec := OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (OracleDecoration.QueryHandle.appendRight spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)

variable {ιₛ : Type} {OStmt : ιₛ → Type}
variable [∀ i, OracleInterface (OStmt i)]

/-- Lift the first-phase oracle context `[OStmt]ₒ + msgSpec₁` into the appended
oracle context `[OStmt]ₒ + msgSpecAppend`. -/
def liftAppendLeftContext :
    QueryImpl ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁)
      (OracleComp
        ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)))
  | .inl q =>
      liftM <| query (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) (.inl q)
  | .inr q =>
      cast (congrArg
        (OracleComp <| [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (OracleDecoration.QueryHandle.appendLeft_range
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) <|
        liftM <| query (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
          (.inr <| OracleDecoration.QueryHandle.appendLeft
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)

/-- Lift the second-phase oracle context `[OStmt]ₒ + msgSpec₂` into the
appended oracle context `[OStmt]ₒ + msgSpecAppend`. -/
def liftAppendRightContext :
    QueryImpl ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)
      (OracleComp
        ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)))
  | .inl q =>
      liftM <| query (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) (.inl q)
  | .inr q =>
      cast (congrArg
        (OracleComp <| [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (OracleDecoration.QueryHandle.appendRight_range
          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) <|
        liftM <| query (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
          (.inr <| OracleDecoration.QueryHandle.appendRight
            spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)

theorem simulateQ_ext
    {ι : Type u} {spec : OracleSpec.{u, v} ι} {r : Type v → Type}
    [Monad r] [LawfulMonad r]
    {impl₁ impl₂ : QueryImpl spec r}
    (himpl : ∀ q, impl₁ q = impl₂ q) :
    ∀ {α : Type v} (oa : OracleComp spec α), simulateQ impl₁ oa = simulateQ impl₂ oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [himpl t, ih]

theorem simulateQ_compose_lambda
    {ι : Type} {spec : OracleSpec ι}
    {ι' : Type} {spec' : OracleSpec ι'}
    {r : Type → Type}
    [Monad r] [LawfulMonad r]
    (so' : QueryImpl spec' r)
    (so : QueryImpl spec (OracleComp spec')) :
    ∀ {α : Type} (oa : OracleComp spec α),
      simulateQ (fun q => simulateQ so' (so q)) oa = simulateQ so' (simulateQ so oa) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [ih]

theorem simulateQ_cast_query
    {ι : Type u} {spec : OracleSpec.{u, v} ι} {r : Type v → Type}
    [Monad r] [LawfulMonad r]
    {α β : Type v} (h : α = β) (impl : QueryImpl spec r) (q : OracleQuery spec α) :
    simulateQ impl (cast (congrArg (OracleComp spec) h) (liftM q)) =
      cast (congrArg r h) (q.cont <$> impl q.input) := by
  cases h
  simp [simulateQ_query]

theorem simulateQ_liftAppendLeftContext_eq
    (oStmt : OracleStatement OStmt) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) oStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (liftAppendLeftContext (spec₁ := spec₁) (spec₂ := spec₂)
          (roles₁ := roles₁) (roles₂ := roles₂)
          (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ q) =
      (OracleDecoration.oracleContextImpl spec₁ roles₁ od₁ oStmt tr₁) q := by
  intro q
  cases q with
  | inl q =>
      simp [OracleDecoration.oracleContextImpl, QueryImpl.add, liftAppendLeftContext,
        simulateQ_query]
  | inr q =>
      calc
        simulateQ
            (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (liftAppendLeftContext (spec₁ := spec₁) (spec₂ := spec₂)
              (roles₁ := roles₁) (roles₂ := roles₂)
              (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ (.inr q))
            =
          cast
            (OracleDecoration.QueryHandle.appendLeft_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) := by
                  simpa [OracleDecoration.oracleContextImpl, QueryImpl.add,
                    liftAppendLeftContext] using
                    (simulateQ_cast_query
                      (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                      (α := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                        (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
                      (β := ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁).Range
                        (Sum.inr q))
                      (h := (OracleDecoration.QueryHandle.appendLeft_range
                        spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q :
                          ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                              (Spec.Decoration.append roles₁ roles₂)
                              (Role.Refine.append od₁ od₂)
                              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                            (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
                          ([OStmt]ₒ + OracleDecoration.toOracleSpec spec₁ roles₁ od₁ tr₁).Range
                            (Sum.inr q)))
                      (impl := OracleDecoration.oracleContextImpl (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂)
                        (Role.Refine.append od₁ od₂) oStmt
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                      (q := query
                        (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                          (Spec.Decoration.append roles₁ roles₂)
                          (Role.Refine.append od₁ od₂)
                          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                        (Sum.inr <| OracleDecoration.QueryHandle.appendLeft
                          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))
        _ = OracleDecoration.answerQuery spec₁ roles₁ od₁ tr₁ q := by
              simpa using OracleDecoration.QueryHandle.answerQuery_appendLeft
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q

theorem simulateQ_liftAppendRightContext_eq
    (oStmt : OracleStatement OStmt) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
          (Spec.Decoration.append roles₁ roles₂)
          (Role.Refine.append od₁ od₂) oStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
          (roles₁ := roles₁) (roles₂ := roles₂)
          (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ q) =
      (QueryImpl.add (OracleInterface.simOracle0 OStmt oStmt)
        (OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂)) q := by
  intro q
  cases q with
  | inl q =>
      simp [OracleDecoration.oracleContextImpl, QueryImpl.add, liftAppendRightContext,
        simulateQ_query]
  | inr q =>
      calc
        simulateQ
            (OracleDecoration.oracleContextImpl (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂) oStmt
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
            (liftAppendRightContext (spec₁ := spec₁) (spec₂ := spec₂)
              (roles₁ := roles₁) (roles₂ := roles₂)
              (od₁ := od₁) (od₂ := od₂) (OStmt := OStmt) tr₁ tr₂ (.inr q))
            =
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)
            (OracleDecoration.answerQuery (spec₁.append spec₂)
              (Spec.Decoration.append roles₁ roles₂)
              (Role.Refine.append od₁ od₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)) := by
                  simpa [OracleDecoration.oracleContextImpl, QueryImpl.add,
                    liftAppendRightContext] using
                    (simulateQ_cast_query
                      (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                      (α := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂)
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                        (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q))
                      (β := ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
                        (roles₂ tr₁) (od₂ tr₁) tr₂).Range (Sum.inr q))
                      (h := (OracleDecoration.QueryHandle.appendRight_range
                        spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q :
                          ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                              (Spec.Decoration.append roles₁ roles₂)
                              (Role.Refine.append od₁ od₂)
                              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).Range
                            (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                              spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q) =
                          ([OStmt]ₒ + OracleDecoration.toOracleSpec (spec₂ tr₁)
                              (roles₂ tr₁) (od₂ tr₁) tr₂).Range
                            (Sum.inr q)))
                      (impl := OracleDecoration.oracleContextImpl (spec₁.append spec₂)
                        (Spec.Decoration.append roles₁ roles₂)
                        (Role.Refine.append od₁ od₂) oStmt
                        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                      (q := query
                        (spec := [OStmt]ₒ + OracleDecoration.toOracleSpec (spec₁.append spec₂)
                          (Spec.Decoration.append roles₁ roles₂)
                          (Role.Refine.append od₁ od₂)
                          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
                        (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                          spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q)))
        _ = OracleDecoration.answerQuery (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁) tr₂ q := by
              simpa using OracleDecoration.QueryHandle.answerQuery_appendRight
                spec₁ spec₂ roles₁ roles₂ od₁ od₂ tr₁ tr₂ q

end QueryRouting

namespace OracleDecoration

/-! ## Bridge definitions

These definitions bridge `OracleDecoration` to `MonadDecoration` and
transcript-indexed output, enabling the unification of `OracleCounterpart`
with `Counterpart.withMonads`. The oracle computation monad `OracleComp`
constrains these definitions to `Spec.{0}`. -/

/-- Compute the per-node `MonadDecoration` from an oracle decoration and
accumulated oracle spec. Sender nodes get `Id` (pure observation, `Id α = α`
definitionally), receiver nodes get `OracleComp (oSpec + [OStmtIn]ₒ + accSpec)`
(oracle computation with current access). The accumulated spec grows at sender
nodes and stays fixed at receiver nodes. -/
def toMonadDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, u} (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → OracleDecoration.{0, 0} spec roles →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Spec.MonadDecoration spec
  | .done, _, _, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x)
         (accSpec + @OracleInterface.spec _ oi)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      ⟨⟨OracleComp (oSpec + [OStmtIn]ₒ + accSpec), inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec⟩

/-- Convert oracle-spec-indexed output to transcript-indexed output by threading
the accumulated oracle spec through the tree. At each `.done` node, applies
`Output` to the final accumulated spec. At sender nodes, the accumulated spec
grows by the sender's oracle interface spec. At receiver nodes, the accumulated
spec is unchanged. -/
def liftOutput
    (Output : {ιₐ : Type} → OracleSpec.{0, u} ιₐ → Type) :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) → OracleDecoration.{u, 0} spec roles →
    {ιₐ : Type} → OracleSpec.{0, u} ιₐ → Spec.Transcript spec → Type
  | .done, _, _, _, accSpec, _ => Output accSpec
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      liftOutput Output (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      liftOutput Output (rest x) (rRest x) (odFn x) accSpec trRest

/-! ## Oracle counterpart (unified with `Counterpart.withMonads`)

`OracleCounterpart` is the round-by-round challenger with growing oracle access,
defined as `Counterpart.withMonads` with the `MonadDecoration` computed from
the oracle decoration. At sender nodes the monad is `Id` (pure observation);
at receiver nodes the monad is `OracleComp` with accumulated oracle access. -/

/-- Round-by-round challenger with growing oracle access, defined as
`Counterpart.withMonads` with the monad decoration computed from the oracle
decoration. The oracle-spec-indexed `Output` is converted to a
transcript-indexed family by `liftOutput`. -/
abbrev OracleCounterpart {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    (Output : {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Type)
    (spec : Spec.{0}) (roles : RoleDecoration spec) (od : OracleDecoration.{0, 0} spec roles)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :=
  Spec.Counterpart.withMonads spec roles
    (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
    (liftOutput Output spec roles od accSpec)

/-- `InteractiveOracleVerifier` is the round-by-round oracle verifier whose
terminal output is a verification function. The return type may depend on both
the input statement and the realized transcript. -/
abbrev InteractiveOracleVerifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec)
    (od : OracleDecoration.{0, 0} pSpec roles)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : StmtIn → Spec.Transcript pSpec → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)] :=
  Spec.Counterpart.withMonads pSpec roles
    (toMonadDecoration oSpec OStmtIn pSpec roles od (ιₐ := PEmpty) []ₒ)
    (fun tr =>
      (s : StmtIn) →
        OracleComp (oSpec + [OStmtIn]ₒ + toOracleSpec pSpec roles od tr)
          (StmtOut s tr))

/-! ## Conversions -/

/-- Map the output of an `OracleCounterpart`, applying `f` at each `.done` leaf.
At sender nodes (monad = `Id`), the map is applied purely. At receiver nodes
(monad = `OracleComp`), the map is lifted through the oracle computation. -/
def OracleCounterpart.mapOutput {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {Output₁ Output₂ : {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Type}
    (f : ∀ {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ), Output₁ accSpec → Output₂ accSpec) :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    (od : OracleDecoration.{0, 0} spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    OracleCounterpart oSpec OStmtIn Output₁ spec roles od accSpec →
    OracleCounterpart oSpec OStmtIn Output₂ spec roles od accSpec
  | .done, _, _, _, accSpec => f accSpec
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, odRest⟩, _, _ =>
      fun oc x => mapOutput f (rest x) (rRest x) (odRest x) _ (oc x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      fun oc => do
        let ⟨x, ocRest⟩ ← oc
        return ⟨x, mapOutput f (rest x) (rRest x) (odFn x) accSpec ocRest⟩

/-! ## Full oracle verifier (batch structure)

The batch `OracleVerifier` bundles:
- `iov` — the round-by-round interactive oracle verifier
- `simulate` — query-level simulation of output oracle queries

The `simulate` field is **transcript-dependent** in the W-type model: the oracle
spec available depends on the path through the interaction tree.

Concrete reification of the output oracle data is intentionally *not* part of
this core structure; it belongs to an optional layer built on top of the oracle
access semantics. -/

/-- Full oracle verifier with oracle-only output semantics. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec)
    (oracleDec : OracleDecoration.{0, 0} pSpec roles)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : StmtIn → Spec.Transcript pSpec → Type)
    {ιₛₒ : Type} (OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    [∀ s tr i, OracleInterface (OStmtOut s tr i)] where
  iov : InteractiveOracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut
  simulate : (s : StmtIn) → (tr : Spec.Transcript pSpec) →
    QueryImpl [OStmtOut s tr]ₒ
      (OracleComp ([OStmtIn]ₒ + toOracleSpec pSpec roles oracleDec tr))

namespace OracleVerifier

/-- Full oracle-only verifier output: the plain output statement together with
the query implementation exposing the output-oracle access. -/
abbrev OutputAccess
    {pSpec : Spec.{0}} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration.{0, 0} pSpec roles}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : StmtIn → Spec.Transcript pSpec → Type}
    {ιₛₒ : Type} (OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)] [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (s : StmtIn) (tr : Spec.Transcript pSpec) :=
  StmtOut s tr × QueryImpl [OStmtOut s tr]ₒ
    (OracleComp ([OStmtIn]ₒ + toOracleSpec pSpec roles oracleDec tr))

/-- Package a verifier's plain output statement together with the verifier's
output-oracle query access. -/
def outputAccess {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {pSpec : Spec.{0}} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration.{0, 0} pSpec roles}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : StmtIn → Spec.Transcript pSpec → Type}
    {ιₛₒ : Type} {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type}
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : OracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut OStmtOut)
    (s : StmtIn) (tr : Spec.Transcript pSpec) (stmtOut : StmtOut s tr) :
    OutputAccess (pSpec := pSpec) (roles := roles) (oracleDec := oracleDec)
      (StmtIn := StmtIn) (OStmtIn := OStmtIn) (StmtOut := StmtOut) OStmtOut s tr :=
  ⟨stmtOut, verifier.simulate s tr⟩

end OracleVerifier

/-! ## Oracle prover and oracle reduction -/

/-- Oracle prover: given a statement `s : StatementIn` bundled with input oracle
data, performs monadic setup in `OracleComp oSpec` and produces a
role-dependent strategy. The honest prover output is the next plain statement
bundled with its output oracle statements, together with the next witness.

This is a specialization of `Prover` with `m = OracleComp oSpec` and the
statement type bundled with named oracle statements. -/
abbrev OracleProver {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (StatementIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (WitnessIn : Type)
    (Context : StatementIn → Spec.{0})
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type)
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    (OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type)
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) :=
  Prover (OracleComp oSpec)
    (StatementWithOracles StatementIn OStmtIn) WitnessIn
    (fun s => Context s.stmt) (fun s => Roles s.stmt)
    (fun s tr => StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
    (fun s tr => WitnessOut s.stmt tr)

/-- Oracle reduction: pairs an oracle prover with a verifier that uses per-node
monads (`Id` at sender, `OracleComp` at receiver) via `Counterpart.withMonads`.
This is the oracle analog of `Reduction`, where the verifier's per-node monad
structure (growing oracle access) replaces the fixed monad of `Counterpart`.

The honest prover outputs the next plain statement bundled with its output
oracle statements. The verifier produces the plain next statement, while the
`simulate` field exposes query-level access to the output oracle family.
Concrete reification of those output oracles is optional and lives in a
separate layer. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StatementIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    (WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s))
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type)
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    (OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type)
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) where
  prover : OracleProver oSpec StatementIn OStmtIn WitnessIn Context Roles
    StatementOut OStmtOut WitnessOut
  verifier : (s : StatementIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    Spec.Counterpart.withMonads (Context s) (Roles s)
      (toMonadDecoration oSpec OStmtIn (Context s) (Roles s) (OD s) accSpec)
      (fun tr => StatementOut s tr)
  simulate : (s : StatementIn) → (tr : Spec.Transcript (Context s)) →
    QueryImpl [OStmtOut s tr]ₒ
      (OracleComp ([OStmtIn]ₒ + toOracleSpec (Context s) (Roles s) (OD s) tr))

namespace OracleReduction

/-- Full oracle-only verifier output for an oracle reduction at transcript `tr`:
the plain output statement together with the query implementation exposing the
output-oracle access. -/
abbrev VerifierOutput
    {StatementIn : Type}
    {Context : StatementIn → Spec.{0}}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration.{0, 0} (Context s) (Roles s)}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    (OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type)
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)] [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (s : StatementIn) (tr : Spec.Transcript (Context s)) :=
  StatementOut s tr × QueryImpl [OStmtOut s tr]ₒ
    (OracleComp ([OStmtIn]ₒ + toOracleSpec (Context s) (Roles s) (OD s) tr))

/-- Package the verifier's plain output statement together with the verifier's
output-oracle query access. -/
def verifierOutput
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec.{0}}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration.{0, 0} (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementIn) (tr : Spec.Transcript (Context s)) (stmtOut : StatementOut s tr) :
    VerifierOutput (Context := Context) (StatementOut := StatementOut)
      (StatementIn := StatementIn) (OStmtIn := OStmtIn)
      (Roles := Roles) (OD := OD) OStmtOut s tr :=
  ⟨stmtOut, reduction.simulate s tr⟩

/-- The verifier-side monad decoration induced by an oracle reduction, starting
from an accumulated sender-message oracle spec `accSpec`. -/
abbrev verifierMD
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec.{0}}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration.{0, 0} (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (_reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementIn) {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    Spec.MonadDecoration (Context s) :=
  toMonadDecoration oSpec OStmtIn (Context s) (Roles s) (OD s) accSpec

end OracleReduction

end OracleDecoration

end Interaction
