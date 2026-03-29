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
- `InteractiveOracleVerifier` — an `OracleCounterpart` whose output is a
  verification function.
- `OracleVerifier` — batch structure with `iov`, `simulate`, and `reify`.
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

The oracle decoration layer (`OracleDecoration`, `QueryHandle`, `toOracleSpec`,
`answerQuery`) is universe-polymorphic in the `Spec` universe. Downstream
definitions (`toMonadDecoration`, `OracleCounterpart`, `OracleVerifier`,
`OracleProver`, `OracleReduction`) are at `Spec.{0}` because `OracleComp`
requires `Type → Type`.
-/

universe u

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
def toMonadDecoration {ι : Type} (oSpec : OracleSpec ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)] :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.MonadDecoration spec
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
    (Output : {ιₐ : Type} → OracleSpec ιₐ → Type) :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.Transcript spec → Type
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
abbrev OracleCounterpart {ι : Type} (oSpec : OracleSpec ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)]
    (Output : {ιₐ : Type} → OracleSpec ιₐ → Type)
    (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :=
  Spec.Counterpart.withMonads spec roles
    (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
    (liftOutput Output spec roles od accSpec)

/-- `InteractiveOracleVerifier` is an `OracleCounterpart` whose output at
`.done` is a verification function: given the statement and accumulated
oracle access, produce `OptionT (OracleComp ...) StmtOut`. -/
abbrev InteractiveOracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) [∀ i, OracleInterface (OStmtIn i)]
    (spec : Spec) (roles : RoleDecoration spec)
    (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :=
  OracleCounterpart oSpec OStmtIn
    (fun {ιₐ} (accSpec : OracleSpec ιₐ) =>
      StmtIn → OptionT (OracleComp (oSpec + [OStmtIn]ₒ + accSpec)) StmtOut)
    spec roles od accSpec

/-! ## Conversions -/

/-- Map the output of an `OracleCounterpart`, applying `f` at each `.done` leaf.
At sender nodes (monad = `Id`), the map is applied purely. At receiver nodes
(monad = `OracleComp`), the map is lifted through the oracle computation. -/
def OracleCounterpart.mapOutput {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Output₁ Output₂ : {ιₐ : Type} → OracleSpec ιₐ → Type}
    (f : ∀ {ιₐ : Type} (accSpec : OracleSpec ιₐ), Output₁ accSpec → Output₂ accSpec) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
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
- `reify` — data-level computation of output oracle data

Both `simulate` and `reify` are **transcript-dependent** in the W-type model:
the oracle spec available depends on the path through the interaction tree. -/

/-- Full oracle verifier with `simulate` and `reify` fields for oracle output. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (pSpec : Spec) (roles : RoleDecoration pSpec)
    (oracleDec : OracleDecoration pSpec roles)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)] where
  iov : InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut
    pSpec roles oracleDec (ιₐ := PEmpty) []ₒ
  simulate : (tr : Spec.Transcript pSpec) →
    QueryImpl [OStmtOut]ₒ
      (OracleComp ([OStmtIn]ₒ + toOracleSpec pSpec roles oracleDec tr))
  reify : (∀ i, OStmtIn i) → Spec.Transcript pSpec → Option (∀ i, OStmtOut i)

/-! ## Oracle prover and oracle reduction -/

/-- Oracle prover: given a statement `s : StatementIn` augmented with oracle data
`∀ i, OStmtIn i`, performs monadic setup in `OracleComp oSpec` and produces a
role-dependent strategy. Uses the full dependency chain: `Context`, `Roles`,
and `WitnessOut` all depend on the statement.

This is a specialization of `Prover` with `m = OracleComp oSpec` and the
statement type augmented with oracle data. -/
abbrev OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StatementIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) :=
  Prover (OracleComp oSpec)
    (StatementIn × (∀ i, OStmtIn i)) WitnessIn
    (fun ⟨s, _⟩ => Context s) (fun ⟨s, _⟩ => Roles s) (fun ⟨s, _⟩ tr => WitnessOut s tr)

/-- Oracle reduction: pairs an oracle prover with a verifier that uses per-node
monads (`Id` at sender, `OracleComp` at receiver) via `Counterpart.withMonads`.
This is the oracle analog of `Reduction`, where the verifier's per-node monad
structure (growing oracle access) replaces the fixed monad of `Counterpart`.

Uses the full dependency chain: `Context`, `Roles`, oracle decoration `OD`,
`StatementOut`, and `WitnessOut` all depend on the statement. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (StatementIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    (WitnessIn : Type)
    (Context : StatementIn → Spec)
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s))
    (StatementOut WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type) where
  prover : OracleProver oSpec StatementIn OStmtIn WitnessIn Context Roles WitnessOut
  verifier : (s : StatementIn) →
    Spec.Counterpart.withMonads (Context s) (Roles s)
      (toMonadDecoration oSpec OStmtIn (Context s) (Roles s) (OD s) (ιₐ := PEmpty) []ₒ)
      (fun tr => StatementOut s tr)

/-! ## Composition infrastructure

To compose oracle reductions, we need that `toMonadDecoration` distributes over
`Spec.append` and `Spec.stateChain`. The accumulated oracle spec after the first phase
serves as the starting spec for the second phase. -/

/-- Accumulated oracle spec after traversing `spec` along transcript `tr`,
starting from `accSpec`. At sender nodes, adds the node's oracle interface spec.
At receiver nodes, the accumulated spec is unchanged. -/
def accSpecAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.Transcript spec →
    Σ (ιₐ' : Type), OracleSpec ιₐ'
  | .done, _, _, _, accSpec, _ => ⟨_, accSpec⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odFn x) accSpec trRest

/-- `toMonadDecoration` distributes over `Spec.append`: the monad decoration for
the appended spec equals `Decoration.append` of the individual monad decorations,
where the second phase starts from the accumulated oracle spec of the first. -/
theorem toMonadDecoration_append
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    toMonadDecoration oSpec OStmtIn (spec₁.append spec₂)
      (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂) accSpec =
    Spec.Decoration.append (toMonadDecoration oSpec OStmtIn spec₁ roles₁ od₁ accSpec)
      (fun tr₁ => toMonadDecoration oSpec OStmtIn (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁)
        (accSpecAfter spec₁ roles₁ od₁ accSpec tr₁).2)
  | .done, _, _, _, _, _, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨oi, odRest⟩, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩) _
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩) _

/-! ## Oracle reduction composition -/

/-- Binary sequential composition of oracle reductions. The first reduction runs
over `ctx₁`, producing intermediate outputs. The second-phase prover and verifier
receive these intermediate outputs and run over `ctx₂`.

The second verifier's monad decoration uses `accSpecAfter` to determine the
oracle spec accumulated from the first phase. -/
def OracleReduction.comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut₂ WitOut₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (r₁ : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid WitMid)
    (prover₂ : (s : StatementIn × (∀ i, OStmtIn i)) →
      (tr₁ : Spec.Transcript (ctx₁ s.1)) → WitMid s.1 tr₁ →
        OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec)
          (ctx₂ s.1 tr₁) (roles₂ s.1 tr₁) (WitOut₂ s.1 tr₁)))
    (verifier₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      StmtMid s tr₁ →
        Spec.Counterpart.withMonads (ctx₂ s tr₁) (roles₂ s tr₁)
          (toMonadDecoration oSpec OStmtIn (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁)
            (accSpecAfter (ctx₁ s) (roles₁ s) (OD₁ s) []ₒ tr₁).2)
          (StmtOut₂ s tr₁)) :
    OracleReduction oSpec StatementIn OStmtIn WitnessIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => (roles₁ s).append (roles₂ s))
      (fun s => Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut₂ s))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut₂ s)) where
  prover sWithOracles w := do
    let strat₁ ← r₁.prover sWithOracles w
    Spec.Strategy.compWithRoles strat₁
      (fun tr₁ wMid => prover₂ sWithOracles tr₁ wMid)
  verifier s := by
    rw [toMonadDecoration_append]
    exact Spec.Counterpart.withMonads.append (r₁.verifier s)
      (fun tr₁ sMid => verifier₂ s tr₁ sMid)

/-- `toMonadDecoration` distributes over `Spec.stateChain`: the monad decoration for
the chained spec equals `Decoration.stateChain` of per-stage monad decorations,
where each stage starts from the accumulated oracle spec of preceding stages. -/
private theorem toMonadDecoration_chain
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Stage : Nat → Type} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    (od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s))
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    toMonadDecoration oSpec OStmtIn (Spec.stateChain Stage spec advance n i s)
      (RoleDecoration.stateChain roles n i s) (Role.Refine.stateChain od n i s) accSpec =
    Spec.Decoration.stateChain
      (fun j st => toMonadDecoration oSpec OStmtIn (spec j st) (roles j st) (od j st) accSpec)
      n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
      simp only [Spec.stateChain_succ, Spec.Decoration.stateChain, Role.Refine.stateChain]
      rw [toMonadDecoration_append]
      congr 1; funext tr
      sorry

/-- N-ary state chain composition of oracle reductions. At each stage, the step functions
transform prover state and verifier state. Each stage's verifier sees oracle
access from `oSpec + [OStmtIn]ₒ` plus the accumulated spec. -/
def OracleReduction.stateChainComp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Stage : Nat → Type}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {od : (i : Nat) → (s : Stage i) → OracleDecoration (spec i s) (roles i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type}
    (n : Nat)
    (initStage : StatementIn → Stage 0)
    (proverInit : (s : StatementIn × (∀ i, OStmtIn i)) → WitnessIn →
      OracleComp oSpec (ProverState 0 (initStage s.1)))
    (proverStep : (i : Nat) → (st : Stage i) → ProverState i st →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (spec i st) (roles i st)
        (fun tr => ProverState (i + 1) (advance i st tr))))
    (verifierInit : (s : StatementIn) → VerifierState 0 (initStage s))
    (verifierStep : (i : Nat) → (st : Stage i) → VerifierState i st →
      Spec.Counterpart.withMonads (spec i st) (roles i st)
        (toMonadDecoration oSpec OStmtIn (spec i st) (roles i st) (od i st)
          (ιₐ := PEmpty) []ₒ)
        (fun tr => VerifierState (i + 1) (advance i st tr))) :
    OracleReduction oSpec StatementIn OStmtIn WitnessIn
      (fun s => Spec.stateChain Stage spec advance n 0 (initStage s))
      (fun s => RoleDecoration.stateChain roles n 0 (initStage s))
      (fun s => Role.Refine.stateChain (fun i st => od i st) n 0 (initStage s))
      (fun s => Spec.Transcript.stateChainFamily VerifierState n 0 (initStage s))
      (fun s => Spec.Transcript.stateChainFamily ProverState n 0 (initStage s)) where
  prover sWithOracles w := do
    let a ← proverInit sWithOracles w
    Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage sWithOracles.1) a
  verifier s := by
    rw [toMonadDecoration_chain]
    exact Spec.Counterpart.withMonads.stateChainComp verifierStep n 0 (initStage s) (verifierInit s)

end OracleDecoration

end Interaction
