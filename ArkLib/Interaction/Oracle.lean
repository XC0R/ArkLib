/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
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

- `OracleCounterpart` — the round-by-round challenger with growing oracle access.
  At each sender node the oracle spec accumulates the new interface; at receiver
  nodes the challenger computes a challenge in `OracleComp` with current access.
- `InteractiveOracleVerifier` — a unified structure that is `OracleCounterpart`
  at internal nodes and a verification function at `.done`.
- `OracleVerifier` — the batch structure with `iov`, `simulate`, and `reify`.
- `OracleProver` / `OracleReduction` — prover and reduction with oracle statements.

## Path-dependent oracle access

In a W-type interaction spec, move types at each node depend on prior moves.
Consequently, the oracle interfaces available to the verifier depend on the
actual transcript. This is reflected in the type of `toOracleSpec`: it takes a
`Transcript` and produces an `OracleSpec` over `QueryHandle` for that specific
path. The verifier's verification function is therefore a dependent function whose
oracle monad varies with the transcript.

This is a fundamental difference from the old flat `ProtocolSpec n` approach,
where message types were independent of prior moves and the oracle spec was
static.

## Growing oracle access

The `OracleCounterpart` and `InteractiveOracleVerifier` model the key concept
of **growing oracle access**: the accumulated oracle spec starts at `[]ₒ` and
grows at each sender node by the `OracleInterface.spec` of that node's message
type. This faithfully models the verifier gaining oracle access to each prover
message as it arrives, which is essential for non-public-coin protocols.
-/

set_option autoImplicit false

universe u

open OracleComp OracleSpec

namespace Interaction

/-! ## Oracle decoration

`OracleDecoration` is a `Role.Refine` specialized to `OracleInterface`:
it carries an `OracleInterface X` at each sender node and recurses directly
at receiver nodes (no junk data). -/

/-- An `OracleDecoration` assigns an `OracleInterface` instance (as data, not a
typeclass) to each sender node. Defined as `Role.Refine OracleInterface`. -/
abbrev OracleDecoration (spec : Spec.{0}) (roles : RoleDecoration spec) :=
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
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    Spec.Transcript spec → Type
  | .done, _, _, _ => Empty
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, ⟨x, trRest⟩ =>
      oi.Query ⊕ QueryHandle (rest x) (rRest x) (odRest x) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (odFn x) trRest

/-- The oracle specification for querying sender-node messages along a given
transcript path. Maps each `QueryHandle` to its response type. -/
def OracleDecoration.toOracleSpec :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
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
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
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

/-! ## Oracle counterpart (interactive challenger)

The `OracleCounterpart` processes the protocol round by round, accumulating
oracle access to prover messages:

- At **sender** nodes: the verifier observes the message (Pi), and the
  accumulated oracle spec grows by `oi.spec` (= `oi.toOC.spec`).
- At **receiver** nodes: the verifier computes a challenge (Sigma) in
  `OracleComp` with the current accumulated oracle access.
- At **done**: no more interaction (`PUnit`).

The `accSpec` parameter tracks the oracle spec accumulated so far from
previously seen sender-node messages. -/

/-- Round-by-round challenger with growing oracle access at sender nodes.
The accumulated oracle spec `accSpec` starts at `[]ₒ` and grows by
`oi.toOC.spec` at each sender node. -/
def OracleCounterpart {ι : Type} (oSpec : OracleSpec ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Type
  | .done, _, _, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec =>
      ∀ x : X, OracleCounterpart oSpec OStmtIn
        (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
  | .node X rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      OracleComp (oSpec + [OStmtIn]ₒ + accSpec)
        ((x : X) × OracleCounterpart oSpec OStmtIn
          (rest x) (rRest x) (odFn x) accSpec)

/-! ## Interactive oracle verifier (unified challenger + verify)

Structurally identical to `OracleCounterpart` at internal nodes, but at `.done`
the type is the verification function instead of `PUnit`. -/

/-- Unified interactive oracle verifier: challenger behavior at internal nodes,
verification function at `.done`. -/
def InteractiveOracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) [∀ i, OracleInterface (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Type
  | .done, _, _, _, accSpec =>
      StmtIn → OptionT (OracleComp (oSpec + [OStmtIn]ₒ + accSpec)) StmtOut
  | .node X rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec =>
      ∀ x : X, InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut
        (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
  | .node X rest, ⟨.receiver, rRest⟩, odFn, _, accSpec =>
      OracleComp (oSpec + [OStmtIn]ₒ + accSpec)
        ((x : X) × InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut
          (rest x) (rRest x) (odFn x) accSpec)

/-! ## Conversions between OracleCounterpart and InteractiveOracleVerifier -/

/-- Extract the challenger part from an `InteractiveOracleVerifier`,
discarding the verification function at `.done`. -/
def toOracleCounterpart {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} [∀ i, OracleInterface (OStmtIn i)]
    (spec : Spec.{0}) (roles : RoleDecoration spec)
    (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut spec roles od accSpec →
    OracleCounterpart oSpec OStmtIn spec roles od accSpec :=
  match spec, roles, od with
  | .done, _, _ => fun _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, odRest⟩ =>
      fun iov x => toOracleCounterpart (rest x) (rRest x) (odRest x) _ (iov x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      fun iov => do
        let ⟨x, iovRest⟩ ← iov
        return ⟨x, toOracleCounterpart (rest x) (rRest x) (odFn x) accSpec iovRest⟩

/-! ## Full oracle verifier (batch structure)

The batch `OracleVerifier` bundles:
- `iov` — the round-by-round interactive oracle verifier
- `simulate` — query-level simulation of output oracle queries
- `reify` — data-level computation of output oracle data

Both `simulate` and `reify` are **transcript-dependent** in the W-type model:
the oracle spec available depends on the path through the interaction tree. -/

/-- Full oracle verifier with `simulate` and `reify` fields for oracle output. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec)
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

/-- Oracle prover: a prover whose statement includes oracle data as an
indexed family. Runs in `OracleComp oSpec`. -/
abbrev OracleProver {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec) :=
  Prover (OracleComp oSpec) pSpec roles
    (StmtIn × (∀ i, OStmtIn i)) WitIn
    (StmtOut × (∀ i, OStmtOut i)) WitOut

/-- Oracle reduction: pairs an oracle prover with an oracle verifier. -/
structure OracleReduction {ι : Type} (oSpec : OracleSpec ι)
    (pSpec : Spec.{0}) (roles : RoleDecoration pSpec)
    (oracleDec : OracleDecoration pSpec roles)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)] where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec roles
  verifier : OracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut OStmtOut

end OracleDecoration

end Interaction
