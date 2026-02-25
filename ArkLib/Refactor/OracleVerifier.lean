/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Verifier

/-!
# Oracle Verifier

`OracleVerifier` is the oracle-access counterpart of `Verifier`. It receives
only the verifier challenges and queries prover messages and input oracle
statements through the `OracleComp` monad.

The prover messages' oracle spec (`oracleSpecOfMessages`) is built directly
from the `OracleInterface` bundled in each `P_to_V` round, eliminating instance
synthesis through `List.get ∘ messageTypes`.

Oracle statements use the existing VCVio `[v]ₒ` infrastructure (function-indexed
with typeclass `OracleInterface`) for compatibility with `SubSpec` and `QueryImpl`.

## Main definitions

- `MessageOracleIdx` — nested-sum index type for message oracle spec
- `oracleSpecOfMessages` — oracle spec from bundled OracleInterface
- `oracleImplOfMessages` — pure oracle implementation from message data
- `OracleVerifier` — structure with `verify`, `simulate`, `reify`
- `OracleVerifier.comp` — sequential composition of two oracle verifiers
- `OracleVerifier.compNth` — `n`-fold composition
- `OracleVerifier.toVerifier` — bridge to plain `Verifier`
-/

open OracleComp OracleSpec

namespace ProtocolSpec

/-- Index type for the oracle spec of prover messages, as a nested sum of query types.
Each `P_to_V` round contributes its bundled `OracleInterface`'s query type;
`V_to_P` rounds are skipped. -/
def MessageOracleIdx : ProtocolSpec → Type
  | [] => PEmpty
  | (.P_to_V _ oi) :: tl => oi.Query ⊕ MessageOracleIdx tl
  | (.V_to_P _) :: tl => MessageOracleIdx tl

@[simp]
theorem MessageOracleIdx_nil : MessageOracleIdx [] = PEmpty := rfl

@[simp]
theorem MessageOracleIdx_cons_P_to_V {T : Type} {oi : OracleInterface T}
    {tl : ProtocolSpec} :
    MessageOracleIdx ((.P_to_V T oi) :: tl) = (oi.Query ⊕ MessageOracleIdx tl) := rfl

@[simp]
theorem MessageOracleIdx_cons_V_to_P {T : Type} {tl : ProtocolSpec} :
    MessageOracleIdx ((.V_to_P T) :: tl) = MessageOracleIdx tl := rfl

/-- Oracle spec for prover messages, built from the bundled `OracleInterface` in each
`P_to_V` round. Produces a nested-sum oracle spec compatible with VCVio's `SubSpec`. -/
def oracleSpecOfMessages : (pSpec : ProtocolSpec) → OracleSpec (MessageOracleIdx pSpec)
  | [] => []ₒ
  | (.P_to_V _ oi) :: tl => @OracleInterface.spec _ oi + oracleSpecOfMessages tl
  | (.V_to_P _) :: tl => oracleSpecOfMessages tl

/-- Build a pure oracle implementation for message queries from actual message data.
Each `P_to_V` query is answered using `OracleInterface.answer` on the corresponding
message. -/
def oracleImplOfMessages :
    (pSpec : ProtocolSpec) → Messages pSpec → QueryImpl (oracleSpecOfMessages pSpec) Id
  | [], _ => fun q => PEmpty.elim q
  | (.P_to_V _ oi) :: tl, msgs => fun
    | .inl q => @OracleInterface.answer _ oi msgs.head q
    | .inr q => oracleImplOfMessages tl msgs.tail q
  | (.V_to_P _) :: tl, msgs => oracleImplOfMessages tl msgs

/-- Build a pure oracle implementation for the combined oracle context
`[OStmtIn]ₒ + oracleSpecOfMessages pSpec` from concrete input-oracle data and message data. -/
def oracleImplOfOStmtInMessages {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)] (pSpec : ProtocolSpec)
    (oStmtInData : ∀ i, OStmtIn i) (msgs : Messages pSpec) :
    QueryImpl ([OStmtIn]ₒ + oracleSpecOfMessages pSpec) Id :=
  QueryImpl.add (OracleInterface.toOracleImpl OStmtIn oStmtInData) (oracleImplOfMessages pSpec msgs)

/-- Oracle verifier with oracle access to input statements and prover messages.

Oracle statements use function-indexed types (`OStmtIn : ιₛᵢ → Type`) for
compatibility with VCVio's `[v]ₒ` notation and existing `SubSpec` / `QueryImpl`
infrastructure. Message oracles use the new list-based `oracleSpecOfMessages`. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
    (pSpec : ProtocolSpec)
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)] where
  /-- Verify: given input statement and challenges, decide to accept/reject
  with oracle access to input statements and messages. -/
  verify : StmtIn → Challenges pSpec →
    OptionT (OracleComp (oSpec + [OStmtIn]ₒ + oracleSpecOfMessages pSpec)) StmtOut
  /-- Simulate output oracle queries using input oracles and message oracles.
  Used in query-level security proofs. -/
  simulate : QueryImpl [OStmtOut]ₒ
    (OracleComp ([OStmtIn]ₒ + oracleSpecOfMessages pSpec))
  /-- Compute output oracle data deterministically from input oracle data and messages.
  Used in completeness proofs and execution. -/
  reify : (∀ i, OStmtIn i) → Messages pSpec → Option (∀ i, OStmtOut i)

/-! ## SubSpec instances for message oracle spec over append

When composing two protocols, `oracleSpecOfMessages pSpec₁` (resp. `pSpec₂`)
embeds into `oracleSpecOfMessages (pSpec₁ ++ pSpec₂)` via left/right injection
of indices. The range types match definitionally at each recursive step. -/

/-- Left embedding: `msgOracles(pSpec₁) ⊂ₒ msgOracles(pSpec₁ ++ pSpec₂)`.
For each `P_to_V` round in `pSpec₁`, the left summand of the index passes through
unchanged, while the right summand (tail queries) recurses via the inductive hypothesis.
`V_to_P` rounds contribute no oracle indices and are skipped. -/
def subSpec_oracleSpecOfMessages_left :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    oracleSpecOfMessages pSpec₁ ⊂ₒ oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
  | [], _ => { toMonadLift := { monadLift := fun q => PEmpty.elim q.input } }
  | (.P_to_V _ _) :: tl, pSpec₂ =>
    let ih := subSpec_oracleSpecOfMessages_left tl pSpec₂
    { toMonadLift := { monadLift := fun q => match q with
      | ⟨Sum.inl t, f⟩ => ⟨Sum.inl t, f⟩
      | ⟨Sum.inr t, f⟩ =>
        let q' := ih.monadLift ⟨t, f⟩
        ⟨Sum.inr q'.1, q'.2⟩ } }
  | (.V_to_P _) :: tl, pSpec₂ => subSpec_oracleSpecOfMessages_left tl pSpec₂

/-- Right embedding: `msgOracles(pSpec₂) ⊂ₒ msgOracles(pSpec₁ ++ pSpec₂)`.
Wraps every index with `Sum.inr` for each `P_to_V` round in `pSpec₁`, pushing
pSpec₂'s queries past all of pSpec₁'s oracle indices. -/
def subSpec_oracleSpecOfMessages_right :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    oracleSpecOfMessages pSpec₂ ⊂ₒ oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
  | [], _ => { toMonadLift := { monadLift := fun q => q } }
  | (.P_to_V _ _) :: tl, pSpec₂ =>
    let ih := subSpec_oracleSpecOfMessages_right tl pSpec₂
    { toMonadLift := { monadLift := fun q =>
      let q' := ih.monadLift q
      ⟨Sum.inr q'.1, q'.2⟩ } }
  | (.V_to_P _) :: tl, pSpec₂ => subSpec_oracleSpecOfMessages_right tl pSpec₂

namespace OracleVerifier

/-- Answer a message oracle query directly from a transcript, walking the protocol
spec to find the relevant round's data and `OracleInterface.answer`. -/
def answerMsgQuery :
    (pSpec : ProtocolSpec) → Transcript pSpec →
    (q : MessageOracleIdx pSpec) → oracleSpecOfMessages pSpec q
  | (.P_to_V _ oi) :: _, tr, .inl q => @OracleInterface.answer _ oi tr.head q
  | (.P_to_V _ _) :: tl, tr, .inr q => answerMsgQuery tl tr.tail q
  | (.V_to_P _) :: tl, tr, q => answerMsgQuery tl tr.tail q

/-- Consistency property connecting `simulate` (query-level) and `reify` (data-level):
if `reify` succeeds on concrete input-oracle data and messages, then `simulate` must reproduce
the same answers when run in the corresponding pure oracle context. -/
def reifySimulateCorrect
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)]
    (ov : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  ∀ (oStmtInData : ∀ i, OStmtIn i) (msgs : Messages pSpec) (i : ιₛₒ)
    (q : OracleInterface.Query (OStmtOut i)),
    match ov.reify oStmtInData msgs with
    | none => True
    | some oStmtOutData =>
        simulateQ (oracleImplOfOStmtInMessages (pSpec := pSpec) oStmtInData msgs)
          (ov.simulate ⟨i, q⟩) = pure (OracleInterface.answer (oStmtOutData i) q)

/-- Convert an oracle verifier to a plain verifier by simulating all oracle queries
with actual data. Extracts challenges and messages from the transcript, builds
pure oracle implementations, and runs the oracle verifier via `simulateQ`. -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ i, OracleInterface (OStmtOut i)]
    (ov : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (oStmtData : ∀ i, OStmtIn i) :
    Verifier (OracleComp oSpec) StmtIn StmtOut pSpec :=
  fun stmt tr =>
    -- Build a QueryImpl that answers all three oracle layers from concrete data:
    --   oSpec queries → forwarded to the ambient oracle
    --   [OStmtIn]ₒ queries → answered purely from oStmtData
    --   message queries → answered purely from the transcript via answerMsgQuery
    let impl : QueryImpl (oSpec + [OStmtIn]ₒ + oracleSpecOfMessages pSpec)
                         (OracleComp oSpec) := fun
      | Sum.inl (Sum.inl i) => liftM (query i)
      | Sum.inl (Sum.inr ⟨i, q⟩) => pure (OracleInterface.answer (oStmtData i) q)
      | Sum.inr q => pure (answerMsgQuery pSpec tr q)
    (simulateQ impl (ov.verify stmt (Transcript.toChallenges pSpec tr)) :
      OracleComp oSpec (Option StmtOut))

/-- Compose two oracle verifiers sequentially.

The `verify` and `simulate` fields require routing oracle queries between the
composed message specs via `SubSpec` coercions (left/right message spec
embeddings). The routing for `verify` composes `ov₁.simulate` to answer
intermediate `[OStmt₂]ₒ` queries from `ov₂`, while routing `pSpec₁`/`pSpec₂`
message queries to the appropriate half of the combined spec.
The `reify` field is fully implemented. -/
def comp
    {ι : Type} {oSpec : OracleSpec ι}
    {S₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    {S₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    {S₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [∀ i, OracleInterface (OStmt₁ i)]
    [∀ i, OracleInterface (OStmt₂ i)]
    [∀ i, OracleInterface (OStmt₃ i)]
    (ov₁ : OracleVerifier oSpec S₁ OStmt₁ S₂ OStmt₂ pSpec₁)
    (ov₂ : OracleVerifier oSpec S₂ OStmt₂ S₃ OStmt₃ pSpec₂)
    : OracleVerifier oSpec S₁ OStmt₁ S₃ OStmt₃ (pSpec₁ ++ pSpec₂) where
  -- The composed verifier operates over `vSpec = oSpec + [OStmt₁]ₒ + msgOracles(pSpec₁ ++ pSpec₂)`.
  -- Both ov₁ and ov₂ expect their own message oracle specs, so we re-embed queries via SubSpec.
  -- The pattern `q'.2 <$> liftM (query ...)` maps the SubSpec continuation over the raw query
  -- result, converting the combined spec's range type back to the component's expected range.
  verify := fun stmt ch =>
    let (ch₁, ch₂) := Challenges.split pSpec₁ pSpec₂ ch
    let ssL := subSpec_oracleSpecOfMessages_left pSpec₁ pSpec₂
    let ssR := subSpec_oracleSpecOfMessages_right pSpec₁ pSpec₂
    let vSpec := oSpec + [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
    -- Lift ov₁'s queries: oSpec and [OStmt₁]ₒ pass through; message queries embed via ssL
    let liftV₁ : QueryImpl
        (oSpec + [OStmt₁]ₒ + oracleSpecOfMessages pSpec₁)
        (OracleComp vSpec) := fun
      | Sum.inl q => liftM (query (spec := vSpec) (Sum.inl q))
      | Sum.inr q =>
        let q' := ssL.monadLift ⟨q, id⟩
        q'.2 <$> liftM (query (spec := vSpec) (Sum.inr q'.1))
    -- Lift ov₂'s queries: oSpec passes through; [OStmt₂]ₒ queries are answered by running
    -- ov₁.simulate (which itself needs its queries lifted into vSpec via `inner`);
    -- pSpec₂ message queries embed via ssR
    let liftV₂ : QueryImpl
        (oSpec + [OStmt₂]ₒ + oracleSpecOfMessages pSpec₂)
        (OracleComp vSpec) := fun
      | Sum.inl (Sum.inl i) => liftM (query (spec := vSpec) (Sum.inl (Sum.inl i)))
      | Sum.inl (Sum.inr q) =>
          let inner : QueryImpl
              ([OStmt₁]ₒ + oracleSpecOfMessages pSpec₁)
              (OracleComp vSpec) := fun
            | Sum.inl q' => liftM (query (spec := vSpec) (Sum.inl (Sum.inr q')))
            | Sum.inr q' =>
              let q'' := ssL.monadLift ⟨q', id⟩
              q''.2 <$> liftM (query (spec := vSpec) (Sum.inr q''.1))
          simulateQ inner (ov₁.simulate q)
      | Sum.inr q =>
        let q' := ssR.monadLift ⟨q, id⟩
        q'.2 <$> liftM (query (spec := vSpec) (Sum.inr q'.1))
    OptionT.mk do
      let mid ← simulateQ liftV₁ (ov₁.verify stmt ch₁)
      match mid with
      | none => pure none
      | some s₂ => simulateQ liftV₂ (ov₂.verify s₂ ch₂)
  -- The composed simulator answers [OStmt₃]ₒ queries by running ov₂.simulate, whose
  -- [OStmt₂]ₒ queries are in turn answered by ov₁.simulate (lifted into the combined spec).
  simulate := fun q =>
    let ssL := subSpec_oracleSpecOfMessages_left pSpec₁ pSpec₂
    let ssR := subSpec_oracleSpecOfMessages_right pSpec₁ pSpec₂
    let sSpec := [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
    -- Lift ov₁.simulate's oracle context into sSpec
    let liftSim : QueryImpl
        ([OStmt₁]ₒ + oracleSpecOfMessages pSpec₁)
        (OracleComp sSpec) := fun
      | Sum.inl q' => liftM (query (spec := sSpec) (Sum.inl q'))
      | Sum.inr q' =>
        let q'' := ssL.monadLift ⟨q', id⟩
        q''.2 <$> liftM (query (spec := sSpec) (Sum.inr q''.1))
    -- Route ov₂.simulate's queries: [OStmt₂]ₒ → ov₁.simulate; messages → ssR embedding
    let liftOuter : QueryImpl
        ([OStmt₂]ₒ + oracleSpecOfMessages pSpec₂)
        (OracleComp sSpec) := fun
      | Sum.inl q' => simulateQ liftSim (ov₁.simulate q')
      | Sum.inr q' =>
        let q'' := ssR.monadLift ⟨q', id⟩
        q''.2 <$> liftM (query (spec := sSpec) (Sum.inr q''.1))
    simulateQ liftOuter (ov₂.simulate q)
  reify := fun oStmtInData msgs => do
    let (msgs₁, msgs₂) := Messages.split pSpec₁ pSpec₂ msgs
    let oStmtMidData ← ov₁.reify oStmtInData msgs₁
    ov₂.reify oStmtMidData msgs₂

/-- Compose an oracle verifier with itself `n` times over the replicated protocol spec. -/
def compNth
    {ι : Type} {oSpec : OracleSpec ι}
    {S : Type} {ιₛ : Type} {OStmt : ιₛ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmt i)] : (n : Nat) →
    OracleVerifier oSpec S OStmt S OStmt pSpec →
    OracleVerifier oSpec S OStmt S OStmt (pSpec.replicate n)
  | 0, _ =>
    { verify := fun stmt _ => pure stmt,
      simulate := fun q =>
        liftM (query (spec := [OStmt]ₒ + oracleSpecOfMessages (pSpec.replicate 0))
          (Sum.inl q)),
      reify := fun oStmtData _ => some oStmtData }
  | n + 1, ov => comp ov (compNth n ov)

end OracleVerifier

end ProtocolSpec
