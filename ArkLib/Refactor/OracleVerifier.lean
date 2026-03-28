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
  | [], _ =>
    { monadLift := fun q => PEmpty.elim q.input
      liftM_map := fun q _ => PEmpty.elim q.input }
  | (.P_to_V _ oi) :: tl, pSpec₂ =>
    let ih := subSpec_oracleSpecOfMessages_left tl pSpec₂
    letI : oracleSpecOfMessages tl ⊂ₒ oracleSpecOfMessages (tl ++ pSpec₂) := ih
    -- Use VCVio's generic `+`-compatibility instance on the right summand.
    (inferInstance :
      (@OracleInterface.spec _ oi + oracleSpecOfMessages tl) ⊂ₒ
        (@OracleInterface.spec _ oi + oracleSpecOfMessages (tl ++ pSpec₂)))
  | (.V_to_P _) :: tl, pSpec₂ => subSpec_oracleSpecOfMessages_left tl pSpec₂

/-- Right embedding: `msgOracles(pSpec₂) ⊂ₒ msgOracles(pSpec₁ ++ pSpec₂)`.
Wraps every index with `Sum.inr` for each `P_to_V` round in `pSpec₁`, pushing
pSpec₂'s queries past all of pSpec₁'s oracle indices. -/
def subSpec_oracleSpecOfMessages_right :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    oracleSpecOfMessages pSpec₂ ⊂ₒ oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
  | [], _ =>
    { monadLift := fun q => q
      liftM_map := by
        intro α β q f
        cases q; rfl }
  | (.P_to_V _ oi) :: tl, pSpec₂ =>
    let ih := subSpec_oracleSpecOfMessages_right tl pSpec₂
    let hRight :
        oracleSpecOfMessages (tl ++ pSpec₂) ⊂ₒ
          (@OracleInterface.spec _ oi + oracleSpecOfMessages (tl ++ pSpec₂)) :=
      inferInstance
    OracleSpec.SubSpec.trans ih hRight
  | (.V_to_P _) :: tl, pSpec₂ => subSpec_oracleSpecOfMessages_right tl pSpec₂

namespace QueryImpl

/-- Build a `QueryImpl` from a `SubSpec` coercion. Each query is lifted through
the SubSpec's `monadLift` and issued as a raw query in the super-spec. -/
def ofSubSpec {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {superSpec : OracleSpec ι₂}
    (ss : spec₁ ⊂ₒ superSpec) : QueryImpl spec₁ (OracleComp superSpec) :=
  fun q =>
    letI q' := ss.monadLift ⟨q, id⟩
    q'.2 <$> liftM (n := OracleComp superSpec) (query (spec := superSpec) q'.1)

end QueryImpl

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

/-- Common forwarding constructor for the migration case where the output oracle
family is exactly the input oracle family and only the public statement changes. -/
def keepInputOracle
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {ιₛ : Type} {OStmt : ιₛ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmt i)]
    (verify : StmtIn → Challenges pSpec →
      OptionT (OracleComp (oSpec + [OStmt]ₒ + oracleSpecOfMessages pSpec)) StmtOut) :
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt pSpec where
  verify := verify
  simulate := fun q =>
    liftM (query (spec := [OStmt]ₒ + oracleSpecOfMessages pSpec) (Sum.inl q))
  reify := fun oStmtData _ => some oStmtData

theorem keepInputOracle_reifySimulateCorrect
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn StmtOut : Type} {ιₛ : Type} {OStmt : ιₛ → Type}
    {pSpec : ProtocolSpec}
    [∀ i, OracleInterface (OStmt i)]
    (verify : StmtIn → Challenges pSpec →
      OptionT (OracleComp (oSpec + [OStmt]ₒ + oracleSpecOfMessages pSpec)) StmtOut) :
    reifySimulateCorrect
      (keepInputOracle (oSpec := oSpec) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (OStmt := OStmt) (pSpec := pSpec) verify) := by
  intro oStmtInData msgs i q
  rfl

/-- Identity oracle verifier on the empty protocol. -/
protected def id
    {ι : Type} {oSpec : OracleSpec ι}
    {S : Type} {ιₛ : Type} {OStmt : ιₛ → Type}
    [∀ i, OracleInterface (OStmt i)] :
    OracleVerifier oSpec S OStmt S OStmt [] :=
  keepInputOracle (oSpec := oSpec) (StmtIn := S) (StmtOut := S)
    (OStmt := OStmt) (pSpec := []) (fun stmt _ => pure stmt)

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

/-- Lift inner input-oracle routing into a context that also contains message oracles. -/
def liftInputQueries
    {Outer_ιₛ : Type} {OuterOStmt : Outer_ιₛ → Type} [∀ i, OracleInterface (OuterOStmt i)]
    {Inner_ιₛ : Type} {InnerOStmt : Inner_ιₛ → Type} [∀ i, OracleInterface (InnerOStmt i)]
    {pSpec : ProtocolSpec}
    (simIn : QueryImpl [InnerOStmt]ₒ (OracleComp [OuterOStmt]ₒ)) :
    QueryImpl [InnerOStmt]ₒ (OracleComp ([OuterOStmt]ₒ + oracleSpecOfMessages pSpec)) :=
  fun q =>
    simulateQ
      (fun q' =>
        liftM (query (spec := [OuterOStmt]ₒ + oracleSpecOfMessages pSpec) (Sum.inl q')))
      (simIn q)

/-- Lift the full verification context `oSpec + [InnerOStmtIn]ₒ + msgOracles`
into `oSpec + [OuterOStmtIn]ₒ + msgOracles`. -/
def liftVerifyQueries
    {ι : Type} {oSpec : OracleSpec ι}
    {Outer_ιₛ : Type} {OuterOStmt : Outer_ιₛ → Type} [∀ i, OracleInterface (OuterOStmt i)]
    {Inner_ιₛ : Type} {InnerOStmt : Inner_ιₛ → Type} [∀ i, OracleInterface (InnerOStmt i)]
    {pSpec : ProtocolSpec}
    (simIn : QueryImpl [InnerOStmt]ₒ (OracleComp [OuterOStmt]ₒ)) :
    QueryImpl (oSpec + [InnerOStmt]ₒ + oracleSpecOfMessages pSpec)
      (OracleComp (oSpec + [OuterOStmt]ₒ + oracleSpecOfMessages pSpec)) := fun
  | Sum.inl (Sum.inl q) =>
      liftM (query (spec := oSpec + [OuterOStmt]ₒ + oracleSpecOfMessages pSpec)
        (Sum.inl (Sum.inl q)))
  | Sum.inl (Sum.inr q) => liftInputQueries (pSpec := pSpec) simIn q
  | Sum.inr q =>
      liftM (query (spec := oSpec + [OuterOStmt]ₒ + oracleSpecOfMessages pSpec) (Sum.inr q))

/-- Lift inner output-oracle simulation into the outer input-oracle/message context. -/
def liftInnerSimulateQueries
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]
    {pSpec : ProtocolSpec}
    (simIn : QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (simulate : QueryImpl [InnerOStmtOut]ₒ
      (OracleComp ([InnerOStmtIn]ₒ + oracleSpecOfMessages pSpec))) :
    QueryImpl [InnerOStmtOut]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + oracleSpecOfMessages pSpec)) :=
  fun q =>
    simulateQ
      (fun
        | Sum.inl q' => liftInputQueries (pSpec := pSpec) simIn q'
        | Sum.inr q' =>
            liftM (query (spec := [OuterOStmtIn]ₒ + oracleSpecOfMessages pSpec) (Sum.inr q')))
      (simulate q)

/-- Compose outer output-oracle routing with the inner verifier's output simulation. -/
def liftOutputQueries
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]
    {pSpec : ProtocolSpec}
    (simOut : QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ)))
    (simIn : QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (simulate : QueryImpl [InnerOStmtOut]ₒ
      (OracleComp ([InnerOStmtIn]ₒ + oracleSpecOfMessages pSpec))) :
    QueryImpl [OuterOStmtOut]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + oracleSpecOfMessages pSpec)) :=
  fun q =>
    simulateQ
      (fun
        | Sum.inl q' =>
            liftM (query (spec := [OuterOStmtIn]ₒ + oracleSpecOfMessages pSpec) (Sum.inl q'))
        | Sum.inr q' =>
            liftInnerSimulateQueries (pSpec := pSpec) simIn simulate q')
      (simOut q)

/-- Lift queries from `[OStmt₁]ₒ + msgOracles(pSpec₁)` into a target spec that
contains both components via given SubSpec coercions. `[OStmt₁]ₒ` queries forward
via `ssOStmt₁`; message queries compose the left message embedding with `ssMsgTarget`. -/
private def comp.liftOStmtMsg
    {ι : Type} {targetSpec : OracleSpec ι}
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ssOStmt₁ : [OStmt₁]ₒ ⊂ₒ targetSpec)
    (ssMsgTarget : oracleSpecOfMessages (pSpec₁ ++ pSpec₂) ⊂ₒ targetSpec) :
    QueryImpl ([OStmt₁]ₒ + oracleSpecOfMessages pSpec₁) (OracleComp targetSpec) :=
  let ssL := subSpec_oracleSpecOfMessages_left pSpec₁ pSpec₂
  fun
  | Sum.inl q => QueryImpl.ofSubSpec ssOStmt₁ q
  | Sum.inr q => QueryImpl.ofSubSpec (SubSpec.trans ssL ssMsgTarget) q

/-- Lift ov₁'s oracle context into the composed verify spec.
`oSpec + [OStmt₁]ₒ` passes through; message queries embed via the left message SubSpec. -/
private def comp.liftVerify₁
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {pSpec₁ pSpec₂ : ProtocolSpec} :
    let vSpec := oSpec + [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
    QueryImpl (oSpec + [OStmt₁]ₒ + oracleSpecOfMessages pSpec₁) (OracleComp vSpec) :=
  let vSpec := oSpec + [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
  let ssL := subSpec_oracleSpecOfMessages_left pSpec₁ pSpec₂
  fun
  | Sum.inl q => liftM (query (spec := vSpec) (Sum.inl q))
  | Sum.inr q => QueryImpl.ofSubSpec
      (SubSpec.trans ssL (OracleQuery.subSpec_add_right (spec₁ := oSpec + [OStmt₁]ₒ))) q

/-- Lift ov₂'s oracle context into the composed verify spec.
`oSpec` passes through; `[OStmt₂]ₒ` queries are answered by running
ov₁.simulate (lifted via `comp.liftOStmtMsg`); pSpec₂ message queries
embed via the right message SubSpec. -/
private def comp.liftVerify₂
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)]
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ov₁_simulate : QueryImpl [OStmt₂]ₒ
      (OracleComp ([OStmt₁]ₒ + oracleSpecOfMessages pSpec₁))) :
    let vSpec := oSpec + [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
    QueryImpl (oSpec + [OStmt₂]ₒ + oracleSpecOfMessages pSpec₂) (OracleComp vSpec) :=
  let vSpec := oSpec + [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
  let ssR := subSpec_oracleSpecOfMessages_right pSpec₁ pSpec₂
  fun
  | Sum.inl (Sum.inl i) => liftM (query (spec := vSpec) (Sum.inl (Sum.inl i)))
  | Sum.inl (Sum.inr q) =>
      simulateQ (comp.liftOStmtMsg
        (SubSpec.trans (OracleQuery.subSpec_add_right (spec₁ := oSpec))
          (OracleQuery.subSpec_add_left (spec₂ := oracleSpecOfMessages (pSpec₁ ++ pSpec₂))))
        (OracleQuery.subSpec_add_right (spec₁ := oSpec + [OStmt₁]ₒ)))
        (ov₁_simulate q)
  | Sum.inr q => QueryImpl.ofSubSpec
      (SubSpec.trans ssR (OracleQuery.subSpec_add_right (spec₁ := oSpec + [OStmt₁]ₒ))) q

/-- Route ov₂.simulate's queries into the composed simulate spec.
`[OStmt₂]ₒ` queries go through ov₁.simulate (lifted via `comp.liftOStmtMsg`);
pSpec₂ message queries embed via the right message SubSpec. -/
private def comp.liftSimulate
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)]
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (ov₁_simulate : QueryImpl [OStmt₂]ₒ
      (OracleComp ([OStmt₁]ₒ + oracleSpecOfMessages pSpec₁))) :
    let sSpec := [OStmt₁]ₒ + oracleSpecOfMessages (pSpec₁ ++ pSpec₂)
    QueryImpl ([OStmt₂]ₒ + oracleSpecOfMessages pSpec₂) (OracleComp sSpec) :=
  let ssR := subSpec_oracleSpecOfMessages_right pSpec₁ pSpec₂
  fun
  | Sum.inl q =>
      simulateQ (comp.liftOStmtMsg
        (OracleQuery.subSpec_add_left (spec₂ := oracleSpecOfMessages (pSpec₁ ++ pSpec₂)))
        (OracleQuery.subSpec_add_right (spec₁ := [OStmt₁]ₒ)))
        (ov₁_simulate q)
  | Sum.inr q => QueryImpl.ofSubSpec
      (SubSpec.trans ssR (OracleQuery.subSpec_add_right (spec₁ := [OStmt₁]ₒ))) q

/-- Compose two oracle verifiers sequentially.

The `verify` and `simulate` fields route oracle queries between the composed message
specs via `SubSpec` coercions (see `comp.liftVerify₁`, `comp.liftVerify₂`,
`comp.liftSimulate`). The `reify` field chains the two verifiers' reify functions. -/
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
  verify := fun stmt ch =>
    let (ch₁, ch₂) := Challenges.split pSpec₁ pSpec₂ ch
    do let s₂ ← OptionT.mk (simulateQ comp.liftVerify₁ (ov₁.verify stmt ch₁))
       OptionT.mk (simulateQ (comp.liftVerify₂ ov₁.simulate) (ov₂.verify s₂ ch₂))
  simulate := fun q =>
    simulateQ (comp.liftSimulate ov₁.simulate) (ov₂.simulate q)
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
  | 0, _ => OracleVerifier.id
  | n + 1, ov => comp ov (compNth n ov)

end OracleVerifier

/-! ## Interactive Oracle Verifier

The `InteractiveOracleVerifier` processes the protocol round by round, accumulating
oracle access to prover messages. Unlike the batch `OracleVerifier` (which receives
all challenges up front), the interactive version computes challenges adaptively
using oracle queries to previously received messages.

This generalizes the public-coin model: if challenges are sampled uniformly, the
result is equivalent to a public-coin `OracleVerifier`. If challenges depend on
oracle queries to prior messages, we have a private-coin protocol.

The accumulated message oracle spec `accMsgSpec` starts at `[]ₒ` and grows
by `oi.spec` at each `P_to_V` round. At `V_to_P` rounds, the verifier runs in
`OracleComp (oSpec + [OStmtIn]ₒ + accMsgSpec)` to compute the challenge. -/

/-- Interactive oracle verifier that processes the protocol round by round.

- At `P_to_V T oi` rounds: the accumulated message oracle spec grows by `oi.spec`
  (the verifier gains oracle access to the newly received message).
- At `V_to_P T` rounds: the verifier computes a challenge of type `T` using
  `OracleComp` with current accumulated oracle access.
- At `[]` (end): the verifier makes a final accept/reject decision. -/
def InteractiveOracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type)
    [∀ i, OracleInterface (OStmtIn i)] :
    {ιₐ : Type} → OracleSpec ιₐ → ProtocolSpec → Type
  | _, accMsgSpec, [] =>
      StmtIn → OptionT (OracleComp (oSpec + [OStmtIn]ₒ + accMsgSpec)) StmtOut
  | _, accMsgSpec, (.P_to_V _ oi) :: tl =>
      InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut
        (accMsgSpec + @OracleInterface.spec _ oi) tl
  | _, accMsgSpec, (.V_to_P T) :: tl =>
      OracleComp (oSpec + [OStmtIn]ₒ + accMsgSpec)
        (T × InteractiveOracleVerifier oSpec StmtIn OStmtIn StmtOut accMsgSpec tl)

end ProtocolSpec
