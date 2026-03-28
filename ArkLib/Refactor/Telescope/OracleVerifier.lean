import ArkLib.Refactor.Telescope.Syntax.Verifier

/-!
# Telescope Oracle Verifier

Statement-indexed oracle verifier infrastructure for `ProtocolCtx`. Unlike the
list-based `ProtocolSpec.OracleVerifier`, both the protocol context and the
input-oracle type may vary with the public statement. The concrete input oracle is
an explicit argument to the verifier, while output-oracle data is tracked via a
separate simulation/reification layer as in the non-dependent API.

The key observation is that the prover messages already present in a dependent
transcript can be repacked into a single oracle-carrying value via
`Transcript.MessageData`. This lets the verifier query prior messages through
`OracleComp` without requiring a static round index. Verifier challenges remain
inspectable through the transcript itself; they are not reified into a separate
oracle layer here.
-/

open OracleComp OracleSpec

namespace ProtocolCtx

instance : OracleInterface PUnit := OracleInterface.instDefault

namespace Transcript

/-- Oracle-carrying view of all prover messages contained in a transcript. Challenge
rounds contribute no data; each message round contributes the sent message together
with the oracle data of the suffix transcript. -/
def MessageData : {ctx : ProtocolCtx} → Transcript ctx → Type
  | .nil, _ => PUnit
  | .P_to_V T _ _, ⟨_, trRest⟩ => T × MessageData trRest
  | .V_to_P _ _, ⟨_, trRest⟩ => MessageData trRest

/-- Reify the prover-message oracle data from a transcript. -/
def messageData : {ctx : ProtocolCtx} → (tr : Transcript ctx) → MessageData tr
  | .nil, _ => PUnit.unit
  | .P_to_V _ _ _, ⟨t, trRest⟩ => ⟨t, messageData trRest⟩
  | .V_to_P _ _, ⟨_, trRest⟩ => messageData trRest

instance instMessageDataOracleInterface :
    {ctx : ProtocolCtx} → (tr : Transcript ctx) → OracleInterface (MessageData tr)
  | .nil, _ => OracleInterface.instDefault
  | .P_to_V T oi _, ⟨t, trRest⟩ => by
      let _ : OracleInterface T := oi
      let _ : OracleInterface (MessageData trRest) := instMessageDataOracleInterface trRest
      simpa [MessageData] using (inferInstance : OracleInterface (T × MessageData trRest))
  | .V_to_P _ _, ⟨_, trRest⟩ => instMessageDataOracleInterface trRest

end Transcript

namespace OracleVerifier

/-- Simulate the oracle interface of a single oracle-carrying value. -/
def simOracleSingle {T : Type} [OracleInterface T] (t : T) :
    QueryImpl (OracleInterface.spec (Message := T)) Id :=
  fun q => OracleInterface.answer t q

/-- Telescope-native oracle implementation built from the prover-message oracle data
extracted from the transcript. The concrete input oracle is already an explicit
parameter of the verifier itself. -/
def oracleImpl
    {ι : Type} {oSpec : OracleSpec ι}
    {ctx : ProtocolCtx} (tr : Transcript ctx) :
    QueryImpl
      (oSpec + OracleInterface.spec (Message := Transcript.MessageData tr))
      (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (simOracleSingle (Transcript.messageData tr))

end OracleVerifier

/-- Result monad for oracle verification after fixing the statement, input oracle, and
realized transcript. The extra oracle layer exposes prior prover messages as a single
oracle-carrying value. -/
abbrev OracleVerifyM
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    (statement : Statement) (inputOracle : InputOracle statement)
    (tr : Transcript (Context statement inputOracle)) :=
  OptionT
    (OracleComp (oSpec + OracleInterface.spec (Message := Transcript.MessageData tr)))
    (StatementOut statement inputOracle tr)

/-- Statement-indexed telescope-native oracle verifier. The verifier result depends on
the concrete input oracle and realized transcript, while output-oracle access is
handled by separate `simulate` and `realize` fields. -/
structure OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type)
    (InputOracle : Statement → Type) [∀ statement, OracleInterface (InputOracle statement)]
    (Context : (statement : Statement) → InputOracle statement → ProtocolCtx)
    (StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type)
    (OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) → Type)
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)] where
  verify :
    (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) →
      OracleVerifyM
        (oSpec := oSpec) (StatementOut := StatementOut)
        statement inputOracle tr
  simulate :
    (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) →
      QueryImpl
        (OracleInterface.spec (Message := OutputOracle statement inputOracle tr))
        (OracleComp (OracleInterface.spec (Message := Transcript.MessageData tr)))
  realize :
    (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) →
      Option (OutputOracle statement inputOracle tr)

/-- `simulate` agrees with the concrete output oracle returned by `realize`
whenever realization succeeds. -/
def SimulationCompatible
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (ov : OracleVerifier oSpec Statement InputOracle Context StatementOut OutputOracle) : Prop :=
  ∀ (statement : Statement) (inputOracle : InputOracle statement)
    (tr : Transcript (Context statement inputOracle))
    (q : OracleInterface.Query (OutputOracle statement inputOracle tr)),
    match ov.realize statement inputOracle tr with
    | none => True
    | some outputOracle =>
        simulateQ
          (OracleVerifier.simOracleSingle (Transcript.messageData tr))
          (ov.simulate statement inputOracle tr q) =
        pure (OracleInterface.answer outputOracle q)

namespace OracleVerifier

open scoped TelescopeSyntax

/-- Common forwarding constructor for the case where the output oracle is exactly the
input oracle. -/
def keepInputOracle
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    (verify : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) →
      OracleVerifyM
        (oSpec := oSpec) (StatementOut := StatementOut)
        statement inputOracle tr) :
    OracleVerifier oSpec Statement InputOracle Context StatementOut
      (fun statement _ _ => InputOracle statement) where
  verify := verify
  simulate := fun _ inputOracle _ q => pure (OracleInterface.answer inputOracle q)
  realize := fun _ inputOracle _ => some inputOracle

theorem keepInputOracle_simulationCompatible
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    (verify : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) →
      OracleVerifyM
        (oSpec := oSpec) (StatementOut := StatementOut)
        statement inputOracle tr) :
    SimulationCompatible
      (keepInputOracle (oSpec := oSpec) (verify := verify)) := by
  unfold SimulationCompatible
  intro _ inputOracle _ q
  rfl

/-- Verifier body for the identity oracle verifier on the empty telescope protocol. -/
private def idVerify
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)] :
    (statement : Statement) → (inputOracle : InputOracle statement) → (tr : Transcript .nil) →
      OracleVerifyM
        (oSpec := oSpec)
        (Context := fun _ _ => .nil)
        (StatementOut := fun _ _ _ => Statement)
        statement inputOracle tr :=
  open scoped TelescopeSyntax in
  verifier!{ statement, _inputOracle, _ => pure statement }

/-- Identity oracle verifier on the empty telescope protocol. -/
protected def id
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)] :
    OracleVerifier oSpec Statement InputOracle
      (fun _ _ => .nil)
      (fun _ _ _ => Statement)
      (fun statement _ _ => InputOracle statement) :=
  keepInputOracle (oSpec := oSpec)
    (verify := idVerify (oSpec := oSpec))

/-- Convert a statement-indexed telescope oracle verifier to a plain verifier after
fixing the concrete input-oracle value for one statement. This only needs to
simulate the transcript-message oracle layer; the input oracle is already explicit. -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : (statement : Statement) → InputOracle statement → ProtocolCtx}
    {StatementOut : (statement : Statement) → (inputOracle : InputOracle statement) →
      Transcript (Context statement inputOracle) → Type}
    {OutputOracle : (statement : Statement) → (inputOracle : InputOracle statement) →
      (tr : Transcript (Context statement inputOracle)) → Type}
    [∀ statement, ∀ inputOracle, ∀ tr,
      OracleInterface (OutputOracle statement inputOracle tr)]
    (ov : OracleVerifier oSpec Statement InputOracle Context StatementOut OutputOracle)
    (statement : Statement) (inputOracle : InputOracle statement) :
    (tr : Transcript (Context statement inputOracle)) →
      OptionT (OracleComp oSpec) (StatementOut statement inputOracle tr) :=
  fun tr =>
    simulateQ (oracleImpl (oSpec := oSpec) tr) (ov.verify statement inputOracle tr)

end OracleVerifier

end ProtocolCtx
