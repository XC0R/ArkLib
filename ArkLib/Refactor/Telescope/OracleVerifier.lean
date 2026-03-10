import ArkLib.Refactor.Telescope.Basic

/-!
# Telescope Oracle Verifier

Statement-indexed oracle verifier infrastructure for `ProtocolCtx`. Unlike the
list-based `ProtocolSpec.OracleVerifier`, both the protocol context and the
input-oracle type may vary with the public statement, while the message-oracle
surface depends on the actual transcript path.

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

/-- Telescope-native oracle implementation built from concrete input-oracle data and
the prover-message oracle data extracted from the transcript. -/
def oracleImpl
    {ι : Type} {oSpec : OracleSpec ι}
    {OStmtIn : Type} [OracleInterface OStmtIn]
    {ctx : ProtocolCtx} (oStmtIn : OStmtIn) (tr : Transcript ctx) :
    QueryImpl
      (oSpec +
        (OracleInterface.spec (Message := OStmtIn) +
          OracleInterface.spec (Message := Transcript.MessageData tr)))
      (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (QueryImpl.add
      (simOracleSingle oStmtIn)
      (simOracleSingle (Transcript.messageData tr)))

end OracleVerifier

/-- Statement-indexed telescope-native oracle verifier. Its monad can query:

1. the ambient oracle `oSpec`,
2. the statement-specific input oracle value `InputOracle statement`,
3. the prover messages already present in the dependent transcript `tr`.

Unlike the list-based oracle verifier, the message oracle spec depends on the actual
transcript path. -/
def OracleVerifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type)
    (InputOracle : Statement → Type) [∀ statement, OracleInterface (InputOracle statement)]
    (Context : Statement → ProtocolCtx)
    (Output : (statement : Statement) → Transcript (Context statement) → Type) :=
  (statement : Statement) → (tr : Transcript (Context statement)) →
    OptionT
      (OracleComp
        (oSpec +
          (OracleInterface.spec (Message := InputOracle statement) +
            OracleInterface.spec (Message := Transcript.MessageData tr))))
      (Output statement tr)

namespace OracleVerifier

/-- Convert a statement-indexed telescope oracle verifier to a plain verifier after
fixing the concrete input-oracle value for one statement. This avoids freezing the
oracle input at construction time. -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type}
    {InputOracle : Statement → Type} [∀ statement, OracleInterface (InputOracle statement)]
    {Context : Statement → ProtocolCtx}
    {Output : (statement : Statement) → Transcript (Context statement) → Type}
    (ov : OracleVerifier oSpec Statement InputOracle Context Output)
    (statement : Statement) (inputOracle : InputOracle statement) :
    (tr : Transcript (Context statement)) → OptionT (OracleComp oSpec) (Output statement tr) :=
  fun tr =>
    simulateQ (oracleImpl (oSpec := oSpec) inputOracle tr) (ov statement tr)

end OracleVerifier

end ProtocolCtx
