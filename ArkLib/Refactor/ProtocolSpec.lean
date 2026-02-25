/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.OracleInterface

/-!
# List-Based Protocol Specifications

`ProtocolSpec` is defined as `List ProtocolSpec.Round`, where each `Round` is either:
- `.P_to_V T oi`: prover sends a message of type `T` with oracle interface `oi`
- `.V_to_P T`: verifier sends a challenge of type `T`

This replaces the old `ProtocolSpec n` (a `Fin n`-indexed pair of direction/type vectors).
Two protocol specs of different lengths are the same type. Append is `List.append`.

The `OracleInterface` is bundled into `P_to_V` rounds to eliminate instance synthesis
problems through `List.get ∘ messageTypes` for abstract specs. Smart constructors
`.msg` and `.chal` allow concise spec definitions by inferring the `OracleInterface`
at construction time.
-/

universe u

namespace ProtocolSpec

/-- A single round in a protocol specification. -/
inductive Round where
  /-- Prover sends a message of type `T`, accessible via oracle interface `oi`. -/
  | P_to_V (T : Type) (oi : OracleInterface T)
  /-- Verifier sends a challenge of type `T`. -/
  | V_to_P (T : Type)

namespace Round

/-- The type carried by a round (message type or challenge type). -/
def type : Round → Type
  | .P_to_V T _ => T
  | .V_to_P T => T

end Round

end ProtocolSpec

/-- A protocol specification is a list of rounds. Each round specifies whether the
prover sends a message or the verifier sends a challenge, along with the type and
(for messages) the oracle interface. -/
@[reducible]
def ProtocolSpec := List ProtocolSpec.Round

namespace ProtocolSpec

open Round

/-!
## Smart constructors
-/

/-- Construct a prover message round, inferring the `OracleInterface` instance. -/
def msg (T : Type) [oi : OracleInterface T] : Round := .P_to_V T oi

/-- Construct a verifier challenge round. -/
def chal (T : Type) : Round := .V_to_P T

/-!
## Message and challenge type extraction
-/

/-- Extract the list of prover message types from a protocol specification. -/
def messageTypes : ProtocolSpec → List Type
  | [] => []
  | (.P_to_V T _) :: tl => T :: messageTypes tl
  | (.V_to_P _) :: tl => messageTypes tl

/-- Extract the list of verifier challenge types from a protocol specification. -/
def challengeTypes : ProtocolSpec → List Type
  | [] => []
  | (.P_to_V _ _) :: tl => challengeTypes tl
  | (.V_to_P T) :: tl => T :: challengeTypes tl

/-!
## Append lemmas (critical for composition)
-/

@[simp]
theorem messageTypes_nil : messageTypes ([] : ProtocolSpec) = [] := rfl

@[simp]
theorem messageTypes_cons_P_to_V {T : Type} {oi : OracleInterface T} {tl : ProtocolSpec} :
    messageTypes ((.P_to_V T oi) :: tl) = T :: messageTypes tl := rfl

@[simp]
theorem messageTypes_cons_V_to_P {T : Type} {tl : ProtocolSpec} :
    messageTypes ((.V_to_P T) :: tl) = messageTypes tl := rfl

@[simp]
theorem challengeTypes_nil : challengeTypes ([] : ProtocolSpec) = [] := rfl

@[simp]
theorem challengeTypes_cons_P_to_V {T : Type} {oi : OracleInterface T} {tl : ProtocolSpec} :
    challengeTypes ((.P_to_V T oi) :: tl) = challengeTypes tl := rfl

@[simp]
theorem challengeTypes_cons_V_to_P {T : Type} {tl : ProtocolSpec} :
    challengeTypes ((.V_to_P T) :: tl) = T :: challengeTypes tl := rfl

@[simp]
theorem messageTypes_append (p₁ p₂ : ProtocolSpec) :
    messageTypes (p₁ ++ p₂) = messageTypes p₁ ++ messageTypes p₂ := by
  induction p₁ with
  | nil => simp [messageTypes]
  | cons hd tl ih =>
    match hd with
    | .P_to_V T oi => simp [messageTypes, ih]
    | .V_to_P T => simp [messageTypes, ih]

@[simp]
theorem challengeTypes_append (p₁ p₂ : ProtocolSpec) :
    challengeTypes (p₁ ++ p₂) = challengeTypes p₁ ++ challengeTypes p₂ := by
  induction p₁ with
  | nil => simp [challengeTypes]
  | cons hd tl ih =>
    match hd with
    | .P_to_V T oi => simp [challengeTypes, ih]
    | .V_to_P T => simp [challengeTypes, ih]

/-!
## Take / drop lemmas (needed for partial transcripts and RBR soundness)
-/

@[simp]
theorem messageTypes_take_zero (pSpec : ProtocolSpec) :
    messageTypes (pSpec.take 0) = [] := rfl

@[simp]
theorem challengeTypes_take_zero (pSpec : ProtocolSpec) :
    challengeTypes (pSpec.take 0) = [] := rfl

theorem messageTypes_take_succ (pSpec : ProtocolSpec) (n : Nat) :
    messageTypes (pSpec.take (n + 1)) =
      match pSpec with
      | [] => []
      | (.P_to_V T _) :: tl => T :: messageTypes (tl.take n)
      | (.V_to_P _) :: tl => messageTypes (tl.take n) := by
  cases pSpec with
  | nil => rfl
  | cons hd tl =>
    match hd with
    | .P_to_V T oi => rfl
    | .V_to_P T => rfl

theorem challengeTypes_take_succ (pSpec : ProtocolSpec) (n : Nat) :
    challengeTypes (pSpec.take (n + 1)) =
      match pSpec with
      | [] => []
      | (.P_to_V _ _) :: tl => challengeTypes (tl.take n)
      | (.V_to_P T) :: tl => T :: challengeTypes (tl.take n) := by
  cases pSpec with
  | nil => rfl
  | cons hd tl =>
    match hd with
    | .P_to_V T oi => rfl
    | .V_to_P T => rfl

/-!
## Getters
-/

/-- Get the type at index `i`. -/
def getType (pSpec : ProtocolSpec) (i : Fin pSpec.length) : Type :=
  (pSpec.get i).type

/-!
## Counting messages and challenges
-/

/-- Count the number of prover messages in a protocol spec. -/
def messageCount : ProtocolSpec → Nat
  | [] => 0
  | (.P_to_V _ _) :: tl => messageCount tl + 1
  | (.V_to_P _) :: tl => messageCount tl

/-- Count the number of verifier challenges in a protocol spec. -/
def challengeCount : ProtocolSpec → Nat
  | [] => 0
  | (.P_to_V _ _) :: tl => challengeCount tl
  | (.V_to_P _) :: tl => challengeCount tl + 1

@[simp]
theorem length_messageTypes (pSpec : ProtocolSpec) :
    (messageTypes pSpec).length = messageCount pSpec := by
  induction pSpec with
  | nil => rfl
  | cons hd tl ih =>
    match hd with
    | .P_to_V _ _ => simp [messageTypes, messageCount, ih]
    | .V_to_P _ => simp [messageTypes, messageCount, ih]

@[simp]
theorem length_challengeTypes (pSpec : ProtocolSpec) :
    (challengeTypes pSpec).length = challengeCount pSpec := by
  induction pSpec with
  | nil => rfl
  | cons hd tl ih =>
    match hd with
    | .P_to_V _ _ => simp [challengeTypes, challengeCount, ih]
    | .V_to_P _ => simp [challengeTypes, challengeCount, ih]

/-!
## Common protocol spec constructors
-/

/-- The empty protocol specification. -/
def empty : ProtocolSpec := []

/-- A single message round (prover to verifier). -/
def singleMessage (T : Type) [oi : OracleInterface T] : ProtocolSpec := [.P_to_V T oi]

/-- A single challenge round (verifier to prover). -/
def singleChallenge (T : Type) : ProtocolSpec := [.V_to_P T]

/-- Replicate a protocol spec `n` times. -/
def replicate : Nat → ProtocolSpec → ProtocolSpec
  | 0, _ => []
  | n + 1, pSpec => pSpec ++ replicate n pSpec

@[simp]
theorem replicate_zero (pSpec : ProtocolSpec) : replicate 0 pSpec = [] := rfl

@[simp]
theorem replicate_succ (n : Nat) (pSpec : ProtocolSpec) :
    replicate (n + 1) pSpec = pSpec ++ replicate n pSpec := rfl

end ProtocolSpec
