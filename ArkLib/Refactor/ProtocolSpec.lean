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

/-- Whether a round is a verifier challenge (`V_to_P`) round. -/
def isChallenge : Round → Bool
  | .V_to_P _ => true
  | .P_to_V _ _ => false

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

/-- Construct a prover message round, inferring the `OracleInterface` instance.
`abbrev` so that instance synthesis can see through to `.P_to_V`. -/
abbrev msg (T : Type) [oi : OracleInterface T] : Round := .P_to_V T oi

/-- Construct a verifier challenge round.
`abbrev` so that instance synthesis can see through to `.V_to_P`. -/
abbrev chal (T : Type) : Round := .V_to_P T

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

/-!
## Challenge indices
-/

/-- Index type for verifier-challenge (`V_to_P`) rounds in a protocol spec. -/
def ChallengeIndex (pSpec : ProtocolSpec) : Type :=
  { i : Fin pSpec.length // (pSpec.get i).isChallenge = true }

instance (pSpec : ProtocolSpec) : Fintype (ChallengeIndex pSpec) :=
  Subtype.fintype _

namespace ChallengeIndex

variable {pSpec₁ pSpec₂ : ProtocolSpec}

lemma leftIndexLt (i : Fin pSpec₁.length) :
    i.1 < (pSpec₁ ++ pSpec₂).length := by
  simpa [List.length_append] using
    Nat.lt_of_lt_of_le i.2 (Nat.le_add_right pSpec₁.length pSpec₂.length)

set_option linter.unnecessarySimpa false in
lemma rightIndexLt' (i : Fin pSpec₂.length) :
    pSpec₁.length + i.1 < (pSpec₁ ++ pSpec₂).length := by
  simpa [List.length_append] using Nat.add_lt_add_left i.2 pSpec₁.length

lemma get_eq_left (i : Fin (pSpec₁ ++ pSpec₂).length) (h : i.1 < pSpec₁.length) :
    (pSpec₁ ++ pSpec₂).get i = pSpec₁.get ⟨i.1, h⟩ := by
  simpa [List.get_eq_getElem] using
    (List.getElem_append_left (as := pSpec₁) (bs := pSpec₂) (i := i.1) h)

lemma rightIndexLt (i : Fin (pSpec₁ ++ pSpec₂).length) (h : pSpec₁.length ≤ i.1) :
    i.1 - pSpec₁.length < pSpec₂.length := by
  have hi : i.1 < pSpec₁.length + pSpec₂.length := by
    simpa [List.length_append] using i.2
  omega

lemma get_eq_right (i : Fin (pSpec₁ ++ pSpec₂).length) (h : pSpec₁.length ≤ i.1) :
    (pSpec₁ ++ pSpec₂).get i = pSpec₂.get ⟨i.1 - pSpec₁.length, rightIndexLt (i := i) h⟩ := by
  simpa [List.get_eq_getElem, rightIndexLt (i := i) h] using
    (List.getElem_append_right (as := pSpec₁) (bs := pSpec₂) (i := i.1) h)

/-- Inject a left challenge index into the appended protocol. -/
def appendLeft (i : ChallengeIndex pSpec₁) : ChallengeIndex (pSpec₁ ++ pSpec₂) := by
  refine ⟨⟨i.1, leftIndexLt (pSpec₂ := pSpec₂) i.1⟩, ?_⟩
  have hEqRound :
      (pSpec₁ ++ pSpec₂).get ⟨i.1, leftIndexLt (pSpec₂ := pSpec₂) i.1⟩ = pSpec₁.get i.1 :=
    get_eq_left (pSpec₂ := pSpec₂) (i := ⟨i.1, leftIndexLt (pSpec₂ := pSpec₂) i.1⟩) i.1.2
  have hchal := i.2
  rw [← hEqRound] at hchal
  exact hchal

/-- Inject a right challenge index into the appended protocol. -/
def appendRight (i : ChallengeIndex pSpec₂) : ChallengeIndex (pSpec₁ ++ pSpec₂) := by
  refine ⟨⟨pSpec₁.length + i.1, rightIndexLt' (pSpec₁ := pSpec₁) i.1⟩, ?_⟩
  have hEqRound :
      (pSpec₁ ++ pSpec₂).get ⟨pSpec₁.length + i.1, rightIndexLt' (pSpec₁ := pSpec₁) i.1⟩ =
        pSpec₂.get i.1 := by
    have hge : pSpec₁.length ≤ pSpec₁.length + i.1 := Nat.le_add_right _ _
    set_option linter.unnecessarySimpa false in
    simpa using get_eq_right (pSpec₁ := pSpec₁)
      (i := ⟨pSpec₁.length + i.1, rightIndexLt' (pSpec₁ := pSpec₁) i.1⟩) hge
  have hchal := i.2
  rw [← hEqRound] at hchal
  exact hchal

/-- Project an appended challenge index to the left component (requires left-location proof). -/
def toLeft (i : ChallengeIndex (pSpec₁ ++ pSpec₂)) (h : i.1 < pSpec₁.length) :
    ChallengeIndex pSpec₁ := by
  refine ⟨⟨i.1, h⟩, ?_⟩
  have hEqRound : (pSpec₁ ++ pSpec₂).get i.1 = pSpec₁.get ⟨i.1, h⟩ := get_eq_left (i := i.1) h
  have hchal := i.2
  rw [hEqRound] at hchal
  exact hchal

/-- Project an appended challenge index to the right component (requires right-location proof). -/
def toRight (i : ChallengeIndex (pSpec₁ ++ pSpec₂)) (h : pSpec₁.length ≤ i.1) :
    ChallengeIndex pSpec₂ := by
  refine ⟨⟨i.1 - pSpec₁.length, rightIndexLt (i := i.1) h⟩, ?_⟩
  have hEqRound :
      (pSpec₁ ++ pSpec₂).get i.1 = pSpec₂.get ⟨i.1 - pSpec₁.length, rightIndexLt (i := i.1) h⟩ :=
    get_eq_right (i := i.1) h
  have hchal := i.2
  rw [hEqRound] at hchal
  exact hchal

/-- Split an appended challenge index into left/right components. -/
def split (i : ChallengeIndex (pSpec₁ ++ pSpec₂)) :
    Sum (ChallengeIndex pSpec₁) (ChallengeIndex pSpec₂) :=
  if h : i.1 < pSpec₁.length then
    .inl (toLeft (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i h)
  else
    .inr (toRight (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i (Nat.le_of_not_lt h))

@[simp] lemma split_appendLeft (i : ChallengeIndex pSpec₁) :
    split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      (appendLeft (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i) = .inl i := by
  unfold split
  simp [appendLeft, toLeft]

@[simp] lemma split_appendRight (i : ChallengeIndex pSpec₂) :
    split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      (appendRight (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i) = .inr i := by
  unfold split
  simp [appendRight, toRight]

/-- Split a challenge index in `replicate (n+1)` into either the first copy or
the tail `replicate n`. -/
def splitReplicate {pSpec : ProtocolSpec} (n : Nat)
    (i : ChallengeIndex (pSpec.replicate (n + 1))) :
    Sum (ChallengeIndex pSpec) (ChallengeIndex (pSpec.replicate n)) := by
  simpa [ProtocolSpec.replicate] using
    (split (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n) i)

@[simp] lemma splitReplicate_inl {pSpec : ProtocolSpec} (n : Nat)
    (i : ChallengeIndex pSpec) :
    splitReplicate (pSpec := pSpec) n
      (appendLeft (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n) i) = .inl i := by
  unfold splitReplicate
  simp

@[simp] lemma splitReplicate_inr {pSpec : ProtocolSpec} (n : Nat)
    (i : ChallengeIndex (pSpec.replicate n)) :
    splitReplicate (pSpec := pSpec) n
      (appendRight (pSpec₁ := pSpec) (pSpec₂ := pSpec.replicate n) i) = .inr i := by
  unfold splitReplicate
  simp

end ChallengeIndex

end ProtocolSpec
