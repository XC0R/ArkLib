/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.HVector
import ArkLib.Refactor.ProtocolSpec

/-!
# Transcripts, Challenges, and Messages

This file defines the transcript types for the list-based protocol specification model:

- `Transcript pSpec`: the full transcript of an interactive protocol, as an `HVector` over
  each round's type.
- `Challenges pSpec`: the tuple of all verifier challenges, as an `HVector id` over the
  challenge type list.
- `Messages pSpec`: the tuple of all prover messages, as an `HVector id` over the
  message type list.
- `PartialTranscript pSpec n`: the transcript up to round `n`, defined via `List.take`.
- `PartialTranscript.concat`: append a single round's value to a partial transcript,
  defined by structural recursion (no `▸` casts).
-/

namespace ProtocolSpec

/-!
## Full transcript
-/

/-- A full transcript of an interactive protocol: one value of type `round.type` for each
round in the protocol spec. -/
def Transcript (pSpec : ProtocolSpec) := HVector Round.type pSpec

/-- The tuple of all verifier challenges. -/
def Challenges (pSpec : ProtocolSpec) := HVector id pSpec.challengeTypes

/-- The tuple of all prover messages. -/
def Messages (pSpec : ProtocolSpec) := HVector id pSpec.messageTypes

/-!
## Partial transcripts (via `List.take`)
-/

/-- A partial transcript up to round `n` (0-indexed). Uses `List.take` for clean
definitional reduction:
- `[].take n = []`
- `l.take 0 = []`
- `(a :: l).take (n+1) = a :: l.take n`
-/
def PartialTranscript (pSpec : ProtocolSpec) (n : Nat) :=
  HVector Round.type (pSpec.take n)

/-- The full transcript is the partial transcript at round `pSpec.length`. -/
theorem Transcript_eq_PartialTranscript_length (pSpec : ProtocolSpec) :
    Transcript pSpec = PartialTranscript pSpec pSpec.length := by
  simp [Transcript, PartialTranscript, List.take_length]

/-!
## Partial challenges and messages
-/

/-- Challenges up to round `n`. -/
def PartialChallenges (pSpec : ProtocolSpec) (n : Nat) :=
  HVector id (pSpec.take n).challengeTypes

/-- Messages up to round `n`. -/
def PartialMessages (pSpec : ProtocolSpec) (n : Nat) :=
  HVector id (pSpec.take n).messageTypes

/-!
## Constructing transcripts
-/

namespace Transcript

/-- The empty transcript for the empty protocol spec. -/
def nil : Transcript [] := .nil

/-- Prepend a value to a transcript. -/
def cons {r : Round} (val : r.type) (tr : Transcript tl) :
    Transcript (r :: tl) :=
  .cons val tr

/-- Split a transcript for `pSpec₁ ++ pSpec₂` into two transcripts. -/
def split {pSpec₁ pSpec₂ : ProtocolSpec} (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    Transcript pSpec₁ × Transcript pSpec₂ :=
  HVector.splitAt pSpec₁ tr

/-- Join two transcripts. -/
def join {pSpec₁ pSpec₂ : ProtocolSpec} (tr₁ : Transcript pSpec₁) (tr₂ : Transcript pSpec₂) :
    Transcript (pSpec₁ ++ pSpec₂) :=
  tr₁ ++ tr₂

end Transcript

/-!
## Constructing challenges
-/

namespace Challenges

/-- The empty challenges. -/
def nil : Challenges [] := .nil

/-- Prepend a challenge for a V_to_P round. -/
def consChallenge {T : Type} (val : T) (ch : Challenges tl) :
    Challenges (.V_to_P T :: tl) :=
  .cons val ch

/-- Skip a P_to_V round (no challenge). -/
def skipMessage {T : Type} {oi : OracleInterface T} (ch : Challenges tl) :
    Challenges (.P_to_V T oi :: tl) := ch

/-- Split challenges for `pSpec₁ ++ pSpec₂`. -/
def split {pSpec₁ pSpec₂ : ProtocolSpec} (ch : Challenges (pSpec₁ ++ pSpec₂)) :
    Challenges pSpec₁ × Challenges pSpec₂ := by
  rw [Challenges, challengeTypes_append] at ch
  exact HVector.splitAt pSpec₁.challengeTypes ch

/-- Join challenges. -/
def join {pSpec₁ pSpec₂ : ProtocolSpec} (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    Challenges (pSpec₁ ++ pSpec₂) := by
  simp only [Challenges, challengeTypes_append]
  exact ch₁ ++ ch₂

end Challenges

/-!
## Constructing messages
-/

namespace Messages

/-- The empty messages. -/
def nil : Messages [] := .nil

/-- Prepend a message for a P_to_V round. -/
def consMessage {T : Type} {oi : OracleInterface T} (val : T) (msgs : Messages tl) :
    Messages (.P_to_V T oi :: tl) :=
  .cons val msgs

/-- Skip a V_to_P round (no message). -/
def skipChallenge {T : Type} (msgs : Messages tl) :
    Messages (.V_to_P T :: tl) := msgs

/-- Split messages for `pSpec₁ ++ pSpec₂`. -/
def split {pSpec₁ pSpec₂ : ProtocolSpec} (msgs : Messages (pSpec₁ ++ pSpec₂)) :
    Messages pSpec₁ × Messages pSpec₂ := by
  rw [Messages, messageTypes_append] at msgs
  exact HVector.splitAt pSpec₁.messageTypes msgs

/-- Join messages. -/
def join {pSpec₁ pSpec₂ : ProtocolSpec}
    (msgs₁ : Messages pSpec₁) (msgs₂ : Messages pSpec₂) :
    Messages (pSpec₁ ++ pSpec₂) := by
  simp only [Messages, messageTypes_append]
  exact msgs₁ ++ msgs₂

end Messages

/-!
## Extracting messages and challenges from a transcript
-/

/-- Extract the prover messages from a full transcript. -/
def Transcript.toMessages : {pSpec : ProtocolSpec} → Transcript pSpec → Messages pSpec
  | [], .nil => .nil
  | (.P_to_V _ _) :: _, .cons val tr => .cons val tr.toMessages
  | (.V_to_P _) :: _, .cons _ tr => tr.toMessages

/-- Extract the verifier challenges from a full transcript. -/
def Transcript.toChallenges : {pSpec : ProtocolSpec} → Transcript pSpec → Challenges pSpec
  | [], .nil => .nil
  | (.P_to_V _ _) :: _, .cons _ tr => tr.toChallenges
  | (.V_to_P _) :: _, .cons val tr => .cons val tr.toChallenges

/-- Reconstruct a transcript from messages and challenges. -/
def Transcript.ofMessagesChallenges :
    {pSpec : ProtocolSpec} → Messages pSpec → Challenges pSpec → Transcript pSpec
  | [], .nil, .nil => .nil
  | (.P_to_V _ _) :: _, .cons msg msgs, chs =>
    .cons msg (ofMessagesChallenges msgs chs)
  | (.V_to_P _) :: _, msgs, .cons ch chs =>
    .cons ch (ofMessagesChallenges msgs chs)

/-!
## PartialTranscript.concat — by structural recursion, no `▸` casts
-/

/-- Append a single round's value to a partial transcript, going from round `n` to round `n+1`.
Defined by structural recursion on the protocol spec and round number, so it reduces
definitionally without any cast lemmas. -/
def PartialTranscript.concat :
    {pSpec : ProtocolSpec} → {n : Nat} → (h : n < pSpec.length) →
    PartialTranscript pSpec n → (pSpec[n]).type → PartialTranscript pSpec (n + 1)
  | _ :: _, 0, _, .nil, val => .cons val .nil
  | _ :: rest, n + 1, h, .cons x xs, val =>
    .cons x (concat (by omega) xs val)

/-- The empty partial transcript at round 0. -/
def PartialTranscript.empty (pSpec : ProtocolSpec) : PartialTranscript pSpec 0 := .nil

/-- Convert a partial transcript at round `pSpec.length` to a full transcript. -/
def PartialTranscript.toFull {pSpec : ProtocolSpec}
    (tr : PartialTranscript pSpec pSpec.length) : Transcript pSpec := by
  simp [PartialTranscript, List.take_length] at tr
  exact tr

/-- Convert a full transcript to a partial transcript at round `pSpec.length`. -/
def Transcript.toPartial {pSpec : ProtocolSpec}
    (tr : Transcript pSpec) : PartialTranscript pSpec pSpec.length := by
  simp [PartialTranscript, List.take_length]
  exact tr

/-!
## PartialTranscript take/drop
-/

/-- Take fewer rounds from a partial transcript. -/
def PartialTranscript.take {pSpec : ProtocolSpec} (m : Nat) (tr : PartialTranscript pSpec n) :
    PartialTranscript pSpec (min m n) := by
  simp only [PartialTranscript]
  rw [List.take_take]
  exact tr

end ProtocolSpec
