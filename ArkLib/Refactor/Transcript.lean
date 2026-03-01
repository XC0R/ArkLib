/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.HVector
import ArkLib.Refactor.ProtocolSpec

/-!
# Transcripts, Challenges, and Messages
-/

namespace ProtocolSpec

open Round

/-! ## Type definitions -/

@[reducible] def Transcript (pSpec : ProtocolSpec) := HVector Round.type pSpec
@[reducible] def Challenges (pSpec : ProtocolSpec) := HVector id (challengeTypes pSpec)
@[reducible] def Messages (pSpec : ProtocolSpec) := HVector id (messageTypes pSpec)
@[reducible] def PartialTranscript (pSpec : ProtocolSpec) (n : Nat) :=
  HVector Round.type (pSpec.take n)

/-! ## Transcript operations -/

namespace Transcript

def nil : Transcript ([] : ProtocolSpec) := HVector.nil

def cons {tl : ProtocolSpec} {r : Round} (val : r.type) (tr : Transcript tl) :
    Transcript (r :: tl) :=
  val ::ₕ tr

def split {pSpec₁ pSpec₂ : ProtocolSpec} (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    Transcript pSpec₁ × Transcript pSpec₂ :=
  HVector.splitAt pSpec₁ tr

def join {pSpec₁ pSpec₂ : ProtocolSpec} (tr₁ : Transcript pSpec₁) (tr₂ : Transcript pSpec₂) :
    Transcript (pSpec₁ ++ pSpec₂) :=
  HVector.append tr₁ tr₂

lemma split_join {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr₁ : Transcript pSpec₁) (tr₂ : Transcript pSpec₂) :
    Transcript.split (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Transcript.join tr₁ tr₂) =
      (tr₁, tr₂) := by
  simp [Transcript.split, Transcript.join, HVector.splitAt_append]

end Transcript

/-! ## Challenges operations

`split` and `join` use structural recursion on `pSpec₁` rather than tactic-mode casts
through `challengeTypes_append`. This ensures all equalities hold definitionally,
which is critical for `OracleVerifier.comp` and downstream composition proofs. -/

namespace Challenges

def nil : Challenges ([] : ProtocolSpec) := HVector.nil

def split :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    Challenges (pSpec₁ ++ pSpec₂) → Challenges pSpec₁ × Challenges pSpec₂
  | [], _, ch => (HVector.nil, ch)
  | (.P_to_V _ _) :: tl, pSpec₂, ch => split tl pSpec₂ ch
  | (.V_to_P _) :: tl, pSpec₂, ch =>
    let (ch₁, ch₂) := split tl pSpec₂ ch.tail
    (ch.head ::ₕ ch₁, ch₂)

def join :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    Challenges pSpec₁ → Challenges pSpec₂ → Challenges (pSpec₁ ++ pSpec₂)
  | [], _, _, ch₂ => ch₂
  | (.P_to_V _ _) :: tl, pSpec₂, ch₁, ch₂ => join tl pSpec₂ ch₁ ch₂
  | (.V_to_P _) :: tl, pSpec₂, ch₁, ch₂ =>
    ch₁.head ::ₕ join tl pSpec₂ ch₁.tail ch₂

end Challenges

/-! ## Messages operations

Same structural recursion strategy as `Challenges.split/join` — `P_to_V` rounds
contribute a message element (dual to challenges where `V_to_P` contributes). -/

namespace Messages

def nil : Messages ([] : ProtocolSpec) := HVector.nil

def split :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    Messages (pSpec₁ ++ pSpec₂) → Messages pSpec₁ × Messages pSpec₂
  | [], _, msgs => (HVector.nil, msgs)
  | (.P_to_V _ _) :: tl, pSpec₂, msgs =>
    let (msgs₁, msgs₂) := split tl pSpec₂ msgs.tail
    (msgs.head ::ₕ msgs₁, msgs₂)
  | (.V_to_P _) :: tl, pSpec₂, msgs => split tl pSpec₂ msgs

def join :
    (pSpec₁ pSpec₂ : ProtocolSpec) →
    Messages pSpec₁ → Messages pSpec₂ → Messages (pSpec₁ ++ pSpec₂)
  | [], _, _, msgs₂ => msgs₂
  | (.P_to_V _ _) :: tl, pSpec₂, msgs₁, msgs₂ =>
    msgs₁.head ::ₕ join tl pSpec₂ msgs₁.tail msgs₂
  | (.V_to_P _) :: tl, pSpec₂, msgs₁, msgs₂ => join tl pSpec₂ msgs₁ msgs₂

end Messages

/-! ## Extracting messages and challenges from a transcript -/

def Transcript.toMessages :
    (pSpec : ProtocolSpec) → Transcript pSpec → Messages pSpec
  | [], _ => HVector.nil
  | (.P_to_V _ _) :: tl, tr => tr.head ::ₕ Transcript.toMessages tl tr.tail
  | (.V_to_P _) :: tl, tr => Transcript.toMessages tl tr.tail

def Transcript.toChallenges :
    (pSpec : ProtocolSpec) → Transcript pSpec → Challenges pSpec
  | [], _ => HVector.nil
  | (.P_to_V _ _) :: tl, tr => Transcript.toChallenges tl tr.tail
  | (.V_to_P _) :: tl, tr => tr.head ::ₕ Transcript.toChallenges tl tr.tail

def Transcript.ofMessagesChallenges :
    (pSpec : ProtocolSpec) → Messages pSpec → Challenges pSpec → Transcript pSpec
  | [], _, _ => HVector.nil
  | (.P_to_V _ _) :: tl, msgs, chs =>
    msgs.head ::ₕ Transcript.ofMessagesChallenges tl msgs.tail chs
  | (.V_to_P _) :: tl, msgs, chs =>
    chs.head ::ₕ Transcript.ofMessagesChallenges tl msgs chs.tail

/-! ## PartialTranscript operations -/

def PartialTranscript.empty (pSpec : ProtocolSpec) : PartialTranscript pSpec 0 := HVector.nil

def PartialTranscript.concat :
    (pSpec : ProtocolSpec) → {n : Nat} → (h : n < pSpec.length) →
    PartialTranscript pSpec n → (pSpec[n]).type → PartialTranscript pSpec (n + 1)
  | _ :: _, 0, _, _, val => val ::ₕ HVector.nil
  | hd :: rest, n + 1, h, tr, val =>
    have : (hd :: rest).length = rest.length + 1 := List.length_cons
    tr.head ::ₕ PartialTranscript.concat rest (by omega) tr.tail val

def PartialTranscript.toFull {pSpec : ProtocolSpec}
    (tr : PartialTranscript pSpec pSpec.length) : Transcript pSpec := by
  simp only [PartialTranscript, List.take_length] at tr
  exact tr

def Transcript.toPartial {pSpec : ProtocolSpec}
    (tr : Transcript pSpec) : PartialTranscript pSpec pSpec.length := by
  simp only [PartialTranscript, List.take_length]
  exact tr

def PartialTranscript.ofTranscript {pSpec : ProtocolSpec} (tr : Transcript pSpec) :
    PartialTranscript pSpec pSpec.length := by
  simp only [PartialTranscript, List.take_length]
  exact tr

def PartialTranscript.take {pSpec : ProtocolSpec} {n : Nat}
    (m : Nat) (tr : PartialTranscript pSpec n) :
    PartialTranscript pSpec (min m n) := by
  simp only [PartialTranscript]
  rw [← List.take_take]
  exact HVector.take m (pSpec.take n) tr

private lemma cast_cons_hvector {r : Round} {l₁ l₂ : List Round}
    (h : l₁ = l₂) (hd : r.type) (tltr : HVector Round.type l₁) :
    (hd, cast (congrArg (fun l => HVector Round.type l) h) tltr) =
      cast (congrArg (fun l => HVector Round.type (r :: l)) h) (hd, tltr) := by
  cases h
  rfl

lemma hvector_take_length_eq {pSpec : ProtocolSpec} (tr : Transcript pSpec) :
    HVector.take pSpec.length pSpec tr = PartialTranscript.ofTranscript tr := by
  induction pSpec with
  | nil =>
      cases tr
      rfl
  | cons r tl ih =>
      cases tr with
      | mk hd tltr =>
          simpa [HVector.take, PartialTranscript.ofTranscript, ih tltr, List.take_length]
            using cast_cons_hvector (h := (List.take_length (l := tl)).symm) hd tltr

lemma hvector_take_succ_eq_concat {pSpec : ProtocolSpec}
    (k : Nat) (hk : k < pSpec.length) (tr : Transcript pSpec) :
    HVector.take (k + 1) pSpec tr =
      PartialTranscript.concat pSpec hk (HVector.take k pSpec tr)
        (HVector.get pSpec tr ⟨k, hk⟩) := by
  induction pSpec generalizing k with
  | nil =>
      cases hk
  | cons r tl ih =>
      cases k with
      | zero =>
          cases tr
          simp [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons]
      | succ k =>
          cases tr with
          | mk hd tltr =>
              have hk' : k < tl.length := by simpa using hk
              simpa [HVector.take, PartialTranscript.concat, HVector.get, HVector.cons,
                HVector.head, HVector.tail] using
                congrArg (fun t => (hd, t)) (ih k hk' tltr)

end ProtocolSpec
