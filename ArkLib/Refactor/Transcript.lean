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

@[simp] theorem Transcript.toMessages_ofMessagesChallenges
    (pSpec : ProtocolSpec) (msgs : Messages pSpec) (chs : Challenges pSpec) :
    Transcript.toMessages pSpec (Transcript.ofMessagesChallenges pSpec msgs chs) = msgs := by
  induction pSpec with
  | nil =>
      rfl
  | cons r tl ih =>
      cases r <;> simp [Transcript.toMessages, Transcript.ofMessagesChallenges, ih]

@[simp] theorem Transcript.toChallenges_ofMessagesChallenges
    (pSpec : ProtocolSpec) (msgs : Messages pSpec) (chs : Challenges pSpec) :
    Transcript.toChallenges pSpec (Transcript.ofMessagesChallenges pSpec msgs chs) = chs := by
  induction pSpec with
  | nil =>
      rfl
  | cons r tl ih =>
      cases r <;> simp [Transcript.toChallenges, Transcript.ofMessagesChallenges, ih]

@[simp] theorem Transcript.ofMessagesChallenges_toMessages_toChallenges
    (pSpec : ProtocolSpec) (tr : Transcript pSpec) :
    Transcript.ofMessagesChallenges pSpec (Transcript.toMessages pSpec tr)
      (Transcript.toChallenges pSpec tr) = tr := by
  induction pSpec with
  | nil =>
      rfl
  | cons r tl ih =>
      cases r <;> cases tr <;>
        simp [Transcript.toMessages, Transcript.toChallenges, Transcript.ofMessagesChallenges, ih]

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

/-- View a partial transcript of `pSpec₁ ++ pSpec₂` (length `k ≤ |pSpec₁|`)
as a partial transcript of `pSpec₁`. -/
def PartialTranscript.leftOfAppend
    {pSpec₁ pSpec₂ : ProtocolSpec} {k : Nat}
    (hk : k ≤ pSpec₁.length)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k) :
    PartialTranscript pSpec₁ k := by
  induction pSpec₁ generalizing k with
  | nil =>
      cases k with
      | zero =>
          exact HVector.nil
      | succ k =>
          exact False.elim (Nat.not_succ_le_zero _ hk)
  | cons r tl ih =>
      cases k with
      | zero =>
          exact HVector.nil
      | succ k =>
          have hk' : k ≤ tl.length := Nat.succ_le_succ_iff.mp hk
          exact tr.head ::ₕ ih hk' tr.tail

/-- Extract the full left transcript from a partial transcript of `pSpec₁ ++ pSpec₂`
once we have seen at least `|pSpec₁|` rounds. -/
def PartialTranscript.leftFullOfAppend
    {pSpec₁ pSpec₂ : ProtocolSpec} {k : Nat}
    (hk : pSpec₁.length ≤ k)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k) :
    Transcript pSpec₁ := by
  induction pSpec₁ generalizing k with
  | nil =>
      exact HVector.nil
  | cons r tl ih =>
      cases k with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero _ hk)
      | succ k =>
          have hk' : tl.length ≤ k := Nat.succ_le_succ_iff.mp hk
          exact tr.head ::ₕ ih hk' tr.tail

/-- Extract the right partial transcript from a partial transcript of `pSpec₁ ++ pSpec₂`
once we have seen at least `|pSpec₁|` rounds. Returns a partial transcript of `pSpec₂`
at the given local index `j`, with `j + |pSpec₁| = k`. -/
def PartialTranscript.rightOfAppend
    {pSpec₁ pSpec₂ : ProtocolSpec} {k j : Nat}
    (h_eq : j + pSpec₁.length = k)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k) :
    PartialTranscript pSpec₂ j := by
  induction pSpec₁ generalizing k j with
  | nil => subst h_eq; exact tr
  | cons r tl ih =>
      cases k with
      | zero => simp [List.length_cons] at h_eq
      | succ k => exact ih (by simp [List.length_cons] at h_eq; omega) tr.tail

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

/-! ## Splitting lemmas for PartialTranscript operations -/

/-- Adding an element at position `k ≥ |pSpec₁|` does not change `leftFullOfAppend`. -/
theorem PartialTranscript.leftFullOfAppend_concat
    {pSpec₁ pSpec₂ : ProtocolSpec} {k : Nat}
    (hk₁ : pSpec₁.length ≤ k) (hk₂ : k < (pSpec₁ ++ pSpec₂).length)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k)
    (msg : ((pSpec₁ ++ pSpec₂)[k]'hk₂).type) :
    PartialTranscript.leftFullOfAppend (show pSpec₁.length ≤ k + 1 by omega)
      (PartialTranscript.concat (pSpec₁ ++ pSpec₂) hk₂ tr msg) =
    PartialTranscript.leftFullOfAppend hk₁ tr := by
  induction pSpec₁ generalizing k with
  | nil => rfl
  | cons r tl ih =>
    cases k with
    | zero => exact absurd hk₁ (by simp [List.length_cons])
    | succ k =>
      have hk₁' : tl.length ≤ k := by simp [List.length_cons] at hk₁; omega
      have hk₂' : k < (tl ++ pSpec₂).length := by
        simp only [List.cons_append, List.length_cons] at hk₂; omega
      change tr.head ::ₕ _ = tr.head ::ₕ _
      exact congrArg (tr.head ::ₕ ·) (ih hk₁' hk₂' tr.tail msg)

/-- Adding an element at position `k < |pSpec₁|` in `pSpec₁ ++ pSpec₂` corresponds to
adding it at position `k` in the left part extracted by `leftOfAppend`. -/
theorem PartialTranscript.leftOfAppend_concat
    {pSpec₁ pSpec₂ : ProtocolSpec} {k : Nat}
    (hk : k < pSpec₁.length)
    (hk₂ : k < (pSpec₁ ++ pSpec₂).length)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k)
    (msg : ((pSpec₁ ++ pSpec₂)[k]'hk₂).type) :
    PartialTranscript.leftOfAppend (show k + 1 ≤ pSpec₁.length by omega)
      (PartialTranscript.concat (pSpec₁ ++ pSpec₂) hk₂ tr msg) =
    PartialTranscript.concat pSpec₁ hk
      (PartialTranscript.leftOfAppend (show k ≤ pSpec₁.length by omega) tr)
      (cast (by
        exact congrArg Round.type (List.getElem_append_left (h' := hk₂) hk)) msg) := by
  induction pSpec₁ generalizing k with
  | nil => exact absurd hk (by simp)
  | cons r tl ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hk' : k < tl.length := by simp [List.length_cons] at hk; omega
      have hk₂' : k < (tl ++ pSpec₂).length := by
        simp only [List.cons_append, List.length_cons] at hk₂; omega
      change tr.head ::ₕ _ = tr.head ::ₕ _
      exact congrArg (tr.head ::ₕ ·) (ih hk' hk₂' tr.tail msg)

/-- Adding an element at position `k ≥ |pSpec₁|` in `pSpec₁ ++ pSpec₂` corresponds to
adding it at position `j + 1` in the right part extracted by `rightOfAppend`. -/
theorem PartialTranscript.rightOfAppend_concat
    {pSpec₁ pSpec₂ : ProtocolSpec} {k j : Nat}
    (h_eq : j + pSpec₁.length = k) (hk₂ : k < (pSpec₁ ++ pSpec₂).length)
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) k)
    (msg : ((pSpec₁ ++ pSpec₂)[k]'hk₂).type) :
    rightOfAppend (show (j + 1) + pSpec₁.length = k + 1 by omega)
      (concat (pSpec₁ ++ pSpec₂) hk₂ tr msg) =
    concat pSpec₂ (show j < pSpec₂.length by
        simp [List.length_append] at hk₂; omega)
      (rightOfAppend h_eq tr)
      (cast (congrArg Round.type (by
        rw [List.getElem_append_right (h₂ := hk₂) (show pSpec₁.length ≤ k by omega)]
        congr 1; omega)) msg) := by
  induction pSpec₁ generalizing k j with
  | nil => subst h_eq; rfl
  | cons r tl ih =>
    cases k with
    | zero => simp [List.length_cons] at h_eq
    | succ k =>
        have hlen : ((r :: tl) ++ pSpec₂).length = (tl ++ pSpec₂).length + 1 := by
          simp [List.length_append, List.length_cons]
        exact ih (by simp [List.length_cons] at h_eq; omega)
          (by omega) tr.tail msg

/-! ## Bridge lemmas for composition -/

@[simp] lemma PartialTranscript.ofTranscript_cons {r : Round} {tl : ProtocolSpec}
    (tr : Transcript (r :: tl)) :
    ofTranscript tr = tr.head ::ₕ ofTranscript tr.tail := by
  cases tr with
  | mk hd tltr =>
    exact (cast_cons_hvector List.take_length.symm hd tltr).symm

/-- At `k = pSpec₁.length`, `leftOfAppend` equals `ofTranscript (leftFullOfAppend ...)`. -/
theorem PartialTranscript.leftOfAppend_eq_ofTranscript_leftFullOfAppend
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr : PartialTranscript (pSpec₁ ++ pSpec₂) pSpec₁.length) :
    leftOfAppend le_rfl tr =
      ofTranscript (leftFullOfAppend le_rfl tr) := by
  induction pSpec₁ with
  | nil => rfl
  | cons r tl ih =>
    simp only [leftOfAppend, leftFullOfAppend, ofTranscript_cons]
    exact congrArg (tr.head ::ₕ ·) (ih tr.tail)

/-- `leftFullOfAppend` applied to a full transcript is the first component of `split`. -/
theorem PartialTranscript.leftFullOfAppend_ofTranscript_eq_split_fst
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    leftFullOfAppend (by simp)
      (ofTranscript tr) =
    (Transcript.split tr).1 := by
  induction pSpec₁ with
  | nil => rfl
  | cons r tl ih =>
    simp only [List.cons_append, ofTranscript_cons, leftFullOfAppend,
      Transcript.split, HVector.splitAt]
    exact congrArg (tr.head ::ₕ ·) (ih tr.tail)

/-- `rightOfAppend` applied to a full transcript at local index `|pSpec₂|`
is `ofTranscript` of the second component of `split`. -/
theorem PartialTranscript.rightOfAppend_ofTranscript_eq_split_snd
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    rightOfAppend (show pSpec₂.length + pSpec₁.length = (pSpec₁ ++ pSpec₂).length by
        simp [List.length_append]; omega)
      (ofTranscript tr) =
    ofTranscript (Transcript.split tr).2 := by
  induction pSpec₁ with
  | nil => rfl
  | cons r tl ih =>
    simp only [List.cons_append, ofTranscript_cons, rightOfAppend,
      List.length_cons, Transcript.split, HVector.splitAt]
    exact ih tr.tail

/-! ## HVector.take bridge lemmas for composition -/

/-- Projecting `HVector.take k` of an appended transcript to `pSpec₁` yields
`HVector.take k` of the split's first component, when `k ≤ |pSpec₁|`. -/
theorem PartialTranscript.leftOfAppend_hvector_take {pSpec₁ pSpec₂ : ProtocolSpec}
    (k : Nat) (hk : k ≤ pSpec₁.length)
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    leftOfAppend hk (HVector.take k (pSpec₁ ++ pSpec₂) tr) =
      HVector.take k pSpec₁ (Transcript.split tr).1 := by
  induction pSpec₁ generalizing k with
  | nil =>
      cases k with
      | zero => rfl
      | succ k => exact False.elim (Nat.not_succ_le_zero _ hk)
  | cons r tl ih =>
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : k ≤ tl.length := Nat.succ_le_succ_iff.mp hk
          exact congrArg (tr.head ::ₕ ·) (ih k hk' tr.tail)

/-- Extracting the full left part from `HVector.take k` (with `k ≥ |pSpec₁|`)
yields the first component of `split`. -/
theorem PartialTranscript.leftFullOfAppend_hvector_take {pSpec₁ pSpec₂ : ProtocolSpec}
    (k : Nat) (hk : pSpec₁.length ≤ k) (hk₂ : k ≤ (pSpec₁ ++ pSpec₂).length)
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    leftFullOfAppend hk (HVector.take k (pSpec₁ ++ pSpec₂) tr) =
      (Transcript.split tr).1 := by
  induction pSpec₁ generalizing k with
  | nil => rfl
  | cons r tl ih =>
      cases k with
      | zero => exact False.elim (Nat.not_succ_le_zero _ hk)
      | succ k =>
          have hk' : tl.length ≤ k := Nat.succ_le_succ_iff.mp hk
          have hk₂' : k ≤ (tl ++ pSpec₂).length := by
            simp only [List.length_append, List.length_cons] at hk₂ ⊢; omega
          simp only [leftFullOfAppend, List.length_cons, List.cons_append, HVector.take,
            List.append_eq, List.length_nil, List.nil_append, Transcript.split, HVector.splitAt]
          exact congrArg (tr.head ::ₕ ·) (ih k hk' hk₂' tr.tail)

lemma PartialTranscript.rightOfAppend_hvector_take_aux {pSpec₁ pSpec₂ : ProtocolSpec}
    (k j : Nat) (h_eq : j + pSpec₁.length = k) (hk₂ : k ≤ (pSpec₁ ++ pSpec₂).length)
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    PartialTranscript.rightOfAppend h_eq (HVector.take k (pSpec₁ ++ pSpec₂) tr) =
      HVector.take j pSpec₂ (Transcript.split tr).2 := by
  induction pSpec₁ generalizing k j with
  | nil =>
      subst h_eq
      rfl
  | cons r tl ih =>
      cases k with
      | zero => simp [List.length_cons] at h_eq
      | succ k =>
          have h_eq' : j + tl.length = k := by simp [List.length_cons] at h_eq; omega
          have hk₂' : k ≤ (tl ++ pSpec₂).length := by
            simp only [List.length_append, List.length_cons] at hk₂ ⊢; omega
          exact ih k j h_eq' hk₂' tr.tail

/-- Extracting the right partial transcript from `HVector.take k` (with `k ≥ |pSpec₁|`)
yields `HVector.take (k - |pSpec₁|)` of the split's second component. -/
theorem PartialTranscript.rightOfAppend_hvector_take {pSpec₁ pSpec₂ : ProtocolSpec}
    (k : Nat) (hk : pSpec₁.length ≤ k) (hk₂ : k ≤ (pSpec₁ ++ pSpec₂).length)
    (tr : Transcript (pSpec₁ ++ pSpec₂)) :
    rightOfAppend (show (k - pSpec₁.length) + pSpec₁.length = k by omega)
      (HVector.take k (pSpec₁ ++ pSpec₂) tr) =
      HVector.take (k - pSpec₁.length) pSpec₂ (Transcript.split tr).2 := by
  exact rightOfAppend_hvector_take_aux k (k - pSpec₁.length) (by omega) hk₂ tr

end ProtocolSpec
