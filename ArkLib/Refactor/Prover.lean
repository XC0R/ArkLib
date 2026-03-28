/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Transcript

/-!
# Prover

`Prover m Output pSpec` is the coinductive prover type defined by structural recursion
on `ProtocolSpec`. For each round:
- `P_to_V`: produces a message and (monadically) continues
- `V_to_P`: receives a challenge and (monadically) continues
- At the end: returns the output

`HonestProver` wraps `Prover` with statement/witness input.

## Main definitions

- `Prover` — the core coinductive type
- `Prover.run` — execute with pre-sampled challenges
- `Prover.comp` — sequential composition of two provers
- `Prover.iterate` — `n`-fold composition (same spec, same state type)
- `HonestProver` — prover with statement/witness input
- `HonestProver.comp` — sequential composition of honest provers
- `HonestProver.compNth` — `n`-fold composition of honest provers
-/

namespace ProtocolSpec

/-- Coinductive prover type, defined by structural recursion on the protocol spec. -/
def Prover (m : Type → Type) (Output : Type) : ProtocolSpec → Type
  | [] => Output
  | (.P_to_V T _) :: tl => T × m (Prover m Output tl)
  | (.V_to_P T) :: tl => T → m (Prover m Output tl)

namespace Prover

/-- Run a prover with pre-sampled challenges, producing a transcript and output. -/
def run {m : Type → Type} [Monad m] {Output : Type} :
    (pSpec : ProtocolSpec) → Prover m Output pSpec → Challenges pSpec →
    m (Transcript pSpec × Output)
  | [], output, _ => pure (HVector.nil, output)
  | (.P_to_V _ _) :: tl, prover, challenges => do
    let (msg, cont) := prover
    let next ← cont
    let (tr, out) ← run tl next challenges
    return (msg ::ₕ tr, out)
  | (.V_to_P _) :: tl, prover, challenges => do
    let next ← prover challenges.head
    let (tr, out) ← run tl next challenges.tail
    return (challenges.head ::ₕ tr, out)

/-- Compose two provers sequentially: the first prover's output is fed into `f` to
produce the second prover. The resulting prover handles `pSpec₁ ++ pSpec₂` by
threading the continuation through each round of `pSpec₁`, then starting `pSpec₂`. -/
def comp {m : Type → Type} [Monad m] {Mid Output : Type} {pSpec₂ : ProtocolSpec} :
    (pSpec₁ : ProtocolSpec) →
    Prover m Mid pSpec₁ → (Mid → m (Prover m Output pSpec₂)) →
    m (Prover m Output (pSpec₁ ++ pSpec₂))
  | [], output, f => f output
  | (.P_to_V _ _) :: tl, prover, f =>
    let (msg, cont) := prover
    pure (msg, do let next ← cont; comp tl next f)
  | (.V_to_P _) :: tl, prover, f =>
    pure fun chal => do let next ← prover chal; comp tl next f

/-- Iterate a prover step `n` times, composing the same protocol spec repeatedly.
Used for protocols like sumcheck where a single round is repeated `n` times. -/
def iterate {m : Type → Type} [Monad m] {S : Type} :
    (pSpec : ProtocolSpec) → (n : Nat) →
    (S → m (Prover m S pSpec)) → S →
    m (Prover m S (pSpec.replicate n))
  | _, 0, _, s => pure s
  | pSpec, n + 1, step, s => do
    let p ← step s
    comp pSpec p (fun mid => iterate pSpec n step mid)

lemma run_comp_join {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        return (Transcript.join tr₁ tr₂, out)) := by
  revert prover₁ ch₁
  induction pSpec₁ with
  | nil =>
      intro prover₁ ch₁
      simp [Prover.comp, Prover.run, Challenges.join, Transcript.join, HVector.append]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover₁ ch₁
          rcases prover₁ with ⟨msg, cont⟩
          simp only [List.cons_append, comp, List.append_eq, Challenges.join, run, bind_pure_comp,
            pure_bind, bind_assoc, Transcript.join, bind_map_left]
          refine congrArg (fun k => cont >>= k) ?_
          funext next
          simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
            congrArg (fun z =>
              (fun a : Transcript (tl ++ pSpec₂) × Output =>
                (Transcript.cons (r := .P_to_V T oi) msg a.1, a.2)) <$> z)
              (ih (prover₁ := next) (ch₁ := ch₁))
      | V_to_P T =>
          intro prover₁ ch₁
          cases ch₁ with
          | mk chal chTail =>
              simp only [List.cons_append, comp, List.append_eq, Challenges.join, id_eq, run,
                HVector.head_cons, HVector.tail_cons, bind_pure_comp, pure_bind, bind_assoc,
                Transcript.join, bind_map_left]
              refine congrArg (fun k => prover₁ chal >>= k) ?_
              funext next
              simpa [Prover.comp, Prover.run, Challenges.join, Transcript.join] using
                congrArg (fun z =>
                  (fun a : Transcript (tl ++ pSpec₂) × Output =>
                    (Transcript.cons (r := .V_to_P T) chal a.1, a.2)) <$> z)
                  (ih (prover₁ := next) (ch₁ := chTail))

/-- Variant of `run_comp_join` with an extra continuation `k` after the run. -/
lemma run_comp_join_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {Mid Output α : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : Prover m Mid pSpec₁)
    (f : Mid → m (Prover m Output pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂)
    (k : Transcript (pSpec₁ ++ pSpec₂) × Output → m α) :
    (do
      let prover ← Prover.comp (m := m) (Mid := Mid) (Output := Output) (pSpec₂ := pSpec₂)
        pSpec₁ prover₁ f
      let z ← Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
        (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂)
      k z) =
      (do
        let (tr₁, mid) ← Prover.run (m := m) (Output := Mid) pSpec₁ prover₁ ch₁
        let prover₂ ← f mid
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ prover₂ ch₂
        k (Transcript.join tr₁ tr₂, out)) := by
  simpa [bind_assoc] using congrArg (fun z => z >>= k) (run_comp_join (m := m)
    (prover₁ := prover₁) (f := f) (ch₁ := ch₁) (ch₂ := ch₂))

/-- Extract the first-stage prover from a prover over `pSpec₁ ++ pSpec₂`.
Running the extracted prover over `pSpec₁` returns the residual prover for `pSpec₂`. -/
def splitPrefix {m : Type → Type} [Monad m] {Output : Type} :
    (pSpec₁ : ProtocolSpec) → {pSpec₂ : ProtocolSpec} →
    Prover m Output (pSpec₁ ++ pSpec₂) → Prover m (Prover m Output pSpec₂) pSpec₁
  | [], _, prover => prover
  | (.P_to_V _ _) :: tl, _, prover =>
      let (msg, cont) := prover
      (msg, do
        let next ← cont
        return splitPrefix tl next)
  | (.V_to_P _) :: tl, _, prover =>
      fun chal => do
        let next ← prover chal
        return splitPrefix tl next

/-- Running a prover over `pSpec₁ ++ pSpec₂` can be decomposed into:
1) run the prefix prover `splitPrefix pSpec₁ prover` on `pSpec₁`,
2) run the returned suffix prover on `pSpec₂`. -/
lemma run_splitPrefix_join
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {Output : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover : Prover m Output (pSpec₁ ++ pSpec₂))
    (ch₁ : Challenges pSpec₁) (ch₂ : Challenges pSpec₂) :
    Prover.run (m := m) (Output := Output) (pSpec₁ ++ pSpec₂) prover
      (Challenges.join pSpec₁ pSpec₂ ch₁ ch₂) =
      (do
        let (tr₁, p₂) ← Prover.run (m := m)
          (Output := Prover m Output pSpec₂) pSpec₁
          (splitPrefix (m := m) (Output := Output) pSpec₁ prover) ch₁
        let (tr₂, out) ← Prover.run (m := m) (Output := Output) pSpec₂ p₂ ch₂
        return (Transcript.join tr₁ tr₂, out)) := by
  revert prover ch₁
  induction pSpec₁ with
  | nil =>
      intro prover ch₁
      have hnil :
          (fun a : Transcript pSpec₂ × Output => (HVector.append HVector.nil a.1, a.2)) = id := by
        funext a
        cases a
        rfl
      simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, hnil]
  | cons r tl ih =>
      cases r with
      | P_to_V T oi =>
          intro prover ch₁
          rcases prover with ⟨msg, cont⟩
          simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, ih, bind_assoc]
      | V_to_P T =>
          intro prover ch₁
          cases ch₁ with
          | mk chal tlCh =>
              simp [splitPrefix, Prover.run, Challenges.join, Transcript.join, ih, bind_assoc]

/-- Run a prover to an intermediate round `n`, producing a partial transcript and the
remaining prover for rounds `n`..end. Required for round-by-round soundness. -/
def runToRound {m : Type → Type} [Monad m] {Output : Type} :
    (pSpec : ProtocolSpec) → (n : Nat) →
    Prover m Output pSpec → Challenges (pSpec.take n) →
    m (PartialTranscript pSpec n × Prover m Output (pSpec.drop n))
  | _, 0, prover, _ => pure (HVector.nil, prover)
  | (.P_to_V _ _) :: tl, n + 1, prover, challenges => do
    let (msg, cont) := prover
    let next ← cont
    let (ptr, rem) ← runToRound tl n next challenges
    return (msg ::ₕ ptr, rem)
  | (.V_to_P _) :: tl, n + 1, prover, challenges => do
    let next ← prover challenges.head
    let (ptr, rem) ← runToRound tl n next challenges.tail
    return (challenges.head ::ₕ ptr, rem)
  | [], _ + 1, prover, _ => pure (HVector.nil, prover)

/-- Map the output type of a prover, preserving message structure. -/
def mapOutput {m : Type → Type} [Functor m] {A B : Type} (f : A → B) :
    (pSpec : ProtocolSpec) → Prover m A pSpec → Prover m B pSpec
  | [], a => f a
  | (.P_to_V _ _) :: tl, (msg, cont) => (msg, (mapOutput f tl) <$> cont)
  | (.V_to_P _) :: tl, recv => fun ch => (mapOutput f tl) <$> recv ch

theorem run_mapOutput {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type} (f : A → B) :
    (pSpec : ProtocolSpec) → (prover : Prover m A pSpec) → (ch : Challenges pSpec) →
    Prover.run pSpec (mapOutput f pSpec prover) ch =
      (fun (tr, out) => (tr, f out)) <$> Prover.run pSpec prover ch
  | [], output, _ => by simp [run, mapOutput]
  | (.P_to_V T oi) :: tl, (msg, cont), ch => by
    show run (.P_to_V T oi :: tl) (mapOutput f (.P_to_V T oi :: tl) (msg, cont)) ch = _
    simp only [run, mapOutput, bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp]
    congr 1; ext next
    rw [run_mapOutput f tl next]
    simp [map_eq_bind_pure_comp, bind_assoc]
  | (.V_to_P T) :: tl, recv, ch => by
    show run (.V_to_P T :: tl) (mapOutput f (.V_to_P T :: tl) recv) ch = _
    simp only [run, mapOutput, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    congr 1; ext next
    rw [run_mapOutput f tl next]
    simp [map_eq_bind_pure_comp, bind_assoc]

end Prover

/-- An honest prover: takes a statement/witness pair and monadically produces
a `Prover` whose output is a new statement/witness pair. -/
def HonestProver (m : Type → Type) (StmtIn WitIn StmtOut WitOut : Type)
    (pSpec : ProtocolSpec) :=
  StmtIn × WitIn → m (Prover m (StmtOut × WitOut) pSpec)

namespace HonestProver

/-- Compose two honest provers sequentially. -/
def comp {m : Type → Type} [Monad m] {S₁ W₁ S₂ W₂ S₃ W₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (p₁ : HonestProver m S₁ W₁ S₂ W₂ pSpec₁)
    (p₂ : HonestProver m S₂ W₂ S₃ W₃ pSpec₂)
    : HonestProver m S₁ W₁ S₃ W₃ (pSpec₁ ++ pSpec₂) :=
  fun ⟨stmt, wit⟩ => do
    let prover₁ ← p₁ (stmt, wit)
    Prover.comp pSpec₁ prover₁ (fun ⟨midStmt, midWit⟩ => p₂ (midStmt, midWit))

/-- Compose an honest prover with itself `n` times over the replicated protocol spec. -/
def compNth {m : Type → Type} [Monad m] {S W : Type}
    {pSpec : ProtocolSpec} (n : Nat)
    (step : HonestProver m S W S W pSpec)
    : HonestProver m S W S W (pSpec.replicate n) :=
  fun sw => Prover.iterate pSpec n step sw

end HonestProver

end ProtocolSpec
