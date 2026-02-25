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
