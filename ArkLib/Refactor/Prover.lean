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
- `Prover.comp` — sequential composition
- `HonestProver` — prover with statement/witness input
- `HonestProver.comp` — sequential composition of honest provers
-/

namespace ProtocolSpec

/-- Coinductive prover type, defined by structural recursion on the protocol spec. -/
def Prover (m : Type → Type) (Output : Type) : ProtocolSpec → Type
  | [] => Output
  | (.P_to_V T _) :: tl => T × m (Prover m Output tl)
  | (.V_to_P T) :: tl => T → m (Prover m Output tl)

namespace Prover

/-- Run a prover with pre-sampled challenges, producing a transcript and output.

Uses outside challenge sampling: challenges are drawn independently and passed in,
rather than being queried as oracles inside the computation. -/
def run [Monad m] {Output : Type} :
    {pSpec : ProtocolSpec} → Prover m Output pSpec → Challenges pSpec →
    m (Transcript pSpec × Output)
  | [], output, _ => pure (.nil, output)
  | (.P_to_V _ _) :: _, prover, challenges => do
    let next ← prover.2
    let (tr, out) ← next.run challenges
    return (.cons prover.1 tr, out)
  | (.V_to_P _) :: _, prover, challenges => do
    let next ← prover challenges.head
    let (tr, out) ← next.run challenges.tail
    return (.cons challenges.head tr, out)

/-- Compose two provers sequentially. The first prover runs for `pSpec₁`, producing
intermediate output, which is fed to produce the second prover for `pSpec₂`.
The result runs for `pSpec₁ ++ pSpec₂`. -/
def comp [Monad m] {Mid Output : Type} :
    {pSpec₁ pSpec₂ : ProtocolSpec} →
    Prover m Mid pSpec₁ → (Mid → m (Prover m Output pSpec₂)) →
    m (Prover m Output (pSpec₁ ++ pSpec₂))
  | [], p, f => f p
  | (.P_to_V _ _) :: _, p, f =>
    return (p.1, do let rest ← p.2; comp rest f)
  | (.V_to_P _) :: _, p, f =>
    return fun chal => do let rest ← p chal; comp rest f

end Prover

/-- An honest prover: takes a statement/witness pair and monadically produces
a `Prover` whose output is a new statement/witness pair. -/
def HonestProver (m : Type → Type) (StmtIn WitIn StmtOut WitOut : Type)
    (pSpec : ProtocolSpec) :=
  StmtIn × WitIn → m (Prover m (StmtOut × WitOut) pSpec)

namespace HonestProver

/-- Compose two honest provers sequentially. -/
def comp [Monad m] {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (p₁ : HonestProver m S₁ W₁ S₂ W₂ pSpec₁)
    (p₂ : HonestProver m S₂ W₂ S₃ W₃ pSpec₂)
    : HonestProver m S₁ W₁ S₃ W₃ (pSpec₁ ++ pSpec₂) :=
  fun ⟨stmt, wit⟩ => do
    let prover₁ ← p₁ (stmt, wit)
    Prover.comp prover₁ (fun ⟨midStmt, midWit⟩ => p₂ (midStmt, midWit))

end HonestProver

end ProtocolSpec
