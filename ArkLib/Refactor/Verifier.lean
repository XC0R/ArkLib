/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Transcript

/-!
# Verifier (Plain)

`Verifier m StmtIn StmtOut pSpec` is a plain verifier that sees all messages directly
via the full transcript. It does not have oracle access.

This is the "plain" track of the dual-track verifier design:
- `Verifier` — sees messages directly (for Fiat-Shamir, BCS output)
- `OracleVerifier` — has oracle access to messages (for IOPs, defined separately)

## Main definitions

- `Verifier` — type alias for the verifier function
- `Verifier.comp` — sequential composition
-/

namespace ProtocolSpec

/-- A plain verifier: takes a statement and full transcript, and either accepts
(returning output statement) or rejects (returning `none`). -/
def Verifier (m : Type → Type) (StmtIn StmtOut : Type) (pSpec : ProtocolSpec) :=
  StmtIn → Transcript pSpec → OptionT m StmtOut

namespace Verifier

/-- Compose two verifiers sequentially. The transcript is split at the boundary,
and the output of the first verifier becomes the input of the second. -/
def comp {m : Type → Type} [Monad m] {S₁ S₂ S₃ : Type}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    (v₁ : Verifier m S₁ S₂ pSpec₁) (v₂ : Verifier m S₂ S₃ pSpec₂)
    : Verifier m S₁ S₃ (pSpec₁ ++ pSpec₂) :=
  fun stmt tr => do
    let (tr₁, tr₂) := Transcript.split tr
    let mid ← v₁ stmt tr₁
    v₂ mid tr₂

end Verifier

end ProtocolSpec
