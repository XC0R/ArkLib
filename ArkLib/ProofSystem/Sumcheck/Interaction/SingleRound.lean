/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Defs

/-!
# Interaction-Native Sum-Check: Single Round

One round of sum-check expressed as an `Interaction.Spec` with role decorations, together with
honest prover, verifier, and reduction builders using CompPoly types.

## Protocol Description

A single round takes a `RoundClaim R` (the current target sum) and proceeds:

1. **Prover** (sender): sends a univariate polynomial `p : CDegreeLE R deg`.
   An honest prover sends a polynomial whose evaluations over the summation domain `D` sum
   to the current target.
2. **Verifier** (receiver): sends a random field element `r ∈ R`.

After the round, the new claim is `p(r)`.

## Main Definitions

- `honestProverStep`: builds a `Strategy.withRoles` for one round from the prover's polynomial.
- `verifierStep`: builds a `Counterpart` for one round that checks the sum condition over `D`,
  samples a challenge, and outputs `Option (RoundClaim R)` — the next claim on success or
  `none` on rejection.
- `roundReduction`: packages the prover and verifier steps into a `Reduction`.
-/

namespace Sumcheck

open Interaction CompPoly CPoly

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] {deg : ℕ}

/-- The honest prover step for a single round of sum-check.

Given the prover's polynomial (of degree ≤ `deg`), produces a `Strategy.withRoles` that:
- Sends the polynomial (sender action)
- Receives the challenge (receiver action)
- Outputs the result of `computeNext` applied to the polynomial and challenge.

The `computeNext` callback abstracts how the prover computes its next-round state. -/
def honestProverStep (m : Type → Type) [Monad m]
    {NextState : Type}
    (poly : CDegreeLE R deg)
    (computeNext : CDegreeLE R deg → R → NextState) :
    Spec.Strategy.withRoles m (roundSpec R deg) (roundRoles R deg)
      (fun _ => NextState) :=
  pure ⟨poly, fun chal => pure (computeNext poly chal)⟩

/-- The verifier step for a single round of sum-check.

Given the current claim, a summation domain `D`, and a way to sample a challenge:
1. Observes the polynomial from the prover (dual of sender).
2. Checks that the polynomial's evaluations over `D` sum to the target (`roundCheck`).
3. Samples a random challenge (dual of receiver).
4. Outputs `some (poly(challenge))` as the next claim if the check passed, or `none` if it
   failed. -/
def verifierStep (m : Type → Type) [Monad m]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : m R)
    (target : RoundClaim R) :
    Spec.Counterpart m (roundSpec R deg) (roundRoles R deg)
      (fun _ => Option (RoundClaim R)) :=
  fun poly => do
    let chal ← sampleChallenge
    if roundCheck R deg D target poly then
      pure ⟨chal, some (CPolynomial.eval chal poly.1)⟩
    else
      pure ⟨chal, none⟩

/-- A single-round sum-check reduction.

- **StatementIn**: the current round claim (`RoundClaim R`).
- **WitnessIn**: the prover's input state, abstracted as `WitIn`.
- **Context**: `roundSpec R deg` (two messages: polynomial then challenge).
- **Roles**: `roundRoles R deg` (sender then receiver).
- **StatementOut**: `Option (RoundClaim R)` — the next claim on success, `none` on rejection.
- **WitnessOut**: the prover's next-round state, indexed by transcript.

The prover sends its polynomial and computes the next witness from the challenge.
The verifier checks the sum condition, samples a challenge, and outputs the next claim. -/
def roundReduction (m : Type → Type) [Monad m]
    {WitIn WitOut : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : m R)
    (proverSend : RoundClaim R → WitIn → m (CDegreeLE R deg))
    (proverNext : WitIn → CDegreeLE R deg → R → WitOut) :
    Reduction m (RoundClaim R) WitIn
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => WitOut) where
  prover target witIn := do
    let poly ← proverSend target witIn
    pure <| honestProverStep m poly
      (fun sentPoly chal =>
        ⟨some (CPolynomial.eval chal sentPoly.1), proverNext witIn sentPoly chal⟩)
  verifier target := verifierStep m D sampleChallenge target

end

end Sumcheck
