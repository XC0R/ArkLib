/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound

/-!
# Interaction-Native Sum-Check: General (n-Round) Protocol

The full `n`-round sum-check protocol, built by chaining the single-round primitive
via `Spec.stateChain` and `Reduction.stateChainCompUniform`.

## Overview

The sum-check protocol verifies `∑ x ∈ D^n, poly(x) = target` where
`poly : CMvDegreeLE R n deg` is a computable multivariate polynomial. The protocol
proceeds in `n` rounds; at each round the prover sends the honest round polynomial
and the verifier sends a random challenge.

## Design

- The prover carries a `Sumcheck.ResidualPoly` as its internal state. At each round,
  it computes the round polynomial via `CMvPolynomial.roundPoly`, then updates the
  residual by `CMvPolynomial.partialEvalFirst` at the received challenge.
- The oracle/verifier side retains the original `CMvDegreeLE R n deg` polynomial
  (formalized separately in the oracle layer).

## Main Definitions

- `fullSpec`: the full `n`-round interaction spec via `Spec.stateChain`.
- `fullRoles`: the full `n`-round role decoration via `RoleDecoration.stateChain`.
- `sumcheckReduction`: the concrete `n`-round sum-check reduction.
-/

namespace Sumcheck

open Interaction CompPoly CPoly

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

/-- The full `n`-round sum-check `Interaction.Spec`, built by chaining `roundSpec`. -/
def fullSpec (n : Nat) (target : RoundClaim R) : Spec :=
  Spec.stateChain (fun _ => RoundClaim R) (roundSpecFn R deg) (advance R deg) n 0 target

/-- The full `n`-round role decoration, built by chaining `roundRoles`. -/
def fullRoles (n : Nat) (target : RoundClaim R) :
    RoleDecoration (fullSpec R deg n target) :=
  RoleDecoration.stateChain (roundRolesFn R deg) n 0 target

variable {R} {deg}

/-- Compute the honest round `CDegreeLE` message from a residual polynomial with
`k + 1` variables and domain `D`. Keeps variable 0 free and sums variables 1..k. -/
def honestRoundMsgAux {m_dom : ℕ} (D : Fin m_dom → R)
    {k : ℕ} (p : CMvPolynomial (k + 1) R)
    (hDeg : CMvPolynomial.IndividualDegreeLE (R := R) deg p) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D k p,
    CMvPolynomial.roundPoly_natDegree_le D p (fun mono hmono =>
      hDeg ⟨0, by omega⟩ mono hmono)⟩

/-- Update a residual polynomial with `k + 1` variables after receiving challenge `r`.
Partially evaluates variable 0 at `r`, producing a polynomial in `k` variables. -/
def updateResidualAux (challenge : R)
    {k : ℕ} (p : CMvPolynomial (k + 1) R)
    (hDeg : CMvPolynomial.IndividualDegreeLE (R := R) deg p) :
    ResidualPoly R deg :=
  { numVars := k
    poly := CMvPolynomial.partialEvalFirst challenge p
    degreeBound := CMvPolynomial.partialEvalFirst_individualDegreeLE challenge p hDeg }

/-- Compute the honest round message from a `ResidualPoly`. Returns a `CDegreeLE R deg`
if the residual has at least 1 variable, or `sorry` otherwise (the protocol should never
reach this case for a well-formed `n`-round invocation). -/
def honestRoundMsg {m_dom : ℕ} (D : Fin m_dom → R)
    (residual : ResidualPoly R deg) :
    CDegreeLE R deg :=
  match residual.numVars, residual.poly, residual.degreeBound with
  | _ + 1, p, hDeg => honestRoundMsgAux D p hDeg
  | 0, _, _ => ⟨0, Nat.zero_le _⟩

/-- Update the residual polynomial after receiving a verifier challenge. -/
def updateResidual (challenge : R)
    (residual : ResidualPoly R deg) :
    ResidualPoly R deg :=
  match residual.numVars, residual.poly, residual.degreeBound with
  | _ + 1, p, hDeg => updateResidualAux challenge p hDeg
  | 0, _, _ => residual

/-- The concrete sum-check reduction for `n` rounds.

Given a multivariate polynomial `poly : CMvDegreeLE R n deg` and an evaluation domain
`D : Fin m_dom → R`, this reduction implements:

- **Honest prover**: at each round, computes `roundPoly D` on the residual polynomial
  and sends it. After receiving the challenge, updates the residual via `partialEvalFirst`.
- **Verifier**: checks that the polynomial's evaluations over `D` sum to the current target.
  On success, outputs `some (p_i(r_i))` as the next claim. On failure, outputs `none`.

**Types:**
- `StatementIn = RoundClaim R` (the initial target).
- `WitnessIn = Unit` (sum-check has no witness).
- `StatementOut = Option (RoundClaim R)` (the final target, or `none` if any check failed).
- `WitnessOut = ResidualPoly R deg` (the prover's residual polynomial state). -/
def sumcheckReduction (m : Type → Type) [Monad m]
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (poly : CMvDegreeLE R n deg)
    (sampleChallenge : m R) :
    Reduction m (RoundClaim R) Unit
      (fun s => fullSpec R deg n s)
      (fun s => fullRoles R deg n s)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => ResidualPoly R deg) :=
  Reduction.stateChainCompUniform
    (spec := roundSpecFn R deg)
    (advance := advance R deg)
    (roles := roundRolesFn R deg)
    n
    id
    (fun _ _ => pure { numVars := n, poly := poly.1, degreeBound := poly.2 })
    (fun _i _target residual => do
      let rp := honestRoundMsg D residual
      pure (honestProverStep m rp (fun _ chal =>
        updateResidual chal residual)))
    some
    (fun _i st optClaim =>
      match optClaim with
      | none => fun _poly => do
          let chal ← sampleChallenge
          pure ⟨chal, none⟩
      | some _ => verifierStep m D sampleChallenge st)

/-! ## Security properties

Perfect completeness and round-by-round knowledge soundness for the full sum-check
protocol are stated using the generic `Reduction` security framework.

- **Completeness**: when the honest prover sends the correct round polynomial
  (via `CMvPolynomial.roundPoly`), the sum check passes at every round and
  the output claim satisfies the output relation.
- **Soundness**: at each round, a cheating prover's polynomial either fails
  the sum check or agrees with the honest polynomial on all of `D`, leaving
  a single-point disagreement caught by the random challenge with probability
  at least `1 - deg / |R|` (Schwartz–Zippel).
-/

end

end Sumcheck
