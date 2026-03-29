/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.General
import ArkLib.Interaction.Oracle

/-!
# Interaction-Native Sum-Check: Oracle Layer

This module formalizes the oracle verifier side of the sum-check protocol, where the
original multivariate polynomial (`CMvDegreeLE R n deg`) persists as an oracle statement
throughout all `n` rounds.

## Overview

In the oracle model, the verifier does not see the multivariate polynomial directly.
Instead, it has oracle access to evaluation queries. The key property is that the
**same** oracle polynomial is available in every round — it is never modified or replaced.

The prover sends round polynomials (each a `CDegreeLE R deg`) that the verifier can
also query as oracles. The oracle decoration attaches `OracleInterface` instances to
these sender messages.

## Design

- `OracleStmt`: the oracle statement type for sum-check is `CMvDegreeLE R n deg`.
- `roundOracleDecoration`: the per-round oracle decoration, attaching the evaluation
  oracle interface to the prover's degree-bounded polynomial message.

### Oracle verifier structure

For a single round, the oracle verifier (via `Counterpart.withMonads` and
`toMonadDecoration`) unfolds to:

1. **Sender node** (monad = `Id`): pure observation of the prover's `CDegreeLE R deg`.
2. **Receiver node** (monad = `OracleComp (oSpec + [OStmtIn]ₒ + roundPolySpec)`):
   the verifier queries the round polynomial at each domain point `D j`, sums the
   results, checks against the target, and samples a challenge. The output is
   `Option (RoundClaim R)`.

The full oracle reduction chains `n` such round verifiers, with the oracle statement
`CMvDegreeLE R n deg` available throughout.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (deg : ℕ)

/-- The oracle statement type for sum-check: the original multivariate polynomial
with individual degree bounds. This persists unchanged throughout all rounds. -/
abbrev OracleStmt (n : ℕ) := CMvDegreeLE R n deg

/-- Oracle decoration for a single round: the prover's `CDegreeLE R deg` message
is queryable via its evaluation oracle interface. The verifier's challenge has no
oracle interface (it is a plain field element). -/
def roundOracleDecoration :
    OracleDecoration (roundSpec R deg) (roundRoles R deg) :=
  ⟨instOracleInterfaceCDegreeLE, fun _ => fun _ => ⟨⟩⟩

/-- The oracle verifier step for a single round of sum-check.

In the oracle model, the verifier cannot directly evaluate the round polynomial.
Instead, it queries the polynomial oracle at each domain point `D j`, sums the
responses, and compares to the target. Then it samples a challenge and outputs
the next claim.

The full definition requires composing oracle queries through the `OracleComp`
monad with the accumulated oracle spec from `toMonadDecoration`. -/
def oracleVerifierStep {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (n : ℕ) {m_dom : ℕ} (_D : Fin m_dom → R) (_target : RoundClaim R) :
    OracleCounterpart oSpec OStmtIn
      (fun {ιₐ} (_accSpec : OracleSpec ιₐ) => Option (RoundClaim R))
      (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
      (ιₐ := PEmpty) []ₒ :=
  sorry

end

end Sumcheck
