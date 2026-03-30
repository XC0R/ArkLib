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
Instead, it has oracle access to evaluation queries on the multivariate polynomial
`poly : CMvDegreeLE R n deg` — an `n`-variate polynomial with individual degree ≤ `deg`.
The key property is that the **same** oracle polynomial is available in every round.

The prover sends round polynomials (each a `CDegreeLE R deg` — a univariate polynomial
with degree ≤ `deg`) that the verifier can also query as oracles via the oracle
decoration.

## Design

- `OracleStmt R deg n`: the concrete oracle statement type, defined as
  `CMvDegreeLE R n deg`. Its `OracleInterface` provides evaluation queries:
  `Query = Fin n → R` (points in `R^n`), `Response = R`.
- `roundOracleDecoration`: the per-round oracle decoration, attaching the evaluation
  oracle interface (`instOracleInterfaceCDegreeLE`) to the prover's `CDegreeLE R deg`
  message. Its `OracleInterface` provides `Query = R`, `Response = R`.

### Oracle verifier structure

For a single round, the oracle verifier (via `Counterpart.withMonads` and
`toMonadDecoration`) unfolds to:

1. **Sender node** (monad = `Id`): pure observation of the prover's `CDegreeLE R deg`.
2. **Receiver node** (monad = `OracleComp (oSpec + [polyOracleSpec]ₒ + roundPolySpec)`):
   the verifier queries the round polynomial at each domain point `D j`, sums the
   results, checks against the target, and samples a challenge. The oracle statement
   `CMvDegreeLE R n deg` is also available for queries but is not used per-round
   (it is queried once at the end of the full protocol to verify the final claim).

The full oracle reduction chains `n` such round verifiers, with the oracle statement
`CMvDegreeLE R n deg` available throughout.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (deg : ℕ)

/-- The oracle statement type for sum-check: the original `n`-variate polynomial
with individual degree at most `deg` in each variable. This persists unchanged
throughout all rounds.

The `OracleInterface` for `CMvDegreeLE R n deg` provides:
- `Query = Fin n → R` — evaluation points in `R^n`
- `Response = R` — the polynomial's value at that point -/
abbrev OracleStmt (n : ℕ) := CMvDegreeLE R n deg

/-- The oracle statement family for sum-check, indexed by `Unit` since there is
exactly one oracle statement (the multivariate polynomial). -/
abbrev OracleStmtFamily (n : ℕ) : Unit → Type :=
  fun _ => OracleStmt R deg n

/-- Oracle decoration for a single round: the prover's `CDegreeLE R deg` message
is queryable via its evaluation oracle interface (`Query = R`, `Response = R`).
The verifier's challenge has no oracle interface (it is a plain field element). -/
def roundOracleDecoration :
    OracleDecoration (roundSpec R deg) (roundRoles R deg) :=
  ⟨instOracleInterfaceCDegreeLE, fun _ => fun _ => ⟨⟩⟩

/-- The oracle verifier step for a single round of sum-check, with the oracle
statement explicitly typed as `CMvDegreeLE R n deg`.

In the oracle model, the verifier has access to:
- `oSpec` — background oracles
- `[OracleStmtFamily R deg n]ₒ` — the multivariate polynomial oracle
  (`CMvDegreeLE R n deg`, queryable at points in `R^n`)
- `(R →ₒ R)` — the round polynomial's evaluation oracle (accumulated from
  the sender node's `OracleInterface` on `CDegreeLE R deg`)

The verifier:
1. Queries the round polynomial oracle at each domain point `D j`.
2. Sums the query results and checks equality with `target`.
3. Samples a random challenge via `sampleChallenge`.
4. If the check passed, queries the polynomial at the challenge to compute
   `poly(chal)` and returns `⟨chal, some poly(chal)⟩`.
5. If the check failed, returns `⟨chal, none⟩`. -/
noncomputable def oracleVerifierStep (n : ℕ)
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleCounterpart oSpec (OracleStmtFamily R deg n)
      (fun {ιₐ} (_accSpec : OracleSpec ιₐ) => Option (RoundClaim R))
      (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
      (ιₐ := PEmpty) []ₒ :=
  let oiSpec := @OracleInterface.spec (CDegreeLE R deg) instOracleInterfaceCDegreeLE
  fun _poly => by
    change OracleComp (oSpec + [OracleStmtFamily R deg n]ₒ + ([]ₒ + oiSpec))
      ((chal : R) × Option (RoundClaim R))
    exact do
      let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
        (fun (acc : R) (j : Fin m_dom) => do
          let val : R ← (query (spec := oiSpec) (D j) : OracleComp oiSpec _)
          return acc + val) (0 : R)
      let chal ← (sampleChallenge : OracleComp oSpec R)
      if total == target then do
        let polyAtChal : R ← (query (spec := oiSpec) chal : OracleComp oiSpec _)
        pure ⟨chal, some polyAtChal⟩
      else
        pure ⟨chal, none⟩

end

end Sumcheck
