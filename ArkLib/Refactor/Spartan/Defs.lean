/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleInterface

/-!
# Refactor Spartan Definitions

Base types and oracle interfaces for the refactor-native Spartan migration surface.
-/

open MvPolynomial Matrix

namespace Spartan.Refactor

noncomputable section

/-- Public parameters for the padded Spartan protocol. -/
structure PublicParams where
  ℓ_m : ℕ
  ℓ_n : ℕ
  ℓ_w : ℕ
  ℓ_w_le_ℓ_n : ℓ_w ≤ ℓ_n := by omega

namespace PublicParams

/-- The padded R1CS size induced by the Spartan public parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size := {
  m := 2 ^ pp.ℓ_m
  n := 2 ^ pp.ℓ_n
  n_w := 2 ^ pp.ℓ_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
}

end PublicParams

section Construction

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- The public input statement for Spartan. -/
@[simp] abbrev Statement := R1CS.Statement R pp.toSizeR1CS

/-- The input oracle family for Spartan: the R1CS matrices. -/
@[simp] abbrev OracleStatement := R1CS.OracleStatement R pp.toSizeR1CS

/-- The private witness for Spartan. -/
@[simp] abbrev Witness := R1CS.Witness R pp.toSizeR1CS

/-- The underlying R1CS relation proven by Spartan. -/
@[simp] abbrev relation := R1CS.relation R pp.toSizeR1CS

/-- Input matrices are exposed through multilinear-extension evaluation oracles. -/
instance : ∀ i, OracleInterface (OracleStatement R pp i) :=
  fun _ => {
    Query := (Fin pp.ℓ_m → R) × (Fin pp.ℓ_n → R)
    toOC.spec := fun _ => R
    toOC.impl := fun ⟨x, y⟩ => do
      return (← read).toMLE ⸨C ∘ x⸩ ⸨y⸩
  }

/-- The witness is exposed as an oracle for evaluating its multilinear extension. -/
instance : OracleInterface (Witness R pp) where
  Query := Fin pp.ℓ_w → R
  toOC.spec := fun _ => R
  toOC.impl := fun evalPoint => do
    return (MLE ((← read) ∘ finFunctionFinEquiv)) ⸨evalPoint⸩

end Construction

end

end Spartan.Refactor
