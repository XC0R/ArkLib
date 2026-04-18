import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.Probability.Notation

open NNReal Finset Function ProbabilityTheory Code Affine
open scoped BigOperators LinearCode ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- The key insight: if we show the AffineSubspaces are equal,
-- we can use the SAME subspace on both sides. Then we just need
-- to convert $ᵖ ↥(affineSpan ...) to $ᵖ ↥(AffSpanFinset ...).

-- Actually, let me try: AffSpanFinset is just .toFinset of the carrier.
-- If I show affineSubspaceAtOrigin = affineSpan, then I can convert
-- the probability to be over affineSpan, and AffSpanFinset is its toFinset.

-- The direct route: show the two uniform probs are equal by showing
-- they sample from the same elements.

-- Simplest working approach: convert via `convert` tactic
-- $ᵖ A and $ᵖ S should be convertible if A.carrier = ↑S

variable {m : ℕ} (C : Fin (m + 2) → ι → F) in
noncomputable def u'C : Fin (m + 2) → ι → F :=
  fun j => if j = 0 then C 0 else C j - C 0

-- Test: can convert handle the probability directly?
example {m : ℕ} {C : Fin (m + 2) → ι → F}
    (S : Finset (ι → F)) [Nonempty S]
    (hS : S = AffSpanFinset C)
    {deg : ℕ} {domain : ι ↪ F} {δ ε : ℝ≥0}
    (hcase : ε < Pr_{let x ← $ᵖ S}[δᵣ(x.val,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ]) :
    Pr_{let y ← $ᵖ ↥(affineSubspaceAtOrigin (F := F) (u'C C 0) (Fin.tail (u'C C)))}[
        δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] > ε := by
  -- Strategy: show affineSubspaceAtOrigin ... = affineSpan F (univ.image C)
  -- Then AffSpanFinset C = (AffSpanSet C).toFinset, and AffSpanSet C = (affineSpan ...).carrier
  -- So $ᵖ ↥(affineSubspace...) and $ᵖ S sample from the same set.
  sorry
