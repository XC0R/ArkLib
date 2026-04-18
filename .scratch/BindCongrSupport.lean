/-
ProbComp.bind_congr_of_forall_mem_support:
Structural bind congruence restricted to support for ProbComp.

For ProbComp, all queries ($[0..n]) have full support (Set.univ),
so every leaf is reachable. This means support-level function equality
suffices for structural bind equality.
-/

import VCVio

open OracleComp OracleSpec

/-- For ProbComp, if two bind-functions agree on the support of the first computation,
    the two binds are equal. This is a structural (not distributional) equality.
    Proof: by ProbComp.inductionOn. Uniform queries have full support, so every
    continuation is reachable and the IH applies. -/
private lemma ProbComp.bind_congr_of_forall_mem_support
    {α β : Type} (mx : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ x ∈ support mx, f x = g x) : mx >>= f = mx >>= g := by
  induction mx using ProbComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp [support_pure])
  | query_bind n k ih =>
    simp only [bind_assoc]
    exact OracleComp.bind_congr' rfl (fun u => ih u (fun x hx =>
      h x ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, hx⟩)))
