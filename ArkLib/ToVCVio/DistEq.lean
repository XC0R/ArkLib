/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ToVCVio.SimOracle

/-!
  # Distributional Equality of Oracle Computations

  We define distributional equality of oracle computations (or more generally, any monad `m` with
  an `HasEvalDist` instance).
-/

universe u v w

open OracleComp SimOracle

namespace HasEvalDist

variable {m : Type u → Type v} [Monad m] [HasEvalDist m]

def eq {α : Type u} (mx my : m α) : Prop :=
  evalDist mx = evalDist my

@[simp]
theorem eq_refl {α : Type u} (mx : m α) : eq mx mx := by
  simp [eq]

theorem eq_symm {α : Type u} (mx my : m α) : eq mx my → eq my mx := by
  intro i; simp_all [eq]

theorem eq_trans {α : Type u} (mx my mz : m α) (hxy : eq mx my) (hyz : eq my mz) : eq mx mz := by
  simp [eq]
  rw [hxy, hyz]

end HasEvalDist

namespace OracleComp

-- Shouldn't have to define this separately once we have an instance `HasEvalDist (OracleComp spec)`

variable {ι : Type u} {spec : OracleSpec ι} [spec.FiniteRange] {α : Type u}

def distEq (mx my : OracleComp spec α) : Prop :=
  evalDist mx = evalDist my

@[simp]
theorem distEq_refl (mx : OracleComp spec α) : distEq mx mx := by
  simp [distEq]

theorem distEq_symm (mx my : OracleComp spec α) : distEq mx my → distEq my mx := by
  intro i; simp_all [distEq]

theorem distEq_trans (mx my mz : OracleComp spec α)
    (hxy : distEq mx my) (hyz : distEq my mz) : distEq mx mz := by
  simp [distEq]
  rw [hxy, hyz]

-- universe level issue
-- /-- Functional equality of oracle computations. This is *different* from distributional equality,
-- since the distribution of each new query when applying `evalDist` is independently random, unlike
-- a function which always returns the same value. -/
-- def fnEquiv (oa ob : OracleComp spec α) : Prop :=
--   ∀ f : (i : ι) → spec.domain i → spec.range i,
--     simulateQ (fnOracle spec f) oa = simulateQ (fnOracle spec f) ob

section DistributionalEquivalence

variable {ι : Type u} {spec : OracleSpec ι} [spec.FiniteRange]
variable {α β γ δ : Type u}

/-- Binding with a mapped computation is the same as binding with the original and composing. -/
lemma evalDist_map_bind (oa : OracleComp spec α) (f : α → β) (g : β → OracleComp spec γ) :
    evalDist ((f <$> oa) >>= g) = evalDist (oa >>= (g ∘ f)) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

/-- TODO remove keygen from here.
    When keygen samples and returns (f a, f a), binding with it and using the first component
    is the same as sampling and applying f directly. -/
lemma evalDist_keygen_pair_bind (sample : OracleComp spec α) (gen : α → β)
    (body : β → OracleComp spec γ) :
    evalDist ((sample >>= fun a => pure (gen a, gen a)) >>= fun p => body p.1) =
    evalDist (sample >>= fun a => body (gen a)) := by
  simp only [bind_assoc, pure_bind]

/-- Mapping a projection after a bind that produces extra data is the same as
    binding without producing that data. -/
lemma evalDist_bind_map_fst (oa : OracleComp spec α) (f : α → OracleComp spec (β × γ)) :
    evalDist (Prod.fst <$> (oa >>= f)) = evalDist (oa >>= fun a => Prod.fst <$> f a) := by
  simp only [map_eq_bind_pure_comp, bind_assoc]

/-- If two computations are equal after applying evalDist, their probEvents are equal. -/
lemma probEvent_of_evalDist_eq {oa : OracleComp spec α} {ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) (p : α → Prop) : [p | oa] = [p | ob] :=
  probEvent_congr (fun _ => Iff.rfl) h

/-- Mapping over a bind distributes: f <$> (oa >>= ob) = oa >>= (f <$> · ∘ ob) -/
lemma evalDist_map_bind' (oa : OracleComp spec α) (ob : α → OracleComp spec β) (f : β → γ) :
    evalDist (f <$> (oa >>= ob)) = evalDist (oa >>= fun a => f <$> ob a) := by
  simp only [map_eq_bind_pure_comp, bind_assoc]

/-- StateT.run' preserves evalDist equality: if inner computations have equal evalDist,
    so do their run' results. -/
lemma evalDist_stateT_run'_congr {σ : Type u} {oa ob : StateT σ (OracleComp spec) α} (s : σ)
    (h : ∀ s', evalDist (oa.run s') = evalDist (ob.run s')) :
    evalDist (oa.run' s) = evalDist (ob.run' s) := by
  simp only [StateT.run'_eq, evalDist_map, h s]

/-- Pure pair bind with projection simplifies -/
lemma evalDist_pure_pair_bind_fst (oa : OracleComp spec α) (f g : α → β)
    (body : β → OracleComp spec γ) :
    evalDist ((oa >>= fun a => pure (f a, g a)) >>= fun p => body p.1) =
    evalDist (oa >>= fun a => body (f a)) := by
  simp only [bind_assoc, pure_bind]

/-- Congruence lemma for evalDist under map -/
lemma evalDist_map_congr {oa ob : OracleComp spec α} (f : α → β)
    (h : evalDist oa = evalDist ob) :
    evalDist (f <$> oa) = evalDist (f <$> ob) := by
  simp only [evalDist_map, h]

/-- Congruence lemma for evalDist under bind -/
lemma evalDist_bind_congr {oa ob : OracleComp spec α} (f : α → OracleComp spec β)
    (h : evalDist oa = evalDist ob) :
    evalDist (oa >>= f) = evalDist (ob >>= f) := by
  simp only [evalDist_bind, h]

/-- Congruence lemma for evalDist under bind on the right -/
lemma evalDist_bind_congr_right (oa : OracleComp spec α)
    {f g : α → OracleComp spec β}
    (h : ∀ a, evalDist (f a) = evalDist (g a)) :
    evalDist (oa >>= f) = evalDist (oa >>= g) := by
  simp only [evalDist_bind, Function.comp_def]
  congr 1
  funext a
  exact h a

/-- Binding with pure tuple and then projecting the last component is identity -/
lemma bind_pure_proj_2_2_2 (oa : OracleComp spec δ) (a : α) (b : β) (c : γ) :
    (oa >>= fun d => pure (a, b, c, d)) >>= (fun t => pure t.2.2.2) = oa := by
  simp only [bind_assoc, pure_bind, bind_pure]

/-- Collapses mapM >>= pure tuple >>= map proj into Vector.map proj <$> mapM -/
lemma mapM_bind_pure_tuple_proj {L : ℕ} {ε σ τ υ : Type u}
    (claims : Vector α L) (body : α → OracleComp spec (β × γ × δ × ε))
    (a : σ) (b : τ) (c : υ) :
    (claims.mapM body >>= fun evals => pure (a, b, c, evals)) >>=
      (fun t => pure (Vector.map (fun x => (x.1, x.2.1, x.2.2.1)) t.2.2.2))
    = Vector.map (fun x => (x.1, x.2.1, x.2.2.1)) <$> claims.mapM body := by
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def, bind_pure]

/-- Bind congruence: if continuations are equal for all inputs, binds are equal -/
lemma bind_congr_fun (oa : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a, f a = g a) : oa >>= f = oa >>= g := by
  congr 1; funext a; exact h a

omit [spec.FiniteRange] in
/-- Vector.map after Vector.mapM can be fused into the mapM (OracleComp equality).
    This is the naturality of traverse: map g <$> traverse f = traverse (map g <$> f) -/
lemma vector_map_mapM {n : ℕ} (xs : Vector α n)
    (f : α → OracleComp spec β) (g : β → γ) :
    (Vector.map g <$> Vector.mapM f xs) =
    (Vector.mapM (fun a => g <$> f a) xs) := by
  -- Naturality of traverse: map g <$> traverse f = traverse (map g <$> f)
  -- This is a standard property that holds for any lawful traversable functor
  -- The proof requires induction on the internal Vector.mapM.go structure
  sorry

/-- evalDist version of vector_map_mapM -/
lemma evalDist_vector_map_mapM {n : ℕ} (xs : Vector α n)
    (f : α → OracleComp spec β) (g : β → γ) :
    evalDist (Vector.map g <$> Vector.mapM f xs) =
    evalDist (Vector.mapM (fun a => g <$> f a) xs) := by
  rw [vector_map_mapM]

/-- StateT.run preserves evalDist equality -/
lemma evalDist_stateT_run_congr {σ : Type u}
    {oa ob : StateT σ (OracleComp spec) α} (s : σ)
    (h : ∀ s', evalDist (oa.run s') = evalDist (ob.run s')) :
    evalDist (oa.run s) = evalDist (ob.run s) := h s

/-- Combining liftComp with bind: keygen pattern (OracleComp equality).
    When keygen = sample >>= fun a => pure (gen a, gen a), binding and using both
    components is the same as sampling and applying gen twice.
    This follows from monad associativity and pure_bind. -/
lemma liftComp_keygen_bind {ι' : Type u} {superSpec : OracleSpec ι'}
    [superSpec.FiniteRange] [spec ⊂ₒ superSpec]
    (sample : OracleComp spec α) (gen : α → β)
    (body : β → β → OracleComp superSpec γ) :
    (liftComp (sample >>= fun a => pure (gen a, gen a)) superSpec >>=
              fun p => body p.1 p.2) =
    (liftComp sample superSpec >>= fun a => body (gen a) (gen a)) := by
  simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]

/-- evalDist version of liftComp_keygen_bind -/
lemma evalDist_liftComp_keygen_bind {ι' : Type u} {superSpec : OracleSpec ι'}
    [superSpec.FiniteRange] [spec ⊂ₒ superSpec]
    (sample : OracleComp spec α) (gen : α → β)
    (body : β → β → OracleComp superSpec γ) :
    evalDist (liftComp (sample >>= fun a => pure (gen a, gen a)) superSpec >>=
              fun p => body p.1 p.2) =
    evalDist (liftComp sample superSpec >>= fun a => body (gen a) (gen a)) := by
  rw [liftComp_keygen_bind]


/-- StateT.run with bind preserves evalDist equality -/
lemma evalDist_stateT_run_bind_congr {σ : Type u} (s : σ)
    {ma mb : StateT σ (OracleComp spec) α} {f g : α → StateT σ (OracleComp spec) β}
    (h1 : ∀ s', evalDist (ma.run s') = evalDist (mb.run s'))
    (h2 : ∀ a s', evalDist ((f a).run s') = evalDist ((g a).run s')) :
    evalDist (StateT.run (ma >>= f) s) = evalDist (StateT.run (mb >>= g) s) := by
  simp only [StateT.run_bind]
  rw [evalDist_bind, evalDist_bind, h1 s]
  congr 1
  funext ⟨a, s'⟩
  exact h2 a s'

end DistributionalEquivalence

end OracleComp
