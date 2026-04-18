import ArkLib
import VCVio

open OracleComp OracleSpec

-- MonadHom preserves map (derive from bind + pure)
private lemma MonadHom.toFun_map {m n : Type → Type*} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n]
    (φ : m →ᵐ n) (f : α → β) (mx : m α) :
    φ.toFun _ (f <$> mx) = f <$> φ.toFun _ mx := by
  simp only [map_eq_bind_pure_comp, φ.toFun_bind']
  congr 1
  ext a
  exact φ.toFun_pure' _

-- List.mapM naturality for monad homs
private lemma List.mapM_hom {m n : Type → Type*} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : m →ᵐ n) (f : α → m β) (l : List α) :
    φ.toFun _ (l.mapM f) = l.mapM (fun x => φ.toFun _ (f x)) := by
  induction l with
  | nil => simp [List.mapM_nil, φ.toFun_pure']
  | cons a l ih =>
    rw [List.mapM_cons, φ.toFun_bind', List.mapM_cons]
    congr 1
    ext b
    rw [φ.toFun_bind']
    congr 1
    · ext bs; exact φ.toFun_pure' _

-- Array.mapM naturality for monad homs
private lemma Array.mapM_hom {m n : Type → Type*} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : m →ᵐ n) (f : α → m β) (a : Array α) :
    φ.toFun _ (a.mapM f) = a.mapM (fun x => φ.toFun _ (f x)) := by
  rw [Array.mapM_eq_mapM_toList, MonadHom.toFun_map φ]
  rw [List.mapM_hom φ f]
  rw [Array.mapM_eq_mapM_toList]

-- Vector.mapM naturality for monad homs
private lemma Vector.mapM_hom {m n : Type → Type*} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : m →ᵐ n) (f : α → m β) {k : ℕ} (xs : Vector α k) :
    φ.toFun _ (xs.mapM f) = xs.mapM (fun x => φ.toFun _ (f x)) := by
  apply Vector.map_toArray_inj.mp
  rw [← MonadHom.toFun_map φ, Vector.toArray_mapM, Vector.toArray_mapM]
  exact Array.mapM_hom φ f xs.toArray

-- Now: lift simulateQ' to an OptionT monad hom
variable {ι : Type} {spec : OracleSpec ι} {r : Type → Type*}
  [Monad r] [LawfulMonad r]

-- The actual lemma — without constructing MonadHom explicitly
-- Instead, use simulateQ' and lift through OptionT
private lemma simulateQ_optionT_mapM_pure_v2 (impl : QueryImpl spec r)
    {α β : Type} (f : α → OptionT (OracleComp spec) β) (g : α → β)
    (hfg : ∀ x, simulateQ impl ((f x : OracleComp spec (Option β))) =
      (pure (some (g x)) : r (Option β)))
    {n : ℕ} (xs : Vector α n) :
    simulateQ impl ((xs.mapM f : OracleComp spec (Option (Vector β n)))) =
      (pure (some (xs.map g)) : r (Option (Vector β n))) := by
  -- Construct the OptionT monad hom inline
  let φ : OptionT (OracleComp spec) →ᵐ OptionT r :=
  { toFun := fun α (mx : OptionT (OracleComp spec) α) =>
      (simulateQ impl mx : OptionT r α)
    toFun_pure' := fun x => simulateQ_pure impl (some x)
    toFun_bind' := fun mx my => by
      -- OptionT bind: mx >>= my = mx >>= fun opt => match opt with | some a => my a | none => pure none
      -- Both sides unfold to the same bind-match at the underlying monad level
      show simulateQ impl (mx >>= fun opt => match opt with
        | some a => my a | none => pure none) =
        simulateQ impl mx >>= fun opt => match opt with
        | some a => simulateQ impl (my a) | none => pure none
      rw [simulateQ_bind]
      congr 1
      ext opt
      cases opt with
      | none => exact simulateQ_pure impl none
      | some a => rfl }
  -- Apply Vector.mapM_hom with this monad hom
  -- Since φ is a `let`, φ.toFun α mx = simulateQ impl mx definitionally
  have h1 := Vector.mapM_hom φ f xs
  -- h1 : φ.toFun _ (xs.mapM f) = xs.mapM (fun x => φ.toFun _ (f x))
  -- φ.toFun _ (xs.mapM f) = simulateQ impl (xs.mapM f) [definitional, since φ is `let`]
  -- φ.toFun _ (f x) = simulateQ impl (f x) = pure (some (g x)) [by hfg]
  -- = (pure (g x) : OptionT r β) [since pure in OptionT r is pure (some _) in r]
  simp only [show ∀ x, φ.toFun _ (f x) = (pure (g x) : OptionT r β) from hfg] at h1
  rw [Vector.mapM_pure] at h1
  exact h1
