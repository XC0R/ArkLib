/-
Task A: Prove bind_eq_of_map_eq helper lemma

Goal: A lemma that lets you decompose `m₁ >>= h₁ = m₂ >>= h₂` when you know 
`f <$> m₁ = g <$> m₂` and the inner functions agree on the projected type.

Key insight from request: If h factors through proj (h = G ∘ proj), then
bind_map_left gives us what we need.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import VCVio.OracleComp.OracleComp

open OracleComp

universe u

section General

variable {m : Type u → Type*} [Monad m] [LawfulMonad m]
variable {α β γ δ : Type u}

-- The key lemma from the request analysis:
-- If f <$> m = f <$> m', then m >>= (G ∘ f) = m' >>= (G ∘ f)
-- This follows from bind_map_left: (f <$> m) >>= G = m >>= (G ∘ f)

lemma bind_comp_eq_of_map_eq {m₁ m₂ : m α} {f : α → γ} {G : γ → m δ}
    (hmap : f <$> m₁ = f <$> m₂) :
    m₁ >>= (G ∘ f) = m₂ >>= (G ∘ f) := by
  have h1 : m₁ >>= (G ∘ f) = (f <$> m₁) >>= G := (bind_map_left f m₁ G).symm
  have h2 : m₂ >>= (G ∘ f) = (f <$> m₂) >>= G := (bind_map_left f m₂ G).symm
  rw [h1, h2, hmap]

-- More general version: if h₁ = G ∘ f and h₂ = G ∘ g, and f <$> m₁ = g <$> m₂,
-- then m₁ >>= h₁ = m₂ >>= h₂
lemma bind_eq_of_map_eq_of_comp {m₁ : m α} {m₂ : m β} 
    {f : α → γ} {g : β → γ} {G : γ → m δ}
    (hmap : f <$> m₁ = g <$> m₂) :
    m₁ >>= (G ∘ f) = m₂ >>= (G ∘ g) := by
  have h1 : m₁ >>= (G ∘ f) = (f <$> m₁) >>= G := (bind_map_left f m₁ G).symm
  have h2 : m₂ >>= (G ∘ g) = (g <$> m₂) >>= G := (bind_map_left g m₂ G).symm
  rw [h1, h2, hmap]

-- The version from the request that requires h₁ a = h₂ b when f a = g b
-- This is actually implied by the factoring condition
lemma bind_eq_of_map_eq_general {m₁ : m α} {m₂ : m β}
    {f : α → γ} {g : β → γ} {h₁ : α → m δ} {h₂ : β → m δ}
    (hmap : f <$> m₁ = g <$> m₂)
    (hinner : ∀ a b, f a = g b → h₁ a = h₂ b)
    -- Need to assume h₁ factors through f (constant on f-fibers)
    (hfactor₁ : ∀ a₁ a₂, f a₁ = f a₂ → h₁ a₁ = h₁ a₂) :
    m₁ >>= h₁ = m₂ >>= h₂ := by
  -- Define G : γ → m δ such that G (f a) = h₁ a
  -- This is well-defined by hfactor₁
  -- Then h₁ = G ∘ f
  -- And h₂ b = h₁ a for any a with f a = g b, so h₂ = G ∘ g
  sorry -- This is more complex, let's focus on the simpler versions

end General

section ProbComp

-- For ProbComp specifically, we can use the SPMF structure

variable {α β γ δ : Type}

-- The simpler version should suffice for our use case
-- In runToRoundFS_default_state_eq, the inner function DOES factor through the projection

end ProbComp

/-
## Application to runToRoundFS_default_state_eq

The IH gives: proj_FS <$> prev_FS = proj_int <$> prev_int
We need: prev_FS >>= inner_FS = prev_int >>= inner_int

If inner_FS = G ∘ proj_FS and inner_int = G ∘ proj_int for some G,
then `bind_eq_of_map_eq_of_comp` gives us exactly what we need.

The question: Does inner_FS factor through proj_FS?

inner_FS processes one round: it depends on (PrvState, σ, Q) where Q is the 
challenge QueryImpl state. But Q doesn't change! So inner_FS depends only on
(PrvState, σ) = proj_FS(full_state).

Similarly, inner_int depends only on (PrvState, σ) = proj_int(full_state).

So both factor through the same projection! And they should give the same G
because when challenges are default, the round processing is identical.
-/

/-
## Application to runToRoundFS_default_state_eq

The IH gives: proj_FS <$> prev_FS = proj_int <$> prev_int
We need: prev_FS >>= inner_FS = prev_int >>= inner_int

If inner_FS = G ∘ proj_FS and inner_int = G ∘ proj_int for some G,
then `bind_eq_of_map_eq_of_comp` gives us exactly what we need.

**Key insight:** After simulation, both sides are ProbComp computations.
The FS side uses StateT (σ × Q) ProbComp, the interactive side uses StateT σ ProbComp.
But after .run with concrete initial states, both become ProbComp values.

The comparison is:
- proj_FS <$> (simulateQ fsImpl prev_FS).run (s, defaultFSImpl)
- proj_int <$> (simulateQ intImpl prev_int).run s

Where proj_FS extracts (PrvState, (σ', Q)) → (PrvState, σ')
And proj_int extracts (Transcript × PrvState, σ') → (PrvState, σ')

The inner functions (for the next round) depend only on (PrvState, σ'),
so they factor through these projections.

**CONCLUSION:** The helper lemma `bind_eq_of_map_eq_of_comp` should work.
The application requires:
1. State the correct projections proj_FS and proj_int
2. Show that inner_FS = G ∘ proj_FS and inner_int = G ∘ proj_int
3. Apply bind_eq_of_map_eq_of_comp with the IH
-/
