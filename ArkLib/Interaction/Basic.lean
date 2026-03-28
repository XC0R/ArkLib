/-!
# Interaction Specifications and Strategies

Interaction specifications (W-types) with transcripts, strategies, decorations,
and structural combinators. This module provides the foundation for modeling
sequential interactions with dependent types.

## Key insight

A standard `FreeT F m α` defined as an *inductive* fails Lean's positivity
checker when `F` or `m` are arbitrary `Type → Type` parameters. However, when
the interaction structure is **finite and determined by a specification**
(a W-type), we define the "transformer" by **structural recursion on the spec**.
This sidesteps all positivity concerns.

This is the Hancock–Setzer (2000) observation: interactive programs in dependent
type theory are defined by recursion on the interaction *interface*, not as a
separate coinductive type.

## Main definitions

- `Spec` — W-type interaction specification with typed moves at each node
- `Spec.Transcript` — root-to-leaf record of exchanged values
- `Spec.Decoration` — per-node structure attachment
- `Spec.Decoration.Refine` — displayed decoration fibered over an existing one
- `Spec.Strategy` — one-player strategy with monadic effects (FreeT analog)
- `Spec.append` — dependent concatenation of specs
- `Spec.Strategy.comp` — sequential composition of strategies

## Universe polymorphism

`Spec.{u}` classifies interactions whose moves at each node live in `Type u`
(and `Spec.{u}` itself lives in `Type (u+1)`). `Transcript`, `Strategy`,
`BundledMonad`, and related definitions follow the same `u` so large universes
(e.g. `Type 1` moves) are first-class without artificial liftings.

## Related work

This framework independently converges with several lines of work:

- **Escardó–Oliva (2023)** "Higher-order Games with Dependent Types" (TCS 974):
  their Agda formalization uses type trees `𝑻` (= our `Spec`), paths `Path` (=
  `Transcript`), a generic `structure S` combinator (= `Decoration S`), and
  strategies (= `Strategy` sans monad). They use multiple independent decorations
  on the same tree (quantifier trees `𝓚`, selection-function trees `𝓙`), with
  `Overline` (= `Decoration.map`) converting between them. Our `Decoration.Refine`
  generalizes this to *dependent* decorations.
  [Code: martinescardo/TypeTopology]

- **Hancock–Setzer (2000)** "Interactive Programs in Dependent Type Theory":
  the key observation that interactive programs over a W-type interface are defined
  by structural recursion, sidestepping positivity/coinduction issues. Our
  `Strategy` is a direct instantiation of this pattern with monadic effects.

- **Interaction Trees** (Xia, Zakowski, et al., POPL 2020): coinductive free
  monad variant in Coq for representing recursive, impure programs. Our `Strategy`
  is the *inductive* (finite) analog, defined by structural recursion on a spec
  rather than coinductively.

- **Displayed algebras / Ornaments** (McBride 2010; Dagand–McBride 2014):
  `Decoration.Refine` is a "displayed decoration" — a fibered structure over an
  existing decoration — analogous to displayed algebras in category theory and
  ornaments in dependently typed programming.

- **Session types**: `Spec` paired with a role decoration (see `TwoParty.lean`)
  yields a dependent session type where the protocol structure depends on prior
  messages. Label-dependent session types (Thiemann–Vasconcelos 2019) and
  parameterized multiparty sessions (Deniélou–Yoshida 2011) are related.

## Future home

This library is intentionally standalone (no ArkLib imports) and is planned to
move to **VCVio** once the API stabilizes after the telescope refactor. VCVio
already provides the computation layer (`OracleComp`); this library adds the
interaction structure layer (`Spec`). Together they form the foundation for
ArkLib's protocol definitions and future MPC formalization efforts.
-/

set_option autoImplicit false

universe u v w

/-! ## Bundled monad -/

/-- Bundled monad (for storing inside inductive types where typeclasses are
not allowed). Standalone — no dependency on `Spec` or `TwoParty`. -/
structure BundledMonad where
  M : Type u → Type v
  inst : Monad M

instance BundledMonad.instMonad (bm : BundledMonad) : Monad bm.M := bm.inst

namespace Interaction

/-- An interaction specification (W-type). Internal nodes are labeled by move
types in `Type u`; children are indexed by moves. Leaves are `done`. -/
inductive Spec : Type (u + 1) where
  | done : Spec
  | node (Moves : Type u) (rest : Moves → Spec) : Spec

namespace Spec

/-- A transcript is a complete record of all values exchanged during an
interaction — a root-to-leaf sequence of moves. -/
def Transcript : Spec → Type u
  | .done => PUnit
  | .node X rest => (x : X) × Transcript (rest x)

/-- Decorate each internal node with structure `S`.
Used to attach metadata (monads, quantifiers, oracles, etc.) without polluting
the spec definition. Universe-polymorphic in `S` so node keys range over
`Type u` while attached data can live in `Type v` (e.g. `Role : Type u` or
`BundledMonad.{u} : Type (u + 1)`). -/
def Decoration (S : Type u → Type v) : Spec → Type (max u v)
  | .done => PUnit
  | .node X rest => S X × (∀ x, Decoration S (rest x))

/-- Apply a natural transformation to a decoration, changing the per-node
structure from `S` to `T`. -/
def Decoration.map {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (spec : Spec) → Decoration S spec → Decoration T spec
  | .done, _ => ⟨⟩
  | .node X rest, ⟨s, dRest⟩ => ⟨f X s, fun x => Decoration.map f (rest x) (dRest x)⟩

/-! ## Refined (displayed) decoration

`Decoration.Refine F spec d` is a decoration whose data at each node depends on
the label from an existing decoration `d`. This is the type-theoretic analog of a
**displayed algebra** (fibered structure over an existing one) or an **ornament**
(McBride 2010; Dagand–McBride 2014) that enriches a labelled tree with per-label
data without changing the underlying tree shape.

Escardó–Oliva (2023, TCS 974) use multiple *independent* decorations on the same
type tree (quantifier trees `𝓚`, selection-function trees `𝓙`). `Refine`
generalizes this to *dependent* decorations: the fiber at each node can depend on
the label from `d`. When the fiber ignores the label, `Refine` degenerates to an
independent `Decoration`. -/

/-- A refined decoration over a label decoration `d : Decoration L spec`. At each
node with label `l : L X`, carries data of type `F X l`, plus refined decorations
on all subtrees. -/
def Decoration.Refine {L : Type u → Type v} (F : ∀ X, L X → Type w) :
    (spec : Spec) → Decoration L spec → Type (max u w)
  | .done, _ => PUnit
  | .node X rest, ⟨l, dRest⟩ =>
      F X l × (∀ x, Decoration.Refine F (rest x) (dRest x))

/-- Apply a fiberwise transformation to a refined decoration. -/
def Decoration.Refine.map {L : Type u → Type v}
    {F : ∀ X, L X → Type w} {G : ∀ X, L X → Type w}
    (f : ∀ X l, F X l → G X l) :
    (spec : Spec) → (d : Decoration L spec) →
    Decoration.Refine F spec d → Decoration.Refine G spec d
  | .done, _, _ => ⟨⟩
  | .node X rest, ⟨l, dRest⟩, ⟨fData, rRest⟩ =>
      ⟨f X l fData, fun x => Refine.map f (rest x) (dRest x) (rRest x)⟩

/-! ## Strategy (Free Monad Transformer by recursion)

`Strategy m spec Output` plays through the interaction spec, interleaving
`m`-effects at each step, producing a transcript-dependent output. Defined by
**structural recursion on the spec**.

We keep monad, moves, transcript, and output in the same `Type u` so
`m (Strategy …)` typechecks with Lean's `Monad (Type u → Type u)`. -/

/-- One-player strategy with monadic effects. At each node, the player
**chooses** a move (Sigma) and performs `m`-work. -/
def Strategy (m : Type u → Type u) :
    (spec : Spec) → (Transcript spec → Type u) → Type u
  | .done, Output => Output ⟨⟩
  | .node X rest, Output =>
      (x : X) × m (Strategy m (rest x) (fun p => Output ⟨x, p⟩))

/-- Non-dependent output variant. -/
abbrev Strategy' (m : Type u → Type u) (spec : Spec) (α : Type u) :=
  Strategy m spec (fun _ => α)

/-! ## Execution -/

/-- Run a strategy, collecting the transcript and producing the output. -/
def Strategy.run {m : Type u → Type u} [Monad m] :
    (spec : Spec) → {Output : Transcript spec → Type u} →
    Strategy m spec Output → m ((tr : Transcript spec) × Output tr)
  | .done, _, output => pure ⟨⟨⟩, output⟩
  | .node _ rest, _, ⟨move, cont⟩ => do
      let next ← cont
      let ⟨tail, out⟩ ← run (rest move) next
      return ⟨⟨move, tail⟩, out⟩

/-- Map the output of a strategy (dependent natural transformation). -/
def Strategy.mapOutput {m : Type u → Type u} [Functor m] :
    {spec : Spec} → {A B : Transcript spec → Type u} →
    (∀ tr, A tr → B tr) → Strategy m spec A → Strategy m spec B
  | .done, _, _, f, a => f ⟨⟩ a
  | .node _ _, _, _, f, ⟨x, cont⟩ =>
      ⟨x, (mapOutput (fun p => f ⟨x, p⟩) ·) <$> cont⟩

/-! ## Structural combinators -/

/-- Dependent append of interaction specs. -/
def append : (s₁ : Spec) → (Transcript s₁ → Spec) → Spec
  | .done, s₂ => s₂ ⟨⟩
  | .node X rest, s₂ => .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))

/-- Join two transcripts into a transcript of the appended spec. -/
def Transcript.join :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Transcript (s₁.append s₂)
  | .done, _, _, tr₂ => tr₂
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ =>
      ⟨x, Transcript.join (rest x) (fun p => s₂ ⟨x, p⟩) tail₁ tr₂⟩

/-- Split a transcript of an appended spec into two parts. -/
def Transcript.split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    Transcript (s₁.append s₂) → (tr₁ : Transcript s₁) × Transcript (s₂ tr₁)
  | .done, _, tr => ⟨⟨⟩, tr⟩
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      let ⟨tr₁, tr₂⟩ := Transcript.split (rest x) (fun p => s₂ ⟨x, p⟩) tail
      ⟨⟨x, tr₁⟩, tr₂⟩

/-- Compose two strategies (dependent Kleisli composition). -/
def Strategy.comp {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ →
      m (Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.join s₁ s₂ tr₁ tr₂)))) →
    m (Strategy m (s₁.append s₂) Output)
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      comp (rest x) (fun p => s₂ ⟨x, p⟩) next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Extract the first-stage strategy from a composed strategy. The output of the
first stage is a strategy for the second stage, absorbing the path-dependence. -/
def Strategy.splitPrefix {m : Type u → Type u} [Functor m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m (s₁.append s₂) Output →
    Strategy m s₁ (fun tr₁ =>
      Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.join s₁ s₂ tr₁ tr₂)))
  | .done, _, _, p => p
  | .node _ rest, s₂, _, ⟨x, cont⟩ =>
      ⟨x, (splitPrefix (rest x) (fun p => s₂ ⟨x, p⟩) ·) <$> cont⟩

/-- Compose two decorations along `Spec.append`. -/
def Decoration.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    (d₁ : Decoration S s₁)
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) :
    Decoration S (s₁.append s₂) :=
  match s₁, d₁ with
  | .done, _ => d₂ ⟨⟩
  | .node _ _, ⟨s, dRest⟩ =>
      ⟨s, fun x => Decoration.append (dRest x)
        (fun p => d₂ ⟨x, p⟩)⟩

/-- Compose two refined decorations along `Spec.append`. -/
def Decoration.Refine.append {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {d₁ : Decoration L s₁}
    {d₂ : (tr₁ : Transcript s₁) → Decoration L (s₂ tr₁)}
    (r₁ : Decoration.Refine F s₁ d₁)
    (r₂ : (tr₁ : Transcript s₁) → Decoration.Refine F (s₂ tr₁) (d₂ tr₁)) :
    Decoration.Refine F (s₁.append s₂) (d₁.append d₂) :=
  match s₁, d₁, r₁ with
  | .done, _, _ => r₂ ⟨⟩
  | .node _ _, ⟨_, _⟩, ⟨fData, rRest⟩ =>
      ⟨fData, fun x => Refine.append (rRest x) (fun p => r₂ ⟨x, p⟩)⟩

/-! ### Naturality of `Decoration.map` over `append` -/

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem Decoration.map_append {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (d₁ : Decoration S s₁) →
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) →
    Decoration.map f (s₁.append s₂) (d₁.append d₂) =
      (Decoration.map f s₁ d₁).append (fun tr₁ => Decoration.map f (s₂ tr₁) (d₂ tr₁))
  | .done, _, _, _ => rfl
  | .node X rest, s₂, ⟨s, dRest⟩, d₂ => by
      simp only [Spec.append, Decoration.append, Decoration.map]
      congr 1; funext x
      exact map_append f (rest x) (fun p => s₂ ⟨x, p⟩) (dRest x) (fun p => d₂ ⟨x, p⟩)

/-! ### Round-trip lemmas for `join` / `split` -/

@[simp, grind =]
theorem Transcript.split_join :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    Transcript.split s₁ s₂ (Transcript.join s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩
  | .done, _, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ => by
      simp only [join, split]; rw [split_join]

@[simp]
theorem Transcript.join_split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    Transcript.join s₁ s₂ tr₁ tr₂ = tr
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ => by
      simp only [split, join]; rw [join_split]

/-! ### Unfolding lemmas for `append` (not `@[simp]` to avoid aggressive unfolding) -/

theorem append_done (s₂ : Transcript Spec.done → Spec) :
    Spec.done.append s₂ = s₂ ⟨⟩ := rfl

theorem append_node (X : Type u) (rest : X → Spec) (s₂ : Transcript (.node X rest) → Spec) :
    (Spec.node X rest).append s₂ =
      .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩)) := rfl

/-! ## N-ary composition

`chain` builds an N-stage interaction by threading a state type `Stage` through
iterated dependent appends. Each stage's spec can depend on the current state,
and `advance` computes the next state from the transcript of the current stage.

`replicate` is the special case where every stage uses the same spec. -/

/-- Non-dependent N-ary append: compose `n` copies of the same spec. -/
def replicate (spec : Spec) : (n : Nat) → Spec
  | 0 => .done
  | n + 1 => spec.append (fun _ => replicate spec n)

@[simp, grind =] theorem replicate_zero (spec : Spec) : spec.replicate 0 = .done := rfl

theorem replicate_succ (spec : Spec) (n : Nat) :
    spec.replicate (n + 1) = spec.append (fun _ => spec.replicate n) := rfl

/-- Join two transcripts into a transcript of `spec.replicate (n + 1)`. -/
abbrev Transcript.replicateCons (spec : Spec) (n : Nat) :
    Transcript spec → Transcript (spec.replicate n) →
    Transcript (spec.replicate (n + 1)) :=
  Transcript.join spec (fun _ => spec.replicate n)

/-- Split a transcript of `spec.replicate (n + 1)` into head and tail. -/
abbrev Transcript.replicateUncons (spec : Spec) (n : Nat) :
    Transcript (spec.replicate (n + 1)) →
    Transcript spec × Transcript (spec.replicate n) :=
  fun tr =>
    let ⟨hd, tl⟩ := Transcript.split spec (fun _ => spec.replicate n) tr
    (hd, tl)

/-- Join `n` transcripts into a transcript of `spec.replicate n`. -/
def Transcript.replicateJoin (spec : Spec) :
    (n : Nat) → (Fin n → Transcript spec) → Transcript (spec.replicate n)
  | 0, _ => ⟨⟩
  | n + 1, trs =>
      Transcript.join spec (fun _ => spec.replicate n)
        (trs 0) (Transcript.replicateJoin spec n (fun i => trs i.succ))

/-- Split a transcript of `spec.replicate n` into `n` individual transcripts. -/
def Transcript.replicateSplit (spec : Spec) :
    (n : Nat) → Transcript (spec.replicate n) → (Fin n → Transcript spec)
  | 0, _ => fun i => i.elim0
  | n + 1, tr => fun i =>
      let ⟨hd, tl⟩ := Transcript.split spec (fun _ => spec.replicate n) tr
      match i with
        | ⟨0, _⟩ => hd
        | ⟨i + 1, h⟩ => Transcript.replicateSplit spec n tl ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp, grind =]
theorem Transcript.replicateSplit_replicateJoin (spec : Spec) :
    (n : Nat) → (trs : Fin n → Transcript spec) → (i : Fin n) →
    Transcript.replicateSplit spec n (Transcript.replicateJoin spec n trs) i = trs i
  | 0, _, i => i.elim0
  | n + 1, trs, ⟨0, _⟩ => by
      simp [replicateSplit, replicateJoin, split_join]
  | n + 1, trs, ⟨i + 1, h⟩ => by
      simp only [replicateSplit, replicateJoin, split_join]
      exact replicateSplit_replicateJoin spec n (fun i => trs i.succ) ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Replicate a decoration `n` times along `Spec.replicate`. -/
def Decoration.replicate {S : Type u → Type v}
    {spec : Spec} (d : Decoration S spec) : (n : Nat) →
    Decoration S (spec.replicate n)
  | 0 => ⟨⟩
  | n + 1 => Decoration.append d (fun _ => Decoration.replicate d n)

/-- Replicate a refined decoration `n` times along `Spec.replicate`. -/
def Decoration.Refine.replicate {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {spec : Spec} {d : Decoration L spec}
    (r : Decoration.Refine F spec d) : (n : Nat) →
    Decoration.Refine F (spec.replicate n) (d.replicate n)
  | 0 => ⟨⟩
  | n + 1 => Refine.append r (fun _ => Refine.replicate r n)

/-- `Decoration.map` commutes with `Decoration.replicate`. -/
theorem Decoration.map_replicate {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) {spec : Spec} (d : Decoration S spec) :
    (n : Nat) →
    Decoration.map f (spec.replicate n) (d.replicate n) =
      (Decoration.map f spec d).replicate n
  | 0 => rfl
  | n + 1 => by
      simp only [Spec.replicate, Decoration.replicate]
      rw [Decoration.map_append]
      congr 1; funext _
      exact map_replicate f d n

/-- Iterate a strategy `n` times over `spec.replicate n`. Each iteration receives
the output of the previous one; the continuation constructs the next strategy. -/
def Strategy.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α → m (Strategy m spec (fun _ => α))) →
    α →
    m (Strategy m (spec.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    Strategy.comp spec (fun _ => spec.replicate n) strat
      (fun _ mid => iterate n (fun i => step i.succ) mid)

/-- Iterate the same strategy `n` times (uniform step). -/
def Strategy.iterateUniform {m : Type u → Type u} [Monad m]
    {spec : Spec} {α : Type u}
    (n : Nat) (step : α → m (Strategy m spec (fun _ => α))) (a : α) :
    m (Strategy m (spec.replicate n) (fun _ => α)) :=
  Strategy.iterate n (fun _ => step) a

/-! ## Dependent N-ary composition (chain)

`chain` generalizes `replicate`: it builds an N-stage interaction where each stage's
spec can depend on a state that evolves based on previous transcripts. The `Stage`
type family gives the state at each index, `spec` chooses the interaction for a
given state, and `advance` computes the next state from the transcript. -/

/-- N-stage dependent composition via a state machine. Builds the iterated dependent
append `spec i s ++ (λ tr => spec (i+1) (advance i s tr) ++ ...)` for `n` stages
starting at index `i` with state `s`. -/
def chain (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → Spec
  | 0, _, _ => .done
  | n + 1, i, s =>
      (spec i s).append (fun tr => chain Stage spec advance n (i + 1) (advance i s tr))

@[simp, grind =]
theorem chain_zero (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (i : Nat) (s : Stage i) :
    Spec.chain Stage spec advance 0 i s = .done := rfl

theorem chain_succ (Stage : Nat → Type u)
    (spec : (i : Nat) → Stage i → Spec)
    (advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1))
    (n : Nat) (i : Nat) (s : Stage i) :
    Spec.chain Stage spec advance (n + 1) i s =
      (spec i s).append (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr)) :=
  rfl

/-- `replicate` is a special case of `chain` with trivial state. -/
theorem replicate_eq_chain (spec : Spec) (n : Nat) (i : Nat) :
    spec.replicate n = Spec.chain (fun _ => PUnit) (fun _ _ => spec)
      (fun _ _ _ => ⟨⟩) n i ⟨⟩ := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [replicate, chain]
    congr 1; funext _; exact ih (i + 1)

/-- Split a chain transcript into the first stage and the remaining chain. -/
def Transcript.chainSplit
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) →
    (tr₁ : Transcript (spec i s)) ×
      Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁)) :=
  Transcript.split (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))

/-- Join a first-stage transcript with a remaining-chain transcript. -/
def Transcript.chainJoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript (Spec.chain Stage spec advance (n + 1) i s) :=
  Transcript.join (spec i s)
    (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr)) tr₁ tr₂

@[simp, grind =]
theorem Transcript.chainSplit_chainJoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr₁ : Transcript (spec i s))
    (tr₂ : Transcript (Spec.chain Stage spec advance n (i + 1) (advance i s tr₁))) :
    Transcript.chainSplit n i s (Transcript.chainJoin n i s tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_join _ _ _ _

/-- Compose a decoration along a chain. Each stage gets its decoration from `deco`. -/
def Decoration.chain {S : Type u → Type v}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (deco : (i : Nat) → (s : Stage i) → Decoration S (spec i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration S (Spec.chain Stage spec advance n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Decoration.append (deco i s)
        (fun tr => Decoration.chain deco n (i + 1) (advance i s tr))

/-- Compose a refined decoration along a chain. -/
def Decoration.Refine.chain {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {deco : (i : Nat) → (s : Stage i) → Decoration L (spec i s)}
    (rDeco : (i : Nat) → (s : Stage i) → Decoration.Refine F (spec i s) (deco i s)) :
    (n : Nat) → (i : Nat) → (s : Stage i) →
    Decoration.Refine F (Spec.chain Stage spec advance n i s)
      (Decoration.chain deco n i s)
  | 0, _, _ => ⟨⟩
  | n + 1, i, s =>
      Refine.append (rDeco i s)
        (fun tr => Refine.chain rDeco n (i + 1) (advance i s tr))

/-- Iterate a strategy family over a chain, threading a constant output type.
Each step produces a strategy for one stage; the output feeds into the next. -/
def Strategy.chainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {α : Type u}
    (step : (i : Nat) → (s : Stage i) → α →
      m (Strategy m (spec i s) (fun _ => α))) :
    (n : Nat) → (i : Nat) → (s : Stage i) → α →
    m (Strategy m (Spec.chain Stage spec advance n i s) (fun _ => α))
  | 0, _, _, a => pure a
  | n + 1, i, s, a => do
    let strat ← step i s a
    Strategy.comp (spec i s) (fun tr => Spec.chain Stage spec advance n (i + 1) (advance i s tr))
      strat (fun tr mid => chainComp step n (i + 1) (advance i s tr) mid)

/-! ## Non-dependent embedding -/

/-- Build an interaction spec from a list of move types. -/
def ofList : List (Type u) → Spec
  | [] => .done
  | T :: tl => .node T (fun _ => ofList tl)

/-! ## Per-node monad decoration -/

/-- Monad decoration on a spec: assigns a bundled monad to each node. -/
abbrev MonadDecoration :=
  Decoration (fun (_ : Type u) => BundledMonad)

/-- Strategy with per-node monads from a decoration. -/
def Strategy.withMonads :
    (spec : Spec.{u}) → MonadDecoration spec → (Transcript spec → Type u) → Type u
  | .done, _, Output => Output ⟨⟩
  | .node X rest, ⟨bm, dRest⟩, Output =>
      (x : X) × bm.M (withMonads (rest x) (dRest x) (fun p => Output ⟨x, p⟩))

/-- Run a per-node-monad strategy by lifting into a common base monad. -/
def Strategy.runWithMonads {m : Type u → Type u} [Monad m]
    (liftM : ∀ (bm : BundledMonad) {α : Type u}, bm.M α → m α) :
    (spec : Spec) → (deco : MonadDecoration spec) →
    {Output : Transcript spec → Type u} →
    Strategy.withMonads spec deco Output → m ((tr : Transcript spec) × Output tr)
  | .done, _, _, output => pure ⟨⟨⟩, output⟩
  | .node _ rest, ⟨bm, dRest⟩, _, ⟨x, cont⟩ => do
      let next ← liftM bm cont
      let ⟨tail, out⟩ ← runWithMonads liftM (rest x) (dRest x) next
      return ⟨⟨x, tail⟩, out⟩

end Spec
end Interaction
