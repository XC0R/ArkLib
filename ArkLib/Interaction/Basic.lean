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

This is the Hancock-Setzer (2000) observation: interactive programs in dependent
type theory are defined by recursion on the interaction *interface*, not as a
separate coinductive type.

## Main definitions

- `Spec` — W-type interaction specification with typed moves at each node
- `Spec.Transcript` — root-to-leaf record of exchanged values
- `Spec.Decoration` — per-node structure attachment
- `Spec.Strategy` — one-player strategy with monadic effects (FreeT analog)
- `Spec.append` — dependent concatenation of specs
- `Spec.Strategy.comp` — sequential composition of strategies

## Universe polymorphism

`Spec.{u}` classifies interactions whose moves at each node live in `Type u`
(and `Spec.{u}` itself lives in `Type (u+1)`). `Transcript`, `Strategy`,
`BundledMonad`, and related definitions follow the same `u` so large universes
(e.g. `Type 1` moves) are first-class without artificial liftings.

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
    (spec : Spec.{u}) → (deco : MonadDecoration spec) →
    {Output : Transcript spec → Type u} →
    Strategy.withMonads spec deco Output → m ((tr : Transcript spec) × Output tr)
  | .done, _, _, output => pure ⟨⟨⟩, output⟩
  | .node _ rest, ⟨bm, dRest⟩, _, ⟨x, cont⟩ => do
      let next ← liftM bm cont
      let ⟨tail, out⟩ ← runWithMonads liftM (rest x) (dRest x) next
      return ⟨⟨x, tail⟩, out⟩

end Spec
end Interaction
