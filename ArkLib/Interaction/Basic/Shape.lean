/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Node
import ArkLib.Interaction.Basic.Decoration

/-!
# Generic local syntax over interaction trees

This file introduces the most general local core underlying the `Interaction`
framework on the syntax side.

`Spec.ShapeOver` is the local-syntax object:
it says what kind of node object an agent has at one protocol node, as a
function of
* the agent,
* the move space at that node,
* the realized node-local context available there, and
* the continuation family after each possible move.

The existing two-party and role-based notions are specializations of this more
general pattern:
* `Spec.Node.Context` is the semantic family of node-local data;
* `Spec.Node.Schema` is the telescope-style front-end for building such
  contexts;
* `Spec.Node.ContextHom` and `ShapeOver.comap` express contravariant
  reindexing of syntax along context morphisms;
* `fun _ => Role` is one example of a simple node context;
* `Counterpart`, `PublicCoinCounterpart`, and `withRoles` are specific shapes;
* the corresponding execution laws are introduced separately in
  `Basic/Interaction`.

Naming note:
`ShapeOver` keeps the suffix form because it is the primary generalized syntax
notion, with plain `Shape` recovered as the trivial-data specialization. This
differs from `Decoration.Over`, which is literally dependent data over a fixed
base decoration value.
-/

universe u a vΓ w

namespace Interaction
namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context}

/--
`ShapeOver Agent Γ` is the most general local-syntax object in the
interaction framework.

It answers the following question:

> Suppose we are standing at one protocol node whose move space is `X`.
> The node carries realized node-local context `γ : Γ X`.
> If the protocol continues with family `Cont : X → Type w`, what is the type
> of the local object that agent `a` stores at this node?

So a `ShapeOver` does **not** describe a whole protocol tree.
It describes the type of one local node object, uniformly for every possible:
* agent,
* move space,
* realized node-local context,
* continuation family.

The whole-tree notion is obtained later by structural recursion on `Spec` via
`ShapeOver.Family`.

This is the most general local syntax layer because:
* binary and multiparty interaction are both recovered by the choice of
  `Agent`;
* role-based interaction is recovered by choosing an appropriate context
  family `Γ`, for example `Γ := fun _ => Role`;
* richer staged metadata can be assembled via `Spec.Node.Schema` and then
  consumed through its realized context `Spec.Node.Schema.toContext`;
* the undecorated case is recovered by taking `Γ = Spec.Node.Context.empty`.
-/
structure ShapeOver
    (Agent : Type a)
    (Γ : Node.Context) where
  /--
  `Node a X γ Cont` is the type of the local object held by agent `a`
  at a node with:
  * move space `X`,
  * realized node-local context `γ : Γ X`,
  * continuation family `Cont : X → Type w`.

  The continuation is indexed by the next move `x : X`, because after choosing
  `x` the protocol does not continue in one fixed type: it continues in the
  subtree corresponding to that specific move.
  -/
  Node :
    (agent : Agent) →
    (X : Type u) →
    (γ : Γ X) →
    (X → Type w) →
    Type w

  /--
  `map` expresses that a node object is functorial in its continuation family.

  If we know how to transform each continuation value `A x` into a
  continuation value `B x`, then we can transform a local node object with
  continuation family `A` into one with continuation family `B`.

  Importantly, `map` does **not** change:
  * the agent,
  * the move space,
  * the node-local context,
  * or the move `x` that will eventually be chosen.

  It only reinterprets what happens *after* each possible move.
  This is the local ingredient needed to define the generic whole-tree
  `ShapeOver.mapOutput` below.
  -/
  map :
    {agent : Agent} →
    {X : Type u} →
    {γ : Γ X} →
    {A B : X → Type w} →
    (∀ x, A x → B x) →
    Node agent X γ A →
    Node agent X γ B

/--
`Shape Agent` is the specialization of `ShapeOver` with no node-local context.

This is the right facade when the protocol tree carries no node metadata at all.
Equivalently, it is `ShapeOver Agent Spec.Node.Context.empty`.
-/
abbrev Shape
    (Agent : Type a) :=
  ShapeOver Agent Node.Context.empty

/--
Reindex a local syntax object contravariantly along a node-context morphism.

If `f : Γ → Δ`, then any shape over `Δ` can be viewed as a shape over `Γ` by
first translating the local context value `γ : Γ X` into `f X γ : Δ X` and
then using the original `Δ`-shape there.

So `ShapeOver` is contravariant in its context parameter.
-/
def ShapeOver.comap {Δ : Node.Context}
    (shape : ShapeOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    ShapeOver Agent Γ where
  Node agent X γ Cont := shape.Node agent X (f X γ) Cont
  map h := shape.map h

/--
`ShapeOver.Family shape a spec ctxs Out` is the whole-tree participant
type for agent `a` induced by the local syntax `shape`.

Inputs:
* `spec` is the underlying protocol tree;
* `ctxs : Decoration Γ spec` assigns a realized node context to each node;
* `Out : Transcript spec → Type w` is the final output family at leaves.

The result is obtained by structural recursion on `spec`:
* at a leaf, the family is just the leaf output `Out`;
* at an internal node, the family is `shape.Node ...` applied to the
  recursively defined continuation family for each child subtree.

So `ShapeOver` is the **local syntax specification**, while `Family` is the induced
**whole-tree syntax** for one agent.
-/
def ShapeOver.Family
    (shape : ShapeOver Agent Γ) :
    (agent : Agent) →
    (spec : Spec) →
    Decoration Γ spec →
    (Transcript spec → Type w) →
    Type w
  | _, .done, _, Out => Out ⟨⟩
  | agent, .node X next, ⟨γ, ctxs⟩, Out =>
      shape.Node agent X γ (fun x =>
        Family shape agent (next x) (ctxs x) (fun tr =>
          Out ⟨x, tr⟩))

/--
`ShapeOver.mapOutput` lifts a pointwise transformation of leaf outputs to a
transformation of whole-tree participant objects.

This is the recursive global form of the local `ShapeOver.map` field.
It leaves the underlying interactive structure unchanged and only rewrites the
terminal output family.
-/
def ShapeOver.mapOutput
    (shape : ShapeOver Agent Γ)
    {agent : Agent}
    {spec : Spec}
    (ctxs : Decoration Γ spec)
    :
    {A B : Transcript spec → Type w} →
    (∀ tr, A tr → B tr) →
    ShapeOver.Family shape agent spec ctxs A →
    ShapeOver.Family shape agent spec ctxs B
  := by
    match spec, ctxs with
    | .done, _ =>
        intro A B f out
        exact f ⟨⟩ out
    | .node X next, ⟨γ, ctxs⟩ =>
        intro A B f node
        exact shape.map
          (agent := agent)
          (γ := γ)
          (fun x =>
            mapOutput shape
              (agent := agent)
              (spec := next x)
              (ctxs := ctxs x)
              (A := fun tr => A ⟨x, tr⟩)
              (B := fun tr => B ⟨x, tr⟩)
              (fun tr => f ⟨x, tr⟩))
          node

/--
Whole-tree families for `shape.comap f` are exactly families for `shape`
evaluated on the mapped decoration `Decoration.map f ctxs`.
-/
theorem ShapeOver.family_comap {Δ : Node.Context}
    (shape : ShapeOver Agent Δ) (f : Node.ContextHom Γ Δ) :
    {agent : Agent} → {spec : Spec} → (ctxs : Decoration Γ spec) →
    {Out : Transcript spec → Type w} →
    ShapeOver.Family (shape.comap f) agent spec ctxs Out =
      ShapeOver.Family shape agent spec (Decoration.map f spec ctxs) Out
  | _, .done, _, _ => rfl
  | agent, .node _ next, ⟨γ, ctxs⟩, Out => by
      simp only [ShapeOver.Family, ShapeOver.comap, Decoration.map]
      congr 1
      funext x
      exact family_comap shape f (agent := agent) (ctxs := ctxs x)
        (Out := fun tr => Out ⟨x, tr⟩)

end Spec
end Interaction
