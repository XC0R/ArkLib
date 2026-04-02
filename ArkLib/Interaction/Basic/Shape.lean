/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
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
* a shared node tag,
* optional agent-local node data depending on that shared tag, and
* the continuation family after each possible move.

The existing two-party and role-based notions are specializations of this more
general pattern:
* `Role` is one choice of shared node tag;
* `Counterpart`, `PublicCoinCounterpart`, and `withRoles` are specific shapes;
* the corresponding execution laws are introduced separately in
  `Basic/Interaction`.

Naming note:
`ShapeOver` keeps the suffix form because it is the primary generalized syntax
notion, with plain `Shape` recovered as the trivial-data specialization. This
differs from `Decoration.Over`, which is literally dependent data over a fixed
base decoration value.
-/

universe u a vTag vData w

namespace Interaction
namespace Spec

variable {Agent : Type a}
variable {Tag : Type u → Type vTag}
variable {Data : Agent → ∀ X, Tag X → Type vData}

/--
`ShapeOver Agent Tag Data` is the most general local-syntax object in the
interaction framework.

It answers the following question:

> Suppose we are standing at one protocol node whose move space is `X`.
> The node carries a shared tag `tag : Tag X`.
> For a given agent `a`, it also carries agent-specific local data
> `data : Data a X tag`.
> If the protocol continues with family `Cont : X → Type w`, what is the type
> of the local object that agent `a` stores at this node?

So a `ShapeOver` does **not** describe a whole protocol tree.
It describes the type of one local node object, uniformly for every possible:
* agent,
* move space,
* shared node tag,
* agent-local node data,
* continuation family.

The whole-tree notion is obtained later by structural recursion on `Spec` via
`ShapeOver.Family`.

The separation between `Tag` and `Data` is intentional:

* `Tag X` is **shared node metadata**.
  Every agent sees the same tag at that node.
  Examples: owner of the node, kind of round, public protocol phase.

* `Data a X tag` is **agent-local metadata** for agent `a` at that node,
  allowed to depend on the shared tag.
  Examples: the monad used by that agent at that node, local privileges,
  agent-specific capabilities, or auxiliary bookkeeping needed only on that
  side.

This is the most general local syntax layer because:
* binary and multiparty interaction are both recovered by the choice of
  `Agent`;
* role-based interaction is recovered by taking `Tag X = Role`;
* the undecorated case is recovered by taking `Data a X tag = PUnit`.
-/
structure ShapeOver
    (Agent : Type a)
    (Tag : Type u → Type vTag)
    (Data : Agent → ∀ X, Tag X → Type vData) where
  /--
  `Node a X tag data Cont` is the type of the local object held by agent `a`
  at a node with:
  * move space `X`,
  * shared tag `tag : Tag X`,
  * agent-local data `data : Data a X tag`,
  * continuation family `Cont : X → Type w`.

  The continuation is indexed by the next move `x : X`, because after choosing
  `x` the protocol does not continue in one fixed type: it continues in the
  subtree corresponding to that specific move.
  -/
  Node :
    (agent : Agent) →
    (X : Type u) →
    (tag : Tag X) →
    Data agent X tag →
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
  * the shared tag,
  * the agent-local data,
  * or the move `x` that will eventually be chosen.

  It only reinterprets what happens *after* each possible move.
  This is the local ingredient needed to define the generic whole-tree
  `ShapeOver.mapOutput` below.
  -/
  map :
    {agent : Agent} →
    {X : Type u} →
    {tag : Tag X} →
    {data : Data agent X tag} →
    {A B : X → Type w} →
    (∀ x, A x → B x) →
    Node agent X tag data A →
    Node agent X tag data B

/--
`Shape Agent Tag` is the specialization of `ShapeOver` with no agent-local
per-node data.

This is the right facade when the only metadata that matters is the shared node
tag `Tag`, and every agent carries no additional local annotation.
Equivalently, it is `ShapeOver Agent Tag (fun _ _ _ => PUnit)`.
-/
abbrev Shape
    (Agent : Type a)
    (Tag : Type u → Type vTag) :=
  ShapeOver Agent Tag (fun _ _ _ => PUnit)

/--
`ShapeOver.Family shape a spec tags data Out` is the whole-tree participant
type for agent `a` induced by the local syntax `shape`.

Inputs:
* `spec` is the underlying protocol tree;
* `tags : Decoration Tag spec` assigns a shared tag to each node;
* `data : Decoration.Over (fun X tag => Data a X tag) spec tags` assigns
  agent-`a`'s local data over those shared tags;
* `Out : Transcript spec → Type w` is the final output family at leaves.

The result is obtained by structural recursion on `spec`:
* at a leaf, the family is just the leaf output `Out`;
* at an internal node, the family is `shape.Node ...` applied to the
  recursively defined continuation family for each child subtree.

So `ShapeOver` is the **local syntax**, while `Family` is the induced
**whole-tree syntax** for one agent.
-/
def ShapeOver.Family
    (shape : ShapeOver Agent Tag Data) :
    (agent : Agent) →
    (spec : Spec) →
    (tags : Decoration Tag spec) →
    Decoration.Over (fun X tag => Data agent X tag) spec tags →
    (Transcript spec → Type w) →
    Type w
  | _, .done, _, _, Out => Out ⟨⟩
  | agent, .node X next, ⟨tag, tags⟩, ⟨data, datas⟩, Out =>
      shape.Node agent X tag data (fun x =>
        Family shape agent (next x) (tags x) (datas x) (fun tr =>
          Out ⟨x, tr⟩))

/--
`ShapeOver.mapOutput` lifts a pointwise transformation of leaf outputs to a
transformation of whole-tree participant objects.

This is the recursive global form of the local `ShapeOver.map` field.
It leaves the underlying interactive structure unchanged and only rewrites the
terminal output family.
-/
def ShapeOver.mapOutput
    (shape : ShapeOver Agent Tag Data)
    {agent : Agent}
    {spec : Spec}
    (tags : Decoration Tag spec)
    (data : Decoration.Over (fun X tag => Data agent X tag) spec tags)
    :
    {A B : Transcript spec → Type w} →
    (∀ tr, A tr → B tr) →
    ShapeOver.Family shape agent spec tags data A →
    ShapeOver.Family shape agent spec tags data B
  := by
    match spec, tags, data with
    | .done, _, _ =>
        intro A B f out
        exact f ⟨⟩ out
    | .node X next, ⟨tag, tags⟩, ⟨nodeData, datas⟩ =>
        intro A B f node
        exact shape.map
          (agent := agent)
          (tag := tag)
          (data := nodeData)
          (fun x =>
            mapOutput shape
              (agent := agent)
              (spec := next x)
              (tags := tags x)
              (data := datas x)
              (A := fun tr => A ⟨x, tr⟩)
              (B := fun tr => B ⟨x, tr⟩)
              (fun tr => f ⟨x, tr⟩))
          node

end Spec
end Interaction
