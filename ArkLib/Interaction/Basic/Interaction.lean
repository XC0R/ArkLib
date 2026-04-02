/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Node
import ArkLib.Interaction.Basic.Shape

/-!
# Generic local execution laws over interaction trees

This file introduces the execution-side counterpart to `Spec.ShapeOver`.

`Spec.InteractionOver` is a local operational law for agent-indexed node
objects. It says how a whole profile of local objects, one for each agent, is
combined at a single protocol node in order to choose the next move and
continue the interaction. The node-local information seen by those objects is
packaged as a realized `Spec.Node.Context`.

The role-based prover/verifier runners used elsewhere in the library are
specializations of this more general notion, obtained by choosing suitable
node contexts and shapes.

Naming note:
`InteractionOver` keeps the suffix form for the same reason as `ShapeOver`:
it is the primary generalized execution notion, while `Interaction` is its
trivial-data specialization rather than a base value that `InteractionOver`
depends on.
-/

universe u a vΓ w

namespace Interaction
namespace Spec

variable {Agent : Type a}
variable {Γ : Node.Context}

/--
`InteractionOver Agent Γ shape m` is the most general local execution
law for agent-indexed participant objects.

It answers the following question:

> Suppose we are standing at one protocol node with move space `X`.
> Every agent `a` has a local node object of type
> `shape.Node a X γ (Cont a)`.
> How do we execute this node, choose the next move `x : X`, and continue with
> the continuation values of all agents at that `x`?

So:
* `ShapeOver` describes the **local syntax** available to each agent;
* `InteractionOver` describes the **local operational semantics** for one
  protocol step built from that syntax.

This is the level at which the execution discipline lives:
who chooses the move, how it is sampled or observed, how the local node objects
synchronize, and how effects in `m` are used.
-/
structure InteractionOver
    (Agent : Type a)
    (Γ : Node.Context)
    (shape : ShapeOver Agent Γ)
    (m : Type w → Type w) where
  /--
  `interact` executes one protocol node.

  Inputs:
  * a move space `X`;
  * realized node-local context `γ : Γ X`;
  * for each agent `a`, a local node object
    `shape.Node a X γ (Cont a)`;
  * a continuation `k` explaining how to proceed once a move `x : X` has been
    chosen and each agent supplies its continuation value at that `x`.

  Output:
  * one monadic step of type `m Result`.

  In other words, `interact` is the one-step execution rule for the whole
  agent profile at this node.
  -/
  interact :
    {X : Type u} →
    {γ : Γ X} →
    {Cont : Agent → X → Type w} →
    {Result : Type w} →
    ((agent : Agent) → shape.Node agent X γ (Cont agent)) →
    ((x : X) → ((agent : Agent) → Cont agent x) → m Result) →
    m Result

/--
`Interaction Agent shape m` is the specialization of `InteractionOver` with no
node-local context.

This is the right facade when the protocol tree carries no node metadata at
all. Equivalently, it is
`InteractionOver Agent Spec.Node.Context.empty shape m`.
-/
abbrev Interaction
    (Agent : Type a)
    (shape : Shape Agent)
    (m : Type w → Type w) :=
  InteractionOver Agent Node.Context.empty shape m

section Run

variable {Agent : Type u}
variable {Γ : Node.Context}
variable {shape : ShapeOver Agent Γ}
variable {m : Type u → Type u}

/--
Execute a whole protocol tree using the local one-step law `interact`.

Inputs:
* `spec` is the underlying interaction tree;
* `ctxs : Decoration Γ spec` supplies the realized node context at each node;
* `Out : Agent → Transcript spec → Type u` is the final output family for each
  agent;
* `profile` supplies, for every agent, that agent's whole-tree participant
  object induced by `shape`.

Output:
* a monadic computation producing
  * a concrete transcript `tr`, and
  * for each agent `a`, the final output `Out a tr` obtained by following that
    transcript.

So `run` is the whole-tree execution induced by the local execution law
`InteractionOver.interact`. It is the generic profile-level analogue of the
specialized two-party runners elsewhere in the library.

This first executable version is intentionally specialized to the common
single-universe setting used throughout the current interaction layer. The
underlying `ShapeOver` and `InteractionOver` abstractions remain more general.
-/
def InteractionOver.run
    (I : InteractionOver Agent Γ shape m) [Monad m]
    {spec : Spec}
    (ctxs : Decoration Γ spec)
    {Out : Agent → Transcript spec → Type u}
    (profile :
      (agent : Agent) → ShapeOver.Family shape agent spec ctxs (Out agent)) :
    m ((tr : Transcript spec) × ((agent : Agent) → Out agent tr)) :=
  match spec, ctxs with
  | .done, _ => pure ⟨PUnit.unit, profile⟩
  | .node _ next, ⟨γ, ctxs⟩ =>
      I.interact
        (γ := γ)
        (Cont := fun agent x =>
          ShapeOver.Family shape agent (next x) (ctxs x)
            (fun tr => Out agent ⟨x, tr⟩))
        (fun agent => profile agent)
        (fun x conts => do
          let ⟨tr, out⟩ ← run I
            (ctxs := ctxs x)
            (Out := fun agent tr => Out agent ⟨x, tr⟩)
            conts
          pure ⟨⟨x, tr⟩, out⟩)

end Run

end Spec
end Interaction
