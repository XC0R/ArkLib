/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec

/-!
# Node-local contexts and schemas

This file isolates the node-local metadata layer of the `Interaction`
framework.

`Spec.Node.Context` is the semantic notion:
for each move space `X`, it gives the type of node-local information available
at a node whose next move lives in `X`.

`Spec.Node.Schema` is the structured, telescope-style front-end for building
such contexts in stages. This follows the use of **contexts** and
**telescopes** in dependent type theory, where later entries may depend on
earlier ones, and it also echoes the **schema / instance** split common in
database theory.

References informing this terminology:
* de Bruijn (1991), telescopes in dependent type theory;
* Castellan–Clairambault–Dybjer (2020), contexts and types in context via
  categories with families;
* Spivak (2012), schemas as structured descriptions whose instances carry data.

The rest of the interaction core consumes realized node contexts, not schemas:
* `Spec.Decoration Γ spec` decorates a protocol tree by concrete values in
  context `Γ`;
* `Spec.ShapeOver` and `Spec.InteractionOver` define syntax and execution over
  those realized contexts.
-/

universe u v

namespace Interaction
namespace Spec
namespace Node

/--
`Context` is the realized family of node-local information.

If `Γ : Node.Context`, then for every move space `X`, the type `Γ X` describes
what metadata is available at a node whose next move lies in `X`.

This is the semantic object consumed by the rest of the interaction core.
Contexts may be written directly, or assembled in stages via `Node.Schema`.
-/
abbrev Context := Type u → Type v

/--
The empty node context, carrying no information at any node.

This is the neutral context used by the plain `Shape` / `Interaction`
specializations.
-/
def Context.empty : Context := fun _ => PUnit

/--
Extend a realized node context by one dependent field.

If `Γ` is the current context and `A X γ` is a new field whose type may depend
on the existing context value `γ : Γ X`, then `Γ.extend A` is the enlarged
context containing both pieces of data.
-/
def Context.extend (Γ : Context) (A : ∀ X, Γ X → Type v) : Context :=
  fun X => Σ γ : Γ X, A X γ

/--
`Schema Γ` is a telescope whose realized node context is `Γ`.

Schemas are the structured front-end for building node-local contexts:
* `nil` is the empty telescope;
* `singleton A` is a one-field schema with no prior dependencies;
* `snoc S A` appends a new field whose type may depend on the earlier realized
  context carried by `S`.

The semantic object used elsewhere in the interaction core is still the
realized context `Γ`; a schema is simply a readable way to assemble such
contexts stage by stage, while keeping the dependency structure visible.
-/
inductive Schema : Context → Type (max (u + 1) (v + 1)) where
  /-- The empty schema. -/
  | nil : Schema Context.empty
  /-- A one-field schema whose realized context is exactly `A`. -/
  | singleton (A : Type u → Type v) : Schema A
  /-- Extend an existing schema by one further dependent field. -/
  | snoc {Γ : Context} (S : Schema Γ) (A : ∀ X, Γ X → Type v) :
      Schema (Γ.extend A)

/--
Interpret a node schema as its realized node context.

This uses the active name `toContext` rather than a noun like `context`
because a schema is a descriptive telescope, while a context is the semantic
family it determines.
-/
abbrev Schema.toContext {Γ : Context} (_ : Schema Γ) : Context := Γ

end Node
end Spec
end Interaction
