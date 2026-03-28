/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Interaction specifications (`Spec`) and transcripts

This file defines the W-type of interaction trees (`Interaction.Spec`) and complete plays
(`Spec.Transcript`). Further structure lives in sibling modules under `ArkLib.Interaction.Basic`:

* `Decoration` — labels on nodes
* `Strategy` — one-player strategies with monadic effects
* `Append`, `Replicate`, `Chain` — composition and iteration of specs

## References

Hancock–Setzer (2000) on recursion over interaction interfaces; Escardó–Oliva (2023, TCS 974) on
games as type trees; displayed algebras / ornaments for `Decoration.Refine` (McBride; Dagand–McBride).
-/

set_option autoImplicit false

universe u

namespace Interaction

/-- Interaction specification (W-type): internal nodes carry a move type `Moves : Type u` and
sub-specs indexed by chosen moves; leaves are `done`. -/
inductive Spec : Type (u + 1) where
  | /-- Empty protocol (no moves). -/
    done : Spec
  | /-- One round: choose `x : Moves`, then continue with `rest x`. -/
    node (Moves : Type u) (rest : Moves → Spec) : Spec

namespace Spec

/-- A transcript is a root-to-leaf path through a spec: at each internal node, a chosen move and
a transcript for the continuation. -/
def Transcript : Spec → Type u
  | .done => PUnit
  | .node X rest => (x : X) × Transcript (rest x)

/-- Build a linear spec from a list of move types (non-dependent `node` chain). -/
def ofList : List (Type u) → Spec
  | [] => .done
  | T :: tl => .node T (fun _ => ofList tl)

end Spec
end Interaction
