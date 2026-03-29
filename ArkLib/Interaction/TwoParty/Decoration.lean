/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Basic.Append
import ArkLib.Interaction.TwoParty.Role

/-!
# Role decorations

A `RoleDecoration spec` is a `Spec.Decoration` with fiber `fun _ => Role`: each internal node is
labeled sender or receiver. This replaces a separate two-party interaction inductive while reusing
all `Spec` infrastructure (`Transcript`, `append`, etc.).
-/

universe u

namespace Interaction

/-- Per-node sender/receiver assignment on a `Spec`. -/
abbrev RoleDecoration := Spec.Decoration (fun _ => Role)

namespace Spec
namespace Decoration

/-- Swap sender ↔ receiver at each node.

Because `RoleDecoration` is an `abbrev` of `Decoration (fun _ => Role)`, dot notation on
`roles : RoleDecoration spec` resolves this `Spec.Decoration.swap` (not `RoleDecoration.swap`). -/
def swap {spec : Spec} (roles : Decoration (fun _ => Role) spec) :
    Decoration (fun _ => Role) spec :=
  map (fun _ => Role.swap) spec roles

end Decoration
end Spec

/-- Explicit `RoleDecoration.swap roles` is the same as `roles.swap` (`Spec.Decoration.swap`). -/
abbrev RoleDecoration.swap {spec : Spec} (roles : RoleDecoration spec) : RoleDecoration spec :=
  Spec.Decoration.swap roles

/-- Append role decorations along `Spec.append` (pointwise `Decoration.append`). -/
abbrev RoleDecoration.append {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    (r₁ : RoleDecoration s₁)
    (r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)) :
    RoleDecoration (s₁.append s₂) :=
  Spec.Decoration.append r₁ r₂

end Interaction
