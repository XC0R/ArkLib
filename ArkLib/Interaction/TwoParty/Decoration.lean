/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

set_option autoImplicit false

universe u

namespace Interaction

/-- Per-node sender/receiver assignment on a `Spec`. -/
abbrev RoleDecoration := Spec.Decoration (fun _ => Role)

/-- Swap sender ↔ receiver at every node. -/
abbrev RoleDecoration.swap {spec : Spec} (roles : RoleDecoration spec) :
    RoleDecoration spec :=
  Spec.Decoration.map (fun _ => Role.swap) spec roles

/-- Append role decorations along `Spec.append` (pointwise `Decoration.append`). -/
abbrev RoleDecoration.append {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
    (r₁ : RoleDecoration s₁)
    (r₂ : (tr₁ : Spec.Transcript s₁) → RoleDecoration (s₂ tr₁)) :
    RoleDecoration (s₁.append s₂) :=
  Spec.Decoration.append r₁ r₂

end Interaction
