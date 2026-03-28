/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Core
import ArkLib.Refactor.FiatShamir
import ArkLib.Refactor.LiftContext
import ArkLib.Refactor.Migration.SendAndRetain
import ArkLib.Refactor.OracleVerifier
import ArkLib.Refactor.Reduction
import ArkLib.Refactor.Security

/-!
# Refactor Migration Ring

Oracle-aware infrastructure and generic transformations that sit above the refactor
core and are intended to support protocol migration:

- `OracleVerifier`
- `Reduction`
- `LiftContext`
- `FiatShamir`
- migration helpers such as `SendAndRetain`
- generic security notions and composition theorems
-/
