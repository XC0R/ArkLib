/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.Refactor.Sumcheck.Security

/-!
# Legacy Sumcheck Compatibility Import

The supported sumcheck protocol definitions and security theorems now live under
`ArkLib.Refactor.Sumcheck.*`.

This module intentionally no longer redefines the legacy `Fin`-indexed general
sumcheck protocol. It remains only as a stable import path for downstream files
that have not yet switched their imports.
-/
