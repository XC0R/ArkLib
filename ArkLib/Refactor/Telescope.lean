/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Telescope.Basic
import ArkLib.Refactor.Telescope.OracleVerifier
import ArkLib.Refactor.Telescope.Reduction
import ArkLib.Refactor.Telescope.Boundary
import ArkLib.Refactor.Telescope.Syntax
import ArkLib.Refactor.Telescope.FiatShamir
import ArkLib.Refactor.Telescope.Security
import ArkLib.Refactor.Telescope.Sumcheck

/-!
# Telescopic Protocol Specifications

Compatibility umbrella for the telescope-native refactor substrate.

- `ArkLib.Refactor.Telescope.Basic` contains the core `ProtocolCtx` / `ProtocolCtxM`
  definitions and composition utilities.
- `ArkLib.Refactor.Telescope.OracleVerifier` and `.Reduction` provide the
  oracle-aware runtime surface.
- `ArkLib.Refactor.Telescope.Boundary` prototypes the new root-boundary /
  stage-boundary lifting substrate.
- `ArkLib.Refactor.Telescope.Syntax` provides opt-in presentation sugar such as
  `rounds!`, `prover!`, `verifier!`, and `⟪...⟫`.
- `ArkLib.Refactor.Telescope.FiatShamir` contains the telescope-native replay-oracle
  and messages-only Fiat-Shamir kernel.
- `ArkLib.Refactor.Telescope.Security` contains the semantic soundness bridge
  and generic composition layer.
- `ArkLib.Refactor.Telescope.Sumcheck` is the first end-to-end protocol slice on
  top of the telescope stack.
-/
