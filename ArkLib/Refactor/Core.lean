/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.HVector
import ArkLib.Refactor.ProtocolSpec
import ArkLib.Refactor.Prover
import ArkLib.Refactor.Transcript
import ArkLib.Refactor.Verifier

/-!
# Refactor Core

Permanent kernel for the replacement IOR substrate:

- `ProtocolSpec`
- `HVector`
- `Transcript`
- `Prover`
- `Verifier`

Everything else in the refactor stack should build on top of this layer.
-/
