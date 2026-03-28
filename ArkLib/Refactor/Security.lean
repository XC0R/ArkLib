/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Refactor.Security.Composition
import ArkLib.Refactor.Security.Defs
import ArkLib.Refactor.Security.StateFunction
import ArkLib.Refactor.Security.StateRestoration

/-!
# Refactor Security

Security layer for the replacement IOR substrate.

This umbrella deliberately excludes protocol-specific security developments such as
sumcheck, which should sit above the generic refactor security framework.
-/
