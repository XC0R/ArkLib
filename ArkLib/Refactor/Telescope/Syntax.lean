import ArkLib.Refactor.Telescope.Boundary
import ArkLib.Refactor.Telescope.Syntax.Core

/-!
# Telescope Syntax

Umbrella syntax surface for telescope-native protocol authoring.

`ArkLib.Refactor.Telescope.Syntax.Core` contains the low-level term macros that only
depend on `Basic`, so core files can use them without import cycles. This umbrella
adds higher-level convenience aliases that depend on boundary/reduction code.
-/

namespace ProtocolCtx

namespace Reduction

/-- Opt-in ergonomic alias for the common input-only pullback wrapper. -/
@[inline] abbrev inputOnly := @_root_.ProtocolCtx.Reduction.pullbackInputOnly

end Reduction

namespace OracleReduction

/-- Opt-in ergonomic alias for the oracle-indexed input-only pullback wrapper. -/
@[inline] abbrev inputOnly := @_root_.ProtocolCtx.OracleReduction.pullbackInputOnly

end OracleReduction

end ProtocolCtx
