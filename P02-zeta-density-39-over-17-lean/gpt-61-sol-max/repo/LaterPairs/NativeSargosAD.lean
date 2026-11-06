module
public import LaterPairs.Native.SquareProductCount

@[expose] public section

namespace TaoTrudgianYang2025.CubicJointCount
open Expdb
open scoped NNReal

/-- Genuine A image of the native Sargos-D pair, used in the third new pair's
remaining beta cover. All analytic estimates are supplied by the native source. -/
theorem exponentPair_sargosAD_bourgain : ExponentPair (9/217) (1461/1736) := by
  convert exponentPair_sargosD_bourgain.aProcess using 1 <;> norm_num


