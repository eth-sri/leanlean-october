module
public import LaterPairs.NativeSharpRow6

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace TaoTrudgianYang2025

/-- The genuine B A image of the native Sargos D Bourgain pair. -/
theorem exponentPair_BATY2 : ExponentPair (593/1736) (235/434) := by
  convert CubicJointCount.exponentPair_sargosD_bourgain.aProcess.bProcess using 1 <;> norm_num

