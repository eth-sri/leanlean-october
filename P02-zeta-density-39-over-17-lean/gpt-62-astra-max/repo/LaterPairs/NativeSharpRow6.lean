module
public import LaterPairs.Native.SquareProductCount
public import TaoTrudgianYang2025.ExponentPairBProcess

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025

/-- The exact B A image of the native new Trudgian--Yang pair. -/
theorem exponentPair_BATYnew2 : ExponentPair (107193/345640) (47947/86410) := by
  convert CubicJointCount.exponentPair_aTrudgianYang_first.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025
