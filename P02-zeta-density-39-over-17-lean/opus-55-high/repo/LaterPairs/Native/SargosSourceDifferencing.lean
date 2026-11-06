module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosDualTentWindow
public import LaterPairs.Native.SargosInitialInterval
public import LaterPairs.Native.SargosSymmetricAveraging
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                       

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_sum_Ico_add_one {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (M : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, f (m+1)) = ∑ m ∈ Finset.Ioc (0:ℤ) M, f m := by
  pm_8040
  grind
  grind
  · intro n hn
    have h := Finset.mem_Ioc.mp hn
    refine ⟨n-1,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  grind

end TaoTrudgianYang2025
