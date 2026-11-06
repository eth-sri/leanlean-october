module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosPlanarKernel
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                           

noncomputable section

open MeasureTheory GafniTao
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

def sargosPlanarSum {ι : Type*} (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ)
    (α γ : ℝ) : ℂ :=
  ∑ i ∈ S, z i*fordAdditiveCharacter (u i*α+v i*γ)

def sargosNearPairs {ι : Type*} (S : Finset ι) (u v : ι → ℝ)
    (a b : ℝ) : Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter (fun p => |u p.1-u p.2| ≤ a ∧ |v p.1-v p.2| ≤ b)

def sargosWeightedPlanarIntegrand {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (a b c d α γ : ℝ) : ℝ :=
  sargosSincKernel a (α-c)*sargosSincKernel b (γ-d)*‖sargosPlanarSum S z u v α γ‖^2

section
variable {ι : Type*} (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ)
include ι S z u v
theorem sargosPlanarSum_norm_sq (α γ : ℝ) :
    ((‖sargosPlanarSum S z u v α γ‖^2 : ℝ) : ℂ) =
      ∑ p ∈ S ×ˢ S, z p.1*conj (z p.2)*
        fordAdditiveCharacter ((u p.1-u p.2)*α+(v p.1-v p.2)*γ) := by
  calc
    _ = sargosPlanarSum S z u v α γ*conj (sargosPlanarSum S z u v α γ) := by
      rw [Complex.mul_conj']
      norm_num
    _ = _ := by
      unfold sargosPlanarSum
      rw [map_sum,Finset.sum_mul_sum,Finset.sum_product]
      pm_2535
      calc
        _ = (z i*conj (z j))*
            (fordAdditiveCharacter (u i*α+v i*γ)*
              fordAdditiveCharacter (-(u j*α+v j*γ))) := by ring
        _ = _ := by
          rw [← fordAdditiveCharacter_add]
          congr 2
          ring

theorem sargosWeightedPlanarIntegrand_eq_gram (a b c d α γ : ℝ) :
    (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ) =
      ∑ p ∈ S ×ˢ S, (z p.1*conj (z p.2))*
        sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ := by
  unfold sargosWeightedPlanarIntegrand
  rw [Complex.ofReal_mul,Complex.ofReal_mul,sargosPlanarSum_norm_sq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold sargosPlanarKernelTerm
  ring

theorem sargosWeightedPlanarIntegrand_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (c d α γ : ℝ) :
    0 ≤ sargosWeightedPlanarIntegrand S z u v a b c d α γ :=
  mul_nonneg (mul_nonneg (sargosSincKernel_nonneg ha _) (sargosSincKernel_nonneg hb _))
    (sq_nonneg _)
end

end TaoTrudgianYang2025
