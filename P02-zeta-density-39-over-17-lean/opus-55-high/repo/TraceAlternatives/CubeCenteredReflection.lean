module
public import TraceAlternatives.CubeReflectionSecond
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def cubeLocalReflectionBudget (T L H R E : ℝ) : ℝ :=
  ((H/L)^2+T^(1/3:ℝ)*(H/L))*R^(2/3:ℝ)*E^(1/3:ℝ)

theorem reflection_local_energy_cube {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ L H : ℝ,2≤T → Real.sqrt T≤L → 0<H → H≤2*T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        (∀ t∈W,∀ u∈W,t≠u → 1≤|t-u|) →
        MathCollab.Density.localReflectionEnergy L H W ≤
          C*T^η*cubeLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := reflection_complete_pair_energy_cube hη
  pm_508 _hSep
  have hTp : 0<T := by linarith
  have hRoot : 0<Real.sqrt T := Real.sqrt_pos.mpr hTp
  have hLp : 0<L := hRoot.trans_le hL
  let X : ℝ := H/L
  have hX : 0<X := div_pos hH hLp
  have hXbound : X≤2*Real.sqrt T := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith [Real.sq_sqrt hTp.le,
      mul_nonneg (sub_nonneg.mpr hL) (Real.sqrt_nonneg T)]
  let S := cubeLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)
  have hS : 0≤S := by dsimp [S,cubeLocalReflectionBudget]; positivity
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M∈reflectionBlocks L H) :
      (∑' j : ℤ,completePairEnergy M (localSet W H j)) ≤ 12*(C*T^η*S) := by
    pm_5763 hLp
    have hMU : (M:ℝ)≤2*X := by
      apply hMhi.trans
      dsimp [X]
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0<Real.pi*L) hLp).mpr
      nlinarith [Real.pi_gt_three,mul_pos hH hLp]
    have hMT : (M:ℝ)≤4*Real.sqrt T := by linarith
    pm_528 h hBound T t₀ hT M hM0 hMT W hW
    pm_497
    have hMono : ((M:ℝ)^2+T^(1/3:ℝ)*M)*
        (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) ≤ 4*S := by
      pm_7684 hMU
      have hQuad : (M:ℝ)^2+T^(1/3:ℝ)*M ≤ 4*(X^2+T^(1/3:ℝ)*X) := by
        nlinarith [mul_nonneg (Real.rpow_nonneg hTp.le (1/3:ℝ)) hX.le]
      calc
        _ ≤ (4*(X^2+T^(1/3:ℝ)*X))*
            (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by gcongr
        _ = _ := by dsimp only [S,cubeLocalReflectionBudget,X]; ring
    have hGrouped : completePairEnergy M W ≤ C*T^η*
        (((M:ℝ)^2+T^(1/3:ℝ)*M)*
          (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ)) := by
      convert h using 1
      ring
    pm_2726
  pm_163

end Montgomery.RationalMoment
