module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport

/-!
# Positive-part reverse-time Steklov energy identities

This module proves the fixed-window energy identities for the positive part of
forward and backward reverse-time Steklov averages.  The chain rule is obtained
from the convex support inequalities for the squared `L²` norm of the positive
part; no derivative of the positive-part curve is asserted.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable (x z : ℝ)

private theorem positivePart_mul_sub_le_half_sq_sub_sq  :
    max z 0 * (x - z) ≤ ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

private theorem half_sq_sub_sq_le_positivePart_mul_sub  :
    ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 ≤ max x 0 * (x - z) := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

/-- Half the squared pivot norm of the positive part. -/
def positivePartHalfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (v : H10HilbertGraph hΩ) : ℝ :=
  (1 / 2 : ℝ) * ‖valueCLM hΩ (h10PositivePart hΩ v)‖ ^ 2

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (hΩ : IsOpen Ω)



private theorem scalarLp_positivePart_support_lower
     :
    inner ℝ (MeasureTheory.Lp.posPart z) (f - z) ≤
      (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 := by
  rw [scalarLp_norm_sq_eq_integral_sq,
    scalarLp_norm_sq_eq_integral_sq]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq _).const_mul _)
      ((scalarLp_integrable_sq _).const_mul _)]
  apply integral_mono_ae
    (L2.integrable_inner _ _)
    (((scalarLp_integrable_sq _).const_mul _).sub
      ((scalarLp_integrable_sq _).const_mul _))
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [positivePart_mul_sub_le_half_sq_sub_sq (f a) (z a)]

private theorem scalarLp_positivePart_support_upper
     :
    (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 ≤
      inner ℝ (MeasureTheory.Lp.posPart f) (f - z) := by
  rw [scalarLp_norm_sq_eq_integral_sq,
    scalarLp_norm_sq_eq_integral_sq]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq _).const_mul _)
      ((scalarLp_integrable_sq _).const_mul _)]
  apply integral_mono_ae
    (((scalarLp_integrable_sq _).const_mul _).sub
      ((scalarLp_integrable_sq _).const_mul _))
    (L2.integrable_inner _ _)
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [half_sq_sub_sq_le_positivePart_mul_sub (f a) (z a)]

private theorem positivePart_support_lower
    
    (x z : H10HilbertGraph hΩ) :
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ z) ≤
      positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_lower _ _

private theorem positivePart_support_upper
    
    (x z : H10HilbertGraph hΩ) :
    positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z ≤
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ x) := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_upper _ _




/-- Chain rule for the half squared `L²` norm of the positive part, derived
from the derivative of the pivoted curve and convex support inequalities. -/
theorem hasDerivAt_positivePartHalfEnergy_of_pivoted_curve
    
    (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x)
    (y : H10HilbertGraphDual hΩ) (t : ℝ)
    (hpivot : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y t) :
    HasDerivAt (fun s => positivePartHalfEnergy hΩ (x s))
      (y (h10PositivePart hΩ (x t))) t := hasDerivAt_of_support_inequalities
    _
    _
    _
    ((continuous_h10PositivePart hΩ).comp hx) y t hpivot
    (fun r s => positivePart_support_lower hΩ _ _)
    (fun r s => positivePart_support_upper hΩ _ _)

/-- Fixed-window forward Steklov positive-part energy identity in the
reverse-time Gelfand triple. -/
theorem reverseTimeForwardSteklov_positivePart_energy_identity
     (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b + h ≤ T) :
    ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u b))‖ ^ 2 -
        ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u a))‖ ^ 2 =
      2 * (∫ t in Set.Icc a b, (reverseTimeForwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))) := by
  let x  := fun t => reverseTimeForwardSteklov T h u t
  let y  := fun t => reverseTimeForwardSteklov T h g t
  let E  := fun t => positivePartHalfEnergy hΩ (x t)
  have hx : Continuous x := continuous_reverseTimeForwardSteklov T h hh u
  have hy : Continuous y := continuous_reverseTimeForwardSteklov T h hh g
  have hE : Continuous E := continuous_const.mul ((continuous_norm.comp ((valueCLM hΩ).continuous.comp
      ((continuous_h10PositivePart hΩ).comp hx))).pow 2)
  have hpair : Continuous (fun t => y t (h10PositivePart hΩ _)) :=
    hy.clm_apply ((continuous_h10PositivePart hΩ).comp hx)
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E
      (y t (h10PositivePart hΩ (x t))) t := by
    intro t ht
    exact hasDerivAt_positivePartHalfEnergy_of_pivoted_curve hΩ x hx _ t
      (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv hh
        (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2]))
  have hFTC : (∫ t in a..b, y t _) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      (hpair.intervalIntegrable a b)
  calc
    _ = 2 * (E b - E a) := by simp only [E, positivePartHalfEnergy]; ring
    _ = 2 * (∫ t in a..b, y t _) := by rw [hFTC]
    _ = 2 * (∫ t in Ioc a b, y t _) := by
      rw [intervalIntegral.integral_of_le hab]
    _ = 2 * (∫ t in Icc a b, y t _) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = _ := rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
