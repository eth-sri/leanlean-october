module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityFormula
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! # The physical density norm has the literal kinetic scaling exponent -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

variable (c : Clock) (e : Point) (F : Point → ℝ) (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)

include hF in
/-- The clock pullback changes a full physical Lebesgue norm by the exact volume factor. -/
theorem poleDensity_clock_eLpNorm (q : ℝ) (hq : 0 < q) :
    eLpNorm (F ∘ c.map e) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (c.r ^ (6 / q : ℝ)) * eLpNorm F (ENNReal.ofReal q) volume := by
  refine (eLpNorm_map_measure (μ := (volume : Measure Point)) (p := ENNReal.ofReal q) hF.aestronglyMeasurable (c.continuous_map e).measurable.aemeasurable).symm.trans ((congrArg (fun μ : Measure Point => eLpNorm F (ENNReal.ofReal q) μ) (c.map_volume e)).trans ((eLpNorm_smul_measure_of_ne_zero_of_ne_top (μ := (volume : Measure Point)) (f := F) (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top (ENNReal.ofReal (c.r ^ 6))).trans ?_))
  rw [smul_eq_mul]
  congr 1
  rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le,
    ENNReal.ofReal_rpow_of_pos (pow_pos c.positive 6)]
  apply congrArg ENNReal.ofReal
  rw [← Real.rpow_natCast c.r 6, ← Real.rpow_mul c.positive.le]
  simp [div_eq_mul_inv]

include hFn in
/-- Removing the velocity weight costs at most `2/r⁴` pointwise, independently of the clock
  centre. -/
theorem polePhysicalDensity_pointwise_bound (p : Point) :
    |polePhysicalDensity c e F p| ≤ |(2 / c.r ^ 4) * F (c.map e p)| := by
  have hb : ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹) * poleInverseVelocity c p ≤
      2 / c.r ^ 4 := by
    apply (mul_le_mul_of_nonneg_left (poleInverseVelocity_le c p) (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))).trans_eq
    field_simp [c.nonzero, ne_of_gt c.positive]
  rw [abs_of_nonneg (polePhysicalDensity_nonneg c e F hFn p),
    abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) (pow_nonneg c.positive.le _)) (hFn _))]
  exact (show polePhysicalDensity c e F p =
    (((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹) * poleInverseVelocity c p) * F (c.map e p)
      from by unfold polePhysicalDensity; ring).le.trans
    (mul_le_mul_of_nonneg_right hb (hFn _))

include hF hFn in
/-- The exact pole density formula has the source norm bound with exponent `6/q - 4`. -/
theorem polePhysicalDensity_eLpNorm_bound (q C : ℝ) (hq : 0 < q) (_hC : 0 ≤ C)
    (hn : eLpNorm F (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C) :
    eLpNorm (polePhysicalDensity c e F) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (2 * C * c.r ^ (6 / q - 4 : ℝ)) := by
  have hb := eLpNorm_mono_ae (μ := volume) (p := ENNReal.ofReal q)
    (g := fun p => (2 / c.r ^ 4) * F (c.map e p))
    (polePhysicalDensity_measurable c e F hF).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by
      exact polePhysicalDensity_pointwise_bound c e F hFn p))
  have hnorm : eLpNorm (fun p => (2 / c.r ^ 4) * F (c.map e p)) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (2 / c.r ^ 4) * ENNReal.ofReal (c.r ^ (6 / q)) *
        eLpNorm F (ENNReal.ofReal q) volume := by
    have hs := eLpNorm_const_smul (2 / c.r ^ 4) (F ∘ c.map e) (ENNReal.ofReal q)
      volume
    exact hs.trans (by rw [Real.enorm_of_nonneg (by positivity),
      poleDensity_clock_eLpNorm c e F hF q hq, mul_assoc])
  apply hb.trans (hnorm.le.trans ((mul_le_mul_of_nonneg_left hn zero_le).trans_eq ?_))
  have hk : 0 ≤ 2 / c.r ^ 4 := div_nonneg (by norm_num) (pow_nonneg c.positive.le _)
  rw [← ENNReal.ofReal_mul hk,
    ← ENNReal.ofReal_mul (mul_nonneg hk (Real.rpow_nonneg c.positive.le _))]
  apply congrArg ENNReal.ofReal
  rw [Real.rpow_sub c.positive]
  rw [show c.r ^ (4 : ℝ) = c.r ^ (4 : ℕ) from Real.rpow_natCast c.r 4]
  field_simp [ne_of_gt c.positive]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
