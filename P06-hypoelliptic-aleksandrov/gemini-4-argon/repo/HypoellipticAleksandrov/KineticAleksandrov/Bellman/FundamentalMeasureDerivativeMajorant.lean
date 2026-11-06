module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeDerivative
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant

/-! # A uniform integrable derivative majorant away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- Time decomposition of the Gaussian derivative bound, for a squared-distance lower bound a. -/
def bellmanDerivativeMajorant (a : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun _ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) t +
  (Ioi (1 : ℝ)).indicator (fun s => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ)) t

/- The derivative majorant is integrable on the positive half-line. -/
theorem integrable_bellmanDerivativeMajorant (a : ℝ) :
    Integrable (fun t : BellmanPositiveTime => bellmanDerivativeMajorant a t.val)
      bellmanPositiveTimeVolume := by
  have hsmall : IntegrableOn (fun _ : ℝ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6))
      (Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hlarge : IntegrableOn (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) *
      s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hi : Integrable (bellmanDerivativeMajorant a) (volume : Measure ℝ) :=
    (hsmall.integrable_indicator measurableSet_Ioc).add
      (hlarge.integrable_indicator measurableSet_Ioi)
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi (0 : ℝ)) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have h : Integrable (bellmanDerivativeMajorant a)
      (Measure.map (Subtype.val : BellmanPositiveTime → ℝ) bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hi.restrict
  exact (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ))
    measurableSet_Ioi).integrable_map_iff.mp h

/- The actual Gaussian time derivative has an integrable separated bound. -/
theorem bellmanGaussianTimeDerivative_le_majorant (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) (t : BellmanPositiveTime) :
    ‖bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q‖ ≤
      bellmanGaussianTimeWeight q * bellmanDerivativeMajorant a t.val := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (bellmanGaussianKernel_pos t q)]
  by_cases ht : t.val ≤ 1
  · simp only [bellmanDerivativeMajorant, indicator_of_mem
      (show t.val ∈ Ioc (0 : ℝ) 1 from ⟨t.property, ht⟩),
      indicator_of_notMem (show t.val ∉ Ioi (1 : ℝ) from not_lt.mpr ht), add_zero]
    have _h_xinl_0 : |bellmanGaussianTimeCoefficient t.val q| ≤ bellmanGaussianTimeWeight q / t.val ^ 4 := by
      have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
      have ht3 : t.val ^ 3 ≤ 1 := by
        calc t.val ^ 3 = t.val ^ 2 * t.val := by ring
             _ ≤ 1 * 1 := mul_le_mul ht2 ht t.property.le (by norm_num)
             _ = 1 := one_mul _
      have he : bellmanGaussianTimeCoefficient t.val q * t.val ^ 4 =
          9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3 := by
        dsimp [bellmanGaussianTimeCoefficient]
        field_simp [ne_of_gt t.property]
      apply (le_div_iff₀ (pow_pos t.property 4)).mpr
      rw [← abs_of_pos (pow_pos t.property 4), ← abs_mul, he]
      calc
        |9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3|
            ≤ |9 * q.1 ^ 2| + |6 * q.1 * q.2 * t.val| +
              |q.2 ^ 2 * t.val ^ 2| + |2 * t.val ^ 3| := by
                have h1 := abs_sub (9 * q.1 ^ 2) (6 * q.1 * q.2 * t.val)
                have h2 := abs_add_le (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val)
                  (q.2 ^ 2 * t.val ^ 2)
                have h3 := abs_sub
                  (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2)
                  (2 * t.val ^ 3)
                linarith only [h1, h2, h3]
        _ ≤ bellmanGaussianTimeWeight q := by
          simp only [abs_mul, abs_of_nonneg (sq_nonneg q.1),
            abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
            abs_of_nonneg (pow_nonneg t.property.le 2),
            abs_of_nonneg (pow_nonneg t.property.le 3)]
          norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have hx : |q.1| * |q.2| = |q.1 * q.2| := (abs_mul _ _).symm
          dsimp [bellmanGaussianTimeWeight]
          rw [mul_assoc 6, hx]
          nlinarith only [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 6 * |q.1 * q.2|),
            mul_le_mul_of_nonneg_left ht2 (sq_nonneg q.2), ht3]
    have h := mul_le_mul _h_xinl_0
      (bellmanGaussianKernel_le_smallTime_four t ht q a ha hq)
      (bellmanGaussianKernel_pos t q).le
      (div_nonneg (bellmanGaussianTimeWeight_nonneg q) (by positivity))
    refine h.trans_eq ?_
    field_simp [ne_of_gt t.property]
  · have h1 : 1 < t.val := lt_of_not_ge ht
    simp only [bellmanDerivativeMajorant, indicator_of_notMem
      (show t.val ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      indicator_of_mem (show t.val ∈ Ioi (1 : ℝ) from h1), zero_add]
    have _h_xinl_0 : |bellmanGaussianTimeCoefficient t.val q| ≤ bellmanGaussianTimeWeight q := by
      have ht := h1.le
      have hp (n : ℕ) : 1 ≤ t.val ^ n := one_le_pow₀ ht
      unfold bellmanGaussianTimeCoefficient
      calc
        |9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
            q.2 ^ 2 / t.val ^ 2 - 2 / t.val|
            ≤ |9 * q.1 ^ 2 / t.val ^ 4| + |6 * q.1 * q.2 / t.val ^ 3| +
              |q.2 ^ 2 / t.val ^ 2| + |2 / t.val| := by
                have h1 := abs_sub (9 * q.1 ^ 2 / t.val ^ 4)
                  (6 * q.1 * q.2 / t.val ^ 3)
                have h2 := abs_add_le
                  (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3)
                  (q.2 ^ 2 / t.val ^ 2)
                have h3 := abs_sub
                  (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
                    q.2 ^ 2 / t.val ^ 2) (2 / t.val)
                linarith only [h1, h2, h3]
        _ ≤ bellmanGaussianTimeWeight q := by
          simp only [abs_div, abs_mul, abs_of_nonneg (sq_nonneg q.1),
            abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
            abs_of_nonneg (pow_nonneg t.property.le 2),
            abs_of_nonneg (pow_nonneg t.property.le 3),
            abs_of_nonneg (pow_nonneg t.property.le 4)]
          norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          dsimp [bellmanGaussianTimeWeight]
          rw [mul_assoc 6, ← abs_mul]
          exact add_le_add (add_le_add (add_le_add
            (div_le_self (by positivity) (hp 4))
            (div_le_self (by positivity) (hp 3)))
            (div_le_self (sq_nonneg _) (hp 2))) (div_le_self (by norm_num) ht)
    have h := mul_le_mul _h_xinl_0
      (bellmanGaussianKernel_le t q) (bellmanGaussianKernel_pos t q).le
      (bellmanGaussianTimeWeight_nonneg q)
    refine h.trans_eq ?_
    rw [Real.rpow_neg t.property.le, Real.rpow_two]
    ring

end HypoellipticAleksandrov.KineticAleksandrov
