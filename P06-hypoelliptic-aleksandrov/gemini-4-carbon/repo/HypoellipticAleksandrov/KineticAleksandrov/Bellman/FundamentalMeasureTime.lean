module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernel
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A uniform quadratic lower bound for the Gaussian precision at small positive time. -/
theorem bellmanGaussianExponent_le_smallTime (t : BellmanPositiveTime) (ht : t.val ≤ 1)
    (q : ℝ × ℝ) :
    bellmanGaussianExponent t q ≤ -(q.1 ^ 2 + q.2 ^ 2) / (8 * t.val) := by
  have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
  have hcoeff : 0 ≤ 24 - 7 * t.val ^ 2 := by linarith only [ht2]
  have hQ : 0 ≤ (24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
      7 * t.val ^ 2 * q.2 ^ 2 := by
    nlinarith only [sq_nonneg (12 * q.1 - 7 * t.val * q.2),
      mul_nonneg hcoeff (sq_nonneg q.1)]
  have hidentity : bellmanGaussianExponent t q +
      (q.1 ^ 2 + q.2 ^ 2) / (8 * t.val) =
      -((24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
        7 * t.val ^ 2 * q.2 ^ 2) / (8 * t.val ^ 3) := by
    dsimp [bellmanGaussianExponent]
    field_simp
    ring
  have hneg : -((24 - t.val ^ 2) * q.1 ^ 2 - 24 * t.val * q.1 * q.2 +
      7 * t.val ^ 2 * q.2 ^ 2) / (8 * t.val ^ 3) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hQ)
      (mul_nonneg (by norm_num) (pow_nonneg t.property.le 3))
  rw [← hidentity] at hneg
  rw [neg_div]
  linarith only [hneg]

/-- Exponential decay dominates the quadratic inverse-power singularity. -/
theorem bellman_exp_neg_le_inv_sq (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 2 / y ^ 2 := by
  have hm := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp y hy.le 2) (Real.exp_pos (-y)).le
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hexp] at hm
  norm_num at hm
  apply (le_div_iff₀ (pow_pos hy 2)).mpr
  nlinarith only [hm]

/-- At small time the kernel is uniformly bounded on each plane set away from the origin. -/
theorem bellmanGaussianKernel_le_smallTime (t : BellmanPositiveTime) (ht : t.val ≤ 1)
    (q : ℝ × ℝ) (a : ℝ) (ha : 0 < a) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) :
    bellmanGaussianKernel t q ≤ 64 * Real.sqrt 3 / (Real.pi * a ^ 2) := by
  have hE : bellmanGaussianExponent t q ≤ -a / (8 * t.val) := by
    refine (bellmanGaussianExponent_le_smallTime t ht q).trans ?_
    exact div_le_div_of_nonneg_right (neg_le_neg hq)
      (mul_nonneg (by norm_num) t.property.le)
  have he : Real.exp (bellmanGaussianExponent t q) ≤
      2 / (a / (8 * t.val)) ^ 2 := by
    refine (Real.exp_le_exp.mpr hE).trans ?_
    rw [neg_div] at *
    exact bellman_exp_neg_le_inv_sq _
      (div_pos ha (mul_pos (by norm_num) t.property))
  have hc : 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (by positivity)
  unfold bellmanGaussianKernel
  refine (mul_le_mul_of_nonneg_left he hc).trans_eq ?_
  field_simp [ne_of_gt t.property]
  norm_num

open MeasureTheory Set

/-- Away from the pole, the time integral defining the fundamental density is finite. -/
theorem integrable_bellmanGaussianKernel_time (q : BellmanPuncturedPlane) :
    Integrable (fun t => bellmanGaussianKernel t q.val) bellmanPositiveTimeVolume := by
  let f : ℝ → ℝ := fun s => Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
    Real.exp (-3 * q.val.1 ^ 2 / s ^ 3 + 3 * q.val.1 * q.val.2 / s ^ 2 - q.val.2 ^ 2 / s)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have ha : 0 < q.val.1 ^ 2 + q.val.2 ^ 2 := by
    refine lt_of_le_of_ne (add_nonneg (sq_nonneg q.val.1) (sq_nonneg q.val.2)) ?_
    intro h
    apply q.property
    have hx : q.val.1 = 0 := by nlinarith only [h, sq_nonneg q.val.2]
    have hv : q.val.2 = 0 := by nlinarith only [h, sq_nonneg q.val.1]
    exact Prod.ext hx hv
  let C : ℝ := Real.sqrt 3 / (2 * Real.pi)
  let M : ℝ := 64 * Real.sqrt 3 / (Real.pi * (q.val.1 ^ 2 + q.val.2 ^ 2) ^ 2)
  have hsmall : IntegrableOn f (Ioc 0 1) := by
    refine (integrableOn_const (measure_Ioc_lt_top :
      (volume : Measure ℝ) (Ioc 0 1) < ⊤).ne (C := M)).mono'
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hpos := bellmanGaussianKernel_pos ⟨s, hs.1⟩ q.val
    change ‖bellmanGaussianKernel ⟨s, hs.1⟩ q.val‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact bellmanGaussianKernel_le_smallTime ⟨s, hs.1⟩ hs.2 q.val
      (q.val.1 ^ 2 + q.val.2 ^ 2) ha le_rfl
  have hlarge : IntegrableOn f (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1) (by norm_num) (by norm_num)).const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := lt_trans (by norm_num) hs
    change ‖bellmanGaussianKernel ⟨s, hspos⟩ q.val‖ ≤ C * s ^ (-2 : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos (bellmanGaussianKernel_pos ⟨s, hspos⟩ q.val)]
    have h := bellmanGaussianKernel_le ⟨s, hspos⟩ q.val
    convert h using 1
    rw [Real.rpow_neg hspos.le, Real.rpow_two]
    ring
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext s
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans (by norm_num) h
    · intro h
      by_cases h1 : s ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hall : IntegrableOn f (Ioi 0) := by
    rw [← hunion]
    exact hsmall.union hlarge
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi 0) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi 0) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have hfi : Integrable f (Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hall
  exact (MeasurableEmbedding.subtype_coe (s := Ioi 0)
    measurableSet_Ioi).integrable_map_iff.mp hfi

/-- The literal fundamental density is finite at every punctured-plane point. -/
theorem bellmanFundamentalDensity_ne_top (q : BellmanPuncturedPlane) :
    bellmanFundamentalDensity q ≠ ⊤ := by
  have h := integrable_bellmanGaussianKernel_time q
  exact (lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
    (ae_of_all _ (fun t => (bellmanGaussianKernel_pos t q.val).le))).mpr h

end HypoellipticAleksandrov.KineticAleksandrov

