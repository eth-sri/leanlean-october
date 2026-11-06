module

public import RequestProject.HerglotzPoincare
public import RequestProject.HerglotzForm
public import Mathlib.Analysis.Complex.Isometry

/-!
# Mean values of Herglotz coefficients over discs

The average of a plane wave over a disc is a fixed multiple of its value at the centre
(`integral_ball_planeWave`, by translation and rotation invariance of Lebesgue measure), hence
`∫_{B(z₁, r)} F_m = j(k, r) F_m(z₁)` for every Herglotz coefficient (`integral_ball_herglotzCoeff`).
In particular, if `F_m(z₁) = 0` then `F_m` has zero mean over every disc centred at `z₁`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The disc integral `j(k, r) = ∫_{B(0, r)} e^{-ik Re u} du`. -/
def ballMean (k r : ℝ) : ℂ := ∫ u in ball 0 r, planeWave k u 0

lemma planeWave_rotate k u φ :
    planeWave k u φ = planeWave k (u * Complex.exp (-(φ * Complex.I))) 0 := by
  unfold planeWave
  simp

/-- Translation: `∫_{B(z₁, r)} f = ∫_{B(0, r)} f(z₁ + ·)`. -/
lemma setIntegral_ball_translate (f : ℂ → ℂ) z₁ r :
    ∫ z in ball z₁ r, f z = ∫ u in ball 0 r, f (z₁ + u) := by
  have hpre : (fun u => z₁ + u) ⁻¹' ball z₁ r = ball 0 r := by
    ext u; simp [dist_eq_norm]
  rw [← hpre, (measurePreserving_add_left volume z₁).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z₁) f (ball z₁ r)]

/-- **Disc integral of a plane wave.** -/
lemma integral_ball_planeWave (k r : ℝ) z₁ φ :
    ∫ z in ball z₁ r, planeWave k z φ = planeWave k z₁ φ * ballMean k r := by
  rw [setIntegral_ball_translate, ← (show ∫ u in ball 0 r, planeWave k u φ = ballMean k r by
    set c := Circle.exp (-φ)
    have hrot : ∀ u, rotation c u = u * Complex.exp (-(φ * Complex.I)) := fun u => by
      rw [rotation_apply, Circle.coe_exp]
      push_cast
      ring_nf
    unfold ballMean
    conv_lhs => rw [← (show (rotation c) ⁻¹' ball 0 r = ball 0 r by
      ext u; simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map])]
    simp_rw [planeWave_rotate k _ φ]
    have := (LinearIsometryEquiv.measurePreserving (rotation c)).setIntegral_preimage_emb ((rotation c).toHomeomorph.measurableEmbedding) (fun v => planeWave k v 0) (ball 0 r)
    simp only [hrot] at this
    convert this using 2), ← integral_const_mul]
  simp_rw [planeWave_add]

/-- **Mean value property of Herglotz coefficients.** -/
theorem integral_ball_herglotzCoeff  (ha : IntervalIntegrable a volume 0 (2 * π))
    k m z₁ r :
    ∫ z in ball z₁ r, herglotzCoeff k a m z = ballMean k r * herglotzCoeff k a m z₁ := by
  have h2π : 0 ≤ 2 * π := by positivity
  set e : ℝ → ℂ := fun φ => Complex.exp (-(m * φ * Complex.I)) with he
  have hen : ∀ φ, ‖e φ‖ = 1 := fun φ => by
    rw [he, Complex.norm_exp]; simp
  have hai :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp ha
  haveI : IsFiniteMeasure (volume.restrict (ball z₁ r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  set F : ℂ → ℝ → ℂ := fun z φ => e φ * (a φ * planeWave k z φ) with hF
  unfold herglotzCoeff
  simp_rw [intervalIntegral.integral_of_le h2π]
  rw [integral_const_mul, (integral_integral_swap (show Integrable (Function.uncurry F) ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) by
    refine ((integrable_const 1).mul_prod hai.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℂ × ℝ => a p.2)
          ((volume.restrict (ball z₁ r)).prod (volume.restrict (Ioc 0 (2 * π)))) :=
        hai.aestronglyMeasurable.comp_snd
      exact ((show Continuous e by rw [he]; fun_prop).comp continuous_snd).aestronglyMeasurable.mul (h1.mul (show Continuous fun p : ℂ × ℝ => planeWave k p.1 p.2 by
        unfold planeWave
        fun_prop).aestronglyMeasurable)
    · simp [Function.uncurry, hF, hen, norm_planeWave]))]
  have hin : ∀ φ, ∫ z in ball z₁ r, F z φ = e φ * (a φ * (planeWave k z₁ φ * ballMean k r)) :=
    fun φ => by
      simp [hF]
      rw [integral_const_mul, integral_const_mul, integral_ball_planeWave]
  have hre : ∀ φ, e φ * (a φ * (planeWave k z₁ φ * ballMean k r)) =
      e φ * (a φ * planeWave k z₁ φ) * ballMean k r := fun φ => by ring
  simp_rw [hin, hre, integral_mul_const]
  simp [he]
  ring

end PolyaNeumann
