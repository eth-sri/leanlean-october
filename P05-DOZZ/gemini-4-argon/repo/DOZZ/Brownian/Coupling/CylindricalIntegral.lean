/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cylindrical integration for three-dimensional radial tests

Use the ordinary complex-plane polar formula on the transverse plane. The remaining substitution
`y = sqrt(x² + ρ²)` and Tonelli reduce a radial exponential tilt to a one-dimensional integral.
The origin and zero-tilt endpoint are retained explicitly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Radius after fixing the longitudinal coordinate and the transverse radius. -/
noncomputable def cylindricalRadius (x ρ : ℝ) : ℝ := Real.sqrt (x ^ 2 + ρ ^ 2)

theorem continuous_cylindricalRadius x : Continuous (cylindricalRadius x) := by
  unfold cylindricalRadius
  fun_prop

theorem cylindricalRadius_pos x {ρ} (hρ : 0 < ρ) :
    0 < cylindricalRadius x ρ := by
  apply Real.sqrt_pos.2
  nlinarith only [sq_nonneg x, sq_pos_of_pos hρ]

theorem cylindricalRadius_sq x ρ : (cylindricalRadius x ρ) ^ 2 = x ^ 2 + ρ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg ρ))






/-- Ordinary complex-plane polar integration contributes the transverse angular factor `2π`. -/
theorem lintegral_complex_cylindricalRadius x (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ) := by
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * F (cylindricalRadius x ‖Complex.polarCoord.symm p‖) :=
      (Complex.lintegral_comp_polarCoord_symm (fun w => F (cylindricalRadius x ‖w‖))).symm
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F (cylindricalRadius x p.1) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    _ = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ρ * F (cylindricalRadius x ρ) :=
      setLIntegral_prod _ (measurable_fst.ennreal_ofReal.mul (hF.comp ((continuous_cylindricalRadius x).measurable.comp measurable_fst))).aemeasurable
    _ = (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ)) *
        ENNReal.ofReal (2 * Real.pi) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [(show Real.pi - -Real.pi = 2 * Real.pi by ring)]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := mul_comm _ _


/-- The triangular longitudinal/radial region after the positive-radius substitution. -/
noncomputable def cylindricalStrip (F H : ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if |p.1| < p.2 then ENNReal.ofReal p.2 * F p.2 * H p.1 else 0





/-- Cylindrical integration on `ℝ × ℂ`: an arbitrary longitudinal weight is integrated on each
radial cross-section, without spherical coordinates or an angular disintegration theorem. -/
theorem lintegral_radial_longitudinal (F H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hH : Measurable H) :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * H p.1) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  have lintegral_cylindrical_tails : (∫⁻ x, ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x) = ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
    have lintegral_cylindricalStrip_left y : (∫⁻ x, cylindricalStrip F H (x, y)) = (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
      calc
        _ = ∫⁻ x, (Ioo (-y) y).indicator (fun x => (ENNReal.ofReal y * F y) * H x) x := by
          apply lintegral_congr
          intro x
          simp only [cylindricalStrip, indicator, mem_Ioo, abs_lt]
        _ = ∫⁻ x in Ioo (-y) y, (ENNReal.ofReal y * F y) * H x :=
          lintegral_indicator measurableSet_Ioo _
        _ = _ := lintegral_const_mul _ hH
    have lintegral_cylindricalStrip_right (F : ℝ → ℝ≥0∞) (H : ℝ → ℝ≥0∞) x : (∫⁻ y, cylindricalStrip F H (x, y)) = ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro y
      rfl
    calc
      _ = ∫⁻ x, ∫⁻ y, cylindricalStrip F H (x, y) := by
        simp_rw [lintegral_cylindricalStrip_right]
      _ = ∫⁻ y, ∫⁻ x, cylindricalStrip F H (x, y) :=
        lintegral_lintegral_swap ((show Measurable (cylindricalStrip F H) by exact ((measurable_snd.ennreal_ofReal.mul (hF.comp measurable_snd)).mul (hH.comp measurable_fst)).ite (measurableSet_lt (continuous_fst.abs.measurable) measurable_snd) measurable_const)).aemeasurable
      _ = ∫⁻ y, (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
        simp_rw [lintegral_cylindricalStrip_left]
      _ = _ := by
        symm
        apply setLIntegral_eq_of_support_subset
        intro y hy
        by_contra hpos
        apply hy
        simp only [(Ioo_eq_empty_of_le (by linarith only [(le_of_not_gt hpos)]) : Ioo (-y) y = ∅), Measure.restrict_empty, lintegral_zero_measure, mul_zero]
  have lintegral_complex_radial_section x (F : ℝ → ℝ≥0∞) (hF : Measurable F) : (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) = ENNReal.ofReal (2 * Real.pi) * ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
    have lintegral_cylindricalRadius x (F : ℝ → ℝ≥0∞) : (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ)) = ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
      have hasDerivAt_cylindricalRadius {ρ} (hρ : 0 < ρ) : HasDerivAt (cylindricalRadius x) (ρ / cylindricalRadius x ρ) ρ := by
        have hder := (((hasDerivAt_id ρ).pow 2).const_add (x ^ 2)).sqrt (by exact (show 0 < x ^ 2 + ρ ^ 2 by nlinarith only [sq_nonneg x, sq_pos_of_pos hρ]).ne')
        simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hder
        change HasDerivAt (cylindricalRadius x) (2 * ρ / (2 * cylindricalRadius x ρ)) ρ at hder
        convert hder using 1
        ring
      have cylindricalRadius_image_Ioi x : cylindricalRadius x '' Ioi 0 = Ioi |x| := by
        have abs_lt_cylindricalRadius {ρ} (hρ : 0 < ρ) : |x| < cylindricalRadius x ρ := by
          nlinarith only [sq_abs x, sq_pos_of_pos hρ, abs_nonneg x, (cylindricalRadius_pos x hρ), (cylindricalRadius_sq x ρ)]
        ext y
        constructor
        · rintro ⟨ρ, hρ, rfl⟩
          exact abs_lt_cylindricalRadius hρ
        · intro hy
          change |x| < y at hy
          have hsq : 0 < y ^ 2 - x ^ 2 := by
            nlinarith only [hy, abs_nonneg x, sq_abs x]
          refine ⟨Real.sqrt (y ^ 2 - x ^ 2), Real.sqrt_pos.2 hsq, ?_⟩
          unfold cylindricalRadius
          rw [Real.sq_sqrt hsq.le, (show x ^ 2 + (y ^ 2 - x ^ 2) = y ^ 2 by ring), Real.sqrt_sq ((abs_nonneg x).trans_lt hy).le]
      have strictMonoOn_cylindricalRadius : StrictMonoOn (cylindricalRadius x) (Ioi 0) := by
        intro a ha b hb hab
        change 0 < a at ha
        change 0 < b at hb
        nlinarith only [ha, hb, hab, (cylindricalRadius_sq x a), (cylindricalRadius_sq x b), (cylindricalRadius_pos x ha), (cylindricalRadius_pos x hb)]
      have hchange := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
        (fun ρ hρ => (hasDerivAt_cylindricalRadius hρ).hasDerivWithinAt)
        (strictMonoOn_cylindricalRadius).injOn (fun y => ENNReal.ofReal y * F y)
      rw [cylindricalRadius_image_Ioi] at hchange
      rw [hchange]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro ρ hρ
      have hy := cylindricalRadius_pos x hρ
      dsimp only
      rw [abs_of_pos (div_pos hρ hy), ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hρ.le hy.le),
        div_mul_cancel₀ _ hy.ne']
    rw [lintegral_complex_cylindricalRadius x F hF, lintegral_cylindricalRadius]
  have hmeas : Measurable (fun p : ℝ × ℂ => F (cylindricalRadius p.1 ‖p.2‖) * H p.1) :=
    (hF.comp (show Continuous (fun p : ℝ × ℂ => cylindricalRadius p.1 ‖p.2‖) by unfold cylindricalRadius; fun_prop).measurable).mul (hH.comp measurable_fst)
  have hsection x :
      (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖) * H x) =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
    rw [lintegral_mul_const _ (show Measurable (fun w => F (cylindricalRadius x ‖w‖)) from
      hF.comp ((continuous_cylindricalRadius x).comp continuous_norm).measurable)]
    rw [lintegral_complex_radial_section x F hF]
    rw [lintegral_mul_const _ (show Measurable (fun y => ENNReal.ofReal y * F y) from
      measurable_id.ennreal_ofReal.mul hF), mul_assoc]
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  simp_rw [hsection]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cylindrical_tails]

/-- Explicit longitudinal exponential integral, allowing either sign of the tilt. -/
theorem integral_exp_longitudinal c y (hc : c ≠ 0) (hy : 0 ≤ y) :
    (∫ x in Ioo (-y) y, Real.exp (c * x)) = 2 * Real.sinh (c * y) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith only [hy]),
    intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  rw [Real.sinh_eq]
  simp only [smul_eq_mul, mul_neg]
  ring



/-- The longitudinal tilt average is nonnegative for either sign of nonzero drift. -/
theorem sinh_div_nonneg_longitudinal c y (hc : c ≠ 0) (hy : 0 ≤ y) :
    0 ≤ Real.sinh (c * y) / c := by
  have h : 0 ≤ ∫ x in Ioo (-y) y, Real.exp (c * x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [integral_exp_longitudinal c y hc hy] at h
  rw [(show 2 * Real.sinh (c * y) / c = 2 * (Real.sinh (c * y) / c) by ring)] at h
  linarith only [h]



/-- The longitudinal/transverse coordinate equivalence for the actual three-real carrier. -/
noncomputable def cylindricalCoordinates : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℂ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) Complex.measurableEquivPi.symm)

/-- Cylindrical coordinates preserve three-dimensional Lebesgue volume. -/
theorem cylindricalCoordinates_measurePreserving : MeasurePreserving cylindricalCoordinates := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    Complex.volume_preserving_equiv_pi.symm).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

/-- The longitudinal component is the first Cartesian component. -/
theorem cylindricalCoordinates_fst z : (cylindricalCoordinates z).1 = z 0 := rfl

/-- Cartesian Euclidean norm equals the cylindrical radius. -/
theorem cylindricalCoordinates_radius z :
    cylindricalRadius (cylindricalCoordinates z).1 ‖(cylindricalCoordinates z).2‖ =
      ‖WithLp.toLp 2 z‖ := by
  have hcomplex : ‖(cylindricalCoordinates z).2‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2 := by
    change ‖Complex.measurableEquivPi.symm (Fin.tail z)‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Fin.tail, pow_two]
  rw [cylindricalRadius, cylindricalCoordinates_fst, (show (z 0) ^ 2 + ‖(cylindricalCoordinates z).2‖ ^ 2 = ‖WithLp.toLp 2 z‖ ^ 2 by rw [hcomplex]; simpa [Fin.sum_univ_succ, add_assoc] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)).symm), Real.sqrt_sq (norm_nonneg _)]

/-- Nonnegative integrals transport directly to the three-real Cartesian carrier. -/
theorem lintegral_cylindricalCoordinates (f : ℝ × ℂ → ℝ≥0∞) :
    (∫⁻ z : Fin 3 → ℝ, f (cylindricalCoordinates z)) = ∫⁻ p : ℝ × ℂ, f p :=
  cylindricalCoordinates_measurePreserving.lintegral_comp_emb
    cylindricalCoordinates.measurableEmbedding f

/-- Weighted radial identity on the exact Euclidean three-coordinate carrier. -/
theorem lintegral_three_radial_exp (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    c (hc : c ≠ 0) :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖ * ENNReal.ofReal (Real.exp (c * z 0))) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
  have lintegral_radial_exp : (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * ENNReal.ofReal (Real.exp (c * p.1))) = ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
    have lintegral_exp_longitudinal y (hc : c ≠ 0) (hy : 0 ≤ y) : (∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) = ENNReal.ofReal (2 * Real.sinh (c * y) / c) := by
      have integrableOn_exp_longitudinal : IntegrableOn (fun x => Real.exp (c * x)) (Ioo (-y) y) := by
        exact ((show Continuous (fun x => Real.exp (c * x)) by fun_prop).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_longitudinal)
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
        integral_exp_longitudinal c y hc hy]
    rw [lintegral_radial_longitudinal F _ hF (show Measurable (fun x => ENNReal.ofReal (Real.exp (c * x))) by fun_prop)]
    have hsection : (∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) *
        ∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) =
        ENNReal.ofReal (2 : ℝ) * ∫⁻ y in Ioi (0 : ℝ),
          F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [lintegral_exp_longitudinal y hc hy.le]
      rw [(show 2 * Real.sinh (c * y) / c = 2 * (Real.sinh (c * y) / c) by ring), (show y * Real.sinh (c * y) / c = y * (Real.sinh (c * y) / c) by ring), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul hy.le]
      ring
    rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
    congr 2
    ring
  rw [← lintegral_radial_exp, ← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius, cylindricalCoordinates_fst]

/-- The Maxwell radial integration formula on the same Cartesian carrier. -/
theorem lintegral_three_radial_zero (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
  have lintegral_radial_zero : (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖)) = ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
    have h := lintegral_radial_longitudinal F (fun _ => 1) hF measurable_const
    simp only [mul_one, lintegral_const, one_mul, Measure.restrict_apply_univ,
      Real.volume_Ioo] at h
    rw [h]
    have hsection : (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal y * F y * ENNReal.ofReal (y - -y)) =
        ENNReal.ofReal (2 : ℝ) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [(show y - -y = 2 * y by ring), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), pow_two,
        ENNReal.ofReal_mul hy.le]
      ring
    rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
    congr 2
    ring
  rw [← lintegral_radial_zero, ← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius]

end DOZZ.Proofs
