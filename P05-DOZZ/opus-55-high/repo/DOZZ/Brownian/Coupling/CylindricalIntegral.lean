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
section
variable (x : ℝ)

theorem continuous_cylindricalRadius : Continuous (cylindricalRadius x) := by
  unfold cylindricalRadius
  fun_prop

theorem cylindricalRadius_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < cylindricalRadius x ρ := by
  apply Real.sqrt_pos.2
  positivity

end

theorem cylindricalRadius_sq (x ρ : ℝ) : (cylindricalRadius x ρ) ^ 2 = x ^ 2 + ρ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg ρ))
section
variable (x : ℝ)

theorem abs_lt_cylindricalRadius {ρ : ℝ} (hρ : 0 < ρ) :
    |x| < cylindricalRadius x ρ := by
  nlinarith only [sq_abs x, sq_pos_of_pos hρ, abs_nonneg x, (cylindricalRadius_pos x hρ), (cylindricalRadius_sq x ρ)]

theorem strictMonoOn_cylindricalRadius :
    StrictMonoOn (cylindricalRadius x) (Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  have hsa := cylindricalRadius_sq x a
  have hsb := cylindricalRadius_sq x b
  have hpa := cylindricalRadius_pos x ha
  have hpb := cylindricalRadius_pos x hb
  nlinarith

/-- Every radius greater than the longitudinal magnitude has a unique positive transverse radius. -/
theorem cylindricalRadius_image_Ioi : cylindricalRadius x '' Ioi 0 = Ioi |x| := by
  ext y
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact abs_lt_cylindricalRadius x hρ
  · intro hy
    change |x| < y at hy
    have hsq : 0 < y ^ 2 - x ^ 2 := by
      nlinarith only [hy, abs_nonneg x, sq_abs x]
    refine ⟨Real.sqrt _, Real.sqrt_pos.2 hsq, ?_⟩
    unfold cylindricalRadius
    rw [Real.sq_sqrt hsq.le]
    have heq : x ^ 2 + (y ^ 2 - x ^ 2) = y ^ 2 := by ring
    rw [heq, Real.sqrt_sq ((abs_nonneg x).trans_lt hy).le]

/-- The cylindrical radial substitution has derivative `ρ / sqrt(x²+ρ²)`. -/
theorem hasDerivAt_cylindricalRadius {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (cylindricalRadius x) (ρ / cylindricalRadius x ρ) ρ := by
  have hnonzero : x ^ 2 + ρ ^ 2 ≠ 0 := by
    positivity
  have hder := (((hasDerivAt_id ρ).pow 2).const_add _).sqrt hnonzero
  simp at hder
  change HasDerivAt (cylindricalRadius x) (2 * ρ / (2 * cylindricalRadius x ρ)) ρ at hder
  grind
section
variable (F : ℝ → ℝ≥0∞)

/-- The one-dimensional Jacobian cancels the radial weight, including arbitrary nonnegative tests. -/
theorem lintegral_cylindricalRadius :
    (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ)) =
      ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun ρ hρ => (hasDerivAt_cylindricalRadius x hρ).hasDerivWithinAt)
    (strictMonoOn_cylindricalRadius x).injOn (fun y => ENNReal.ofReal y * F y)
  rw [cylindricalRadius_image_Ioi] at hchange
  rw [hchange]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  have hy := cylindricalRadius_pos x hρ
  dsimp only
  rw [abs_of_pos (div_pos hρ hy), ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hρ.le hy.le),
    div_mul_cancel₀ _ hy.ne']
section
variable (hF : Measurable F)
include hF

/-- Ordinary complex-plane polar integration contributes the transverse angular factor `2π`. -/
theorem lintegral_complex_cylindricalRadius :
    (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (cylindricalRadius x p.1)) :=
    measurable_fst.ennreal_ofReal.mul (hF.comp ((continuous_cylindricalRadius x).measurable.comp
      measurable_fst))
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * F _ :=
      (Complex.lintegral_comp_polarCoord_symm (fun w => F _)).symm
    _ = ∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F _ := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    _ = ∫⁻ ρ in Ioi 0, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ρ * F _ :=
      setLIntegral_prod _ hm.aemeasurable
    _ = (∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * F _) *
        ENNReal.ofReal _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      have hlength : Real.pi - -Real.pi = 2 * Real.pi := by ring
      rw [hlength]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := mul_comm ..

/-- After changing the positive transverse radius, only `y > |x|` remains. -/
theorem lintegral_complex_radial_section :
    (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
  rw [lintegral_complex_cylindricalRadius x F hF, lintegral_cylindricalRadius]

end

end

end

/-- The triangular longitudinal/radial region after the positive-radius substitution. -/
noncomputable def cylindricalStrip (F H : ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if |p.1| < p.2 then ENNReal.ofReal p.2 * F p.2 * H p.1 else 0
section
variable (F H : ℝ → ℝ≥0∞)

theorem measurable_cylindricalStrip (hF : Measurable F) (hH : Measurable H) : Measurable (cylindricalStrip F H) := ((measurable_snd.ennreal_ofReal.mul (hF.comp measurable_snd)).mul
    (hH.comp measurable_fst)).ite
      (measurableSet_lt (continuous_fst.abs.measurable) measurable_snd) measurable_const

/-- Vertical sections are exactly the radial tails `y > |x|`. -/
theorem lintegral_cylindricalStrip_right (x : ℝ) :
    (∫⁻ y, cylindricalStrip F H (x, y)) =
      ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
  rw [← lintegral_indicator measurableSet_Ioi]
  rfl

/-- Horizontal sections are the interval `(-y,y)` of longitudinal coordinates. -/
theorem lintegral_cylindricalStrip_left (hH : Measurable H) (y : ℝ) :
    (∫⁻ x, cylindricalStrip F H (x, y)) =
      (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  calc
    _ = ∫⁻ x, (Ioo (-y) y).indicator (fun x => (ENNReal.ofReal y * F y) * H x) x := by
      apply lintegral_congr
      intro x
      simp only [cylindricalStrip, indicator, mem_Ioo, abs_lt]
    _ = ∫⁻ x in Ioo (-y) y, (ENNReal.ofReal y * F y) * H x :=
      lintegral_indicator measurableSet_Ioo _
    _ = _ := lintegral_const_mul _ hH
section
variable (hF : Measurable F) (hH : Measurable H)
include hF hH

/-- Tonelli converts radial tails at fixed longitudinal coordinate into bounded longitudinal
intervals at fixed radius, with the positive-radius endpoint retained. -/
theorem lintegral_cylindrical_tails :
    (∫⁻ x, ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x) =
      ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  calc
    _ = ∫⁻ x, ∫⁻ y, cylindricalStrip F H (x, y) := by
      simp_rw [lintegral_cylindricalStrip_right]
    _ = ∫⁻ y, ∫⁻ x, cylindricalStrip F H _ :=
      lintegral_lintegral_swap (measurable_cylindricalStrip F H hF hH).aemeasurable
    _ = ∫⁻ y, (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
      simp_rw [lintegral_cylindricalStrip_left F H hH]
    _ = _ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro y hy
      simp_all

/-- Cylindrical integration on `ℝ × ℂ`: an arbitrary longitudinal weight is integrated on each
radial cross-section, without spherical coordinates or an angular disintegration theorem. -/
theorem lintegral_radial_longitudinal :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * H p.1) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  have hradius : Continuous (fun p : ℝ × ℂ => cylindricalRadius p.1 ‖p.2‖) := by
    continuity
  have hmeas : Measurable (fun p : ℝ × ℂ => F (cylindricalRadius p.1 ‖p.2‖) * H p.1) :=
    (hF.comp hradius.measurable).mul (hH.comp measurable_fst)
  have hsection (x : ℝ) :
      (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖) * H x) =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
    rw [lintegral_mul_const _ (show Measurable (fun w => F (cylindricalRadius x ‖w‖)) from
      hF.comp ((continuous_cylindricalRadius x).comp continuous_norm).measurable)]
    rw [lintegral_complex_radial_section x F hF]
    rw [lintegral_mul_const _ (show Measurable (fun y : ℝ => ENNReal.ofReal y * F y) from
      measurable_id.ennreal_ofReal.mul hF), mul_assoc]
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  simp_rw [hsection]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cylindrical_tails F H hF hH]

end

end
section
variable (c y : ℝ)

/-- Explicit longitudinal exponential integral, allowing either sign of the tilt. -/
theorem integral_exp_longitudinal (hc : c ≠ 0) (hy : 0 ≤ y) :
    (∫ x in Ioo (-y) y, Real.exp (c * x)) = 2 * Real.sinh (c * y) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  rw [Real.sinh_eq]
  ring

/-- The exponential is integrable on every bounded longitudinal section. -/
theorem integrableOn_exp_longitudinal :
    IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Ioo (-y) y) := by
  have hcont : Continuous (fun x => Real.exp (c * x)) := by fun_prop
  exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
section
variable (hc : c ≠ 0) (hy : 0 ≤ y)
include hc hy

/-- Nonnegative integral version of the longitudinal tilt calculation. -/
theorem lintegral_exp_longitudinal :
    (∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) =
      ENNReal.ofReal (2 * Real.sinh (c * y) / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_longitudinal c y)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
    integral_exp_longitudinal c y hc hy]

/-- The longitudinal tilt average is nonnegative for either sign of nonzero drift. -/
theorem sinh_div_nonneg_longitudinal :
    0 ≤ Real.sinh (c * y) / c := by
  have h : 0 ≤ ∫ x in Ioo (-y) y, Real.exp (c * x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [integral_exp_longitudinal c y hc hy] at h
  grind

end

end
section
variable (F : ℝ → ℝ≥0∞)
section
variable (hF : Measurable F)
include hF

/-- Weighted radial identity in cylindrical coordinates. This is valid also for infinite tests. -/
theorem lintegral_radial_exp (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * ENNReal.ofReal (Real.exp (c * p.1))) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
  have hH : Measurable (fun x => ENNReal.ofReal (Real.exp (c * x))) := by fun_prop
  rw [lintegral_radial_longitudinal F _ hF hH]
  have hsection : (∫⁻ y in Ioi 0, (ENNReal.ofReal y * F y) *
      ∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) =
      ENNReal.ofReal 2 * ∫⁻ y in Ioi 0,
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [lintegral_exp_longitudinal c y hc hy.le]
    have hn := sinh_div_nonneg_longitudinal c y hc hy.le
    have heq : 2 * Real.sinh (c * y) / c = 2 * (Real.sinh (c * y) / c) := by ring
    have heq' : y * Real.sinh (c * y) / c = y * (Real.sinh (c * y) / c) := by ring
    rw [heq, heq', ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul hy.le]
    ring
  rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  grind

/-- Zero tilt gives the ordinary three-dimensional radial weight `4πy²`. -/
theorem lintegral_radial_zero :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖)) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
  have h := lintegral_radial_longitudinal F (fun _ => 1) hF measurable_const
  simp only [mul_one, lintegral_const, one_mul, Measure.restrict_apply_univ,
    Real.volume_Ioo] at h
  rw [h]
  have hsection : (∫⁻ y in Ioi 0, ENNReal.ofReal y * F y * ENNReal.ofReal (y - -y)) =
      ENNReal.ofReal 2 * ∫⁻ y in Ioi 0, F y * ENNReal.ofReal (y ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    have heq : y - -y = 2 * y := by ring
    rw [heq, ENNReal.ofReal_mul (by norm_num), pow_two,
      ENNReal.ofReal_mul hy.le]
    ring
  rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  ring

end

end

/-- The longitudinal/transverse coordinate equivalence for the actual three-real carrier. -/
noncomputable def cylindricalCoordinates : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℂ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) Complex.measurableEquivPi.symm)

/-- Cylindrical coordinates preserve three-dimensional Lebesgue volume. -/
theorem cylindricalCoordinates_measurePreserving : MeasurePreserving cylindricalCoordinates := ((MeasurePreserving.id volume).prod
    Complex.volume_preserving_equiv_pi.symm).comp
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)
section
variable (z : Fin 3 → ℝ)

/-- The longitudinal component is the first Cartesian component. -/
theorem cylindricalCoordinates_fst : (cylindricalCoordinates z).1 = z 0 := rfl

/-- Cartesian Euclidean norm equals the cylindrical radius. -/
theorem cylindricalCoordinates_radius :
    cylindricalRadius (cylindricalCoordinates z).1 ‖(cylindricalCoordinates z).2‖ =
      ‖WithLp.toLp 2 z‖ := by
  have hcomplex : ‖(cylindricalCoordinates z).2‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2 := by
    change ‖Complex.measurableEquivPi.symm (Fin.tail z)‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Fin.tail, pow_two]
  have heq : (z 0) ^ 2 + ‖(cylindricalCoordinates z).2‖ ^ 2 = ‖WithLp.toLp 2 z‖ ^ 2 := by
    rw [hcomplex]
    simpa [Fin.sum_univ_succ, add_assoc] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)).symm
  rw [cylindricalRadius, cylindricalCoordinates_fst, heq, Real.sqrt_sq (norm_nonneg _)]

end

/-- Nonnegative integrals transport directly to the three-real Cartesian carrier. -/
theorem lintegral_cylindricalCoordinates (f : ℝ × ℂ → ℝ≥0∞) :
    (∫⁻ z : Fin 3 → ℝ, f (cylindricalCoordinates z)) = ∫⁻ p : ℝ × ℂ, f p :=
  cylindricalCoordinates_measurePreserving.lintegral_comp_emb
    cylindricalCoordinates.measurableEmbedding f
section
variable (F : ℝ → ℝ≥0∞)
section
variable (hF : Measurable F)
include hF

/-- Weighted radial identity on the exact Euclidean three-coordinate carrier. -/
theorem lintegral_three_radial_exp (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖ * ENNReal.ofReal (Real.exp (c * z 0))) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
  rw [← lintegral_radial_exp F hF c hc, ← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius, cylindricalCoordinates_fst]

/-- The Maxwell radial integration formula on the same Cartesian carrier. -/
theorem lintegral_three_radial_zero :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
  rw [← lintegral_radial_zero F hF, ← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius]

end

end

end DOZZ.Proofs
