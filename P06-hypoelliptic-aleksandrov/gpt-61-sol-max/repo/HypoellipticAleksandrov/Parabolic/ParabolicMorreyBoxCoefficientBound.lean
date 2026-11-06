module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormTransport
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy

open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le from HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy


/-!
# Normalized coefficients on parabolic Morrey boxes

This module bounds the constant and velocity-slope coefficients of the
canonical affine moment projection on one literal forward physical box by its
normalized `L^(d + 1)` mean norm.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

private theorem isProbabilityMeasure_parabolicNormalizedVolumeOn
    {d : Nat} {Q : HypoellipticAleksandrov.Parabolic.Region d}
    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞) :
    IsProbabilityMeasure (parabolicNormalizedVolumeOn Q) := by
  refine ⟨?_⟩
  rw [parabolicNormalizedVolumeOn, Measure.smul_apply,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hQpos.ne' hQtop.ne




variable {d : Nat}

private theorem parabolicMorreyUnitAverage_eq_integral_normalizedVolume
     (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    parabolicMorreyUnitAverage f =
      ∫ z, f z ∂(parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
  simp_all [parabolicMorreyUnitAverage, parabolicNormalizedVolumeOn]

private theorem abs_integral_le_parabolicLpMeanNormOn
     {Q : HypoellipticAleksandrov.Parabolic.Region d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞)
    (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) :
    |∫ z, f z ∂(parabolicNormalizedVolumeOn Q)| ≤
      parabolicLpMeanNormOn d f Q hf := by
  let μ  := parabolicNormalizedVolumeOn Q

  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_parabolicNormalizedVolumeOn hQpos hQtop



  have hreal := ENNReal.toReal_mono (ne_of_lt (memLp_iff.mp hf)) (by
      calc
        ‖∫ z, f z ∂μ‖ₑ ≤ ∫⁻ z, ‖f z‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm f
        _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm (hf.aestronglyMeasurable)).symm
        _ ≤ eLpNorm f (parabolicExponent d) μ := eLpNorm_le_eLpNorm_of_exponent_le (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d))
  exact hreal

private theorem abs_parabolicMorreyUnitVelocityCoeff_le_parabolicLpMeanNormOn
     (g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hg : MemLp g (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)))
    (i : Fin d) :
    |parabolicMorreyUnitVelocityCoeff g i| ≤
      3 * parabolicLpMeanNormOn d g _ hg := by
  let sharedTerm_253015f777 := ((parabolicBox 1 1 0 (0 : PDE.Vec d)))
  let U  := parabolicMorreyUnitBox d
  let μ  := parabolicNormalizedVolumeOn U
  let p  := parabolicExponent d
  have hUpos : 0 < volume U := by
    change 0 < volume sharedTerm_253015f777
    exact volume_parabolicMorreyBox_pos 0 0 (by norm_num)
  have hUtop : volume U < ∞ := by
    change volume sharedTerm_253015f777 < ∞
    exact volume_parabolicMorreyBox_lt_top 0 0 (by norm_num)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_parabolicNormalizedVolumeOn hUpos hUtop


  have hweighted_meas  :=
    (show AEStronglyMeasurable g μ by
        exact hg.aestronglyMeasurable).mul ((continuous_apply i).comp continuous_snd).aestronglyMeasurable
  have hweighted_norm : eLpNorm (fun z  => g z * z.2 i) p μ ≤
      eLpNorm g p μ := by
    apply eLpNorm_mono_ae hweighted_meas
    filter_upwards [((id (Measure.ae_smul_measure (ae_restrict_mem (measurableSet_parabolicBox 1 1 0 0)) (volume U)⁻¹)))] with z hz
    change z ∈ sharedTerm_253015f777 at hz
    rw [mem_parabolicBox_iff] at hz
    rcases hz with ⟨_, _, hz⟩

    calc
      ‖g z * z.2 i‖ = |g z| * |z.2 i| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |g z| := mul_le_of_le_one_right (abs_nonneg _) (by
          change ∀ j : Fin d, |z.2 j - (0 : PDE.Vec d) j| < 1 at hz
          simpa using (hz i).le)
      _ = ‖g z‖ := (Real.norm_eq_abs _).symm
  have hweighted_mem  :=
    memLp_iff.mpr (lt_of_le_of_lt hweighted_norm
      ((memLp_iff.mp hg)))

  have hintegral  := abs_integral_le_parabolicLpMeanNormOn hUpos hUtop
      (hweighted_mem)
  rw [parabolicMorreyUnitVelocityCoeff,
    parabolicMorreyUnitAverage_eq_integral_normalizedVolume]
  rw [abs_mul, abs_of_nonneg (by norm_num)]
  exact mul_le_mul_of_nonneg_left (hintegral.trans (by
      rw [parabolicLpMeanNormOn_eq_toReal, parabolicLpMeanNormOn_eq_toReal, parabolicELpMeanNormOn]
      apply ENNReal.toReal_mono (ne_of_lt (memLp_iff.mp hg))
      exact hweighted_norm)) (by norm_num)

variable (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)))

private theorem parabolicLpMeanNormOn_parabolicBox_eq_unit
      :
    parabolicLpMeanNormOn d f _ hf =
      parabolicLpMeanNormOn d _
        _
        ((memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf) := by
  rw [parabolicLpMeanNormOn_eq_toReal, parabolicLpMeanNormOn_eq_toReal,
    parabolicELpMeanNormOn_parabolicBox_eq t₀ v₀ hr f]

include hr in
/-- The normalized constant coefficient of the canonical affine moment
projection is bounded by the normalized mean norm on the same forward box. -/
theorem abs_parabolicMorreyBoxAverage_le_parabolicLpMeanNormOn

     :
    |parabolicMorreyBoxAverage t₀ v₀ r f| <=
      parabolicLpMeanNormOn d f _ hf := by


  have hunit := abs_integral_le_parabolicLpMeanNormOn
    (d := d)
    (Q := parabolicMorreyUnitBox d)
    (by simpa only [parabolicMorreyUnitBox] using
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num : (0 : Real) < 1)))
    ((volume_parabolicMorreyBox_lt_top 0 0 (by norm_num : (0 : Real) < 1))) ((memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf)
  rw [← parabolicMorreyUnitAverage_eq_integral_normalizedVolume] at hunit
  exact hunit.trans_eq (parabolicLpMeanNormOn_parabolicBox_eq_unit t₀ v₀ hr f hf).symm

include hr in
/-- The radius-weighted `l¹` velocity slopes of the canonical affine moment
projection are bounded by the normalized mean norm on the same forward box. -/
theorem radius_sum_abs_parabolicMorreyBoxVelocitySlope_le_parabolicLpMeanNormOn

     :
    r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| <=
      (3 * (d : Real)) *
        parabolicLpMeanNormOn d f _ hf := by
  let g  := pullbackScalar f t₀ v₀ r
  let hg  :=
    (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf

  calc
    r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| =
        ∑ i : Fin d, r * |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin d, 3 * parabolicLpMeanNormOn d g _ hg :=
      Finset.sum_le_sum fun i _ => (show ∀ i : Fin d,
      r * |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| ≤
        3 * parabolicLpMeanNormOn d g _ hg by
          intro i
          rw [parabolicMorreyBoxVelocitySlope]
          have hcancel : r * |r⁻¹ * parabolicMorreyUnitVelocityCoeff g i| =
              |parabolicMorreyUnitVelocityCoeff g i| := by
            rw [abs_mul, abs_inv, abs_of_pos hr]
            field_simp [hr.ne']
          rw [show pullbackScalar f t₀ v₀ r = g by rfl, hcancel]
          exact abs_parabolicMorreyUnitVelocityCoeff_le_parabolicLpMeanNormOn g hg i) i
    _ = (3 * (d : Real)) *
        parabolicLpMeanNormOn d f _ hf := by
      simp_all [parabolicLpMeanNormOn_parabolicBox_eq_unit] <;> ring

include hr in
/-- The combined constant and radius-weighted velocity coefficient bound for
the canonical affine moment projection on one forward physical box. -/
theorem parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn

     :
    |parabolicMorreyBoxAverage t₀ v₀ r f| +
        r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| <=
      (1 + 3 * (d : Real)) *
        parabolicLpMeanNormOn d f _ hf := by
  let sharedTerm_1b3c76df42 := (parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf)
  have havg := abs_parabolicMorreyBoxAverage_le_parabolicLpMeanNormOn
    t₀ v₀ hr f hf
  have hslope :=
    radius_sum_abs_parabolicMorreyBoxVelocitySlope_le_parabolicLpMeanNormOn
      t₀ v₀ hr f hf
  calc
    |parabolicMorreyBoxAverage t₀ v₀ r f| +
        r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| ≤
        sharedTerm_1b3c76df42 +
          (3 * (d : Real)) *
            sharedTerm_1b3c76df42 :=
      add_le_add havg hslope
    _ = (1 + 3 * (d : Real)) *
        sharedTerm_1b3c76df42 := by
      ring

end HypoellipticAleksandrov.Parabolic
