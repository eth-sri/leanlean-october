module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormTransport
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Normalized coefficients on parabolic Morrey boxes

This module bounds the constant and velocity-slope coefficients of the
canonical affine moment projection on one literal forward physical box by its
normalized `L^(d + 1)` mean norm.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : Nat} {Q : Set (TimeVelocity d)} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real}

theorem isProbabilityMeasure_parabolicNormalizedVolumeOn
    
    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞) :
    IsProbabilityMeasure (parabolicNormalizedVolumeOn Q) := by
  refine ⟨?_⟩
  rw [parabolicNormalizedVolumeOn, Measure.smul_apply,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hQpos.ne' hQtop.ne

theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := le_add_of_nonneg_left bot_le

private theorem parabolicMorreyUnitAverage_eq_integral_normalizedVolume
     (f : TimeVelocity d -> Real) :
    parabolicMorreyUnitAverage f =
      ∫ z, f z ∂(parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
  simp only [parabolicMorreyUnitAverage, parabolicNormalizedVolumeOn,
    integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

private theorem abs_integral_le_parabolicLpMeanNormOn
     {f : TimeVelocity d -> Real}
    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞)
    (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) :
    |∫ z, f z ∂(parabolicNormalizedVolumeOn Q)| ≤
      parabolicLpMeanNormOn d f Q hf := by
  let μ  := parabolicNormalizedVolumeOn Q
  let p  := parabolicExponent d
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_parabolicNormalizedVolumeOn hQpos hQtop
  have hmeas : AEStronglyMeasurable f μ := by
    simpa using hf.aestronglyMeasurable
  have hp : (1) ≤ p := by
    simpa using parabolicExponent_one_le d
  have hnorm : ‖∫ z, f z ∂μ‖ₑ ≤ eLpNorm f p μ := by
    calc
      ‖∫ z, f z ∂μ‖ₑ ≤ ∫⁻ z, ‖f z‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm f
      _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm hmeas).symm
      _ ≤ eLpNorm f p μ := eLpNorm_le_eLpNorm_of_exponent_le hp
  have hreal := ENNReal.toReal_mono (ne_of_lt (memLp_iff.mp hf)) hnorm
  simpa only [μ, p, toReal_enorm, Real.norm_eq_abs,
    parabolicLpMeanNormOn_eq_toReal, parabolicELpMeanNormOn] using hreal

private theorem abs_parabolicMorreyUnitVelocityCoeff_le_parabolicLpMeanNormOn
     (g : TimeVelocity d -> Real)
    (hg : MemLp g (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)))
    (i : Fin d) :
    |parabolicMorreyUnitVelocityCoeff g i| ≤
      3 * parabolicLpMeanNormOn d g (parabolicMorreyUnitBox d) hg := by
  let U  := parabolicMorreyUnitBox d
  let μ  := parabolicNormalizedVolumeOn U
  let p  := parabolicExponent d
  have hUpos : 0 < volume U := volume_parabolicMorreyBox_pos 0 0 (by norm_num)
  have hUtop : volume U < ∞ := volume_parabolicMorreyBox_lt_top 0 0 (by norm_num)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_parabolicNormalizedVolumeOn hUpos hUtop
  have hUae : ∀ᵐ z ∂μ, z ∈ U := Measure.ae_smul_measure
      (ae_restrict_mem (measurableSet_parabolicBox 1 1 0 _)) _
  have hgmeas : AEStronglyMeasurable g μ := by
    simpa using hg.aestronglyMeasurable
  have hweighted_meas : AEStronglyMeasurable (fun z : TimeVelocity d =>
      g z * z.2 i) μ :=
    hgmeas.mul ((continuous_apply i).comp continuous_snd).aestronglyMeasurable
  have hweighted_norm : eLpNorm (fun z : TimeVelocity d => g z * z.2 i) p μ ≤
      eLpNorm g p μ := by
    apply eLpNorm_mono_ae hweighted_meas
    filter_upwards [hUae] with z hz
    change z ∈ parabolicBox 1 1 0 _ at hz
    rw [mem_parabolicBox_iff] at hz
    rcases hz with ⟨_, _, hz⟩
    have hcoord : |z.2 i| ≤ 1 := by
      simpa using (hz i).le
    calc
      ‖g z * z.2 i‖ = |g z| * |z.2 i| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |g z| := mul_le_of_le_one_right (abs_nonneg _) hcoord
      _ = ‖g z‖ := (Real.norm_eq_abs _).symm
  have hweighted_mem : MemLp _ p μ :=
    memLp_iff.mpr (lt_of_le_of_lt hweighted_norm
      (by simpa using (memLp_iff.mp hg)))
  have hweighted_real :
      parabolicLpMeanNormOn d _ U
          (by simpa using hweighted_mem) ≤
        parabolicLpMeanNormOn d g U (by simpa using hg) := by
    apply ENNReal.toReal_mono (ne_of_lt (memLp_iff.mp hg))
    simpa only [p, μ, U, parabolicELpMeanNormOn] using hweighted_norm
  have hintegral :
      |∫ z, g z * z.2 i ∂(parabolicNormalizedVolumeOn U)| ≤
        parabolicLpMeanNormOn d _ U
          (by simpa using hweighted_mem) := abs_integral_le_parabolicLpMeanNormOn hUpos hUtop
      _
  rw [parabolicMorreyUnitVelocityCoeff,
    parabolicMorreyUnitAverage_eq_integral_normalizedVolume]
  rw [abs_mul, abs_of_nonneg (by norm_num)]
  exact mul_le_mul_of_nonneg_left (hintegral.trans hweighted_real) (by norm_num)

private theorem parabolicLpMeanNormOn_parabolicBox_eq_unit
     (hr : 0 < r)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀))) :
    parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf =
      parabolicLpMeanNormOn d (pullbackScalar f t₀ v₀ r)
        (parabolicMorreyUnitBox d)
        ((memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf) := by
  rw [parabolicLpMeanNormOn_eq_toReal, parabolicLpMeanNormOn_eq_toReal,
    parabolicELpMeanNormOn_parabolicBox_eq t₀ v₀ hr]

/-- The normalized constant coefficient of the canonical affine moment
projection is bounded by the normalized mean norm on the same forward box. -/
theorem abs_parabolicMorreyBoxAverage_le_parabolicLpMeanNormOn
     (hr : 0 < r)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀))) :
    |parabolicMorreyBoxAverage t₀ v₀ r f| <=
      parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf := by
  let g  := pullbackScalar f t₀ v₀ r
  let hg : MemLp g _
      _ :=
    (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf
  have hunit := abs_integral_le_parabolicLpMeanNormOn
    (d := d)
    (Q := parabolicMorreyUnitBox d)
    (by simpa only [parabolicMorreyUnitBox] using
      (volume_parabolicMorreyBox_pos 0 0 (by norm_num)))
    (by simpa only [parabolicMorreyUnitBox] using
      (volume_parabolicMorreyBox_lt_top 0 0 (by norm_num))) hg
  rw [← parabolicMorreyUnitAverage_eq_integral_normalizedVolume] at hunit
  simpa only [parabolicMorreyBoxAverage, g] using
    hunit.trans_eq (parabolicLpMeanNormOn_parabolicBox_eq_unit t₀ v₀ hr f hf).symm

/-- The radius-weighted `l¹` velocity slopes of the canonical affine moment
projection are bounded by the normalized mean norm on the same forward box. -/
theorem radius_sum_abs_parabolicMorreyBoxVelocitySlope_le_parabolicLpMeanNormOn
     (hr : 0 < r)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀))) :
    r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| <=
      (3 * (d : Real)) *
        parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf := by
  let g  := pullbackScalar f t₀ v₀ r
  let hg : MemLp g _
      _ :=
    (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mp hf
  have hterm : ∀ i : Fin d,
      r * |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| ≤
        3 * parabolicLpMeanNormOn d g _ hg := by
    intro i
    rw [parabolicMorreyBoxVelocitySlope]
    have hcancel : r * |r⁻¹ * parabolicMorreyUnitVelocityCoeff g i| =
        |parabolicMorreyUnitVelocityCoeff g i| := by
      rw [abs_mul, abs_inv, abs_of_pos hr]
      field_simp
    rw [hcancel]
    exact abs_parabolicMorreyUnitVelocityCoeff_le_parabolicLpMeanNormOn g hg i
  calc
    r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| =
        ∑ i : Fin d, r * |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin d, 3 * parabolicLpMeanNormOn d g _ hg :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (3 * d) *
        parabolicLpMeanNormOn d f _ hf := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← parabolicLpMeanNormOn_parabolicBox_eq_unit t₀ v₀ hr f hf]
      ring

/-- The combined constant and radius-weighted velocity coefficient bound for
the canonical affine moment projection on one forward physical box. -/
theorem parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
     (hr : 0 < r)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀))) :
    |parabolicMorreyBoxAverage t₀ v₀ r f| +
        r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| <=
      (1 + 3 * (d : Real)) *
        parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf := by
  have havg := abs_parabolicMorreyBoxAverage_le_parabolicLpMeanNormOn
    t₀ v₀ hr f hf
  have hslope :=
    radius_sum_abs_parabolicMorreyBoxVelocitySlope_le_parabolicLpMeanNormOn
      t₀ v₀ hr f hf
  calc
    |parabolicMorreyBoxAverage t₀ v₀ r f| +
        r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| ≤
        parabolicLpMeanNormOn d f _ hf +
          (3 * d) *
            parabolicLpMeanNormOn d f _ hf :=
      add_le_add havg hslope
    _ = (1 + 3 * d) *
        parabolicLpMeanNormOn d f _ hf := by
      ring

end HypoellipticAleksandrov.Parabolic
