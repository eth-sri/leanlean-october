module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormRestriction
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionMoments
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import HypoellipticAleksandrov.Measure.TimeVelocity
import HypoellipticAleksandrov.Parabolic.HarnackGeometry

/-!
# Nested parabolic Morrey affine projections

This module compares the canonical affine moment projections on nested forward
parabolic boxes.  The comparison is relative to the residual from the larger
projection and is valid in every spatial dimension, including dimension zero.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal

private theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := by
  unfold parabolicExponent
  exact le_add_of_nonneg_left bot_le

private theorem physicalProjection_recenter
    {d } (t_b : Real) (v_b : PDE.Vec d) (r_b : Real)
    (t_s : Real) (v_s : PDE.Vec d) (u : TimeVelocity d -> Real)
    (z : TimeVelocity d) :
    parabolicMorreyBoxAffineProjection t_b v_b r_b u z =
      parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) +
        ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_b v_b r_b u i *
          (z.2 i - v_s i) := by
  simp only [parabolicMorreyBoxAffineProjection]
  have hterm : ∀ i : Fin d,
      parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (z.2 i - v_b i) =
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (v_s i - v_b i) +
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (z.2 i - v_s i) := by
    intro i
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  ring

private theorem physicalProjection_pullback_recenter
    {d } (t_b : Real) (v_b : PDE.Vec d) (r_b : Real)
    (t_s : Real) (v_s : PDE.Vec d) {r_s } (_hr_s : 0 < r_s)
    (u : TimeVelocity d -> Real) :
    pullbackScalar (parabolicMorreyBoxAffineProjection t_b v_b r_b u)
      t_s v_s r_s =
      fun z => parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) +
        ∑ i : Fin d, (r_s *
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) * z.2 i := by
  funext z
  rw [pullbackScalar_apply, physicalProjection_recenter]
  simp only [parabolicAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem unit_raw_integrable_of_physical_mean_memLp
    {d } (t_s : Real) (v_s : PDE.Vec d) {r_s } (hr_s : 0 < r_s)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s))) :
    Integrable (pullbackScalar f t_s v_s r_s)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  have hmean := (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff
    t_s v_s hr_s f).mp hf
  have hUpos : 0 < volume (parabolicMorreyUnitBox d) :=
    (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).1
  have hUtop : volume (parabolicMorreyUnitBox d) < ∞ :=
    lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)
  have hraw := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
    hUpos hUtop hmean
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) := ⟨hUtop⟩
  exact hraw.integrable (parabolicExponent_one_le d)

private theorem unit_raw_integrable_affine
    {d } (a : Real) (b : Fin d -> Real) :
    Integrable (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) :=
    ⟨lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)⟩
  exact (Continuous.memLp_parabolicMorreyUnitBox (by fun_prop)).integrable
    (parabolicExponent_one_le d)

private theorem unit_average_affine
    {d } (a : Real) (b : Fin d -> Real) :
    parabolicMorreyUnitAverage
      (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) = a := by
  have hzero := congrFun (parabolicMorreyUnitAffineProjection_reproduces_velocity_affine a b) (0, 0)
  simpa only [parabolicMorreyUnitAffineProjection, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero] using hzero

private theorem unit_coeff_affine
    {d } (a : Real) (b : Fin d -> Real) (j : Fin d) :
    parabolicMorreyUnitVelocityCoeff
      (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) j = b j := by
  have hprojection :=
    parabolicMorreyUnitAffineProjection_reproduces_velocity_affine a b
  have havg :=
    unit_average_affine a b
  let e : PDE.Vec d := fun i => if i = j then 1 else 0
  have hsumCoeff : ∑ i : Fin d,
      parabolicMorreyUnitVelocityCoeff
        (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) i * e i =
      parabolicMorreyUnitVelocityCoeff
        (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) j := by
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hsumAffine : ∑ i : Fin d, b i * e i = b j := by
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have he := congrFun hprojection (0, e)
  have heq : parabolicMorreyUnitAverage
      (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) +
      ∑ i : Fin d,
        parabolicMorreyUnitVelocityCoeff
          (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) i * e i =
      a + ∑ i : Fin d, b i * e i := by
    simpa only [parabolicMorreyUnitAffineProjection] using he
  rw [hsumCoeff, hsumAffine, havg] at heq
  linarith

private theorem unit_raw_integrable_mul_velocity
    {d f}
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (i : Fin d) :
    Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  refine hf.mul_bdd (c := 1) ?_ ?_
  · exact ((continuous_apply i).comp continuous_snd).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
      (measurableSet_parabolicBox 1 1 0 (0 : PDE.Vec d))] with z hz
    change z ∈ parabolicBox 1 1 0 (0 : PDE.Vec d) at hz
    rw [mem_parabolicBox_iff] at hz
    change |z.2 i| ≤ 1
    simpa only [Pi.zero_apply, sub_zero] using (hz.2.2 i).le

theorem parabolicMorreyNestedProjection_discrepancy_le_largeResidual
    {d } (t_b : Real) (v_b : PDE.Vec d) {r_b } (hr_b : 0 < r_b)
    (t_s : Real) (v_s : PDE.Vec d) {r_s } (hr_s : 0 < r_s)
    (hsub : parabolicBox 1 r_s t_s v_s ⊆ parabolicBox 1 r_b t_b v_b)
    (u : TimeVelocity d -> Real)
    (hbig : MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_b t_b v_b))) :
    |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
      (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d
          (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
          (parabolicBox 1 r_b t_b v_b) hbig := by
  let f : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z
  have hsmall : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s)) := by
      have hrawᵦ := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
        (volume_parabolicMorreyBox_pos t_b v_b hr_b)
        (volume_parabolicMorreyBox_lt_top t_b v_b hr_b) hbig
      have hrawₛ :=
        hrawᵦ.mono_measure (Measure.restrict_mono_set volume hsub)
      exact memLp_parabolicNormalizedVolumeOn_of_memLp
        (volume_parabolicMorreyBox_pos t_s v_s hr_s) hrawₛ

    /- The guarded real normalized mean norm on a smaller contained forward box
    is bounded by that on the larger box with the exact parabolic radius factor. -/
  have hsmallbound : |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
      (1 + 3 * (d : Real)) * parabolicLpMeanNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
        (parabolicBox 1 r_s t_s v_s) hsmall := by
    have hbound := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
      t_s v_s hr_s
        (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z) hsmall
    have _h_inl_20 : parabolicMorreyBoxAverage t_s v_s r_s
        (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z) =
        parabolicMorreyBoxAverage t_s v_s r_s u -
          parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) := by
      let B :=
        parabolicMorreyBoxAffineProjection t_b v_b r_b u
      let f : TimeVelocity d -> Real := fun z => u z - B z
      let fhat := pullbackScalar f t_s v_s r_s
      let bhat := pullbackScalar B t_s v_s r_s
      have hfhat : Integrable fhat (volume.restrict (parabolicMorreyUnitBox d)) := by
        dsimp only [fhat, f]
        exact unit_raw_integrable_of_physical_mean_memLp t_s v_s hr_s _ hsmall
      have hbhat_shape : bhat = fun z => B (t_s, v_s) + ∑ i : Fin d,
          (r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) * z.2 i := by
        dsimp only [bhat, B]
        exact physicalProjection_pullback_recenter t_b v_b r_b t_s v_s hr_s u
      have hbhat : Integrable bhat (volume.restrict (parabolicMorreyUnitBox d)) := by
        rw [hbhat_shape]
        exact unit_raw_integrable_affine _ _
      have hsum : pullbackScalar u t_s v_s r_s = fhat + bhat := by
        funext z
        simp only [fhat, bhat, f, B, pullbackScalar_apply, Pi.add_apply]
        ring
      have havg := parabolicMorreyUnitAverage_add fhat bhat hfhat hbhat
      rw [← hsum] at havg
      have hBavg : parabolicMorreyUnitAverage bhat = B (t_s, v_s) := by
        rw [hbhat_shape]
        exact unit_average_affine _ _
      change parabolicMorreyUnitAverage fhat =
        parabolicMorreyUnitAverage (pullbackScalar u t_s v_s r_s) - B (t_s, v_s)
      rw [hBavg] at havg
      linarith
    rw [_h_inl_20]
      at hbound
    have hslope : ∀ i : Fin d,
        parabolicMorreyBoxVelocitySlope t_s v_s r_s
          (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z) i =
          parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
            parabolicMorreyBoxVelocitySlope t_b v_b r_b u i := by
      intro i
      let B :=
        parabolicMorreyBoxAffineProjection t_b v_b r_b u
      let f : TimeVelocity d -> Real := fun z => u z - B z
      let fhat := pullbackScalar f t_s v_s r_s
      let bhat := pullbackScalar B t_s v_s r_s
      have hfhat : Integrable fhat (volume.restrict (parabolicMorreyUnitBox d)) := by
        dsimp only [fhat, f]
        exact unit_raw_integrable_of_physical_mean_memLp t_s v_s hr_s _ hsmall
      have hbhat_shape : bhat = fun z => B (t_s, v_s) + ∑ j : Fin d,
          (r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u j) * z.2 j := by
        dsimp only [bhat, B]
        exact physicalProjection_pullback_recenter t_b v_b r_b t_s v_s hr_s u
      have hbhat : Integrable bhat (volume.restrict (parabolicMorreyUnitBox d)) := by
        rw [hbhat_shape]
        exact unit_raw_integrable_affine _ _
      have hfhatmul :=
        unit_raw_integrable_mul_velocity hfhat i
      have hbhatmul :=
        unit_raw_integrable_mul_velocity hbhat i
      have hsum : pullbackScalar u t_s v_s r_s = fhat + bhat := by
        funext z
        simp only [fhat, bhat, f, B, pullbackScalar_apply, Pi.add_apply]
        ring
      have hcoeff := parabolicMorreyUnitVelocityCoeff_add fhat bhat i hfhatmul hbhatmul
      rw [← hsum] at hcoeff
      have hBcoeff : parabolicMorreyUnitVelocityCoeff bhat i =
          r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u i := by
        rw [hbhat_shape]
        exact unit_coeff_affine _ _ i
      change r_s⁻¹ * parabolicMorreyUnitVelocityCoeff fhat i =
        r_s⁻¹ * parabolicMorreyUnitVelocityCoeff (pullbackScalar u t_s v_s r_s) i -
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i
      rw [hBcoeff] at hcoeff
      rw [hcoeff]
      field_simp [hr_s.ne']
      ring
    simp_rw [hslope] at hbound
    exact hbound
  have hnorm : parabolicLpMeanNormOn d f (parabolicBox 1 r_s t_s v_s) hsmall ≤ (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) * parabolicLpMeanNormOn d f (parabolicBox 1 r_b t_b v_b) hbig := by
    have _h_xinl_0 : volume (parabolicBox 1 r_b t_b v_b) ≠ ∞ := by
        exact (
      ne_of_lt (volume_parabolicMorreyBox_lt_top t_b v_b hr_b)
      )
    have hratio_top :
        volume (parabolicBox 1 r_b t_b v_b) /
            volume (parabolicBox 1 r_s t_s v_s) ≠ ∞ :=
      ENNReal.div_ne_top _h_xinl_0
        (volume_parabolicMorreyBox_pos t_s v_s hr_s).ne'
    have hfactor_top :
        ((volume (parabolicBox 1 r_b t_b v_b) /
            volume (parabolicBox 1 r_s t_s v_s)) ^
              (1 / parabolicExponent d).toReal) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hratio_top
    have hright_top :
        ((volume (parabolicBox 1 r_b t_b v_b) /
            volume (parabolicBox 1 r_s t_s v_s)) ^
              (1 / parabolicExponent d).toReal) *
            parabolicELpMeanNormOn d f (parabolicBox 1 r_b t_b v_b) ≠ ∞ := by
      exact ENNReal.mul_ne_top hfactor_top (ne_of_lt (memLp_iff.mp hbig))
    have hreal := ENNReal.toReal_mono hright_top (parabolicELpMeanNormOn_mono_set (d := d) (volume_parabolicMorreyBox_pos t_s v_s hr_s) (volume_parabolicMorreyBox_lt_top t_s v_s hr_s) (volume_parabolicMorreyBox_pos t_b v_b hr_b) (volume_parabolicMorreyBox_lt_top t_b v_b hr_b) hsub f)
    have _h_inl_9 (d) : (parabolicExponent d).toReal = (d : Real) + 1 := by
      unfold parabolicExponent
      have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by
        norm_num
      rw [hcast, ENNReal.toReal_natCast]
      norm_num
    have _h_inl_10 : ((volume (parabolicBox 1 r_b t_b v_b) / volume (parabolicBox 1 r_s t_s v_s)) ^ (1 / parabolicExponent d).toReal).toReal = (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) := by
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_div,
        volume_parabolicMorreyBox_toReal t_b v_b hr_b,
        volume_parabolicMorreyBox_toReal t_s v_s hr_s]
      simp only [ENNReal.toReal_div, ENNReal.toReal_one, _h_inl_9]
      have htwo : (2 : Real) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
      have hratio :
          ((2 : Real) ^ d * r_b ^ (d + 2)) /
              ((2 : Real) ^ d * r_s ^ (d + 2)) =
            (r_b / r_s) ^ (d + 2) := by
        rw [mul_div_mul_left _ _ htwo, (div_pow _ _ _).symm]
      rw [hratio, ← Real.rpow_natCast,
        ← Real.rpow_mul (div_nonneg hr_b.le hr_s.le)]
      congr 1
      have hp : (d : Real) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hp]
    simpa only [parabolicLpMeanNormOn_eq_toReal, ENNReal.toReal_mul,
      _h_inl_10] using hreal
  calc
    |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
        (1 + 3 * (d : Real)) *
          parabolicLpMeanNormOn d f (parabolicBox 1 r_s t_s v_s) hsmall := by
      simpa only [f] using hsmallbound
    _ ≤ (1 + 3 * (d : Real)) *
        ((r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
          parabolicLpMeanNormOn d f (parabolicBox 1 r_b t_b v_b) hbig) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d f (parabolicBox 1 r_b t_b v_b) hbig := by
      ring

/- Two nested canonical affine projections differ pointwise by the same
large-box residual bound on the small forward box. -/
theorem parabolicMorreyNestedProjection_abs_sub_le_largeResidual
    {d } (t_b : Real) (v_b : PDE.Vec d) {r_b } (hr_b : 0 < r_b)
    (t_s : Real) (v_s : PDE.Vec d) {r_s } (hr_s : 0 < r_s)
    (hsub : parabolicBox 1 r_s t_s v_s ⊆ parabolicBox 1 r_b t_b v_b)
    (u : TimeVelocity d -> Real) (z )
    (hz : z ∈ parabolicBox 1 r_s t_s v_s)
    (hbig : MemLp (fun w => u w - parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_b t_b v_b))) :
    |parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z| ≤
      (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d
          (fun w => u w - parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
          (parabolicBox 1 r_b t_b v_b) hbig := by
  have _h_inl_21 : |parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z| ≤
      |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| := by
    have hcoord : ∀ i : Fin d, |z.2 i - v_s i| ≤ r_s := by
      intro i
      rw [mem_parabolicBox_iff] at hz
      exact (hz.2.2 i).le
    have hdiff :
        parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
          parabolicMorreyBoxAffineProjection t_b v_b r_b u z =
          (parabolicMorreyBoxAverage t_s v_s r_s u -
            parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)) +
          ∑ i : Fin d,
            (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                (z.2 i - v_s i) := by
      rw [physicalProjection_recenter t_b v_b r_b t_s v_s u z]
      simp only [parabolicMorreyBoxAffineProjection]
      have hsumdiff :
          (∑ i : Fin d,
            (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                (z.2 i - v_s i)) =
            (∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_s v_s r_s u i *
              (z.2 i - v_s i)) -
            ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_b v_b r_b u i *
              (z.2 i - v_s i) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsumdiff]
      ring
    have hsum : |∑ i : Fin d,
        (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
            (z.2 i - v_s i)| ≤
        r_s * ∑ i : Fin d,
          |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
            parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| := by
      calc
        |∑ i : Fin d,
            (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                (z.2 i - v_s i)| ≤
            ∑ i : Fin d,
              |(parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
                parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                  (z.2 i - v_s i)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin d,
            |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| *
                |z.2 i - v_s i| := by
          simp_rw [abs_mul]
        _ ≤ ∑ i : Fin d,
            |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| * r_s := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
        _ = r_s * ∑ i : Fin d,
            |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| := by
          rw [Finset.mul_sum]
          ac_rfl
    rw [hdiff]
    calc
      |(parabolicMorreyBoxAverage t_s v_s r_s u -
            parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)) +
          ∑ i : Fin d,
            (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                (z.2 i - v_s i)| ≤
          |parabolicMorreyBoxAverage t_s v_s r_s u -
            parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
          |∑ i : Fin d,
            (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
              parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                (z.2 i - v_s i)| := abs_add_le _ _
      _ ≤ _ := add_le_add (le_refl _) hsum
  exact _h_inl_21.trans
      (parabolicMorreyNestedProjection_discrepancy_le_largeResidual
        t_b v_b hr_b t_s v_s hr_s hsub u hbig)

end HypoellipticAleksandrov.Parabolic
