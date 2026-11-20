module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSlices
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import PDEFoundation.Measure.LpPower
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import HypoellipticAleksandrov.Parabolic.ABP
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceCollarCutoff
import HypoellipticAleksandrov.Parabolic.ParabolicPoincareMoments

/-!
# Temporal derivatives of time-slice velocity projections

This module proves the temporal moment-affine Poincare estimate and its finite
real corollary from private smooth-calculus, scalar Poincare, and Fubini layers.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators Topology

private theorem velocityCube_subset_closed {d : Nat} :
    velocityCube (0 : PDE.Vec d) 1 ⊆ velocityClosedCube 0 1 :=
  fun _ hv i => (hv i).le

section
variable {d : Nat} {g : TimeVelocity d -> Real} (hg : Continuous g)
include hg

private theorem continuous_integral_velocity_weighted_of_continuous
    (w : PDE.Vec d → ℝ) (hw : Continuous w) :
    Continuous (fun t : ℝ => ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * w v) := by
  have hμ : (volume.restrict (velocityCube (0 : PDE.Vec d) 1)).restrict
      (velocityClosedCube 0 1) = volume.restrict (velocityCube 0 1) := by
    rw [Measure.restrict_restrict' (measurableSet_velocityCube (0 : PDE.Vec d) 1),
      Set.inter_eq_right.mpr velocityCube_subset_closed]
  simpa only [hμ] using
    (continuous_parametric_integral_of_continuous
      (μ := volume.restrict (velocityCube (0 : PDE.Vec d) 1))
      (f := fun t v => g (t, v) * w v) (hg.mul (hw.comp continuous_snd))
      (isCompact_velocityClosedCube (0 : PDE.Vec d) 1))

private theorem continuous_parabolicMorreyUnitVelocityAverage :
    Continuous (parabolicMorreyUnitVelocityAverage g) := by
  unfold parabolicMorreyUnitVelocityAverage
  simpa only [mul_one] using
    (continuous_integral_velocity_weighted_of_continuous hg (fun _ => 1) continuous_const).const_mul
      ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹

private theorem continuous_parabolicMorreyUnitVelocityCoeffAt (i : Fin d) :
    Continuous (fun t => parabolicMorreyUnitVelocityCoeffAt g t i) := by
  simpa only [parabolicMorreyUnitVelocityCoeffAt] using
    (continuous_integral_velocity_weighted_of_continuous hg (fun v => v i) (continuous_apply i)).const_mul
      (3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)

/-- The spatial affine projection of a continuous function is continuous in both variables. -/
theorem continuous_parabolicMorreyUnitSpatialAffineProjection :
    Continuous (parabolicMorreyUnitSpatialAffineProjection g) :=
  ((continuous_parabolicMorreyUnitVelocityAverage hg).comp continuous_fst).add
    (continuous_finset_sum _ fun i _ =>
      ((continuous_parabolicMorreyUnitVelocityCoeffAt hg i).comp continuous_fst).mul
        ((continuous_apply i).comp continuous_snd))

end

section
variable {d : Nat} {u : TimeVelocity d -> Real} (hu : ContDiff Real 2 u)
include hu

private theorem hasDerivAt_integral_velocity_weighted (w : PDE.Vec d → ℝ)
    (hw : Continuous w) (t : ℝ) :
    HasDerivAt
      (fun s => ∫ v in velocityCube (0 : PDE.Vec d) 1, u (s, v) * w v)
      (∫ v in velocityCube (0 : PDE.Vec d) 1, timeDerivative u (t, v) * w v) t := by
  let V := velocityCube (0 : PDE.Vec d) 1
  let F := fun s v => u (s, v) * w v
  let F' := fun s v => timeDerivative u (s, v) * w v
  have hF (s : ℝ) : Continuous (F s) :=
    (hu.continuous.comp (continuous_const.prodMk continuous_id)).mul hw
  have hF' : Continuous (Function.uncurry F') :=
    (timeDerivative_cutoff_continuous hu).mul (hw.comp continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t - 1) (b := t + 1) |>.prod
    (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)).exists_bound_of_continuousOn hF'.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict V) (F := F) (F' := F') (bound := fun _ => C)
    (Metric.ball_mem_nhds t zero_lt_one)
    (.of_forall fun s => (hF s).aestronglyMeasurable)
    (continuous_integrable_unit_velocity_cube (hF t))
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ?_ (continuous_integrable_unit_velocity_cube continuous_const)
    (.of_forall fun v s _ => (time_slice_hasDerivAt (hu.differentiable (by norm_num) (s, v))).mul_const (w v))).2
  filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)] with v hv
  intro s hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  exact hC (s, v) ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, velocityCube_subset_closed hv⟩

private theorem hasDerivAt_parabolicMorreyUnitVelocityAverage (t : Real) :
    HasDerivAt (parabolicMorreyUnitVelocityAverage u)
      (parabolicMorreyUnitVelocityAverage (timeDerivative u) t) t := by
  change HasDerivAt
    (fun s => ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
      ∫ v in velocityCube 0 1, u (s, v)) _ t
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
    (hasDerivAt_integral_velocity_weighted hu (fun _ : PDE.Vec d => 1)
      continuous_const t).const_mul
      ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹

private theorem hasDerivAt_parabolicMorreyUnitVelocityCoeffAt (i : Fin d) (t : Real) :
    HasDerivAt (fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i)
      (parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i) t := by
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
    (hasDerivAt_integral_velocity_weighted hu (fun v : PDE.Vec d => v i)
      (continuous_apply i) t).const_mul
      (3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)

private theorem hasDerivAt_parabolicMorreyUnitSpatialAffineProjection (v : PDE.Vec d) (t : Real) :
    HasDerivAt
      (fun s : Real => parabolicMorreyUnitSpatialAffineProjection u (s, v))
      (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
      t := by
  have hs := (hasDerivAt_parabolicMorreyUnitVelocityAverage hu t).add
    (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).mul_const (v i))
  convert hs using 1 <;> first | rfl | (ext s; simp [parabolicMorreyUnitSpatialAffineProjection, Finset.sum_apply])

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory

private theorem unitTime_meanPoincare_rpow
    {p : ℝ} {f f' : ℝ → ℝ}
    (hp : 1 ≤ p) (hf' : Continuous f')
    (hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t) :
    ∫ t in Set.Ioo (0 : ℝ) 1,
        |f t - ∫ s in Set.Ioo (0 : ℝ) 1, f s| ^ p ≤
      ∫ t in Set.Ioo (0 : ℝ) 1, |f' t| ^ p := by
  simp_rw [← integral_Icc_eq_integral_Ioo]
  let J := Icc (0 : ℝ) 1
  let A := ∫ s in J, f s
  let B := ∫ s in J, |f' s|
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hv : volume J = 1 := by norm_num [J, Real.volume_Icc]
  have hvol : volume.real J = 1 := by simp [Measure.real, hv]
  have hconst (c : ℝ) : (∫ s in J, c) = c := by rw [setIntegral_const, hvol, one_smul]
  have hfin : volume J ≠ ⊤ := by simp [hv]
  have hi : IntegrableOn (fun s => |f' s|) J := hf'.abs.integrableOn_Icc
  have hpw : Continuous (fun s => |f' s| ^ p) := (Real.continuous_rpow_const (by linarith)).comp hf'.abs
  have hpoint (t : ℝ) (ht : t ∈ J) : |f t - A| ≤ B := by
    rw [← hconst (f t), show A = ∫ s in J, f s from rfl,
      ← integral_sub (integrableOn_const (C := f t) hfin) hf.integrableOn_Icc, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrableOn_const (C := B) hfin) ?_).trans_eq (hconst B)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hf'.intervalIntegrable s t)]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans <|
      setIntegral_mono_set hi (ae_of_all _ fun _ => abs_nonneg _)
        (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)).eventuallyLE
  have hJensen := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn isClosed_Ici
    (show volume J ≠ 0 by simp [hv]) hfin (ae_of_all _ fun _ => abs_nonneg _) hi hpw.integrableOn_Icc
  have hB : B ^ p ≤ ∫ t in J, |f' t| ^ p := by
    simpa only [setAverage_eq, hvol, inv_one, one_smul, B, Function.comp_apply] using hJensen
  change (∫ t in J, |f t - A| ^ p) ≤ _
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (integrableOn_const (C := B ^ p) hfin) ?_).trans ((hconst (B ^ p)).le.trans hB)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact Real.rpow_le_rpow (abs_nonneg _) (hpoint t ht) (by linarith)

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem continuous_parabolicMorreyUnitAffineProjection
    {d : Nat} (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  fun_prop

private theorem parabolicMorreyUnitBox_volume_toReal_eq_velocityCube (d : Nat) :
    (volume (parabolicMorreyUnitBox d)).toReal =
      (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
  rw [volume_parabolicMorreyUnitBox_toReal,
    volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : Real) ≤ 1)]
  simp only [mul_one]

section
variable {d : Nat} {u : TimeVelocity d → ℝ}

private theorem parabolicMorreyUnitAverage_eq_integral_velocityAverage
    (hu : Continuous u) :
    parabolicMorreyUnitAverage u =
      ∫ t in Set.Ioo (0 : ℝ) 1, parabolicMorreyUnitVelocityAverage u t := by
  have hi := continuous_integrable_unit hu
  rw [parabolicMorreyUnitBox_restrict_volume_eq_prod] at hi
  unfold parabolicMorreyUnitAverage parabolicMorreyUnitVelocityAverage
  rw [parabolicMorreyUnitBox_volume_toReal_eq_velocityCube]
  change _ * (∫ z, u z ∂volume.restrict (parabolicMorreyUnitBox d)) = _
  rw [parabolicMorreyUnitBox_restrict_volume_eq_prod, integral_prod _ hi, integral_const_mul]

private theorem parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt
    (hu : ContDiff Real 2 u) (i : Fin d) :
    parabolicMorreyUnitVelocityCoeff u i =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityCoeffAt u t i := by
  unfold parabolicMorreyUnitVelocityCoeff parabolicMorreyUnitVelocityCoeffAt
  have hcont : Continuous (fun z : TimeVelocity d => u z * z.2 i) :=
    hu.continuous.mul (continuous_apply i |>.comp continuous_snd)
  have haverage := parabolicMorreyUnitAverage_eq_integral_velocityAverage hcont
  change 3 * parabolicMorreyUnitAverage (fun z => u z * z.2 i) = _
  rw [haverage]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t _
  unfold parabolicMorreyUnitVelocityAverage
  ring

private theorem parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
    (hu : ContDiff Real 2 u) (v : PDE.Vec d) :
    parabolicMorreyUnitAffineProjection u (0, v) =
      ∫ t in Set.Ioo (0 : Real) 1,
        parabolicMorreyUnitSpatialAffineProjection u (t, v) := by
  let I : Set Real := Set.Ioo 0 1
  have hi {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f I :=
    hf.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hCoeffInt (i : Fin d) : IntegrableOn
      (fun t => parabolicMorreyUnitVelocityCoeffAt u t i * v i) I :=
    hi ((continuous_parabolicMorreyUnitVelocityCoeffAt hu.continuous i).mul continuous_const)
  have hAvgInt := hi (continuous_parabolicMorreyUnitVelocityAverage hu.continuous)
  have hSumInt := integrable_finset_sum Finset.univ fun i _ => hCoeffInt i
  unfold parabolicMorreyUnitAffineProjection parabolicMorreyUnitSpatialAffineProjection
  rw [parabolicMorreyUnitAverage_eq_integral_velocityAverage hu.continuous]
  simp_rw [parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt hu]
  rw [MeasureTheory.integral_add hAvgInt hSumInt,
    MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hCoeffInt i)]
  simp_rw [MeasureTheory.integral_mul_const]
  ring

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem parabolicELpNormOn_spatialAffineProjection_timeDerivative_le
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
  let I : Set Real := Set.Ioo 0 1
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let p : ENNReal := parabolicExponent d
  let q : Real -> ENNReal := fun t =>
    PDE.eLpNormOn V p (fun v =>
      parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
  let r : Real -> ENNReal := fun t =>
    PDE.eLpNormOn V p (fun v => timeDerivative u (t, v))
  have htime : Continuous (timeDerivative u) := _root_.HypoellipticAleksandrov.Parabolic.timeDerivative_cutoff_continuous hu
  have hTae : AEMeasurable (timeDerivative u)
      (volume.restrict (parabolicMorreyUnitBox d)) := htime.aemeasurable
  have hslicebound (t : Real) : q t ≤ ENNReal.ofReal (1 + 3 * (d : Real)) * r t := by
    simpa only [q, r, p, V,
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le
        (fun v => timeDerivative u (t, v))
        (htime.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hScont : Continuous (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)) :=
    continuous_parabolicMorreyUnitSpatialAffineProjection htime
  have hsliceNorm : eLpNorm q p (volume.restrict I) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm r p (volume.restrict I) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (by simpa only [q, I, V, p] using
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm _
          hScont.aemeasurable).aestronglyMeasurable) ?_
    filter_upwards with t
    simpa only [enorm_eq_self] using hslicebound t

  calc
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) = eLpNorm q p (volume.restrict I) := by
      simpa only [q, p, V, I] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)) hScont.aemeasurable
    _ ≤ ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm r p (volume.restrict I) := hsliceNorm
    _ = ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
      rw [parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
        (timeDerivative u) hTae]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

private theorem temporalResidual_setIntegral_rpow_le_spatialProjection
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) <=
      ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) z| ^
          ((d : Real) + 1) := by
  let I : Set Real := Set.Ioo 0 1
  let V : Set (PDE.Vec d) := velocityCube 0 1
  let B : Set (TimeVelocity d) := parabolicMorreyUnitBox d
  let p : Real := (d : Real) + 1
  let R : TimeVelocity d -> Real := fun z =>
    parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z
  let S : TimeVelocity d -> Real :=
    parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  let μ : Measure Real := volume.restrict I
  let ν : Measure (PDE.Vec d) := volume.restrict V

  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hp1 : 1 <= p := by
    dsimp only [p]
    linarith
  have hRcont : Continuous R :=
    (continuous_parabolicMorreyUnitSpatialAffineProjection hu.continuous).sub
      (continuous_parabolicMorreyUnitAffineProjection u)
  have hScont : Continuous S :=
    continuous_parabolicMorreyUnitSpatialAffineProjection
      (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_cutoff_continuous hu)
  have hprod {f : TimeVelocity d → ℝ} (hf : Continuous f) :
      Integrable (fun z => |f z| ^ p) (μ.prod ν) := by
    have hi := continuous_integrable_unit
      ((Real.continuous_rpow_const hp.le).comp hf.abs)
    rw [parabolicMorreyUnitBox_restrict_volume_eq_prod] at hi
    exact hi
  have hRprod := hprod hRcont
  have hSprod := hprod hScont

  have hpoint (v : PDE.Vec d) :
      ∫ t, |R (t, v)| ^ p ∂μ <= ∫ t, |S (t, v)| ^ p ∂μ := by
    have hmean := parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
      hu v
    have hscalar := unitTime_meanPoincare_rpow (p := p) hp1
      (hScont.comp (continuous_id.prodMk continuous_const))
      (hasDerivAt_parabolicMorreyUnitSpatialAffineProjection hu v)
    have haffine (t : Real) :
        parabolicMorreyUnitAffineProjection u (t, v) =
          parabolicMorreyUnitAffineProjection u (0, v) := by
      simp only [parabolicMorreyUnitAffineProjection]
    change ∫ t in I,
        |parabolicMorreyUnitSpatialAffineProjection u (t, v) -
          parabolicMorreyUnitAffineProjection u (t, v)| ^ p <=
      ∫ t in I, |S (t, v)| ^ p
    simp_rw [haffine, hmean]
    simpa only [I, S, p, Function.comp_def, id_eq] using hscalar
  change ∫ z, |R z| ^ p ∂volume.restrict B ≤ ∫ z, |S z| ^ p ∂volume.restrict B
  rw [show volume.restrict B = μ.prod ν from parabolicMorreyUnitBox_restrict_volume_eq_prod d,
    integral_prod_symm _ hRprod, integral_prod_symm _ hSprod]
  exact integral_mono_ae hRprod.integral_prod_right hSprod.integral_prod_right
    (.of_forall hpoint)

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

section
variable (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u)
include hu

private theorem parabolicELpNormOn_temporalResidual_le_spatialProjection :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) := by
  let p : Real := (d : Real) + 1
  let R : TimeVelocity d -> Real := fun z => parabolicMorreyUnitSpatialAffineProjection u z -
    parabolicMorreyUnitAffineProjection u z
  let S : TimeVelocity d -> Real := parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  have hp : 0 < p := by dsimp [p]; positivity
  have hR : MemLp R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_parabolicMorreyUnitSpatialAffineProjection hu.continuous).sub
          (continuous_parabolicMorreyUnitAffineProjection u))
  have hS : MemLp S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        (continuous_parabolicMorreyUnitSpatialAffineProjection
          (_root_.HypoellipticAleksandrov.Parabolic.timeDerivative_cutoff_continuous hu))
  have hpower := temporalResidual_setIntegral_rpow_le_spatialProjection d u hu
  have hpow :
      (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p <=
        (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p := by
    rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hR,
      PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hS]
    simpa [R, S, p] using hpower
  have hroot := (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hp).mp hpow

  have hENN : eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) <=
      eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) :=
    (ENNReal.toReal_le_toReal hR.eLpNorm_ne_top hS.eLpNorm_ne_top).mp hroot
  simpa [parabolicELpNormOn, R, S, p, parabolicExponent_eq_ofReal] using hENN

/-- Temporal Poincare control of the time-dependent moment-affine projection
by the time derivative on the literal unit box. -/
theorem parabolicMorreyUnitTemporalAffinePoincareELpNorm_le :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) * parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) :=
  (parabolicELpNormOn_temporalResidual_le_spatialProjection d u hu).trans
    (parabolicELpNormOn_spatialAffineProjection_timeDerivative_le d u hu)

end

end HypoellipticAleksandrov.Parabolic
