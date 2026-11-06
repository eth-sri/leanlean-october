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
public import HypoellipticAleksandrov.Parabolic.MovingLensSourceLowerBound

/-!
# Temporal derivatives of time-slice velocity projections

This module proves the temporal moment-affine Poincare estimate and its finite
real corollary from private smooth-calculus, scalar Poincare, and Fubini layers.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators Topology

variable {d : Nat} {u : TimeVelocity d -> Real}

private theorem timeSlice_hasDerivAt
    
    (hu : ContDiff Real 2 u) (z : TimeVelocity d) :
    HasDerivAt (fun s : Real => u (s, z.2)) (timeDerivative u z) z.1 := by
  have huDiff : Differentiable Real u := hu.differentiable (by norm_num)
  have hline : HasDerivAt (fun s : Real => (s, z.2))
      ((1, 0)) z.1 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := Real) z.1).prodMk
        (hasDerivAt_const (x := z.1) (c := z.2)))
  simpa only [timeDerivative, Function.comp_def] using
    (huDiff z).hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem hasDerivAt_integral_velocity_weighted
    
    (hu : ContDiff Real 2 u) (w : PDE.Vec d -> Real)
    (hw : Continuous w) (t : Real) :
    HasDerivAt
      (fun s : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, u (s, v) * w v)
      (∫ v in velocityCube (0 : PDE.Vec d) 1,
        timeDerivative u (t, v) * w v)
      t := by
  let V : Set (PDE.Vec d) := velocityCube (0) 1
  let W : Set (PDE.Vec d) := velocityClosedCube (0) 1
  let K : Set (TimeVelocity d) := Set.Icc (t - 1) (t + 1) ×ˢ W
  let F : Real -> PDE.Vec d -> Real := fun s v => u (s, v) * w v
  let F' : Real -> PDE.Vec d -> Real := fun s v => timeDerivative u (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : ∀ s : Real, Continuous (F s) := by
    fun_prop
  have htimeDerivative : Continuous (timeDerivative u) :=
    continuous_timeDerivative hu
  have hF'cont : Continuous (fun z : TimeVelocity d =>
      timeDerivative u z * w z.2) :=
    htimeDerivative.mul (hw.comp continuous_snd)
  have hF'contSlice : ∀ s : Real, Continuous (F' s) := by
    fun_prop
  have hKcompact : IsCompact K :=
    isCompact_Icc.prod (isCompact_velocityClosedCube _ 1)
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hF'cont.continuousOn
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (volume.restrict V) :=
    Filter.Eventually.of_forall fun s => (hFcont s).aestronglyMeasurable
  have hF_int : Integrable (F t) (volume.restrict V) := by
    have hF_int_closed : IntegrableOn (F t) W volume :=
      (hFcont t).continuousOn.integrableOn_compact
        (isCompact_velocityClosedCube _ 1)
    simpa only [IntegrableOn] using hF_int_closed.mono_set hVW
  have hF'_meas : AEStronglyMeasurable (F' t) (volume.restrict V) :=
    (hF'contSlice t).aestronglyMeasurable
  have h_bound : ∀ᵐ v ∂volume.restrict V,
      ∀ s ∈ Metric.ball t 1, ‖F' s v‖ ≤ (fun _ : PDE.Vec d => C) v := by
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0) 1)]
      with v hv
    intro s hs
    apply hC _
    constructor
    · rw [Metric.mem_ball, Real.dist_eq] at hs
      grind
    grind
  have hbound_int  := by
    have hbound_int_closed : IntegrableOn (fun _ : PDE.Vec d => C) W volume :=
      continuousOn_const.integrableOn_compact
        (isCompact_velocityClosedCube _ 1)
    simpa only [IntegrableOn] using hbound_int_closed.mono_set hVW
  have hdiff : ∀ᵐ v ∂volume.restrict V,
      ∀ s ∈ Metric.ball t 1, HasDerivAt (F · v) (F' s v) s :=
    Filter.Eventually.of_forall fun v s _ => by
      simpa only [F, F'] using (timeSlice_hasDerivAt hu (s, v)).mul_const _
  simpa only [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict V)
      (x₀ := t) (s := Metric.ball t 1)
      (F := F)
      (F' := F')
      (bound := fun _ : PDE.Vec d => C)
      (Metric.ball_mem_nhds t zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int hdiff).2

private theorem hasDerivAt_parabolicMorreyUnitVelocityAverage
    
    (hu : ContDiff Real 2 u) (t : Real) :
    HasDerivAt (parabolicMorreyUnitVelocityAverage u)
      (parabolicMorreyUnitVelocityAverage (timeDerivative u) t) t := by
  change HasDerivAt
    (fun s => ((volume _).toReal)⁻¹ *
      ∫ v in velocityCube 0 1, u _) _ t
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
    (hasDerivAt_integral_velocity_weighted hu (fun _ : PDE.Vec d => 1)
      continuous_const t).const_mul
      _

private theorem hasDerivAt_parabolicMorreyUnitVelocityCoeffAt
    
    (hu : ContDiff Real 2 u) (i : Fin d) (t : Real) :
    HasDerivAt (fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i)
      (parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i) t := by
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
    (hasDerivAt_integral_velocity_weighted hu _
      (continuous_apply i) t).const_mul
      _

private theorem hasDerivAt_parabolicMorreyUnitSpatialAffineProjection
    
    (hu : ContDiff Real 2 u) (v : PDE.Vec d) (t : Real) :
    HasDerivAt
      (fun s : Real => parabolicMorreyUnitSpatialAffineProjection u (s, v))
      (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
      t := by
  have haverage : HasDerivAt
      (fun s : Real => parabolicMorreyUnitVelocityAverage u s)
      _ t :=
    hasDerivAt_parabolicMorreyUnitVelocityAverage hu t
  have hsum : HasDerivAt
      (∑ i : Fin d, fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i * v i)
      (∑ i : Fin d,
        parabolicMorreyUnitVelocityCoeffAt _ t i * v i) t :=
    HasDerivAt.sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).mul_const _
  have hfun :
      (fun s : Real => parabolicMorreyUnitVelocityAverage u s +
        ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u s i * v i) =
        (fun s : Real => parabolicMorreyUnitVelocityAverage u s) +
          ∑ i : Fin d, fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i * v i := by
    aesop
  change HasDerivAt
    (fun s : Real => parabolicMorreyUnitVelocityAverage u s +
      ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u s i * v i)
    (parabolicMorreyUnitVelocityAverage _ t +
      ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt _ t i * v i) t
  rw [hfun]
  exact haverage.add hsum

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem unitTime_meanPoincare_rpow
    {p : ℝ} {f f' : ℝ → ℝ}
    (hp : 1 ≤ p) (hf' : Continuous f')
    (hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t) :
    ∫ t in Set.Ioo (0 : ℝ) 1,
        |f t - ∫ s in Set.Ioo (0 : ℝ) 1, f s| ^ p ≤
      ∫ t in Set.Ioo (0 : ℝ) 1, |f' t| ^ p := by
  classical
  let J : Set ℝ := Set.Icc 0 1
  let A  := ∫ s in J, f s
  let B  := ∫ s in J, |f' s|
  have hp0 : 0 ≤ p := by linarith
  have hf : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hJmeas : MeasurableSet J := by
    aesop
  have hvol : volume.real J = 1 := by
    aesop
  have hvol_top : volume J ≠ ⊤ := by
    aesop
  have hvol_ne : volume J ≠ 0 := by
    aesop
  have hf_int : IntegrableOn f J volume := by
    simpa using hf.integrableOn_Icc
  have hfp_abs_int : IntegrableOn (fun s : ℝ => |f' s|) J volume := by
    simpa using hf'.abs.integrableOn_Icc
  have hfp_pow_cont : Continuous (fun s : ℝ => |f' s| ^ p) :=
    (Real.continuous_rpow_const hp0).comp hf'.abs
  have hfp_pow_int : IntegrableOn (fun s : ℝ => |f' s| ^ p) J volume := by
    simpa using hfp_pow_cont.integrableOn_Icc
  have hosc : ∀ ⦃t s : ℝ⦄, t ∈ J → s ∈ J → |f t - f s| ≤ B := by
    intro t s ht hs
    have hft  :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _hx => hderiv x) (hf'.intervalIntegrable s t)
    rw [← hft]
    calc
      |∫ x in s..t, f' x| = ‖∫ x in s..t, f' x‖ := by
        simp
      _ ≤ ∫ x in Set.uIoc s t, ‖f' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ x in J, |f' x| := by
        apply MeasureTheory.setIntegral_mono_set hfp_abs_int
          (Filter.Eventually.of_forall fun x => abs_nonneg _)
        exact (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc hs ht)).eventuallyLE
      _ = B := rfl
  have hmean : ∀ t : ℝ, f t - A = ∫ s in J, (f t - f s) := by
    intro t
    have hconst : IntegrableOn (fun _ : ℝ => f t) J volume :=
      integrableOn_const hvol_top
    calc
      f t - A = (∫ s in J, f t) - ∫ s in J, f s := by
        aesop
      _ = ∫ s in J, (f t - f s) :=
        (MeasureTheory.integral_sub hconst hf_int).symm
  have hpoint : ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ≤ B := by
    intro t ht
    rw [hmean]
    calc
      |∫ s in J, (f t - f s)| = ‖∫ s in J, (f t - f s)‖ := by
        simp
      _ ≤ ∫ s in J, ‖f t - f s‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ s in J, B := by
        refine MeasureTheory.setIntegral_mono_on
          (by simpa using
            (continuous_const.sub hf).abs.integrableOn_Icc)
          (integrableOn_const hvol_top)
          hJmeas fun s hs => ?_
        simp_all
      _ = B := by
        simp_all
  have hpoint_pow : ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ^ p ≤ B ^ p := by
    intro t ht
    exact Real.rpow_le_rpow (abs_nonneg _) (hpoint ht) hp0
  have hjensen : B ^ p ≤ ∫ s in J, |f' s| ^ p := by
    have h := (convexOn_rpow hp).map_set_average_le
      (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hvol_ne hvol_top
      (by
        simp) hfp_abs_int
      (by aesop)
    simpa only [MeasureTheory.setAverage_eq, hvol, inv_one, one_smul, B] using h
  have hleft_cont : Continuous (fun t : ℝ => |f t - A| ^ p) :=
    (Real.continuous_rpow_const hp0).comp ((hf.sub continuous_const).abs)
  have hleft_int : IntegrableOn (fun t : ℝ => |f t - A| ^ p) J volume := by
    simpa using hleft_cont.integrableOn_Icc
  have hclosed :
      ∫ t in J, |f t - A| ^ p ≤ ∫ t in J, |f' t| ^ p := by
    calc
      ∫ t in J, |f t - A| ^ p ≤ ∫ t in J, B ^ p := by
        refine MeasureTheory.setIntegral_mono_on hleft_int (integrableOn_const hvol_top)
          hJmeas fun t ht => hpoint_pow ht
      _ = B ^ p := by
        simp_all
      _ ≤ ∫ t in J, |f' t| ^ p := hjensen
  have hmean_endpoints :
      ∫ s in J, f s = ∫ s in Set.Ioo (0) 1, f s := by
    simpa using
      (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume) (f := f) (x := (0)) (y := 1))
  calc
    ∫ t in Set.Ioo _ 1,
        |f t - ∫ s in Set.Ioo _ 1, f s| ^ p =
        ∫ t in J, |f t - A| ^ p := by
      rw [← hmean_endpoints]
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume)
          (f := fun t : ℝ => |f t - ∫ s in J, f s| ^ p) (x := (0)) (y := 1)).symm
    _ ≤ ∫ t in J, |f' t| ^ p := hclosed
    _ = ∫ t in Set.Ioo _ 1, |f' t| ^ p := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume)
          (f := fun t : ℝ => |f' t| ^ p) (x := (0)) (y := 1))

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable {d : Nat} {f : TimeVelocity d -> Real} {u : TimeVelocity d -> Real}

private theorem continuous_parabolicMorreyUnitVelocityAverage
    
    (hu : ContDiff Real 2 u) :
    Continuous (parabolicMorreyUnitVelocityAverage u) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityAverage hu t).continuousAt

private theorem continuous_parabolicMorreyUnitVelocityCoeffAt
    
    (hu : ContDiff Real 2 u) (i : Fin d) :
    Continuous (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).continuousAt

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection
    
    (hu : ContDiff Real 2 u) :
    Continuous (parabolicMorreyUnitSpatialAffineProjection u) := by
  apply Continuous.add
  · exact (continuous_parabolicMorreyUnitVelocityAverage hu).comp continuous_fst
  · apply continuous_finset_sum
    intro i _
    exact ((continuous_parabolicMorreyUnitVelocityCoeffAt hu i).comp continuous_fst).mul
      (continuous_apply i |>.comp continuous_snd)

private theorem continuous_parabolicMorreyUnitAffineProjection
     (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  fun_prop

private theorem continuous_integrable_parabolicMorreyUnitBox
     (hf : Continuous f) :
    Integrable f (volume.restrict (parabolicMorreyUnitBox d)) := by
  let K  :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact : IsCompact K :=
    isCompact_parabolicClosedBox 1 1 0 _
  have hsubset : parabolicMorreyUnitBox d ⊆ K := by
    rintro ⟨t, v⟩ hz
    rcases hz with ⟨⟨htLeft, htRight⟩, hv⟩
    exact ⟨⟨htLeft.le, htRight.le⟩, fun i => (hv i).le⟩
  exact (hf.continuousOn.integrableOn_compact hKcompact).mono_set hsubset


private theorem parabolicMorreyUnitBox_volume_toReal_eq_velocityCube (d : Nat) :
    (volume (parabolicMorreyUnitBox d)).toReal =
      (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
  rw [volume_parabolicMorreyUnitBox_toReal,
    volume_velocityCube_toReal (v₀ := (0)) (by norm_num)]
  simp

private theorem integrableOn_parabolicMorreyUnitBox_as_prod
    
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d))) :
    IntegrableOn f
      (Set.Ioo (0 : Real) 1 ×ˢ velocityCube (0 : PDE.Vec d) 1)
      ((volume : Measure Real).prod (volume : Measure (PDE.Vec d))) := by
  change Integrable f ((volume.prod _).restrict
    _)
  rw [← Measure.prod_restrict, ← parabolicMorreyUnitBox_restrict_volume_eq_prod]
  exact hf

private theorem parabolicMorreyUnitAverage_eq_integral_velocityAverage
    
    (hu : Continuous u) :
    parabolicMorreyUnitAverage u =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityAverage u t := by
  let I : Set Real := Set.Ioo 0 1
  let V  := velocityCube (0 : PDE.Vec d) 1
  have huInt  :=
    continuous_integrable_parabolicMorreyUnitBox hu
  have huProd : IntegrableOn u (I ×ˢ V)
      (volume.prod volume) := by
    simpa using integrableOn_parabolicMorreyUnitBox_as_prod huInt
  have hFubini : ∫ z in parabolicMorreyUnitBox d, u z =
      ∫ t in I, ∫ v in V, u (t, v) := by
    rw [parabolicMorreyUnitBox_restrict_volume_eq_prod]
    have huProd' : Integrable u
        ((volume.restrict I).prod (volume.restrict V)) := by
      rw [Measure.prod_restrict]
      aesop
    simpa using MeasureTheory.integral_prod u huProd'
  unfold parabolicMorreyUnitAverage parabolicMorreyUnitVelocityAverage
  rw [hFubini, parabolicMorreyUnitBox_volume_toReal_eq_velocityCube, ← MeasureTheory.integral_const_mul]

private theorem parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt
    
    (hu : ContDiff Real 2 u) (i : Fin d) :
    parabolicMorreyUnitVelocityCoeff u i =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityCoeffAt u t i := by
  unfold parabolicMorreyUnitVelocityCoeff parabolicMorreyUnitVelocityCoeffAt
  have hcont : Continuous (fun z : TimeVelocity d => u z * z.2 i) :=
    hu.continuous.mul (continuous_apply i |>.comp continuous_snd)
  have haverage := parabolicMorreyUnitAverage_eq_integral_velocityAverage hcont
  rw [haverage, ← MeasureTheory.integral_const_mul]
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
  have hAvgCont  :=
    continuous_parabolicMorreyUnitVelocityAverage hu
  have hAvgInt : IntegrableOn (parabolicMorreyUnitVelocityAverage u) I volume := (hAvgCont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hCoeffCont  :=
    fun i => continuous_parabolicMorreyUnitVelocityCoeffAt hu i
  have hCoeffInt : ∀ i : Fin d, IntegrableOn
      (fun t => parabolicMorreyUnitVelocityCoeffAt u t i * v i) I volume := by
    intro i
    exact ((hCoeffCont i).mul continuous_const).integrableOn_Icc.mono_set
      Set.Ioo_subset_Icc_self
  have hSumInt : IntegrableOn (fun t => ∑ i : Fin d,
      parabolicMorreyUnitVelocityCoeffAt u t i * v i) I volume := integrable_finset_sum Finset.univ fun i _ => hCoeffInt i
  unfold parabolicMorreyUnitAffineProjection parabolicMorreyUnitSpatialAffineProjection
  rw [parabolicMorreyUnitAverage_eq_integral_velocityAverage hu.continuous]
  simp_rw [parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt hu]
  rw [MeasureTheory.integral_add hAvgInt hSumInt,
    MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hCoeffInt i)]
  simp_rw [MeasureTheory.integral_mul_const]
  ring

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable {d : Nat} {g : TimeVelocity d -> Real}

private theorem continuous_integral_velocity_weighted_of_continuous
     (hg : Continuous g)
    (w : PDE.Vec d -> Real) (hw : Continuous w) :
    Continuous (fun t : Real =>
      ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * w v) := by
  rw [continuous_iff_continuousAt]
  intro t
  let J : Set Real := Set.Icc (t - 1) (t + 1)
  let V : Set (PDE.Vec d) := velocityCube (0) 1
  let W : Set (PDE.Vec d) := velocityClosedCube (0) 1
  let F : Real -> PDE.Vec d -> Real := fun s v => g (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : Continuous (Function.uncurry F) := by
    fun_prop
  have hKcompact : IsCompact (J ×ˢ W) :=
    isCompact_Icc.prod (isCompact_velocityClosedCube _ 1)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFcont.continuousOn
  have hFmeas : ∀ s ∈ J, AEStronglyMeasurable (F s) (volume.restrict V) := by
    fun_prop
  have hbound : ∀ s ∈ J, ∀ᵐ v ∂volume.restrict V, ‖F s v‖ ≤ C := by
    intro s hs
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0) 1)]
      with v hv
    exact hC (s, v) ⟨hs, hVW hv⟩
  have hCint : Integrable (fun _ : PDE.Vec d => C) (volume.restrict V) := by
    have hclosed : IntegrableOn (fun _ : PDE.Vec d => C) W volume :=
      continuousOn_const.integrableOn_compact
        (isCompact_velocityClosedCube _ 1)
    simpa only [IntegrableOn] using hclosed.mono_set hVW
  have hcont : ∀ᵐ v ∂volume.restrict V, ContinuousOn (fun s => F s v) J := by
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
      with v _
    fun_prop
  have hJ : J ∈ nhds t := by
    aesop
  exact (continuousOn_of_dominated hFmeas hbound hCint hcont).continuousAt hJ

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
     (hg : Continuous g) :
    Continuous (parabolicMorreyUnitSpatialAffineProjection g) := by
  apply Continuous.add
  · have hInt : Continuous (fun t : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * 1) :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun _ : PDE.Vec d => 1)
        (continuous_const : Continuous (fun _ : PDE.Vec d => (1 : Real)))
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
      (continuous_const.mul hInt).comp
        continuous_fst
  · apply continuous_finset_sum
    intro i _
    have hInt : Continuous (fun t : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * v i) :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun v : PDE.Vec d => v i) (continuous_apply i)
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
      ((continuous_const.mul hInt).comp
          continuous_fst).mul (continuous_apply i |>.comp continuous_snd)

private theorem parabolicELpNormOn_spatialAffineProjection_timeDerivative_le
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
  let I : Set Real := Set.Ioo 0 1
  let V  := velocityCube (0 : PDE.Vec d) 1
  let p  := parabolicExponent d
  let q  := fun t =>
    PDE.eLpNormOn V p (fun v =>
      parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
  let r  := fun t =>
    PDE.eLpNormOn V p (fun v => timeDerivative u (t, v))
  have htime  := continuous_timeDerivative hu
  have hTae : AEMeasurable _
      (volume.restrict (parabolicMorreyUnitBox d)) := htime.aemeasurable
  have hslicebound (t : Real) : q t ≤ ENNReal.ofReal (1 + 3 * d) * r t := by
    simpa only [q, r, p, V,
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le
        (fun v => timeDerivative u (t, v))
        (htime.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hScont  :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous htime
  have hsliceNorm : eLpNorm q p (volume.restrict I) ≤
      ENNReal.ofReal (1 + 3 * d) * eLpNorm r p (volume.restrict I) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (by simpa using
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm _
          hScont.aemeasurable).aestronglyMeasurable) ?_
    simp_all

  calc
    parabolicELpNormOn d _
        _ = eLpNorm q p _ := by
      simpa using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          _ hScont.aemeasurable
    _ ≤ ENNReal.ofReal _ * eLpNorm r p _ := hsliceNorm
    _ = ENNReal.ofReal _ *
        parabolicELpNormOn d _ _ := by
      rw [parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
        _ hTae]

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
  let B  := parabolicMorreyUnitBox d
  let p  := (d : Real) + 1
  let R  := fun z =>
    parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z
  let S  :=
    parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  let μ : Measure Real := volume.restrict I
  let ν : Measure (PDE.Vec d) := volume.restrict V

  have hp : 0 < p := by
    positivity
  have hp1 : 1 <= p := by
    grind
  have hRcont : Continuous R :=
    (continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
      (continuous_parabolicMorreyUnitAffineProjection u)
  have hScont : Continuous S :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
      (continuous_timeDerivative hu)
  have hRpow : Integrable (fun z => |R z| ^ p) (volume.restrict B) := by
    have hRmem  := by
      simpa using Continuous.memLp_parabolicMorreyUnitBox hRcont
    simpa [parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
      Real.norm_eq_abs] using hRmem.integrable_norm_rpow
        (by simp [parabolicExponent]) (by simp [parabolicExponent])
  have hSpow : Integrable (fun z => |S z| ^ p) (volume.restrict B) := by
    have hSmem  := by
      simpa using Continuous.memLp_parabolicMorreyUnitBox hScont
    simpa [parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
      Real.norm_eq_abs] using hSmem.integrable_norm_rpow
        (by simp [parabolicExponent]) (by simp [parabolicExponent])
  have hRprod : Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |R (t, v)| ^ p) (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact integrableOn_parabolicMorreyUnitBox_as_prod hRpow
  have hSprod : Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |S (t, v)| ^ p) (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact integrableOn_parabolicMorreyUnitBox_as_prod hSpow
  have hpoint (v : PDE.Vec d) :
      ∫ t, |R (t, v)| ^ p ∂μ <= ∫ t, |S (t, v)| ^ p ∂μ := by
    have hmean := parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
      hu v
    have hscalar := unitTime_meanPoincare_rpow (p := p) hp1
      ((continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
        (continuous_timeDerivative hu)).comp (continuous_id.prodMk continuous_const))
      (hasDerivAt_parabolicMorreyUnitSpatialAffineProjection hu v)
    have haffine (t : Real) :
        parabolicMorreyUnitAffineProjection u (t, v) =
          parabolicMorreyUnitAffineProjection u (0, v) := by
      aesop
    grind
  have hiter :
      ∫ t, ∫ v, |R (t, v)| ^ p ∂ν ∂μ <=
        ∫ t, ∫ v, |S (t, v)| ^ p ∂ν ∂μ := by
    rw [MeasureTheory.integral_integral_swap hRprod,
      MeasureTheory.integral_integral_swap hSprod]
    exact MeasureTheory.integral_mono_ae hRprod.integral_prod_right
      hSprod.integral_prod_right (Filter.Eventually.of_forall hpoint)
  calc
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) =
        ∫ t, ∫ v, |R _| ^ p ∂ν ∂μ := by
      rw [show volume.restrict B = μ.prod ν by
        simpa using parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact MeasureTheory.integral_prod _ hRprod
    _ <= ∫ t, ∫ v, |S _| ^ p ∂ν ∂μ := hiter
    _ = ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection _ z| ^
          ((d : Real) + 1) := by
      rw [show volume.restrict B = μ.prod ν by
        simpa using parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact (MeasureTheory.integral_prod _ hSprod).symm

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : TimeVelocity d -> Real)

private theorem parabolicELpNormOn_temporalResidual_le_spatialProjection
     (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) := by
  let p  := (d : Real) + 1
  let R  := fun z => parabolicMorreyUnitSpatialAffineProjection u z -
    parabolicMorreyUnitAffineProjection u z
  let S  := parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  have hp : 0 < p := by positivity
  have hR : MemLp R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
          (continuous_parabolicMorreyUnitAffineProjection u))
  have hS : MemLp S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        (continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
          (continuous_timeDerivative hu))
  have hpower := temporalResidual_setIntegral_rpow_le_spatialProjection d u hu
  have hpow :
      (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p <=
        (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p := by
    rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hR,
      PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hS]
    omega
  have hroot  := by
    calc
      (eLpNorm R _ _).toReal =
          ((eLpNorm R _
            _).toReal ^ p) ^ p⁻¹ :=
        (Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne').symm
      _ <= ((eLpNorm S _
        _).toReal ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = (eLpNorm S _ _).toReal :=
        Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne'
  have hENN  :=
    (ENNReal.toReal_le_toReal hR.eLpNorm_ne_top hS.eLpNorm_ne_top).mp hroot
  simpa [parabolicELpNormOn, R, S, p, parabolicExponent_eq_ofReal] using hENN

/-- Temporal Poincare control of the time-dependent moment-affine projection
by the time derivative on the literal unit box. -/
theorem parabolicMorreyUnitTemporalAffinePoincareELpNorm_le
     (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) * parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) :=
  (parabolicELpNormOn_temporalResidual_le_spatialProjection d u hu).trans
    (parabolicELpNormOn_spatialAffineProjection_timeDerivative_le d u hu)

/-- Real-valued corollary of the temporal moment-affine Poincare estimate. -/
theorem parabolicMorreyUnitTemporalAffinePoincareLpNorm_le
     (hu : ContDiff Real 2 u) :
    parabolicLpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      (1 + 3 * (d : Real)) * parabolicLpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) := by
  have hT  :=
    Continuous.memLp_parabolicMorreyUnitBox (continuous_timeDerivative hu)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.eLpNorm_ne_top)
    (parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu)
  rw [ENNReal.toReal_ofReal_mul _ _ (by positivity)] at h
  exact h

end HypoellipticAleksandrov.Parabolic
