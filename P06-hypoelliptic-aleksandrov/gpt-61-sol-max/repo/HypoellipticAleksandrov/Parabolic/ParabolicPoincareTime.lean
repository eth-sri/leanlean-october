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
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.ContactMap
import all HypoellipticAleksandrov.Parabolic.ABP

open private HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal from HypoellipticAleksandrov.Parabolic.ABP


/-!
# Temporal derivatives of time-slice velocity projections

This module proves the temporal moment-affine Poincare estimate and its finite
real corollary from private smooth-calculus, scalar Poincare, and Fubini layers.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators Topology

variable {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiff Real 2 u)

include hu
private theorem timeSlice_hasDerivAt
     (z : TimeVelocity d) :
    HasDerivAt (fun s  => u (s, z.2)) (timeDerivative u z) z.1 := by


  simpa only [timeDerivative, Function.comp_def] using
    ((hu.differentiable (by norm_num)) z).hasFDerivAt.comp_hasDerivAt z.1 (by
        simpa using
          ((hasDerivAt_id'  z.1).prodMk
            (hasDerivAt_const (x := z.1) (c := z.2))))



private theorem hasDerivAt_integral_velocity_weighted
     (w : PDE.ScalarField d)
    (hw : Continuous w) (t : Real) :
    HasDerivAt
      (fun s  =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, u (s, v) * w v)
      (∫ v in velocityCube (0 : PDE.Vec d) 1,
        timeDerivative u (t, v) * w v)
      t := by
  let sharedTerm_357d5aad98 := ((isCompact_velocityClosedCube (0 : PDE.Vec d) 1))
  let V  := velocityCube (0 : PDE.Vec d) 1
  let W  := velocityClosedCube (0 : PDE.Vec d) 1

  let F  := fun s v => u (s, v) * w v
  let F'  := fun s v => timeDerivative u (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : ∀ s : Real, Continuous (F s) := by
    intro s
    exact (hu.continuous.comp (continuous_const.prodMk continuous_id)).mul hw

  have hF'cont : Continuous (fun z  =>
      timeDerivative u z * w z.2) :=
    (continuous_timeDerivative hu).mul (hw.comp continuous_snd)
  have hF'contSlice : ∀ s : Real, Continuous (F' s) := by
    intro s
    exact hF'cont.comp (continuous_const.prodMk continuous_id)

  obtain ⟨C, hC⟩ :=
    (show IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ W) from isCompact_Icc.prod sharedTerm_357d5aad98).exists_bound_of_continuousOn hF'cont.continuousOn






  simpa only [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le





      (Metric.ball_mem_nhds t zero_lt_one) (Filter.Eventually.of_forall fun s => (hFcont s).aestronglyMeasurable) (by
          have hF_int_closed : IntegrableOn (F t) W  :=
            (hFcont t).continuousOn.integrableOn_compact
              sharedTerm_357d5aad98
          exact hF_int_closed.mono_set hVW) ((hF'contSlice t).aestronglyMeasurable) (by
          filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
            with v hv
          intro s hs
          apply hC (s, v)
          constructor
          · rw [Metric.mem_ball, Real.dist_eq] at hs
            rcases abs_lt.mp hs with ⟨hleft, hright⟩
            constructor <;> linarith
          · exact hVW hv) (by
          have hbound_int_closed : IntegrableOn (fun _ : PDE.Vec d => C) W  :=
            continuousOn_const.integrableOn_compact
              sharedTerm_357d5aad98
          exact hbound_int_closed.mono_set hVW) (Filter.Eventually.of_forall fun v s _ => (id (HasDerivAt.mul_const (timeSlice_hasDerivAt hu (s, v)) (w v))))).2

private theorem hasDerivAt_parabolicMorreyUnitVelocityAverage
     (t : Real) :
    HasDerivAt (parabolicMorreyUnitVelocityAverage u)
      (parabolicMorreyUnitVelocityAverage (timeDerivative u) t) t := by
  let sharedTerm_ae33808216 := (((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)
  change HasDerivAt
    (fun s => sharedTerm_ae33808216 *
      ∫ v in velocityCube 0 1, u (s, v)) _ t
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
    (hasDerivAt_integral_velocity_weighted hu (fun _  => 1)
      continuous_const t).const_mul
      sharedTerm_ae33808216

private theorem hasDerivAt_parabolicMorreyUnitVelocityCoeffAt
     (i : Fin d) (t : Real) :
    HasDerivAt (fun s  => parabolicMorreyUnitVelocityCoeffAt u s i)
      (parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i) t := (id
  (HasDerivAt.const_mul (3 * (volume (velocityCube 0 1)).toReal⁻¹)
    (hasDerivAt_integral_velocity_weighted hu (fun v => v i) (continuous_apply i) t)))

private theorem hasDerivAt_parabolicMorreyUnitSpatialAffineProjection
     (v : PDE.Vec d) (t : Real) :
    HasDerivAt
      (fun s  => parabolicMorreyUnitSpatialAffineProjection u (s, v))
      (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
      t := (id
  (Eq.mpr
    (id
      (congrArg
        (fun _a =>
          HasDerivAt _a
            (parabolicMorreyUnitVelocityAverage (timeDerivative u) t +
              ∑ i, parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i * v i)
            t)
        (funext fun s =>
          of_eq_true
            (Eq.trans
              (congrArg
                (Eq (parabolicMorreyUnitVelocityAverage u s + ∑ i, parabolicMorreyUnitVelocityCoeffAt u s i * v i))
                (congrArg (HAdd.hAdd (parabolicMorreyUnitVelocityAverage u s))
                  (Finset.sum_apply s Finset.univ fun c s => parabolicMorreyUnitVelocityCoeffAt u s c * v c)))
              (eq_self
                (parabolicMorreyUnitVelocityAverage u s + ∑ i, parabolicMorreyUnitVelocityCoeffAt u s i * v i))))))
    (HasDerivAt.add (hasDerivAt_parabolicMorreyUnitVelocityAverage hu t)
      (HasDerivAt.sum fun i x => HasDerivAt.mul_const (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t) (v i)))))

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
  let sharedTerm_8d448764b4 := (∫ s in Set.Ioo (0 : ℝ) 1, f s)
  classical
  let J : Set ℝ := Set.Icc 0 1
  let A : ℝ := ∫ s in J, f s
  let B : ℝ := ∫ s in J, |f' s|
  have hp0 : 0 ≤ p := by linarith
  have hf : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hJmeas : MeasurableSet J := by
    exact measurableSet_Icc
  have hvol : volume.real J = 1 := by
    change volume.real (Set.Icc 0 1) = 1
    rw [Real.volume_real_Icc_of_le]
    norm_num
    norm_num
  have hvol_top : volume J ≠ ⊤ := by
    simpa only [J] using (measure_Icc_lt_top : volume (Set.Icc (0 : ℝ) 1) < ⊤).ne
  have hvol_ne : volume J ≠ 0 := by
    simp only [J, Real.volume_Icc]
    norm_num
  have hf_int : IntegrableOn f J  := by
    simpa only [J] using hf.integrableOn_Icc
  have hfp_abs_int : IntegrableOn (fun s  => |f' s|) J  := by
    simpa only [J] using hf'.abs.integrableOn_Icc

  have hfp_pow_int : IntegrableOn (fun s  => |f' s| ^ p) J  := by
    exact ((Real.continuous_rpow_const hp0).comp hf'.abs).integrableOn_Icc

  have hmean : ∀ t : ℝ, f t - A = ∫ s in J, (f t - f s) := by
    intro t
    have hconst : IntegrableOn (fun _ : ℝ => f t) J  :=
      integrableOn_const hvol_top
    calc
      f t - A = (∫ s in J, f t) - ∫ s in J, f s := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
        simp only [one_mul, A]
      _ = ∫ s in J, (f t - f s) :=
        (MeasureTheory.integral_sub hconst hf_int).symm
  have hpoint : ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ≤ B := by
    intro t ht
    rw [hmean]
    calc
      |∫ s in J, (f t - f s)| = ‖∫ s in J, (f t - f s)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in J, ‖f t - f s‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ s in J, B := (setIntegral_mono_on (id (Continuous.integrableOn_Icc (Continuous.abs (Continuous.sub continuous_const hf))))
  (integrableOn_const hvol_top enorm_ne_top) hJmeas fun s hs => (show ∀ ⦃t s : ℝ⦄, t ∈ J → s ∈ J → |f t - f s| ≤ B by
      intro t s ht hs
      have hft : ∫ x in s..t, f' x = f t - f s :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _hx => hderiv x) (hf'.intervalIntegrable s t)
      rw [← hft]
      calc
        |∫ x in s..t, f' x| = ‖∫ x in s..t, f' x‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x in Set.uIoc s t, ‖f' x‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ x in J, |f' x| := by
          apply MeasureTheory.setIntegral_mono_set hfp_abs_int
            (Filter.Eventually.of_forall fun x => abs_nonneg (f' x))
          exact (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc hs ht)).eventuallyLE
        _ = B := rfl) ht hs)
      _ = B := by
        simp_all


  have hleft_cont : Continuous (fun t  => |f t - A| ^ p) :=
    (Real.continuous_rpow_const hp0).comp ((hf.sub continuous_const).abs)


  have hmean_endpoints :
      ∫ s in J, f s = sharedTerm_8d448764b4 := by
    exact (MeasureTheory.integral_Icc_eq_integral_Ioo    )
  calc
    ∫ t in Set.Ioo (0 : ℝ) 1,
        |f t - sharedTerm_8d448764b4| ^ p =
        ∫ t in J, |f t - A| ^ p := by
      rw [← hmean_endpoints]
      simpa only [A] using
        (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume)
          (f := fun t  => |f t - ∫ s in J, f s| ^ p) (x := (0 )) (y := 1)).symm
    _ ≤ ∫ t in J, |f' t| ^ p := (by
        calc
          ∫ t in J, |f t - A| ^ p ≤ ∫ t in J, B ^ p := by
            refine MeasureTheory.setIntegral_mono_on (by
                simpa only [J] using hleft_cont.integrableOn_Icc) (integrableOn_const hvol_top)
              hJmeas fun t ht => (show ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ^ p ≤ B ^ p by
                  intro t ht
                  exact Real.rpow_le_rpow (abs_nonneg _) (hpoint ht) hp0) ht
          _ = B ^ p := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
            simp
          _ ≤ ∫ t in J, |f' t| ^ p := (by
              have h := (convexOn_rpow hp).map_set_average_le
                (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hvol_ne hvol_top
                (by
                  filter_upwards [ae_restrict_mem hJmeas] with x hx
                  exact abs_nonneg (f' x)) hfp_abs_int
                (hfp_pow_int)
              simpa only [MeasureTheory.setAverage_eq, hvol, inv_one, one_smul, B] using h))
    _ = ∫ t in Set.Ioo (0 : ℝ) 1, |f' t| ^ p := integral_Icc_eq_integral_Ioo

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable {d : Nat}

section
variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiff Real 2 u)

include hu
private theorem continuous_parabolicMorreyUnitVelocityAverage
      :
    Continuous (parabolicMorreyUnitVelocityAverage u) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityAverage hu t).continuousAt

private theorem continuous_parabolicMorreyUnitVelocityCoeffAt
      (i : Fin d) :
    Continuous (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).continuousAt

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection
      :
    Continuous (parabolicMorreyUnitSpatialAffineProjection u) := by
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply Continuous.add
  · exact (continuous_parabolicMorreyUnitVelocityAverage hu).comp continuous_fst
  · apply continuous_finset_sum
    intro i _
    exact ((continuous_parabolicMorreyUnitVelocityCoeffAt hu i).comp continuous_fst).mul
      (continuous_apply i |>.comp continuous_snd)
end


private theorem continuous_parabolicMorreyUnitAffineProjection
     (u : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_apply i |>.comp continuous_snd)

private theorem continuous_integrable_parabolicMorreyUnitBox
     {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hf : Continuous f) :
    Integrable f (volume.restrict (parabolicMorreyUnitBox d)) := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact (isCompact_parabolicClosedBox 1 1 0 0) (Continuous.continuousOn hf)) fun ⦃a⦄ =>
  Prod.casesOn (motive := fun x => x ∈ parabolicMorreyUnitBox d → x ∈ parabolicClosedBox 1 1 0 0) a fun t v hz =>
    id
      (fun hz =>
        id
          (And.casesOn hz fun left hv =>
            And.casesOn left fun htLeft htRight => ⟨⟨LT.lt.le htLeft, LT.lt.le htRight⟩, fun i => LT.lt.le (hv i)⟩))
      hz)

variable (d : Nat)




private theorem parabolicMorreyUnitBox_volume_toReal_eq_velocityCube  :
    (volume (parabolicMorreyUnitBox d)).toReal =
      (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
  rw [volume_parabolicMorreyUnitBox_toReal,
    volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : Real) ≤ 1)]
  simp

variable {d : Nat}

private theorem integrableOn_parabolicMorreyUnitBox_as_prod
     {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d))) :
    IntegrableOn f
      (Set.Ioo (0 : Real) 1 ×ˢ velocityCube (0 : PDE.Vec d) 1)
      ((volume : Measure Real).prod (volume )) := by
  change Integrable f (((volume : Measure Real).prod (volume : Measure (PDE.Vec d))).restrict
    (Set.Ioo (0 : Real) 1 ×ˢ velocityCube (0 : PDE.Vec d) 1))
  rw [← Measure.prod_restrict, ← parabolicMorreyUnitBox_restrict_volume_eq_prod]
  exact hf

variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem parabolicMorreyUnitAverage_eq_integral_velocityAverage

    (hu : Continuous u) :
    parabolicMorreyUnitAverage u =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityAverage u t := by
  let I : Set Real := Set.Ioo 0 1
  let V  := velocityCube (0 : PDE.Vec d) 1
  have huInt  :=
    continuous_integrable_parabolicMorreyUnitBox hu

  have hFubini : ∫ z in parabolicMorreyUnitBox d, u z =
      ∫ t in I, ∫ v in V, u (t, v) := by
    change ∫ z, u z ∂volume.restrict (parabolicMorreyUnitBox d) =
      ∫ t, ∫ v, u (t, v) ∂volume.restrict V ∂volume.restrict I
    rw [parabolicMorreyUnitBox_restrict_volume_eq_prod]

    simpa only [I, V] using MeasureTheory.integral_prod u (by
        rw [Measure.prod_restrict]
        exact (integrableOn_parabolicMorreyUnitBox_as_prod huInt))
  unfold parabolicMorreyUnitAverage parabolicMorreyUnitVelocityAverage
  rw [hFubini, parabolicMorreyUnitBox_volume_toReal_eq_velocityCube]
  rw [← MeasureTheory.integral_const_mul]

private theorem parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt

    (hu : ContDiff Real 2 u) (i : Fin d) :
    parabolicMorreyUnitVelocityCoeff u i =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityCoeffAt u t i := by
  unfold parabolicMorreyUnitVelocityCoeff parabolicMorreyUnitVelocityCoeffAt
  have hcont : Continuous (fun z  => u z * z.2 i) :=
    hu.continuous.mul (continuous_apply i |>.comp continuous_snd)

  change 3 * parabolicMorreyUnitAverage (fun z => u z * z.2 i) = _
  rw [(parabolicMorreyUnitAverage_eq_integral_velocityAverage hcont)]
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



  have hCoeffInt : ∀ i : Fin d, IntegrableOn
      (fun t => parabolicMorreyUnitVelocityCoeffAt u t i * v i) I  := by
    intro i
    exact ((((continuous_parabolicMorreyUnitVelocityCoeffAt hu)) i).mul continuous_const).integrableOn_Icc.mono_set
      Set.Ioo_subset_Icc_self

  unfold parabolicMorreyUnitAffineProjection parabolicMorreyUnitSpatialAffineProjection
  rw [parabolicMorreyUnitAverage_eq_integral_velocityAverage hu.continuous]
  simp_rw [parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt hu]
  rw [MeasureTheory.integral_add (by
      exact ((continuous_parabolicMorreyUnitVelocityAverage hu).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self) (integrable_finset_sum Finset.univ fun i _ => hCoeffInt i),
    MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hCoeffInt i)]
  simp_rw [MeasureTheory.integral_mul_const]
  ring

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

section
variable {d : Nat} {g : HypoellipticAleksandrov.Parabolic.ScalarField d} (hg : Continuous g)

include hg
private theorem continuous_integral_velocity_weighted_of_continuous

    (w : PDE.ScalarField d) (hw : Continuous w) :
    Continuous (fun t  =>
      ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * w v) := by
  rw [continuous_iff_continuousAt]
  intro t
  let J  := Set.Icc (t - 1) (t + 1)
  let V  := velocityCube (0 : PDE.Vec d) 1
  let W  := velocityClosedCube (0 : PDE.Vec d) 1
  let F  := fun s v => g (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : Continuous (Function.uncurry F) := hg.mul (hw.comp continuous_snd)

  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)).exists_bound_of_continuousOn hFcont.continuousOn





  exact (continuousOn_of_dominated (by
      intro s _
      exact (hFcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) (by
      intro s hs
      filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
        with v hv
      exact hC (s, v) ⟨hs, hVW hv⟩) (by
      have hclosed : IntegrableOn (fun _ : PDE.Vec d => C) W  :=
        continuousOn_const.integrableOn_compact
          (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
      exact hclosed.mono_set hVW) (by
      filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
        with v _
      exact (hFcont.comp (continuous_id.prodMk continuous_const)).continuousOn)).continuousAt (by
      simpa only [J] using
        (Icc_mem_nhds (show t - 1 < t by linarith) (show t < t + 1 by linarith)))

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
     :
    Continuous (parabolicMorreyUnitSpatialAffineProjection g) := by
  let sharedTerm_1869930cda := (((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply Continuous.add
  · have hInt  :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun _  => 1)
        (continuous_const )
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
      ((continuous_const : Continuous (fun _ : Real =>
      sharedTerm_1869930cda)).mul hInt).comp
        (continuous_fst : Continuous (fun z : TimeVelocity d => z.1))
  · apply continuous_finset_sum
    intro i _
    have hInt  :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun v  => v i) (continuous_apply i)
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
      (((continuous_const : Continuous (fun _ : Real =>
        3 * sharedTerm_1869930cda)).mul hInt).comp
          continuous_fst).mul (continuous_apply i |>.comp continuous_snd)
end


private theorem parabolicELpNormOn_spatialAffineProjection_timeDerivative_le
    (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
  let sharedTerm_9056306cf9 := (ENNReal.ofReal (1 + 3 * (d : Real)))
  let I : Set Real := Set.Ioo 0 1
  let V  := velocityCube (0 : PDE.Vec d) 1
  let p  := parabolicExponent d
  let q  := fun t =>
    PDE.eLpNormOn V p (fun v =>
      parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
  let r  := fun t =>
    PDE.eLpNormOn V p (fun v => timeDerivative u (t, v))
  have htime  := continuous_timeDerivative hu


  have hslicebound (t : Real) : q t ≤ sharedTerm_9056306cf9 * r t := by
    simpa only [q, r, p, V,
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le
        (fun v => timeDerivative u (t, v))
        (htime.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hScont  :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous htime


  calc
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) = eLpNorm q p (volume.restrict I) := parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)) hScont.aemeasurable
    _ ≤ sharedTerm_9056306cf9 * eLpNorm r p (volume.restrict I) := (by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
          (by simpa only [q, I, V, p] using
            (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm _
              hScont.aemeasurable).aestronglyMeasurable) ?_
        filter_upwards with t
        exact hslicebound t)
    _ = sharedTerm_9056306cf9 *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
      rw [parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
        _ htime.aemeasurable]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

private theorem temporalResidual_setIntegral_rpow_le_spatialProjection
    (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) :
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) <=
      ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) z| ^
          ((d : Real) + 1) := by
  let sharedTerm_74facb25a1 := (((volume : Measure Real).prod (volume : Measure (PDE.Vec d))))
  let I : Set Real := Set.Ioo 0 1
  let V : PDE.VelocityRegion d := velocityCube 0 1
  let B  := parabolicMorreyUnitBox d
  let p : Real := (d : Real) + 1
  let R  := fun z =>
    parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z
  let S  :=
    parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  let μ : Measure Real := volume.restrict I
  let ν : Measure (PDE.Vec d) := volume.restrict V

  have hp : 0 < p := by
    dsimp only [p]
    positivity

  have hRcont : Continuous R :=
    (continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
      (continuous_parabolicMorreyUnitAffineProjection u)
  have hScont : Continuous S :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
      (continuous_timeDerivative hu)


  have hRprod : Integrable (Function.uncurry fun t  => fun v : PDE.Vec d =>
      |R (t, v)| ^ p) (μ.prod ν) := by
    change Integrable (Function.uncurry fun t  => fun v : PDE.Vec d =>
      |R (t, v)| ^ p) ((volume.restrict I).prod (volume.restrict V))
    rw [Measure.prod_restrict]
    change IntegrableOn (fun z => |R z| ^ p) (I ×ˢ V)
      sharedTerm_74facb25a1
    exact integrableOn_parabolicMorreyUnitBox_as_prod (by
        have hRmem : MemLp R (parabolicExponent d) (volume.restrict B) := by
          exact Continuous.memLp_parabolicMorreyUnitBox hRcont
        simpa [_root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
          Real.norm_eq_abs] using hRmem.integrable_norm_rpow
            (by simp [parabolicExponent]) (by simp [parabolicExponent]))
  have hSprod : Integrable (Function.uncurry fun t  => fun v : PDE.Vec d =>
      |S (t, v)| ^ p) (μ.prod ν) := by
    change Integrable (Function.uncurry fun t  => fun v : PDE.Vec d =>
      |S (t, v)| ^ p) ((volume.restrict I).prod (volume.restrict V))
    rw [Measure.prod_restrict]
    change IntegrableOn (fun z => |S z| ^ p) (I ×ˢ V)
      sharedTerm_74facb25a1
    exact integrableOn_parabolicMorreyUnitBox_as_prod (by
        have hSmem : MemLp S (parabolicExponent d) (volume.restrict B) := by
          exact Continuous.memLp_parabolicMorreyUnitBox hScont
        simpa [_root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
          Real.norm_eq_abs] using hSmem.integrable_norm_rpow
            (by simp [parabolicExponent]) (by simp [parabolicExponent]))
  have hpoint (v : PDE.Vec d) :
      ∫ t, |R (t, v)| ^ p ∂μ <= ∫ t, |S (t, v)| ^ p ∂μ := by
    have hmean := parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
      hu v
    have hscalar := unitTime_meanPoincare_rpow  (show 1 <= p by
        dsimp only [p]

        linarith)
      ((continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
        (continuous_timeDerivative hu)).comp (continuous_id.prodMk continuous_const))
      (hasDerivAt_parabolicMorreyUnitSpatialAffineProjection hu v)
    have haffine (t : Real) :
        parabolicMorreyUnitAffineProjection u (t, v) =
          parabolicMorreyUnitAffineProjection u (0, v) := rfl
    change ∫ t in I,
        |parabolicMorreyUnitSpatialAffineProjection u (t, v) -
          parabolicMorreyUnitAffineProjection u (t, v)| ^ p <=
      ∫ t in I, |S (t, v)| ^ p
    simp_rw [haffine, hmean]
    exact hscalar

  calc
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) =
        ∫ t, ∫ v, |R (t, v)| ^ p ∂ν ∂μ := by
      change ∫ z, |R z| ^ p ∂volume.restrict B = _
      rw [show volume.restrict B = μ.prod ν by
        exact parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact MeasureTheory.integral_prod _ hRprod
    _ <= ∫ t, ∫ v, |S (t, v)| ^ p ∂ν ∂μ := (by
        rw [MeasureTheory.integral_integral_swap hRprod,
          MeasureTheory.integral_integral_swap hSprod]
        exact MeasureTheory.integral_mono_ae hRprod.integral_prod_right
          hSprod.integral_prod_right (Filter.Eventually.of_forall hpoint))
    _ = ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) z| ^
          ((d : Real) + 1) := by
      change _ = ∫ z, |S z| ^ p ∂volume.restrict B
      rw [show volume.restrict B = μ.prod ν by
        exact parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact (MeasureTheory.integral_prod _ hSprod).symm

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u)

include hu
private theorem parabolicELpNormOn_temporalResidual_le_spatialProjection
     :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) := by
  let p : Real := (d : Real) + 1
  let R  := fun z => parabolicMorreyUnitSpatialAffineProjection u z -
    parabolicMorreyUnitAffineProjection u z
  let S  := parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  have hp : 0 < p := by dsimp [p]; positivity
  have hR : MemLp R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
          (continuous_parabolicMorreyUnitAffineProjection u))
  have hS : MemLp S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa only [R, S, p, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        (continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
          (continuous_timeDerivative hu))
  have hpower := temporalResidual_setIntegral_rpow_le_spatialProjection d u hu



  simpa [parabolicELpNormOn, R, S, p, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal] using ((ENNReal.toReal_le_toReal hR.eLpNorm_ne_top hS.eLpNorm_ne_top).mp (by
      calc
        (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal =
            ((eLpNorm R (ENNReal.ofReal p)
              (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p) ^ p⁻¹ :=
          (Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne').symm
        _ <= ((eLpNorm S (ENNReal.ofReal p)
          (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p) ^ p⁻¹ :=
          Real.rpow_le_rpow (by positivity) (by
              rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hR,
                PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hS]
              assumption) (by positivity)
        _ = (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal :=
          Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne'))

/-- Temporal Poincare control of the time-dependent moment-affine projection
by the time derivative on the literal unit box. -/
theorem parabolicMorreyUnitTemporalAffinePoincareELpNorm_le
     :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) * parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) :=
  (parabolicELpNormOn_temporalResidual_le_spatialProjection d u hu).trans
    (parabolicELpNormOn_spatialAffineProjection_timeDerivative_le d u hu)

/-- Real-valued corollary of the temporal moment-affine Poincare estimate. -/
theorem parabolicMorreyUnitTemporalAffinePoincareLpNorm_le
     :
    parabolicLpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      (1 + 3 * (d : Real)) * parabolicLpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) := by

  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Continuous.memLp_parabolicMorreyUnitBox (continuous_timeDerivative hu)).eLpNorm_ne_top)
    (parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu)
  unfold parabolicLpNormOn
  rw [ENNReal.toReal_ofReal_mul (1 + 3 * (d : Real)) _ (by positivity)] at h
  exact h

end HypoellipticAleksandrov.Parabolic
