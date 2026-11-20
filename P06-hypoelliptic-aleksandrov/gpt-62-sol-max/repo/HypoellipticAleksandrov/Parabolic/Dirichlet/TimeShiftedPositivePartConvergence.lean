module

import HypoellipticAleksandrov.Analysis.L2Convergence

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence

/-!
# Continuity of affine-threshold shifted positive parts in reverse time

This module decomposes the finite-measure Vitali argument proving strong
continuity of the affine-threshold shifted positive-part operation on the
reverse-time Bochner `L²` space.
-/

@[expose] public section

open HypoellipticAleksandrov.Analysis Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The affine-threshold shifted positive-part operation is strongly
continuous on reverse-time Bochner `L²(V)`. -/
theorem continuous_reverseTimeShiftedPositivePart
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0) :
    Continuous (reverseTimeShiftedPositivePart hΩ T M N :
      ReverseTimeL2V hΩ T → ReverseTimeL2V hΩ T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T)))
  exact continuous_L2_of_pointwise (coeFn_reverseTimeShiftedPositivePart hΩ T M N)
    (fun t => (continuous_h10ShiftedPositivePart hΩ).comp (continuous_id.prodMk continuous_const))
    (fun t f => norm_h10ShiftedPositivePart_le hΩ f (reverseTimeAffineThreshold M N t))

section
variable {E : Type*}

/-- The forward Steklov average as a totalized reverse-time Bochner `L²`
class.  Nonpositive averaging widths are assigned the original class. -/
noncomputable def reverseTimeForwardSteklovL2 [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T) :=
  if hh : 0 < h then
    reverseTimeL2OfContinuousOn T (reverseTimeForwardSteklov T h f)
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  else
    f

/-- At a positive averaging width, the lifted forward Steklov class is
represented almost everywhere by the pointwise average. -/
theorem coeFn_reverseTimeForwardSteklovL2_of_pos [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) {h : ℝ} (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    reverseTimeForwardSteklovL2 T h f =ᵐ[reverseTimeVolume T]
      reverseTimeForwardSteklov T h f := by
  rw [reverseTimeForwardSteklovL2, dif_pos hh]
  exact coeFn_reverseTimeL2OfContinuousOn T _ _

/-- The totalized forward Steklov lift converges strongly to the original
reverse-time Bochner `L²` class as the averaging width tends to zero from the
right. -/
theorem tendsto_reverseTimeForwardSteklovL2 [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Tendsto (fun h : ℝ => reverseTimeForwardSteklovL2 T h f)
      (nhdsWithin 0 (Ioi 0)) (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq := tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f
  have hsqrt : Tendsto
      (fun h : ℝ => √(∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Continuous.tendsto Real.continuous_sqrt 0).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hraw :=
    memLp_two_reverseTime_of_continuousOn T _
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  let hsub := hraw.sub (Lp.memLp f)
  have htoLp : hsub.toLp
      (reverseTimeForwardSteklov T h f - fun t => f t) =
      reverseTimeForwardSteklovL2 T h f - f := by
    apply Lp.ext
    filter_upwards [hsub.coeFn_toLp,
        coeFn_reverseTimeForwardSteklovL2_of_pos T hh f,
        Lp.coeFn_sub (reverseTimeForwardSteklovL2 T h f) f]
      with t hsubt hlift hliftSub
    rw [hsubt]
    calc
      (reverseTimeForwardSteklov T h f - fun t => f t) t =
          reverseTimeForwardSteklovL2 T h f t - f t := by
        rw [Pi.sub_apply, hlift]
      _ = (reverseTimeForwardSteklovL2 T h f - f) t := hliftSub.symm
  have hint : (∫ t in Icc 0 T,
      ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
      ‖hsub.toLp
        (reverseTimeForwardSteklov T h f - fun t => f t)‖ ^ 2 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, Pi.sub_apply] using
      integral_norm_sq_eq_norm_sq_toLp
        (reverseTimeForwardSteklov T h f - fun t => f t) hsub
  rw [← Real.sqrt_sq (norm_nonneg
    (reverseTimeForwardSteklovL2 T h f - f)), ← htoLp, ← hint]

end

/-- Strong reverse-time `L²` convergence gives local convergence of the
square of the spatial `L²` value norm. -/
theorem tendsto_integral_abs_valueCLM_sq_of_tendsto
    {ι : Type*} {l : Filter ι} (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (un : ι → ReverseTimeL2V hΩ T)
    (hun : Tendsto un l (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |‖valueCLM hΩ (un n t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|)
      l (𝓝 0) := by
  simpa only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs] using
    tendsto_integral_norm_bilin_sub_of_tendsto
      ((innerSL ℝ).bilinearComp (valueCLM hΩ) (valueCLM hΩ)) hμ hun hun

/-- A bounded scalar functional sends strong reverse-time `L²` convergence to
local `L¹` convergence. -/
theorem tendsto_integral_abs_continuousLinearMap_of_tendsto
    {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T a b : ℝ} (Q : E →L[ℝ] ℝ)
    (u : MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (un : ι → MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (hun : Tendsto un l (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b, |Q (un n t) - Q (u t)|)
      l (𝓝 0) := by
  let : IsFiniteMeasure (reverseTimeVolume T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T)))
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (reverseTimeVolume T) := memLp_const 1
  let one := hone.toLp (fun _ => 1)
  let B := (ContinuousLinearMap.lsmul ℝ ℝ).bilinearComp (ContinuousLinearMap.id ℝ ℝ) Q
  refine (tendsto_integral_norm_bilin_sub_of_tendsto B hμ
    (tendsto_const_nhds (x := one)) hun).congr' ?_
  filter_upwards with n
  apply integral_congr_ae
  filter_upwards [hone.coeFn_toLp.filter_mono (ae_mono hμ)] with t ht
  change |one t * Q (un n t) - one t * Q (u t)| = _
  rw [show one t = 1 from ht, one_mul, one_mul]

private theorem shifted_integrable_dualPairing
    (hΩ : IsOpen Ω) {μ : Measure ℝ}
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => (g t) (u t)) μ := by
  let pairing : H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  simpa only [pairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply] using
    memLp_one_iff_integrable.mp (pairing.memLp_of_bilin 1 hg hu)

private theorem integral_abs_sub_mul_sub_le
    {μ : Measure ℝ} (A B X Y : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ t, |A t - c * X t - (B t - c * Y t)| ∂μ) ≤
      (∫ t, |A t - B t| ∂μ) + c * (∫ t, |X t - Y t| ∂μ) := by
  have hAB := (hA.sub hB).norm
  have hXY := (hX.sub hY).norm
  have hAB' : Integrable (fun t => |A t - B t|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hAB
  have hXY' : Integrable (fun t => |X t - Y t|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hXY
  calc
    _ ≤ ∫ t, |A t - B t| + c * |X t - Y t| ∂μ := by
      apply integral_mono
      · exact ((hA.sub (hX.const_mul c)).sub
          (hB.sub (hY.const_mul c))).norm
      · exact hAB'.add (hXY'.const_mul c)
      · intro t
        calc
          |A t - c * X t - (B t - c * Y t)| =
              |(A t - B t) - c * (X t - Y t)| := by
            congr 1
            ring
          _ ≤ |A t - B t| + |c * (X t - Y t)| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hc]
    _ = _ := by
      rw [integral_add hAB' (hXY'.const_mul c), integral_const_mul]

/-- Strong convergence in the primal and dual reverse-time `L²` spaces gives
local `L¹` convergence of their pointwise dual pairing. -/
theorem tendsto_integral_abs_dualPairing_of_tendsto
    {ι : Type*} {l : Filter ι} (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (un : ι → ReverseTimeL2V hΩ T)
    (gn : ι → ReverseTimeL2VStar hΩ T)
    (hun : Tendsto un l (𝓝 u)) (hgn : Tendsto gn l (𝓝 g))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |(gn n t) (un n t) - (g t) (u t)|) l (𝓝 0) := by
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, Real.norm_eq_abs] using
    tendsto_integral_norm_bilin_sub_of_tendsto (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ))
      hμ hgn hun

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      shiftedPositivePartEnergy hΩ M N
        (fun t => reverseTimeForwardSteklov T h u t) t * eta.deriv t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergy hΩ M N (fun t => u t) t * eta.deriv t)) := by
  have hT : 0 < T := by linarith
  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T :=
    Measure.restrict_mono (Icc_subset_Ioo ha hb) le_rfl
  let uh : ℝ → ReverseTimeL2V hΩ T := fun h =>
    reverseTimeForwardSteklovL2 T h u
  let up : ReverseTimeL2V hΩ T := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp : ℝ → ReverseTimeL2V hΩ T := fun h =>
    reverseTimeShiftedPositivePart hΩ T M N (uh h)
  have huh : Tendsto uh (𝓝[>] 0) (𝓝 u) :=
    tendsto_reverseTimeForwardSteklovL2 T hT u
  have huhp : Tendsto uhp (𝓝[>] 0) (𝓝 up) :=
    (continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp huh
  have hclass := tendsto_integral_abs_valueCLM_sq_of_tendsto
    hΩ up uhp huhp hμ
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h :=
    self_mem_nhdsWithin
  have hEabs : Tendsto (fun h => ∫ t in Icc a b,
      |shiftedPositivePartEnergy hΩ M N
          (fun t => reverseTimeForwardSteklov T h u t) t -
        shiftedPositivePartEnergy hΩ M N (fun t => u t) t|)
      (𝓝[>] 0) (𝓝 0) := by
    apply hclass.congr'
    filter_upwards [hpos] with h hn
    apply integral_congr_ae
    filter_upwards
        [(coeFn_reverseTimeForwardSteklovL2_of_pos T hn u).filter_mono
            (ae_mono hμ),
          (coeFn_reverseTimeShiftedPositivePart hΩ T M N (uh h)).filter_mono
            (ae_mono hμ),
          (coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
            (ae_mono hμ)]
      with t hraw hshift hlimit
    simp only [uhp, up, shiftedPositivePartEnergy]
    rw [hshift, hlimit, hraw]
  have hraw : Integrable
      (shiftedPositivePartEnergy hΩ M N (fun t => u t))
      (volume.restrict (Icc a b)) := by
    have hm := (Lp.memLp up).mono_measure hμ
    have hv := hm.continuousLinearMap_comp (valueCLM hΩ)
    apply (hv.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    filter_upwards [(coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
        (ae_mono hμ)] with t ht
    simp only [shiftedPositivePartEnergy]
    rw [ht]
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable
      (shiftedPositivePartEnergy hΩ M N
        (fun t => reverseTimeForwardSteklov T h u t))
      (volume.restrict (Icc a b)) := by
    filter_upwards [hpos] with h hn
    exact (((valueCLM hΩ).continuous.comp
      ((continuous_h10ShiftedPositivePart hΩ).comp
        ((continuous_reverseTimeForwardSteklov T h hn u).prodMk
          (continuous_const.add
            (continuous_real_toNNReal.mul continuous_const))))).norm.pow 2).integrableOn_Icc
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs

section
variable (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)

private theorem ae_shiftedPositivePartEnergyRate_forwardSteklovL2 {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    (fun t => shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun r => reverseTimeForwardSteklov T h u r)
      (fun r => reverseTimeForwardSteklov T h g r) t) =ᵐ[reverseTimeVolume T]
    fun t => (reverseTimeForwardSteklovL2 T h g t)
      (reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u) t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N
          (reverseTimeForwardSteklovL2 T h u) t) := by
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := by infer_instance
  filter_upwards [coeFn_reverseTimeForwardSteklovL2_of_pos T hh u,
      coeFn_reverseTimeForwardSteklovL2_of_pos T hh g,
      coeFn_reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u)] with t hu hg hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  simp only [← hup, ← hu, ← hg]

private theorem ae_shiftedPositivePartEnergyRate_L2 (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    (fun t => shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun r => u r) (fun r => g r) t) =ᵐ[reverseTimeVolume T]
    fun t => (g t) (reverseTimeShiftedPositivePart hΩ T M N u t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N u t) := by
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  rw [hup]

end

section
variable (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)

private theorem integrable_shiftedPositivePartEnergyRate_L2_on_Icc (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun t => u t) (fun t => g t)) (volume.restrict (Icc a b)) := by
  have huLocal := (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).mono_measure hμ
  have hgLocal := (Lp.memLp g).mono_measure hμ
  have hp := shifted_integrable_dualPairing hΩ
    (reverseTimeShiftedPositivePart hΩ T M N u) g huLocal hgLocal
  have hm := huLocal.continuousLinearMap_comp
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
  apply (hp.sub ((hm.integrable (by norm_num)).const_mul (N : ℝ))).congr
  exact (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).symm.filter_mono
    (ae_mono hμ)

private theorem integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (a b : ℝ) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun t => reverseTimeForwardSteklov T h u t)
      (fun t => reverseTimeForwardSteklov T h g t))
      (volume.restrict (Icc a b)) := by
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  exact (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
    (continuous_const.mul
      (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp))
    |>.integrableOn_Icc)

end

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy rate in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun t => reverseTimeForwardSteklov T h u t)
        (fun t => reverseTimeForwardSteklov T h g t) t * eta t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => u t) (fun t => g t) t * eta t)) := by
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := by infer_instance
  have hT : 0 < T := by linarith
  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T :=
    Measure.restrict_mono (Icc_subset_Ioo ha hb) le_rfl
  let uh : ℝ → ReverseTimeL2V hΩ T := fun h =>
    reverseTimeForwardSteklovL2 T h u
  let gh : ℝ → ReverseTimeL2VStar hΩ T := fun h =>
    reverseTimeForwardSteklovL2 T h g
  let up : ReverseTimeL2V hΩ T := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp : ℝ → ReverseTimeL2V hΩ T := fun h =>
    reverseTimeShiftedPositivePart hΩ T M N (uh h)
  have huh : Tendsto uh (𝓝[>] 0) (𝓝 u) :=
    tendsto_reverseTimeForwardSteklovL2 T hT u
  have hgh : Tendsto gh (𝓝[>] 0) (𝓝 g) :=
    tendsto_reverseTimeForwardSteklovL2 T hT g
  have huhp : Tendsto uhp (𝓝[>] 0) (𝓝 up) :=
    (continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp huh
  let Q := (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  have hpair := tendsto_integral_abs_dualPairing_of_tendsto
    hΩ up g uhp gh huhp hgh hμ
  have hmass := tendsto_integral_abs_continuousLinearMap_of_tendsto Q up uhp huhp hμ
  have herrClass : Tendsto (fun h => ∫ t in Icc a b,
      |(gh h t) (uhp h t) - (N : ℝ) *
          Q (uhp h t) -
        ((g t) (up t) - (N : ℝ) *
          Q (up t))|)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (g := fun h =>
      (∫ t in Icc a b, |(gh h t) (uhp h t) - (g t) (up t)|) +
      (N : ℝ) * (∫ t in Icc a b,
        |Q (uhp h t) - Q (up t)|))
    · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
    · filter_upwards with h
      have huLocal := (Lp.memLp up).mono_measure hμ
      have huhLocal := (Lp.memLp (uhp h)).mono_measure hμ
      have hgLocal : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2
          (volume.restrict (Icc a b)) := (Lp.memLp g).mono_measure hμ
      have hghLocal : MemLp (gh h : ℝ → H10HilbertGraphDual hΩ) 2
          (volume.restrict (Icc a b)) := (Lp.memLp (gh h)).mono_measure hμ
      have hp0 := shifted_integrable_dualPairing hΩ up g huLocal hgLocal
      have hp1 := shifted_integrable_dualPairing hΩ (uhp h) (gh h)
        huhLocal hghLocal
      have hm0 := huLocal.continuousLinearMap_comp
        Q
      have hm1 := huhLocal.continuousLinearMap_comp
        Q
      exact integral_abs_sub_mul_sub_le
        (fun t => (gh h t) (uhp h t)) (fun t => (g t) (up t))
        (fun t => Q (uhp h t)) (fun t => Q (up t)) (N : ℝ) N.coe_nonneg
        hp1 hp0 (hm1.integrable (by norm_num)) (hm0.integrable (by norm_num))
    · have hscaled : Tendsto (fun h => (N : ℝ) * (∫ t in Icc a b,
          |Q (uhp h t) - Q (up t)|))
          (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul hmass
      simpa only [zero_add] using hpair.add hscaled
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h :=
    self_mem_nhdsWithin
  have herr : Tendsto (fun h => ∫ t in Icc a b,
      |shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => reverseTimeForwardSteklov T h u t)
          (fun t => reverseTimeForwardSteklov T h g t) t -
        shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => u t) (fun t => g t) t|) (𝓝[>] 0) (𝓝 0) := by
    apply herrClass.congr'
    filter_upwards [hpos] with h hn
    apply integral_congr_ae
    filter_upwards
        [(ae_shiftedPositivePartEnergyRate_forwardSteklovL2 hΩ hΩbounded
            M N T hn u g).filter_mono (ae_mono hμ),
          (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).filter_mono
            (ae_mono hμ)] with t hforwardRate hlimitRate
    exact congrArg₂ (fun x y : ℝ => |x - y|) hforwardRate.symm hlimitRate.symm
  have hraw := integrable_shiftedPositivePartEnergyRate_L2_on_Icc
    hΩ hΩbounded M N T u g hμ
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable
      (shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun t => reverseTimeForwardSteklov T h u t)
        (fun t => reverseTimeForwardSteklov T h g t))
      (volume.restrict (Icc a b)) := by
    filter_upwards [hpos] with h hn
    exact integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc
      hΩ hΩbounded M N T hn u g a b
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le herr

end HypoellipticAleksandrov.Parabolic.Dirichlet
