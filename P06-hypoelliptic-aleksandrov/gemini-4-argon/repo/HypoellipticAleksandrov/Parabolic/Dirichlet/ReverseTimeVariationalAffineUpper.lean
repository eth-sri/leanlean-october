module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceShiftedPositivePartBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormShiftedPositivePartSmooth
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.IntegralGronwall
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Mass
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormShiftedPositivePart

/-! # Sharp affine upper bound for reverse-time variational solutions -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private def affineUpperClamp (T r : ℝ) := min T (max 0 r)

private theorem affineUpperClamp_mem {T : ℝ} (hT : 0 < T) (r : ℝ) :
    affineUpperClamp T r ∈ Icc 0 T :=
  ⟨le_min hT.le (le_max_left _ _), min_le_left _ _⟩

private theorem affineUpperClamp_eq {T r : ℝ} (hr : r ∈ Icc 0 T) :
    affineUpperClamp T r = r := by
  simp only [affineUpperClamp, max_eq_right hr.1, min_eq_right hr.2]

private theorem affineUpper_initial_energy_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hT : 0 < T)
    (M N : ℝ≥0) (Ubar : C(Icc 0 T, PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hzero : shiftedPositivePartValue M (Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0) :
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N 0)
      (Ubar ⟨affineUpperClamp T 0, affineUpperClamp_mem hT 0⟩)‖ ^ 2 = 0 := by
  have hc : (⟨affineUpperClamp T 0, affineUpperClamp_mem hT 0⟩ : Icc 0 T) =
      ⟨0, ⟨le_rfl, hT.le⟩⟩ := Subtype.ext (affineUpperClamp_eq ⟨le_rfl, hT.le⟩)
  rw [hc]
  simp only [reverseTimeAffineThreshold, Real.toNNReal_zero, zero_mul, add_zero,
    hzero, norm_zero]
  norm_num

private theorem affineUpper_shiftedPositivePart_zero
    {d } {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T)
    (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g) (K ) (hK : 0 ≤ K)
    (hrate : ∀ᵐ r ∂reverseTimeVolume T,
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r)) -
        (N : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r)))) +
        0 * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M N r))‖ ^ 2)
    (hzero : shiftedPositivePartValue M
      (reverseTimeHilbertRepresentative hΩ T hT u g hd
        ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0) :
    ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
        (reverseTimeHilbertRepresentative hΩ T hT u g hd ⟨t, ht⟩) = 0 := by
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hd
  let E : ℝ → ℝ := fun r =>
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
      (Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2
  have _h_inl_18 : Continuous (affineUpperClamp T) := by
      exact (
    continuous_const.min (continuous_const.max continuous_id)
    )
  have hEc : ContinuousOn E (Icc 0 T) :=
    ((continuous_shiftedPositivePartValue_of_isBounded hΩbounded).comp
      (Ubar.continuous.comp
        (_h_inl_18.subtype_mk _) |>.prodMk
          (continuous_const.add
            (continuous_real_toNNReal.mul continuous_const)))).norm.pow 2 |>.continuousOn
  have hEn : ∀ r ∈ Icc 0 T, 0 ≤ E r := fun _ _ => sq_nonneg _
  have hE0 : E 0 = 0 := affineUpper_initial_energy_zero hT M N Ubar hzero
  have hpair :=
    (integrable_reverseTimeDualPairing hΩ T (reverseTimeShiftedPositivePart hΩ T M N u) g).congr
      (by filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with r hr; rw [hr])
  have hmass : Integrable (fun r => spatialMassCLM hΩbounded
      (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M N r)))) (reverseTimeVolume T) :=
    (integrable_reverseTimeShiftedPositivePart_spatialMass
      hΩ hΩbounded T M N u).congr (by
        filter_upwards with r
        exact (spatialMassCLM_apply hΩbounded _).symm)
  have hvalue : Integrable (fun r => ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
      (reverseTimeAffineThreshold M N r))‖ ^ 2) (reverseTimeVolume T) := by
    have hm := (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).continuousLinearMap_comp
      (valueCLM hΩ)
    exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).congr (by
      filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with r hr
      rw [hr])
  have hEle : ∀ t ∈ Icc 0 T, E t ≤ (2 * K) * ∫ r in Ioc 0 t, E r := by
    intro t ht
    have hinc := reverseTimeHilbertRepresentative_shiftedPositivePart_norm_sq_increment
      hΩ hΩbounded T hT M N u g hd 0 t ⟨le_rfl, hT.le⟩ ht ht.1
    have hint := setIntegral_mono_ae_restrict (s := Ioc 0 t)
      ((hpair.sub (hmass.const_mul (N : ℝ))).const_mul 2).integrableOn
      (hvalue.const_mul (2 * K)).integrableOn
      (ae_restrict_of_ae (by
        filter_upwards [hrate] with r hr
        simpa only [zero_mul, add_zero, Pi.sub_def] using hr))
    rw [integral_const_mul, integral_const_mul] at hint
    have hval : (∫ r in Ioc 0 t,
        ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r))‖ ^ 2 ∂reverseTimeVolume T) =
      ∫ r in Ioc 0 t,
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
          (reverseTimeHilbertRepresentative hΩ T hT u g hd
            ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2 := by
      let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hd
      have hUbar := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hd).1
      calc
        _ = ∫ r in Ioc 0 t,
            ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
              (Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2
              ∂reverseTimeVolume T := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hUbar,
            ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with r hUr hr
          have hrcc : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
          have hUr' : Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩ =
              valueCLM hΩ (u r) := by
            simpa only [affineUpperClamp_eq hrcc] using hUr hr
          rw [hUr', valueCLM_h10ShiftedPositivePart]
        _ = _ := by
            rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
              Measure.restrict_restrict measurableSet_Ioc]
            congr 2
            exact inter_eq_left.mpr (Ioc_subset_Icc_self.trans fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
    have hc : (⟨affineUpperClamp T t, affineUpperClamp_mem hT t⟩ : Icc 0 T) =
        ⟨t, ht⟩ := Subtype.ext (affineUpperClamp_eq ht)
    dsimp only [E]
    have hzero' : shiftedPositivePartValue (reverseTimeAffineThreshold M N 0)
        (reverseTimeHilbertRepresentative hΩ T hT u g hd
          ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0 := by
      simpa only [reverseTimeAffineThreshold, Real.toNNReal_zero, zero_mul, add_zero]
        using hzero
    rw [hzero', norm_zero, zero_pow (by norm_num), sub_zero] at hinc
    calc
      _ = ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
          (Ubar ⟨t, ht⟩)‖ ^ 2 := congrArg (fun q : Icc 0 T =>
            ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t) (Ubar q)‖ ^ 2) hc
      _ = 2 * (∫ r in Ioc 0 t,
          (g r) (h10ShiftedPositivePart hΩ (u r) (reverseTimeAffineThreshold M N r)) -
            (N : ℝ) * spatialMassCLM hΩbounded
              (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
                (reverseTimeAffineThreshold M N r))) ∂reverseTimeVolume T) := hinc
      _ ≤ 2 * K * (∫ r in Ioc 0 t,
          ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r))‖ ^ 2 ∂reverseTimeVolume T) := hint
      _ = _ := congrArg (fun q : ℝ => 2 * K * q) hval
  have hz := eq_zero_on_Icc_of_nonneg_le_mul_integral hT
    (mul_nonneg (by norm_num) hK) E hEc hEn hE0 hEle
  intro t ht
  have hc : (⟨affineUpperClamp T t, affineUpperClamp_mem hT t⟩ : Icc 0 T) =
      ⟨t, ht⟩ := Subtype.ext (affineUpperClamp_eq ht)
  have hs : ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
      (Ubar ⟨t, ht⟩)‖ ^ 2 = 0 := by
    simpa only [E, hc] using hz t ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

theorem IsReverseTimeVariationalEnergySolution.reverseTimeHilbertRepresentative_le_affine
    {d Ω}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (Minit MF ) (hMinit : 0 ≤ Minit) (hMF : 0 ≤ MF)
    (hFbound : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      |F z.1 z.2| ≤ MF)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, initial y ≤ Minit)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y ≤ Minit + τ * MF := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let M0 := Minit.toNNReal
  let NF := MF.toNNReal
  have hM0 : (M0 : ℝ) = Minit := Real.coe_toNNReal _ hMinit
  have hNF : (NF : ℝ) = MF := Real.coe_toNNReal _ hMF
  obtain ⟨K, hK, hrate⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 2 * ((g τ) (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)) - (NF : ℝ) * spatialMassCLM hΩbounded (valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)))) + lam * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ))‖ ^ 2 ≤ 2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ))‖ ^ 2 := by
    have hFbound : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → |F z.1 z.2| ≤ (NF : ℝ) := by
      simpa only [hNF] using hFbound
    obtain ⟨K, hK, hGard⟩ := reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
    refine ⟨K, hK, ?_⟩
    rcases hu with ⟨_, heq⟩
    filter_upwards [heq, ae_restrict_mem measurableSet_Ioo] with τ heqτ hτ
    have hτcc : τ ∈ Icc 0 (r₁ - r₀) := ⟨hτ.1.le, hτ.2.le⟩
    let w := h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)
    let f := reverseTimeSourceSlice r₁ τ F
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
        r₀ r₁ hΩ hΩbounded F hFSmooth τ hτcc)
    have hf : ∀ᵐ y ∂PDE.volumeOn Ω, |f y| ≤ (NF : ℝ) := by
      filter_upwards [coeFn_reverseTimeSourceSlice r₁ τ F _,
        ae_restrict_mem hΩ.measurableSet] with y hyF hy
      rw [hyF]
      exact hFbound (r₁ - τ, y)
        ⟨⟨by linarith [h₀₁, hτ.2], by linarith [hτ.1]⟩, subset_closure hy⟩
    have hsource : reverseTimeSourceFunctional hΩ f
          (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)) ≤
        (NF : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ))) := by
      let u := (u τ)
      let k := (reverseTimeAffineThreshold M0 NF τ)
      let w :=
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
      letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
        isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
      have hwNonneg : ∀ᵐ y ∂PDE.volumeOn Ω, 0 ≤ w y := by
        filter_upwards [coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hy
        rw [show w y = max (valueCLM hΩ u y - (k : ℝ)) 0 by exact hy]
        exact le_max_right _ _
      have hwIntegrable :=
        (Lp.memLp w).integrable (by norm_num)
      rw [reverseTimeSourceFunctional_apply, L2.inner_def,
        spatialMassCLM_apply, ← integral_neg, ← integral_const_mul]
      apply integral_mono_ae
        (L2.integrable_inner (𝕜 := ℝ) w f).neg
        (hwIntegrable.const_mul (NF : ℝ))
      filter_upwards [hf, hwNonneg] with y hyf hyw
      simp only [RCLike.inner_apply, conj_trivial]
      calc
        -(f y * w y) ≤ w y * |f y| := by
          simpa only [mul_comm, neg_mul] using
            (mul_le_mul_of_nonneg_left (neg_le_abs (f y)) hyw)
        _ ≤ w y * (NF : ℝ) := mul_le_mul_of_nonneg_left hyf hyw
        _ = (NF : ℝ) * w y := mul_comm _ _
    have hshift : reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)) ≥
        reverseTimeSpatialForm hΩ r₁ τ a b c
          (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)) (h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M0 NF τ)) := by
      let u := (u τ)
      let k := (reverseTimeAffineThreshold M0 NF τ)
      let q := fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y
      let U := valueCLM hΩ u
      let W := valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
      obtain ⟨C, hC, hCbound⟩ :=
        exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
          r₀ r₁ hΩbounded c hcSmooth
      have hqMeas : AEStronglyMeasurable q (PDE.volumeOn Ω) := by
        exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
          r₀ r₁ τ c hcSmooth hτcc).aestronglyMeasurable hΩ.measurableSet
      have hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C := by
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
        simpa only [q, Real.norm_eq_abs] using hCbound τ hτcc y hy
      have hScalarSquare : Integrable (fun y => q y * W y * W y) (PDE.volumeOn Ω) := by
        refine (L2.integrable_inner (𝕜 := ℝ)
          (scalarL2Multiplier q hqMeas C hC hqBound W) W).congr ?_
        filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound W] with y hy
        rw [hy]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      have hScalarCross : Integrable (fun y => q y * U y * W y) (PDE.volumeOn Ω) := by
        refine (L2.integrable_inner (𝕜 := ℝ)
          (scalarL2Multiplier q hqMeas C hC hqBound U) W).congr ?_
        filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound U] with y hy
        rw [hy]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      have hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω, q y ≤ 0 := by
        have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
          constructor <;> linarith [h₀₁, hτcc.1, hτcc.2]
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
        simpa only [q, reverseTimeScalarCoefficient_apply] using
          hcNonpos (r₁ - τ, y) ⟨htime, subset_closure hy⟩
      exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge hΩ r₁ τ a b c u k
        hScalarNonpos (by simpa only [q, W] using hScalarSquare)
        (by simpa only [q, U, W] using hScalarCross)
    have hgard := hGard τ hτcc w
    have he := heqτ hτ w
    dsimp only [w] at he hsource hshift hgard ⊢
    linarith
  let Ubar := reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT u g hdu
  have hzero : shiftedPositivePartValue M0 (Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0 := by
    rw [show Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩ = initial by exact hu.1]
    apply Lp.ext
    filter_upwards [coeFn_shiftedPositivePartValue M0 initial,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω), hinitial] with y hs hz hi
    rw [hs, hz, hM0]
    exact max_eq_right (sub_nonpos.mpr hi)
  have hrate0 : ∀ᵐ r ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r)) -
        (NF : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M0 NF r)))) +
        0 * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 := by
    filter_upwards [hrate] with r hr
    have hg : 0 ≤ lam * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa only [zero_mul, add_zero] using (show
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r)) -
        (NF : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M0 NF r)))) ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 by linarith)
  intro τ hτ
  have hz := affineUpper_shiftedPositivePart_zero hΩ hΩbounded (r₁ - r₀) hT
    M0 NF u g hdu K hK hrate0 hzero τ hτ
  filter_upwards [Lp.ext_iff.mp hz,
    coeFn_shiftedPositivePartValue (reverseTimeAffineThreshold M0 NF τ) (Ubar ⟨τ, hτ⟩),
    Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω)] with y hy hs h0
  rw [hs, h0] at hy
  have hle := max_eq_right_iff.mp hy
  rw [coe_reverseTimeAffineThreshold_of_nonneg M0 NF hτ.1, hM0, hNF] at hle
  exact sub_nonpos.mp hle

end HypoellipticAleksandrov.Parabolic.Dirichlet
