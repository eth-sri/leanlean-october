module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarIncrement

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
import HypoellipticAleksandrov.Analysis.L2Convergence

/-!
# Scalar reverse-time energy representatives

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)
include d Ω hΩ T u

private noncomputable def rawEnergy : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (u t)‖ ^ 2

private noncomputable def rawEnergyRate (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (g t) (u t)

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)

private theorem integrable_rawEnergy :
    Integrable (rawEnergy hΩ T u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (u t)) 2 (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp u).continuousLinearMap_comp (valueCLM hΩ)
  unfold rawEnergy
  exact hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

private theorem integrable_rawEnergyRate (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawEnergyRate hΩ T u g) (reverseTimeVolume T) := by
  unfold rawEnergyRate
  exact
    (integrable_reverseTimeDualPairing hΩ T u g).const_mul 2

end

theorem memLp_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

theorem tendsto_integral_abs_valueSq_of_sqNorm
    (μ : Measure ℝ) (u : ℝ → H10HilbertGraph hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hu : MemLp u (2 : ℝ≥0∞) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs] using
    Analysis.tendsto_integral_norm_bilin_sub_of_sqNorm
      ((innerSL ℝ).bilinearComp (valueCLM hΩ) (valueCLM hΩ)) hu hu huh huh hU hU

private theorem tendsto_forwardSteklov_valueSq_error_on_Icc (T : ℝ)
    (u : ReverseTimeL2V hΩ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
        ‖valueCLM hΩ (u t)‖ ^ 2|) (𝓝[>] 0) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ, reverseTimeVolume, reverseTimeOpenInterval,
      Measure.restrict_restrict_of_subset hK] using
      (MeasureTheory.Lp.memLp u).restrict (Icc a b)
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h u) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeForwardSteklov T h u)
      (continuous_reverseTimeForwardSteklov T h hh u) a b
  have hU := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab hb
  change Tendsto (fun h : ℝ => ∫ t,
    |‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
      ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_integral_abs_valueSq_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (fun h t => reverseTimeForwardSteklov T h u t)
    hu huh hU

end

theorem tendsto_integral_mul_of_tendsto_integral_abs
    {μ : Measure ℝ} {F : ℝ → ℝ → ℝ} {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h : ℝ => ∫ t, |F h t - f t| ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t, F h t * phi t ∂μ) (𝓝[>] 0)
      (𝓝 (∫ t, f t * phi t ∂μ)) := Analysis.tendsto_integral_mul_of_tendsto_integral_abs hF hf hphi hbound hlim

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ) (u : ReverseTimeL2V hΩ T)
include d Ω hΩ T h u

private noncomputable def forwardSteklovEnergy : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2

private noncomputable def forwardSteklovEnergyRate (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (reverseTimeForwardSteklov T h g t)
    (reverseTimeForwardSteklov T h u t)

end

theorem abs_two_mul_sub (x y : ℝ) :
    |2 * x - 2 * y| = 2 * |x - y| := by
  simp [← mul_sub, abs_mul]

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
include hT hderiv

private theorem rawEnergy_test_deriv
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_reverseTimeScalarTest_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hraw : Integrable (rawEnergy hΩ T u) (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_rawEnergy hΩ T u).restrict
  have hpair : Integrable (fun t => (g t) (u t)) (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_reverseTimeDualPairing hΩ T u g).restrict
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t, forwardSteklovEnergy hΩ T h u t * eta.deriv t ∂reverseTimeVolume T) =
        -(∫ t, forwardSteklovEnergyRate hΩ T h u g t * eta t ∂reverseTimeVolume T) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
      (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
      with h hh hsmall
    have hQ : Continuous (forwardSteklovEnergyRate hΩ T h u g) := by
      exact continuous_const.mul
        ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
          (continuous_reverseTimeForwardSteklov T h hh u))
    have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
        forwardSteklovEnergy hΩ T h u t - forwardSteklovEnergy hΩ T h u s =
          ∫ r in Icc s t, forwardSteklovEnergyRate hΩ T h u g r := by
      intro s hs t ht hst
      change ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
          ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s)‖ ^ 2 = _
      calc
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
            ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s)‖ ^ 2 =
            2 * (∫ r in Icc s t,
              (reverseTimeForwardSteklov T h g r)
                (reverseTimeForwardSteklov T h u r)) :=
          reverseTimeForwardSteklov_energy_identity hΩ T hT u g hderiv hh
            (le_trans ha.le hs.1) hst
            (by linarith [ht.2, hsmall])
        _ = ∫ r in Icc s t, forwardSteklovEnergyRate hΩ T h u g r := by
          change 2 * (∫ r in Icc s t,
              (reverseTimeForwardSteklov T h g r)
                (reverseTimeForwardSteklov T h u r)) =
            ∫ r in Icc s t, 2 * (reverseTimeForwardSteklov T h g r)
              (reverseTimeForwardSteklov T h u r)
          rw [integral_const_mul]
    rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
      integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
    exact integral_mul_deriv_eq_neg_integral_of_increment_Icc hab.le hQ.integrableOn_Icc hinc
      (eta.contDiff.of_le (by simp)) heta
  have hEForward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovEnergy hΩ T h u) (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact ((valueCLM hΩ).continuous.comp
      (continuous_reverseTimeForwardSteklov T h hh u)).norm.pow 2 |>.integrableOn_Icc
  have hQForward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovEnergyRate hΩ T h u g) (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact (continuous_const.mul
      ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
        (continuous_reverseTimeForwardSteklov T h hh u))).integrableOn_Icc
  have hEabs := tendsto_forwardSteklov_valueSq_error_on_Icc hΩ T u ha hab.le hb
  have hQabs := tendsto_forwardSteklov_dualPairing_integral_on_Icc hΩ T u g ha hab.le hb
  have hEtest := tendsto_integral_mul_of_tendsto_integral_abs hEForward hraw
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs
  have hQraw : Integrable (rawEnergyRate hΩ T u g) (volume.restrict (Icc a b)) :=
    hpair.const_mul 2
  have hQabs2 : Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |forwardSteklovEnergyRate hΩ T h u g t - rawEnergyRate hΩ T u g t|)
      (𝓝[>] 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul hQabs using 1
    · funext h
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      exact (abs_two_mul_sub _ _)
    · norm_num
  have hQtest := tendsto_integral_mul_of_tendsto_integral_abs hQForward hQraw
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le hQabs2
  have hforwardIcc : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, forwardSteklovEnergy hΩ T h u t * eta.deriv t) =
        -(∫ t in Icc a b, forwardSteklovEnergyRate hΩ T h u g t * eta t) := by
    filter_upwards [hforward] with h hh
    rw [← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
      ← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
    exact hh
  have hIccLimit := hEtest.add hQtest
  have hConst : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, rawEnergy hΩ T u t * eta.deriv t) +
        ∫ t in Icc a b, rawEnergyRate hΩ T u g t * eta t)) := by
    apply hIccLimit.congr'
    filter_upwards [hforwardIcc] with h hh
    linarith
  have hzeroIcc : (∫ t in Icc a b, rawEnergy hΩ T u t * eta.deriv t) +
      ∫ t in Icc a b, rawEnergyRate hΩ T u g t * eta t = 0 := by
    exact tendsto_nhds_unique hConst tendsto_const_nhds
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  linarith

private theorem exists_continuous_reverseTimeScalarEnergyRepresentative_raw :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T] rawEnergy hΩ T u ∧
      ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  obtain ⟨e, he, ha, hi⟩ := exists_continuous_reverseTime_representative_of_weakDeriv hT
    (integrable_rawEnergy hΩ T u) (integrable_rawEnergyRate hΩ T u g)
    (rawEnergy_test_deriv hΩ T hT u g hderiv)
  refine ⟨e, he, reverseTime_nonneg_on_closedInterval_of_ae hT he ?_, ha, hi⟩
  filter_upwards [ha] with t ht
  rw [ht]
  exact sq_nonneg _

/-- A continuous scalar reverse-time energy representative of a Gelfand weak
derivative on the closed reverse-time interval. -/
theorem exists_continuous_reverseTimeScalarEnergyRepresentative :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T]
        (fun t => ‖valueCLM hΩ (u t)‖ ^ 2) ∧
      ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
        e t - e s =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heNonneg, heAE, heSub⟩ :=
    exists_continuous_reverseTimeScalarEnergyRepresentative_raw hΩ T hT u g hderiv
  refine ⟨e, heCont, heNonneg, ?_, ?_⟩
  · exact heAE
  · intro s t hs ht hst
    rw [heSub s t hs ht hst]
    simp only [rawEnergyRate, integral_const_mul]

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
