module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePartSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy

/-!
# Positive-part reverse-time energy increments

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (eta : ReverseTimeScalarTest T)

private def rawPositivePartEnergy
    
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (h10PositivePart hΩ (u t))‖ ^ 2

private def rawPositivePartEnergyRate
    
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (g t) (h10PositivePart hΩ (u t))

private def reverseTimePositivePartEnergyPrimitive
    
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Set.Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T

private theorem integrable_rawPositivePartEnergy
     :
    Integrable (rawPositivePartEnergy hΩ T u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo _ T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (h10PositivePart hΩ (u t))) 2
      _ :=
    memLp_congr_ae (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
        simp_all) |>.mp
      ((MeasureTheory.Lp.memLp (reverseTimePositivePart hΩ T u)).continuousLinearMap_comp
        (valueCLM hΩ))
  exact hu.integrable_norm_pow (by norm_num)

private theorem integrable_rawPositivePartEnergyRate
     :
    Integrable (rawPositivePartEnergyRate hΩ T u g) (reverseTimeVolume T) := ((integrable_reverseTimeDualPairing hΩ T
    (reverseTimePositivePart hΩ T u) g).const_mul 2).congr (by
      filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
      aesop)

private theorem continuousOn_reverseTimePositivePartEnergyPrimitive
     :
    ContinuousOn (reverseTimePositivePartEnergyPrimitive hΩ T u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo _ T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_rawPositivePartEnergyRate hΩ T u g).integrableOn

private theorem reverseTimePositivePartEnergyPrimitive_sub
    
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    reverseTimePositivePartEnergyPrimitive hΩ T u g t -
        reverseTimePositivePartEnergyPrimitive hΩ T u g s =
      ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  change (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) -
      ∫ r in Ioc 0 s, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_rawPositivePartEnergyRate hΩ T u g).intervalIntegrable
      (integrable_rawPositivePartEnergyRate hΩ T u g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]







private theorem eventually_memLp_reverseTimeForwardSteklov_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) (a b : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h f) 2
        (volume.restrict (Icc a b)) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
    with h hh
  exact memLp_on_Icc_of_continuous _
    (continuous_reverseTimeForwardSteklov T h hh f) a b

private theorem memLp_restrict_Icc_of_subset
    {E : Type*} [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) {a b : ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) :
    MemLp (f : ℝ → E) 2 (volume.restrict (Icc a b)) := by
  rw [← Measure.restrict_restrict_of_subset hK]
  exact (Lp.memLp f).restrict _



private def forwardSteklovPositivePartEnergy
     (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))‖ ^ 2

private def forwardSteklovPositivePartEnergyRate
     (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (reverseTimeForwardSteklov T h g t)
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))


private theorem abs_forwardSteklovPositivePartEnergyRate_sub_eq
     (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (t : ℝ) :
    |forwardSteklovPositivePartEnergyRate hΩ T h u g t - rawPositivePartEnergyRate hΩ T u g t| =
      2 * |(reverseTimeForwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)) -
          (g t) (h10PositivePart hΩ (u t))| := abs_two_mul_sub _ _

private theorem forwardSteklovPositivePartEnergy_increment
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b s t : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hsmall : h < T - b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    forwardSteklovPositivePartEnergy hΩ T h u t -
        forwardSteklovPositivePartEnergy hΩ T h u s =
      ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
  calc
    _ = 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
        _) :=
      reverseTimeForwardSteklov_positivePart_energy_identity hΩ T hT u g hderiv hh
        (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall])
    _ = ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
      change 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
          _) =
        ∫ r in Icc s t, 2 * (reverseTimeForwardSteklov T h g r)
          _
      rw [integral_const_mul]

private theorem eventually_forwardSteklov_positivePartEnergy_test_identity
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b)
    (hetaDeriv : tsupport eta.deriv ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t
        ∂reverseTimeVolume T) =
      -(∫ t, forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t
        ∂reverseTimeVolume T) := by
  have hK : Icc a b ⊆ Ioo (0) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  have hE : Continuous (forwardSteklovPositivePartEnergy hΩ T h u) := ((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
      (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2
  have hQ : Continuous (forwardSteklovPositivePartEnergyRate hΩ T h u g) := continuous_const.mul
      ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
        ((continuous_h10PositivePart hΩ).comp
          (continuous_reverseTimeForwardSteklov T h hh u)))
  have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      forwardSteklovPositivePartEnergy hΩ T h u t - forwardSteklovPositivePartEnergy hΩ T h u s =
        ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
    intro s hs t ht hst
    exact forwardSteklovPositivePartEnergy_increment hΩ T hT u g hderiv hh ha hsmall
      hs ht hst
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment hab.le hE hQ hinc
    (eta.contDiff.of_le (by simp)) heta

private theorem tendsto_forwardSteklov_positivePartEnergy_test
     {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        rawPositivePartEnergy hΩ T u t * eta.deriv t)) := by
  have hraw : Integrable (rawPositivePartEnergy hΩ T u) (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_rawPositivePartEnergy hΩ T u).restrict
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovPositivePartEnergy hΩ T h u)
        (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact ((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
      (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2 |>.integrableOn_Icc
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let up  := fun t => h10PositivePart hΩ (u t)
  let uhp  := fun h t =>
    h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)
  have huLocal : MemLp u (2) μ := by
    simpa using memLp_restrict_Icc_of_subset T u hK
  have hup : MemLp up (2) μ := by
    apply MemLp.of_le huLocal
    · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
        huLocal.aestronglyMeasurable
    · filter_upwards with r
      exact norm_h10PositivePart_le hΩ _
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h u) (2) μ := by
    simpa using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b
  have huhp : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uhp h) (2) μ := by
    filter_upwards [huh] with h hh
    apply MemLp.of_le hh
    · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
        hh.aestronglyMeasurable
    · filter_upwards with r
      exact norm_h10PositivePart_le hΩ _
  have hUraw := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb
  have hUpos := tendsto_positivePart_sqNorm_integral_of_sqNorm hΩ μ
    _ _
    huLocal huh hUraw
  have hEabs : Tendsto (fun h : ℝ => ∫ r in Icc a b,
      |‖valueCLM hΩ _‖ ^ 2 - ‖valueCLM hΩ _‖ ^ 2|)
      _ _ :=
    tendsto_integral_abs_valueSq_of_sqNorm hΩ μ up uhp hup huhp hUpos
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs

private theorem tendsto_forwardSteklov_positivePartEnergyRate_test
     {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        rawPositivePartEnergyRate hΩ T u g t * eta t)) := by
  have hpair : Integrable (fun t => (g t) (h10PositivePart hΩ (u t)))
      (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_reverseTimeDualPairing_positivePart hΩ T u g).restrict
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovPositivePartEnergyRate hΩ T h u g)
        (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact (continuous_const.mul
      ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
        ((continuous_h10PositivePart hΩ).comp
          (continuous_reverseTimeForwardSteklov T h hh u)))).integrableOn_Icc
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let up  := fun t => h10PositivePart hΩ (u t)
  let uhp  := fun h t =>
    h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)
  have huLocal : MemLp u (2) μ := by
    simpa using memLp_restrict_Icc_of_subset T u hK
  have hgLocal : MemLp g 2 μ := by
    simpa using memLp_restrict_Icc_of_subset T g hK
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h u) (2) μ := by
    simpa using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b
  have hgh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h g) 2 μ := by
    simpa using eventually_memLp_reverseTimeForwardSteklov_on_Icc T g a b
  have hUraw := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb
  have hGraw := tendsto_forwardSteklov_sqNorm_integral_on_Icc T g ha hab.le hb
  have hQabs : Tendsto (fun h : ℝ => ∫ r in Icc a b,
      |(reverseTimeForwardSteklov T h g r) (uhp h r) - (g r) (up r)|)
      _ _ :=
    tendsto_dualPairing_positivePart_of_sqNorm hΩ μ
      _ _
      _
      _
      huLocal hgLocal huh hgh hUraw hGraw
  have hQabs2 : Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |forwardSteklovPositivePartEnergyRate hΩ T h u g t -
        rawPositivePartEnergyRate hΩ T u g t|) (𝓝[>] 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul hQabs using 1
    · funext h
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      exact abs_forwardSteklovPositivePartEnergyRate_sub_eq hΩ T h u g t
    · norm_num
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward (hpair.const_mul 2)
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le hQabs2

private theorem rawPositivePartEnergy_test_deriv
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hforward := eventually_forwardSteklov_positivePartEnergy_test_identity
    hΩ T hT u g hderiv eta ha hab hb heta hetaDeriv
  have hEtest := tendsto_forwardSteklov_positivePartEnergy_test
    hΩ T u eta ha hab hb hK
  have hQtest := tendsto_forwardSteklov_positivePartEnergyRate_test
    hΩ T u g eta ha hab hb hK
  have hforwardIcc : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t) =
        -(∫ t in Icc a b,
          forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t) := by
    filter_upwards [hforward] with h hh
    rw [← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
      ← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
    exact hh
  have hConst : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, rawPositivePartEnergy hΩ T u t * eta.deriv t) +
        ∫ t in Icc a b, rawPositivePartEnergyRate hΩ T u g t * eta t)) := by
    apply (hEtest.add hQtest).congr'
    filter_upwards [hforwardIcc] with h hh
    exact (eq_neg_iff_add_eq_zero).mp hh
  have hzeroIcc  :=
    tendsto_nhds_unique hConst tendsto_const_nhds
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  linarith

private theorem integrable_reverseTimePositivePartEnergyPrimitive
     :
    Integrable (reverseTimePositivePartEnergyPrimitive hΩ T u g) (reverseTimeVolume T) := (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self


private theorem reverseTimePositivePartEnergyPrimitive_test_deriv
     :
    (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  have hrate := integrable_rawPositivePartEnergyRate hΩ T u g
  have hrateIcc : IntegrableOn (rawPositivePartEnergyRate hΩ T u g) (Icc (0) T) volume := by
    change Integrable _ _
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] using hrate
  have hae : (fun t => reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t) =ᵐ[
      reverseTimeVolume T] fun t =>
        PDE.intervalPrimitive 0 (rawPositivePartEnergyRate hΩ T u g) t * _root_.deriv eta t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) *
        eta.deriv t = _
    rw [show (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) =
        ∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂volume by
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        Measure.restrict_restrict measurableSet_Ioc]
      rw [inter_eq_left.mpr]
      intro r hr
      exact ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩,
      (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
      PDE.intervalPrimitive]
  calc
    (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
        ∫ t, PDE.intervalPrimitive 0 _ t * _root_.deriv eta t
          ∂reverseTimeVolume T := integral_congr_ae hae
    _ = -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo hrateIcc
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

private theorem exists_continuous_reverseTimePositivePartEnergyRepresentative_raw
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u ∧
      ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  let defect  := fun t =>
    rawPositivePartEnergy hΩ T u t - reverseTimePositivePartEnergyPrimitive hΩ T u g t
  have hdefInt : Integrable defect _ :=
    (integrable_rawPositivePartEnergy hΩ T u).sub
      (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g)
  have hdefZero : ∀ eta : ReverseTimeScalarTest T,
      (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) = 0 := by
    intro eta
    have hrawInt := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_rawPositivePartEnergy hΩ T u) eta
    have hprimInt := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g) eta
    rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
        (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) -
          ∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
            ∂reverseTimeVolume T by
      rw [← integral_sub hrawInt hprimInt]
      apply integral_congr_ae
      filter_upwards with t
      ring,
      rawPositivePartEnergy_test_deriv hΩ T hT u g hderiv,
      reverseTimePositivePartEnergyPrimitive_test_deriv]
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt hdefZero
  let e  := fun t => reverseTimePositivePartEnergyPrimitive hΩ T u g t + c
  have heCont : ContinuousOn e _ :=
    (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).add continuousOn_const
  have heAE : e =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u := by
    filter_upwards [hc] with t ht
    linarith
  have heNonneg : ∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t := by
    have heIcc  := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heAE
    have hmaxAE : e =ᵐ[volume.restrict (Icc (0) T)] fun t => max (e t) 0 := by
      filter_upwards [heIcc] with t ht
      rw [ht]
      simp only [rawPositivePartEnergy, max_eq_left (sq_nonneg _)]
    have hmaxCont : ContinuousOn (fun t => max (e t) 0) (Icc 0 T) := heCont.sup continuousOn_const
    have heEqOn := Measure.eqOn_Icc_of_ae_eq volume hT.ne hmaxAE heCont hmaxCont
    intro t ht
    rw [heEqOn ht]
    exact le_max_right _ _
  refine ⟨e, heCont, heNonneg, heAE, ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = reverseTimePositivePartEnergyPrimitive hΩ T u g t -
        reverseTimePositivePartEnergyPrimitive hΩ T u g s := by
          ring
    _ = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T :=
      reverseTimePositivePartEnergyPrimitive_sub hΩ T u g hs ht hst

/-- A continuous scalar reverse-time energy representative of a Gelfand weak
derivative on the closed reverse-time interval. -/
theorem exists_continuous_reverseTimePositivePartEnergyRepresentative
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T]
        (fun t => ‖valueCLM hΩ (h10PositivePart hΩ (u t))‖ ^ 2) ∧
      ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
        e t - e s =
          2 * (∫ r in Set.Ioc s t,
            (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heNonneg, heAE, heSub⟩ :=
    exists_continuous_reverseTimePositivePartEnergyRepresentative_raw hΩ T hT u g hderiv
  refine ⟨e, heCont, heNonneg, ?_, ?_⟩
  · exact heAE
  · intro s t hs ht hst
    rw [heSub s t hs ht hst]
    simp only [rawPositivePartEnergyRate, integral_const_mul]

/-- Positive-part energy increment for the canonical closed-time Hilbert representative. -/
theorem reverseTimeHilbertRepresentative_posPart_norm_sq_increment
    
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    ‖MeasureTheory.Lp.posPart
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩)‖ ^ 2 -
      ‖MeasureTheory.Lp.posPart
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩)‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t,
        (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, _heNonneg, heAE, heInc⟩ :=
    exists_continuous_reverseTimePositivePartEnergyRepresentative hΩ T hT u g hderiv
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let E  := fun r => if hr : r ∈ Icc 0 T then
    ‖MeasureTheory.Lp.posPart (Ubar ⟨r, hr⟩)‖ ^ 2 else 0
  have hECont : ContinuousOn E (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict E = fun r =>
        ‖MeasureTheory.Lp.posPart (Ubar r)‖ ^ 2 := by
      funext r
      simp only [Set.domRestrict_apply, E, dif_pos r.2]
    rw [hEq]
    exact (continuous_norm.comp
      (MeasureTheory.Lp.continuous_posPart.comp Ubar.continuous)).pow 2
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by
    have hrep'  := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hrep
    have he'  := by
      have heRaw  := heAE
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heRaw
    have hi : ∀ᵐ r ∂volume.restrict (Icc 0 T), r ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hrep', he', hi] with r hU he hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
    change (if h : r ∈ Icc 0 T then ‖MeasureTheory.Lp.posPart _‖ ^ 2
      else 0) = e r
    rw [dif_pos hr', hU hr, ← valueCLM_h10PositivePart]
    exact he.symm
  have hEqOn : EqOn E e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE hECont heCont
  calc
    _ = E t - E s := by
      dsimp only [E]
      rw [dif_pos, dif_pos]
    _ = e t - e s := congrArg₂ _ (hEqOn ht) (hEqOn hs)
    _ = _ := heInc s t hs ht hst

end HypoellipticAleksandrov.Parabolic.Dirichlet
