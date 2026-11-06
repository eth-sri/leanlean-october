module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePartSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing

open private HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_integral_abs_valueSq_of_sqNorm from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_integral_mul_of_tendsto_integral_abs from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_sqNorm_valueCLM_sub_le from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_sq_sub_le_of_bounds from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
open private HypoellipticAleksandrov.Parabolic.Dirichlet.abs_two_mul_sub from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy


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

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)

private def rawPositivePartEnergy
     : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (h10PositivePart hΩ (u t))‖ ^ 2

variable (g : ReverseTimeL2VStar hΩ T)

private def rawPositivePartEnergyRate
      : ℝ → ℝ :=
  fun t => 2 * (g t) (h10PositivePart hΩ (u t))

private def reverseTimePositivePartEnergyPrimitive
      : ℝ → ℝ :=
  fun t => ∫ r in Set.Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T

private theorem integrable_rawPositivePartEnergy
     :
    Integrable (rawPositivePartEnergy hΩ T u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (h10PositivePart hΩ (u t))) 2
      (reverseTimeVolume T) :=
    memLp_congr_ae (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
        exact congrArg (valueCLM hΩ) ht) |>.mp
      ((MeasureTheory.Lp.memLp (reverseTimePositivePart hΩ T u)).continuousLinearMap_comp
        (valueCLM hΩ))
  exact hu.integrable_norm_pow (by norm_num : (2 ) ≠ 0)

variable (g : ReverseTimeL2VStar hΩ T)

private theorem integrable_rawPositivePartEnergyRate
      :
    Integrable (rawPositivePartEnergyRate hΩ T u g) (reverseTimeVolume T) := ((integrable_reverseTimeDualPairing hΩ T
    (reverseTimePositivePart hΩ T u) g).const_mul 2).congr (by
      filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
      simp only [rawPositivePartEnergyRate]
      rw [ht])

private theorem continuousOn_reverseTimePositivePartEnergyPrimitive
      :
    ContinuousOn (reverseTimePositivePartEnergyPrimitive hΩ T u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
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
















variable {E : Type*}




private theorem eventually_memLp_reverseTimeForwardSteklov_on_Icc
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) (a b : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h f) 2
        (volume.restrict (Icc a b)) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
    with h hh
  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.memLp_on_Icc_of_continuous _
    (continuous_reverseTimeForwardSteklov T h hh f) a b

private theorem memLp_restrict_Icc_of_subset
     [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) {a b : ℝ}
    (hK : Icc a b ⊆ Ioo (0 ) T) :
    MemLp (f : ℝ → E) 2 (volume.restrict (Icc a b)) := by
  dsimp only [reverseTimeVolume, reverseTimeOpenInterval]
  rw [← Measure.restrict_restrict_of_subset hK]
  exact (Lp.memLp f).restrict _







variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T h : ℝ) (u : ReverseTimeL2V hΩ T)

private def forwardSteklovPositivePartEnergy
     : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))‖ ^ 2

private def forwardSteklovPositivePartEnergyRate
     (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (reverseTimeForwardSteklov T h g t)
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))




variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private theorem abs_forwardSteklovPositivePartEnergyRate_sub_eq
     (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (t : ℝ) :
    |forwardSteklovPositivePartEnergyRate hΩ T h u g t - rawPositivePartEnergyRate hΩ T u g t| =
      2 * |(reverseTimeForwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)) -
          (g t) (h10PositivePart hΩ (u t))| := by
  change |2 * (reverseTimeForwardSteklov T h g t)
      (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)) -
        2 * (g t) (h10PositivePart hΩ (u t))| = _
  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.abs_two_mul_sub _ _

variable (T : ℝ)

section
variable (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv
private theorem forwardSteklovPositivePartEnergy_increment

    {h a b s t : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hsmall : h < T - b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    forwardSteklovPositivePartEnergy hΩ T h u t -
        forwardSteklovPositivePartEnergy hΩ T h u s =
      ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
  change ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))‖ ^ 2 -
      ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u s))‖ ^ 2 = _
  calc
    _ = 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))) :=
      reverseTimeForwardSteklov_positivePart_energy_identity hΩ T hT u g hderiv hh
        (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall])
    _ = ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
      change 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
          (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))) =
        ∫ r in Icc s t, 2 * (reverseTimeForwardSteklov T h g r)
          (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))
      rw [integral_const_mul]

private theorem eventually_forwardSteklov_positivePartEnergy_test_identity

    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b)
    (hetaDeriv : tsupport eta.deriv ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t
        ∂reverseTimeVolume T) =
      -(∫ t, forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t
        ∂reverseTimeVolume T) := by
  have hK : Icc a b ⊆ Ioo (0 ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall



  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment hab.le (((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
        (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2) (continuous_const.mul
        ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
          ((continuous_h10PositivePart hΩ).comp
            (continuous_reverseTimeForwardSteklov T h hh u)))) (by
      intro s hs t ht hst
      exact forwardSteklovPositivePartEnergy_increment hΩ T hT u g hderiv hh ha hsmall
        hs ht hst)
    (eta.contDiff.of_le (by simp)) heta
end


variable (u : ReverseTimeL2V hΩ T)

private theorem tendsto_forwardSteklov_positivePartEnergy_test

     (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hK : Icc a b ⊆ Ioo (0 ) T) :
    Tendsto (fun h  => ∫ t in Icc a b,
      forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        rawPositivePartEnergy hΩ T u t * eta.deriv t)) := by


  let μ : Measure ℝ := volume.restrict (Icc a b)

  let uhp  := fun h t =>
    h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)
  have huLocal : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 ) μ := by
    simpa only [μ] using memLp_restrict_Icc_of_subset T u hK

  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h u) (2 ) μ := by
    simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b


  have hUpos := tendsto_positivePart_sqNorm_integral_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (fun h r => reverseTimeForwardSteklov T h u r)
    huLocal huh (tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb)

  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_integral_mul_of_tendsto_integral_abs (by
      filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
        with h hh
      exact ((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
        (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2 |>.integrableOn_Icc) (by
      rw [← Measure.restrict_restrict_of_subset hK]
      exact (integrable_rawPositivePartEnergy hΩ T u).restrict)
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_integral_abs_valueSq_of_sqNorm hΩ μ (fun t => h10PositivePart hΩ (u t)) uhp (by
        apply MemLp.of_le huLocal
        · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
            huLocal.aestronglyMeasurable
        · filter_upwards with r
          exact norm_h10PositivePart_le hΩ _) (by
        filter_upwards [huh] with h hh
        apply MemLp.of_le hh
        · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
            hh.aestronglyMeasurable
        · filter_upwards with r
          exact norm_h10PositivePart_le hΩ _) hUpos)

private theorem tendsto_forwardSteklov_positivePartEnergyRate_test

     (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hK : Icc a b ⊆ Ioo (0 ) T) :
    Tendsto (fun h  => ∫ t in Icc a b,
      forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        rawPositivePartEnergyRate hΩ T u g t * eta t)) := by


  let μ : Measure ℝ := volume.restrict (Icc a b)

  let uhp  := fun h t =>
    h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)






  have hQabs : Tendsto (fun h  => ∫ r in Icc a b,
      |(reverseTimeForwardSteklov T h g r) (uhp h r) - (g r) ((fun t => h10PositivePart hΩ (u t)) r)|)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_dualPairing_positivePart_of_sqNorm hΩ μ
      (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
      (fun h r => reverseTimeForwardSteklov T h u r)
      (fun h r => reverseTimeForwardSteklov T h g r)
      (by
          simpa only [μ] using memLp_restrict_Icc_of_subset T u hK) (by
          simpa only [μ] using memLp_restrict_Icc_of_subset T g hK) (by
          simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b) (by
          simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T g a b) (tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb) (tendsto_forwardSteklov_sqNorm_integral_on_Icc T g ha hab.le hb)

  exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_integral_mul_of_tendsto_integral_abs (by
      filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
        with h hh
      exact (continuous_const.mul
        ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
          ((continuous_h10PositivePart hΩ).comp
            (continuous_reverseTimeForwardSteklov T h hh u)))).integrableOn_Icc) ((show Integrable (fun t => (g t) (h10PositivePart hΩ (u t)))
      (volume.restrict (Icc a b)) by
                dsimp only [reverseTimeVolume, reverseTimeOpenInterval]
                rw [← Measure.restrict_restrict_of_subset hK]
                exact (integrable_reverseTimeDualPairing_positivePart hΩ T u g).restrict).const_mul 2)
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le (by
        convert tendsto_const_nhds.mul hQabs using 1
        · funext h
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          exact abs_forwardSteklovPositivePartEnergyRate_sub_eq hΩ T h u g t
        · norm_num)

private theorem rawPositivePartEnergy_test_deriv
      (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hforward := eventually_forwardSteklov_positivePartEnergy_test_identity
    hΩ T hT u g hderiv eta ha hab hb heta hetaDeriv
  have hEtest := tendsto_forwardSteklov_positivePartEnergy_test
    hΩ T u eta ha hab hb hK
  have hQtest := tendsto_forwardSteklov_positivePartEnergyRate_test
    hΩ T u g eta ha hab hb hK


  have hzeroIcc  :=
    tendsto_nhds_unique (by
        apply (hEtest.add hQtest).congr'
        filter_upwards [(show ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t) =
        -(∫ t in Icc a b,
          forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t) by
            filter_upwards [hforward] with h hh
            rw [← _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
              ← _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
            exact hh)] with h hh
        exact (eq_neg_iff_add_eq_zero).mp hh) tendsto_const_nhds
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact (eq_neg_iff_add_eq_zero).mpr hzeroIcc

private theorem integrable_reverseTimePositivePartEnergyPrimitive

    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (reverseTimePositivePartEnergyPrimitive hΩ T u g) (reverseTimeVolume T) := by
  change IntegrableOn (reverseTimePositivePartEnergyPrimitive hΩ T u g) (Ioo (0 ) T)
  exact (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self




variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ)

private theorem reverseTimePositivePartEnergyPrimitive_test_deriv

    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by



  calc
    (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
        ∫ t, PDE.intervalPrimitive 0 (rawPositivePartEnergyRate hΩ T u g) t * _root_.deriv eta t
          ∂reverseTimeVolume T := integral_congr_ae (by
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
              change (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) *
                  eta.deriv t = _
              rw [show (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) =
                  ∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r by
                simp only [reverseTimeVolume, reverseTimeOpenInterval,
                  Measure.restrict_restrict measurableSet_Ioc]
                rw [inter_eq_left.mpr]
                intro r hr
                exact ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩,
                (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
                PDE.intervalPrimitive])
    _ = -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo (by
            change Integrable (rawPositivePartEnergyRate hΩ T u g) (volume.restrict (Icc (0 ) T))
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc] using (integrable_rawPositivePartEnergyRate hΩ T u g))
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

variable (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv in
private theorem exists_continuous_reverseTimePositivePartEnergyRepresentative_raw
      :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t) ∧
      (e) =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u ∧
      ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  let defect  := fun t =>
    rawPositivePartEnergy hΩ T u t - reverseTimePositivePartEnergyPrimitive hΩ T u g t
  have hdefInt : Integrable defect (reverseTimeVolume T) :=
    (integrable_rawPositivePartEnergy hΩ T u).sub
      (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g)

  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt (show _ by
      intro eta
      have hrawInt := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv
        (integrable_rawPositivePartEnergy hΩ T u) eta
      have hprimInt := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv
        (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g) eta
      rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
          (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) -
            ∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
              ∂reverseTimeVolume T by
        rw [← integral_sub hrawInt hprimInt]
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [defect]
        ring,
        rawPositivePartEnergy_test_deriv hΩ T hT u g hderiv eta,
        reverseTimePositivePartEnergyPrimitive_test_deriv hΩ T u g eta]
      ring)
  let e  := fun t => reverseTimePositivePartEnergyPrimitive hΩ T u g t + c
  have heCont : ContinuousOn e (Icc 0 T) :=
    (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).add continuousOn_const
  have heAE : e =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u := by
    filter_upwards [hc] with t ht
    dsimp only [defect] at ht
    dsimp only [e]
    linarith
  have heNonneg : ∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t := by




    intro t ht
    rw [(Measure.eqOn_Icc_of_ae_eq volume hT.ne (by
        filter_upwards [(show e =ᵐ[volume.restrict (Icc (0 : ℝ) T)] rawPositivePartEnergy hΩ T u by
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc] using heAE)] with t ht
        rw [ht]
        simp only [rawPositivePartEnergy, max_eq_left (sq_nonneg _)]) heCont (show ContinuousOn (fun t => max (e t) 0) (Icc 0 T) by
        exact heCont.sup continuousOn_const)) ht]
    exact le_max_right _ _
  refine ⟨e, heCont, heNonneg, heAE, ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = reverseTimePositivePartEnergyPrimitive hΩ T u g t -
        reverseTimePositivePartEnergyPrimitive hΩ T u g s := by
          dsimp only [e]
          ring
    _ = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T :=
      reverseTimePositivePartEnergyPrimitive_sub hΩ T u g hs ht hst

include hderiv in
/-- A continuous scalar reverse-time energy representative of a Gelfand weak
derivative on the closed reverse-time interval. -/
theorem exists_continuous_reverseTimePositivePartEnergyRepresentative
      :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ e t) ∧
      (e) =ᵐ[reverseTimeVolume T]
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

  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by



    filter_upwards [(show ∀ᵐ r ∂volume.restrict (Icc 0 T),
        ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) by
        simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
          reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hrep), (show e =ᵐ[volume.restrict (Icc 0 T)] rawPositivePartEnergy hΩ T u by

        simpa only [reverseTimeVolume, reverseTimeOpenInterval,
          restrict_Ioo_eq_restrict_Icc] using (show e =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u from heAE)), (by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact ae_restrict_mem measurableSet_Ioo)] with r hU he hr

    change (if h : r ∈ Icc 0 T then ‖MeasureTheory.Lp.posPart (Ubar ⟨r, h⟩)‖ ^ 2
      else 0) = e r
    rw [dif_pos (⟨hr.1.le, hr.2.le⟩), hU hr, ← valueCLM_h10PositivePart]
    exact he.symm
  have hEqOn : EqOn E e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE (by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Icc 0 T).domRestrict E = fun r =>
            ‖MeasureTheory.Lp.posPart (Ubar r)‖ ^ 2 := by
          funext r
          simp only [Set.domRestrict_apply, E, dif_pos r.2]
        rw [hEq]
        exact (continuous_norm.comp
          (MeasureTheory.Lp.continuous_posPart.comp Ubar.continuous)).pow 2) heCont
  calc
    _ = E t - E s := by
      change ‖MeasureTheory.Lp.posPart (Ubar ⟨t, ht⟩)‖ ^ 2 -
        ‖MeasureTheory.Lp.posPart (Ubar ⟨s, hs⟩)‖ ^ 2 = _
      dsimp only [E]
      rw [dif_pos ht, dif_pos hs]
    _ = e t - e s := congrArg₂ (· - ·) (hEqOn ht) (hEqOn hs)
    _ = _ := heInc s t hs ht hst

end HypoellipticAleksandrov.Parabolic.Dirichlet
