module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePartSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeShiftedPositivePartConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartValueContinuity
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy

open private HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
open private HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy


/-!
# Shifted-positive-part reverse-time energy increments

This module proves the moving affine-threshold energy identity for the
canonical closed-time Hilbert representative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private def rawShiftedPositivePartEnergy
     (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) : ℝ → ℝ :=
  shiftedPositivePartEnergy hΩ M N u

variable (hΩbounded : Bornology.IsBounded Ω)

private def rawShiftedPositivePartEnergyRate

     (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ → ℝ :=
  fun t => 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t

private def reverseTimeShiftedPositivePartEnergyPrimitive

     (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Ioc 0 t,
    rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T

private theorem integrable_rawShiftedPositivePartEnergy
     (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    Integrable (rawShiftedPositivePartEnergy hΩ M N u) (reverseTimeVolume T) := (id
  (id
    (MemLp.integrable_norm_pow
      ((memLp_congr_ae
            (mp_mem (coeFn_reverseTimeShiftedPositivePart hΩ T M N u)
              (univ_mem' (id fun t ht => congrArg (⇑(valueCLM hΩ)) ht)))).mp
        (MemLp.continuousLinearMap_comp (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)) (valueCLM hΩ)))
      (Mathlib.Meta.NormNum.isNat_eq_false (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2))
        (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 0)) (Eq.refl false)))))

variable (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)

private theorem integrable_rawShiftedPositivePartEnergyRate

     :
    Integrable (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (reverseTimeVolume T) := by

  have hm := integrable_reverseTimeShiftedPositivePart_spatialMass
    hΩ hΩbounded T M N u
  unfold rawShiftedPositivePartEnergyRate
  apply Integrable.const_mul
  unfold shiftedPositivePartEnergyRate
  apply ((integrable_reverseTimeDualPairing_shiftedPositivePart hΩ T M N u g).sub (hm.const_mul (N : ℝ))).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  rw [spatialMassCLM_apply]

private theorem continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive

     :
    ContinuousOn (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).integrableOn

private theorem reverseTimeShiftedPositivePartEnergyPrimitive_sub


    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t -
        reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g s =
      ∫ r in Ioc s t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
        ∂reverseTimeVolume T := by
  change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) -
      (∫ r in Ioc 0 s, _ ∂reverseTimeVolume T) = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]







private theorem integral_energy_mul_deriv_eq_neg_integral_rate_of_increment
    {a b : ℝ} {E Q : ℝ → ℝ} (hab : a ≤ b)
    (hQ : Continuous Q)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      E t - E s = ∫ r in Icc s t, Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, E t * deriv eta t) = -(∫ t in Icc a b, Q t * eta t) := by
  let sharedTerm_af342da220 := (∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t)
  have hQIcc : IntegrableOn Q (Icc a b)  := hQ.integrableOn_Icc
  have hEformula : ∀ t ∈ Icc a b, E t = PDE.intervalPrimitive a Q t + E a := by
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    calc
      E t = (∫ r in Icc a t, Q r) + E a := by linarith
      _ = PDE.intervalPrimitive a Q t + E a := by
        rw [PDE.intervalPrimitive_eq_setIntegral_Icc ht.1]
  rw [show (∫ t in Icc a b, E t * deriv eta t) =
      sharedTerm_af342da220 by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hEformula t ht]]
  calc
    (sharedTerm_af342da220) =
        (∫ t in Icc a b, PDE.intervalPrimitive a Q t * deriv eta t) +
          ∫ t in Icc a b, E a * deriv eta t := by
      rw [← integral_add]
      · apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        ring
      · exact ((PDE.continuousOn_intervalPrimitive hab hQIcc).mul
          (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
      · exact (heta.continuous_deriv (by simp)).integrableOn_Icc.const_mul (E a)
    _ = -(∫ t in Icc a b, Q t * eta t) := by
      rw [PDE.intervalPrimitive_scalar_weak_identity_Icc hQIcc heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab]
        have ha  := image_eq_zero_of_notMem_tsupport
          (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1)
        have hb  := image_eq_zero_of_notMem_tsupport
          (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2)
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (T : ℝ)

section
variable (hT : 0 < T) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (eta : ReverseTimeScalarTest T)

include hderiv
private theorem eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
      {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N
          ((reverseTimeForwardSteklov T h u)) t * eta.deriv t) =
      -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
          ((reverseTimeForwardSteklov T h u))
          ((reverseTimeForwardSteklov T h g)) t * eta t) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  let x := (reverseTimeForwardSteklov T h u)
  let y := (reverseTimeForwardSteklov T h g)
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)


  exact integral_energy_mul_deriv_eq_neg_integral_rate_of_increment hab.le (show _ by
      exact continuous_const.mul
        (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
          (continuous_const.mul
            (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp)))) (show _ by
      intro s hs t ht hst
      rw [reverseTimeForwardSteklov_shiftedPositivePart_energy_identity hΩ hΩbounded T hT
        M N u g hderiv hh (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall]),
        integral_const_mul])
    (eta.contDiff.of_le (by simp)) heta

private theorem rawShiftedPositivePartEnergy_test_deriv
      :
    (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 ) T := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hid := eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
    hΩ hΩbounded T hT M N u g hderiv eta ha hab hb heta
  have hE := tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    hΩ M N T u eta ha hab hb
  have hQ := tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    hΩ hΩbounded M N T u g eta ha hab hb

  have hz := tendsto_nhds_unique (by
      apply (hE.add (tendsto_const_nhds.mul hQ)).congr'
      filter_upwards [hid] with h hh
      have hfactor : (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
          ((reverseTimeForwardSteklov T h u))
          ((reverseTimeForwardSteklov T h g)) t * eta t) =
          2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩbounded M N
            ((reverseTimeForwardSteklov T h u))
            ((reverseTimeForwardSteklov T h g)) t * eta t := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with r
        ring
      rw [hfactor] at hh
      exact (eq_neg_iff_add_eq_zero).mp hh) tendsto_const_nhds
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  change _ = -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
    hΩ hΩbounded M N u g t * eta t)
  rw [show (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N u g t * eta t) =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate
        hΩ hΩbounded M N u g t * eta t by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    ring]
  exact (eq_neg_iff_add_eq_zero).mpr hz
end


private theorem integrable_reverseTimeShiftedPositivePartEnergyPrimitive
     (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (reverseTimeVolume T) := (id
  (IntegrableOn.mono_set
    (ContinuousOn.integrableOn_Icc (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g))
    Ioo_subset_Icc_self))




variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (T : ℝ)

private theorem reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv
     (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t *
      eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by



  calc
    _ = ∫ t, PDE.intervalPrimitive 0
        (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g) t * deriv eta t
        ∂reverseTimeVolume T := integral_congr_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
            change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) * eta.deriv t = _
            rw [show (∫ r in Ioc 0 t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
                ∂reverseTimeVolume T) = ∫ r in Ioc 0 t,
                  rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r by
              simp only [reverseTimeVolume, reverseTimeOpenInterval,
                Measure.restrict_restrict measurableSet_Ioc]
              rw [inter_eq_left.mpr]
              intro r hr'
              exact ⟨hr'.1, lt_of_le_of_lt hr'.2 ht.2⟩,
              (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
              PDE.intervalPrimitive])
    _ = _ := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo (by
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc, IntegrableOn] using (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g))
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

variable (hT : 0 < T) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

include hderiv in
private theorem exists_continuous_shiftedPositivePartEnergyRepresentative
      :
    ∃ e : ℝ → ℝ, ContinuousOn e (Icc 0 T) ∧
      e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u ∧
      ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T := by
  let P := reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g
  let defect := fun t => rawShiftedPositivePartEnergy hΩ M N u t - P t
  have hdefInt : Integrable defect (reverseTimeVolume T) :=
    (integrable_rawShiftedPositivePartEnergy hΩ T M N u).sub
      (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g)

  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt (by
      intro eta
      have hraw := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv
        (integrable_rawShiftedPositivePartEnergy hΩ T M N u) eta
      have hprim := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_mul_reverseTimeScalarTest_deriv
        (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g) eta
      rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
          (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
            ∂reverseTimeVolume T) -
          ∫ t, P t * eta.deriv t ∂reverseTimeVolume T by
        rw [← integral_sub hraw hprim]
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [defect]
        ring,
        rawShiftedPositivePartEnergy_test_deriv hΩ hΩbounded T hT M N u g hderiv eta,
        reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv hΩ hΩbounded T M N u g eta]
      ring)
  let e := fun t => P t + c
  have heCont : ContinuousOn e (Icc 0 T) :=
    (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g).add continuousOn_const

  refine ⟨e, heCont, (by
      filter_upwards [hc] with t ht
      dsimp only [defect, e] at ht ⊢
      linarith), ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = P t - P s := by dsimp only [e]; ring
    _ = _ := reverseTimeShiftedPositivePartEnergyPrimitive_sub
      hΩ hΩbounded T M N u g hs ht hst

/-- Moving-threshold shifted-positive-part energy increment for the canonical
closed-time Hilbert representative. -/
theorem reverseTimeHilbertRepresentative_shiftedPositivePart_norm_sq_increment

    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩)‖ ^ 2 -
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩)‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t,
        ((g r) (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r)) -
          (N : ℝ) * spatialMassCLM hΩbounded
            (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
              (reverseTimeAffineThreshold M N r))))
        ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heAE, heInc⟩ :=
    exists_continuous_shiftedPositivePartEnergyRepresentative
      hΩ hΩbounded T hT M N u g hderiv
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let E  := fun r => if hr : r ∈ Icc 0 T then
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, hr⟩)‖ ^ 2
    else 0

  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1

  have hEqOn : EqOn E e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne (by



        filter_upwards [(show ∀ᵐ r ∂volume.restrict (Icc 0 T),
            ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) by
            simpa only [Ubar, reverseTimeVolume, reverseTimeOpenInterval,
              ReverseTimeHilbertRepresentativeAgrees, restrict_Ioo_eq_restrict_Icc] using hrep), (show e =ᵐ[volume.restrict (Icc 0 T)]
            rawShiftedPositivePartEnergy hΩ M N u by
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc] using heAE), (by
            rw [← restrict_Ioo_eq_restrict_Icc]
            exact ae_restrict_mem measurableSet_Ioo)] with r hU he hr

        change (if h : r ∈ Icc 0 T then
          ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, h⟩)‖ ^ 2
          else 0) = e r
        rw [dif_pos (⟨hr.1.le, hr.2.le⟩), hU hr, ← valueCLM_h10ShiftedPositivePart]
        exact he.symm) (by
        rw [continuousOn_iff_continuous_domRestrict]
        have hEq : (Icc 0 T).domRestrict E = fun r : (Icc 0 T) =>
            ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N (r : ℝ))
              (Ubar r)‖ ^ 2 := by
          funext r
          simp only [Set.domRestrict_apply, E, dif_pos r.2]
        rw [hEq]
        exact (continuous_norm.comp
          ((continuous_shiftedPositivePartValue_of_isBounded hΩbounded).comp
            (Ubar.continuous.prodMk
              ((continuous_const.add (continuous_real_toNNReal.mul continuous_const)).comp
                continuous_subtype_val)))).pow 2) heCont
  calc
    _ = E t - E s := by
      change ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t) (Ubar ⟨t, ht⟩)‖ ^ 2 -
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s) (Ubar ⟨s, hs⟩)‖ ^ 2 = _
      dsimp only [E]
      rw [dif_pos ht, dif_pos hs]
    _ = e t - e s := congrArg₂ (· - ·) (hEqOn ht) (hEqOn hs)
    _ = _ := by
      rw [heInc s t hs ht hst]
      simp only [rawShiftedPositivePartEnergyRate, shiftedPositivePartEnergyRate,
        integral_const_mul]

end HypoellipticAleksandrov.Parabolic.Dirichlet
