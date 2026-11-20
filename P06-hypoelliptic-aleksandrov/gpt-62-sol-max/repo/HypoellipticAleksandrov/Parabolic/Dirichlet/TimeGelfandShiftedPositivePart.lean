module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarIncrement

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePartSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeShiftedPositivePartConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartValueContinuity

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

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

private noncomputable def rawShiftedPositivePartEnergy (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) : ℝ → ℝ :=
  shiftedPositivePartEnergy hΩ M N u

private noncomputable def rawShiftedPositivePartEnergyRate
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ → ℝ :=
  fun t => 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

private theorem integrable_rawShiftedPositivePartEnergy (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    Integrable (rawShiftedPositivePartEnergy hΩ M N u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (h10ShiftedPositivePart hΩ (u t)
      (reverseTimeAffineThreshold M N t))) 2 (reverseTimeVolume T) :=
    memLp_congr_ae (by
      filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t ht
      exact congrArg (valueCLM hΩ) ht) |>.mp
      ((Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).continuousLinearMap_comp
        (valueCLM hΩ))
  unfold rawShiftedPositivePartEnergy shiftedPositivePartEnergy
  exact hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

section
variable (hΩbounded : Bornology.IsBounded Ω) (T : ℝ)

private theorem integrable_rawShiftedPositivePartEnergyRate (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (reverseTimeVolume T) := by
  have hp := integrable_reverseTimeDualPairing_shiftedPositivePart hΩ T M N u g
  have hm := integrable_reverseTimeShiftedPositivePart_spatialMass
    hΩ hΩbounded T M N u
  unfold rawShiftedPositivePartEnergyRate
  apply Integrable.const_mul
  unfold shiftedPositivePartEnergyRate
  apply (hp.sub (hm.const_mul (N : ℝ))).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  rw [spatialMassCLM_apply]

private theorem eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N
          (fun r => reverseTimeForwardSteklov T h u r) t * eta.deriv t) =
      -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  let x := fun r => reverseTimeForwardSteklov T h u r
  let y := fun r => reverseTimeForwardSteklov T h g r
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  have hQ : Continuous (fun r => 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N x y r) := by
    exact continuous_const.mul
      (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
        (continuous_const.mul
          (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp)))
  have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      shiftedPositivePartEnergy hΩ M N x t - shiftedPositivePartEnergy hΩ M N x s =
        ∫ r in Icc s t, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N x y r := by
    intro s hs t ht hst
    rw [reverseTimeForwardSteklov_shiftedPositivePart_energy_identity hΩ hΩbounded T hT
      M N u g hderiv hh (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall]),
      integral_const_mul]
  exact integral_mul_deriv_eq_neg_integral_of_increment_Icc hab.le hQ.integrableOn_Icc hinc
    (eta.contDiff.of_le (by simp)) heta

end

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (T : ℝ)
  (hT : 0 < T) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
include hT hderiv

private theorem rawShiftedPositivePartEnergy_test_deriv
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_reverseTimeScalarTest_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hid := eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
    hΩ hΩbounded T hT M N u g hderiv eta ha hab hb heta
  have hE := tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    hΩ M N T u eta ha hab hb
  have hQ := tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    hΩ hΩbounded M N T u g eta ha hab hb
  have hzero : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N u t * eta.deriv t) +
        2 * ∫ t in Icc a b,
          shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t)) := by
    apply (hE.add (tendsto_const_nhds.mul hQ)).congr'
    filter_upwards [hid] with h hh
    have hfactor : (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun r => reverseTimeForwardSteklov T h u r)
        (fun r => reverseTimeForwardSteklov T h g r) t * eta t) =
        2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [hfactor] at hh
    exact (eq_neg_iff_add_eq_zero).mp hh
  have hz := tendsto_nhds_unique hzero tendsto_const_nhds
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
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

private theorem exists_continuous_shiftedPositivePartEnergyRepresentative :
    ∃ e : ℝ → ℝ, ContinuousOn e (Icc 0 T) ∧
      e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u ∧
      ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T :=
  exists_continuous_reverseTime_representative_of_weakDeriv hT
    (integrable_rawShiftedPositivePartEnergy hΩ T M N u)
    (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g)
    (rawShiftedPositivePartEnergy_test_deriv hΩ hΩbounded T hT M N u g hderiv)

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
  let E : ℝ → ℝ := fun r => if hr : r ∈ Icc 0 T then
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, hr⟩)‖ ^ 2
    else 0
  have hECont : ContinuousOn E (Icc 0 T) := by
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
            continuous_subtype_val)))).pow 2
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by
    have hrep' : ∀ᵐ r ∂volume.restrict (Icc 0 T),
        ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc, IntegrableOn] using hrep
    have he' : e =ᵐ[volume.restrict (Icc 0 T)]
        rawShiftedPositivePartEnergy hΩ M N u := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heAE
    have hi : ∀ᵐ r ∂volume.restrict (Icc 0 T), r ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hrep', he', hi] with r hU he hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
    change (if h : r ∈ Icc 0 T then
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, h⟩)‖ ^ 2
      else 0) = e r
    rw [dif_pos hr', hU hr, ← valueCLM_h10ShiftedPositivePart]
    exact he.symm
  have hEqOn :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE hECont heCont
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

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
