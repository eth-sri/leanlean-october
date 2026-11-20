module

public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel

/-!
# Reverse-time scalar increment testing

This module converts a continuous scalar increment identity on the literal
reverse-time interval into its compactly supported distributional identity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

theorem exists_strict_reverseTimeScalarTest_collar
    (T : ℝ) (hT : 0 < T) (eta : ReverseTimeScalarTest T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧
      tsupport (eta : ℝ → ℝ) ⊆ Ioo a b ∧ tsupport eta.deriv ⊆ Ioo a b := by
  have hderiv : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) :=
    closure_minimal support_deriv_subset (isClosed_tsupport _)
  suffices ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧ tsupport (eta : ℝ → ℝ) ⊆ Ioo a b by
    obtain ⟨a, b, ha, hab, hb, hs⟩ := this
    exact ⟨a, b, ha, hab, hb, hs, hderiv.trans hs⟩
  by_cases hsupport : (tsupport (eta : ℝ → ℝ)).Nonempty
  · obtain ⟨lo, hlo, hloMin⟩ :=
      eta.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
    obtain ⟨hi, hhi, hhiMax⟩ :=
      eta.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
    obtain ⟨a, ha, halo⟩ := exists_between (eta.tsupport_subset hlo).1
    obtain ⟨b, hhib, hb⟩ := exists_between (eta.tsupport_subset hhi).2
    exact ⟨a, b, ha, halo.trans_le ((hloMin hhi).trans hhib.le), hb,
      fun t ht => ⟨halo.trans_le (hloMin ht), (hhiMax ht).trans_lt hhib⟩⟩
  · refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_⟩
    exact not_nonempty_iff_eq_empty.mp hsupport ▸ empty_subset _

theorem integral_reverseTime_eq_integral_Icc_of_tsupport_subset
    {T a b : ℝ} {F phi : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) (hphi : tsupport phi ⊆ Ioo a b) :
    (∫ t, F t * phi t ∂reverseTimeVolume T) = ∫ t in Icc a b, F t * phi t := by
  change (∫ t in Ioo (0 : ℝ) T, F t * phi t) = ∫ t in Icc a b, F t * phi t
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hK
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hts => ht.2
    ⟨le_of_lt (hphi hts).1, le_of_lt (hphi hts).2⟩)]
  ring

/-- Integration by parts on a compact interval, starting from an increment identity. -/
theorem integral_mul_deriv_eq_neg_integral_of_increment_Icc
    {a b : ℝ} {e q : ℝ → ℝ}
    (hab : a ≤ b) (hq : IntegrableOn q (Icc a b) volume)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      e t - e s = ∫ r in Icc s t, q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, e t * deriv eta t) = -(∫ t in Icc a b, q t * eta t) := by
  let P := PDE.intervalPrimitive a q
  have hP : ContinuousOn P (Icc a b) := PDE.continuousOn_intervalPrimitive hab hq
  have hd := (heta.continuous_deriv le_rfl).continuousOn (s := Icc a b)
  have hcongr : (∫ t in Icc a b, e t * deriv eta t) =
      ∫ t in Icc a b, P t * deriv eta t + e a * deriv eta t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    rw [← PDE.intervalPrimitive_eq_setIntegral_Icc ht.1] at h
    change e t * deriv eta t = _
    rw [show e t = P t + e a by linarith]
    ring
  have hd0 : ∫ t in Icc a b, deriv eta t = 0 := by
    have ha : eta a = 0 := image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl a (hsupp h).1)
    have hb : eta b = 0 := image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl b (hsupp h).2)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab, ha, hb, sub_self]
  have hpint : IntegrableOn (fun t => P t * deriv eta t) (Icc a b) :=
    (hP.mul hd).integrableOn_Icc
  rw [hcongr, integral_add hpint (hd.integrableOn_Icc.const_mul (e a)),
    show (∫ t in Icc a b, P t * deriv eta t) = _ from
      PDE.intervalPrimitive_scalar_weak_identity_Icc hq heta hsupp,
    integral_const_mul, hd0, mul_zero, add_zero]

/-- A reverse-time scalar increment identity yields its compactly supported
distributional testing identity on the literal restricted time measure. -/
theorem integral_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_increment
    (T : ℝ) (hT : 0 < T)
    (q e : ℝ → ℝ)
    (hq : MeasureTheory.Integrable q (reverseTimeVolume T))
    (_he : ContinuousOn e (Set.Icc 0 T))
    (hinc : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
      e t - e s = ∫ r in Set.Ioc s t, q r ∂reverseTimeVolume T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, e t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, q t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ :=
    exists_strict_reverseTimeScalarTest_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hqIcc : IntegrableOn q (Icc a b) volume := by
    change Integrable q (volume.restrict (Ioo (0 : ℝ) T)) at hq
    simpa only [Measure.restrict_restrict_of_subset hK, IntegrableOn] using
      hq.restrict (s := Icc a b)
  have hincIcc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      e t - e s = ∫ r in Icc s t, q r := by
    intro s hs t ht hst
    rw [hinc s t
      ⟨(hK hs).1.le, (hK hs).2.le⟩
      ⟨(hK ht).1.le, (hK ht).2.le⟩ hst]
    have hIoc : Ioc s t ⊆ Ioo (0 : ℝ) T := by
      intro r hr
      exact ⟨lt_of_lt_of_le (hK hs).1 (mem_Ioc.mp hr).1.le,
        lt_of_le_of_lt (mem_Ioc.mp hr).2 (hK ht).2⟩
    change (∫ r, q r ∂(volume.restrict (Ioo (0 : ℝ) T)).restrict (Ioc s t)) = _
    rw [Measure.restrict_restrict_of_subset hIoc, ← integral_Icc_eq_integral_Ioc]
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact integral_mul_deriv_eq_neg_integral_of_increment_Icc hab.le hqIcc hincIcc
    (eta.contDiff.of_le (by norm_num)) heta

section
variable {T : ℝ}

private theorem integrable_mul_reverseTimeScalarTest_deriv {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T)) (eta : ReverseTimeScalarTest T) :
    Integrable (fun t => f t * eta.deriv t) (reverseTimeVolume T) := by
  obtain ⟨C, hC⟩ := eta.exists_norm_deriv_le
  exact hf.mul_bdd eta.contDiff_deriv.continuous.aestronglyMeasurable (Eventually.of_forall hC)

/-- Integrating the scalar weak derivative gives a continuous representative
on the closed interval. The kernel of the weak derivative consists of constants. -/
theorem exists_continuous_reverseTime_representative_of_weakDeriv (hT : 0 < T) {E Q : ℝ → ℝ}
    (hE : Integrable E (reverseTimeVolume T)) (hQ : Integrable Q (reverseTimeVolume T))
    (hweak : ∀ eta : ReverseTimeScalarTest T,
      (∫ t, E t * eta.deriv t ∂reverseTimeVolume T) =
        -(∫ t, Q t * eta t ∂reverseTimeVolume T)) :
    ∃ e : ℝ → ℝ, ContinuousOn e (Icc 0 T) ∧ e =ᵐ[reverseTimeVolume T] E ∧
      ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t, Q r ∂reverseTimeVolume T := by
  let P (t : ℝ) := ∫ r in (0 : ℝ)..t, Q r ∂reverseTimeVolume T
  letI : NullSingletonClass (reverseTimeVolume T) :=
    inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T)))
  have hPc : ContinuousOn P (Icc 0 T) := by
    simpa only [P, uIcc_of_le hT.le] using
      (intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) hQ.integrableOn)
  have hPi : Integrable P (reverseTimeVolume T) := hPc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hinc s t (_ : s ∈ Icc 0 T) (_ : t ∈ Icc 0 T) (hst : s ≤ t) :
      P t - P s = ∫ r in Ioc s t, Q r ∂reverseTimeVolume T := by
    dsimp only [P]
    rw [intervalIntegral.integral_interval_sub_left hQ.intervalIntegrable hQ.intervalIntegrable,
      intervalIntegral.integral_of_le hst]
  have hzero (eta : ReverseTimeScalarTest T) :
      ∫ t, (E t - P t) * eta.deriv t ∂reverseTimeVolume T = 0 := by
    simp only [sub_mul, integral_sub (integrable_mul_reverseTimeScalarTest_deriv hE eta)
      (integrable_mul_reverseTimeScalarTest_deriv hPi eta), hweak,
      integral_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_increment T hT Q P hQ hPc hinc,
      sub_self]
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT (hE.sub hPi) hzero
  refine ⟨fun t => P t + c, hPc.add continuousOn_const, ?_, ?_⟩
  · filter_upwards [hc] with t ht
    change E t - P t = c at ht
    linarith
  · intro s t hs ht hst
    simpa only [add_sub_add_right_eq_sub] using hinc s t hs ht hst

/-- Positivity of a continuous scalar representative follows from positivity a.e. -/
theorem reverseTime_nonneg_on_closedInterval_of_ae (hT : 0 < T) {e : ℝ → ℝ}
    (he : ContinuousOn e (Icc 0 T)) (h0 : ∀ᵐ t ∂reverseTimeVolume T, 0 ≤ e t) :
    ∀ t ∈ Icc 0 T, 0 ≤ e t := by
  have hae : e =ᵐ[volume.restrict (Icc 0 T)] fun t => max (e t) 0 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [h0] with t h
    exact (max_eq_left h).symm
  intro t ht
  rw [Measure.eqOn_Icc_of_ae_eq volume hT.ne hae he (he.sup continuousOn_const) ht]
  exact le_max_right _ _

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
