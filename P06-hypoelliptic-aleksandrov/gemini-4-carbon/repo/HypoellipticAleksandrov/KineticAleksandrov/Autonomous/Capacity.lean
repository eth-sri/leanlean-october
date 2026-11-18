module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Velocity occupation is bounded by strip width times interval length over ellipticity. -/
theorem strip_capacity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (E : Interval) :
    stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 ∈ E.carrier} ≤
      ENNReal.ofReal ((H.hi - H.lo) / lam * (E.hi - E.lo))  := by
  have capacity_diffusion_integral_le (Phi : ℝ → ℝ) (chi : ℝ → ℝ) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (_hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hn : ∀ v, 0 ≤ chi v ∧ chi v ≤ 1) (hsecond : ∀ v, deriv (deriv Phi) v = 2 * chi v) {D : ℝ} (hD : 0 ≤ D) (hd : ∀ v, |deriv Phi v| ≤ D) :
      (∫ p, 2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0)
      ∂stripGreen hH hLE hlam hLam A H T e) ≤ D * (H.hi - H.lo) := by
    let phi : Point → ℝ := fun p => Phi (p.velocity 0)
    let Ω := stripExit hH hLE hlam hLam A H T e
    have hp : e.1.velocity 0 ∈ Icc H.lo H.hi := ⟨e.2.2.1.le, e.2.2.2.le⟩
    have hdiff (v : ℝ) (hv : v ∈ Icc H.lo H.hi) :
        |Phi v - Phi (e.1.velocity 0)| ≤ D * (H.hi - H.lo) :=
      capacity_test_difference hPhi hD hd H hp hv
    have hbound (v : ℝ) (hv : v ∈ Icc H.lo H.hi) :
        |Phi v| ≤ |Phi (e.1.velocity 0)| + D * (H.hi - H.lo) := by
      have h := abs_add_le (Phi v - Phi (e.1.velocity 0)) (Phi (e.1.velocity 0))
      rw [sub_add_cancel] at h
      linarith [hdiff v hv]
    have hop (p : Point) : forwardScalarOperator A.a phi p =
        2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0) := by
      rw [capacity_velocity_operator, hsecond]
      ring
    have hsrc (p : Point) :
        |forwardScalarOperator A.a phi p| ≤ 2 * Lam := by
      rw [hop, abs_of_nonneg]
      · nlinarith [(A.bounds (p.position 0) (p.velocity 0)).2,
          (A.bounds (p.position 0) (p.velocity 0)).1, (hn (p.velocity 0)).1,
          (hn (p.velocity 0)).2]
      · exact mul_nonneg (mul_nonneg (by norm_num)
          (hlam.trans_le (A.bounds (p.position 0) (p.velocity 0)).1).le)
          (hn (p.velocity 0)).1
    have hid := strip_identity_bounded_smooth hH hLE hlam hLam A H T e phi
      (capacity_velocity_smooth hPhi) (by
        refine ⟨|Phi (e.1.velocity 0)| + D * (H.hi - H.lo) + 2 * Lam, ?_⟩
        intro p hv
        have hv' : p.velocity 0 ∈ Icc H.lo H.hi := ⟨hv.1.le, hv.2.le⟩
        exact ⟨by dsimp only [phi]; linarith [hbound _ hv'],
          by linarith [hsrc p, abs_nonneg (Phi (e.1.velocity 0)),
            mul_nonneg hD (sub_pos.mpr H.ordered).le]⟩)
    have hΩ : ∀ᵐ p ∂Ω, p.velocity 0 ∈ Icc H.lo H.hi := by
      filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A H _
        (stripEvolution_spec hH hLE hlam hLam A H) T e] with p hp'
      exact hp'.2.2
    have hpc : Continuous phi :=
      hPhi.continuous.comp ((continuous_apply 0).comp continuous_velocity)
    have hi : Integrable phi Ω := by
      apply Integrable.mono' (integrable_const
        (|Phi (e.1.velocity 0)| + D * (H.hi - H.lo)))
        hpc.measurable.aestronglyMeasurable
      filter_upwards [hΩ] with p hp'
      simpa using hbound _ hp'
    have hupper : (∫ p, phi p ∂Ω) ≤ Phi (e.1.velocity 0) + D * (H.hi - H.lo) := by
      calc
        _ ≤ ∫ _p, Phi (e.1.velocity 0) + D * (H.hi - H.lo) ∂Ω :=
          integral_mono_ae hi (integrable_const _) (by
            filter_upwards [hΩ] with p hp'
            linarith [le_abs_self (Phi (p.velocity 0) - Phi (e.1.velocity 0)), hdiff _ hp'])
        _ = _ := by simp
    rw [(funext hop)] at hid
    change Phi (e.1.velocity 0) = _ at hid
    change (∫ p, phi p ∂Ω) ≤ _ at hupper
    linarith
  obtain ⟨chi, Phi, hchi, _hc, hn, h1, _hm, hPhi, hsecond, hd⟩ :=
    exists_capacity_test E
  let Γ := stripGreen hH hLE hlam hLam A H T e
  let U : Set Point := {p | p.velocity 0 ∈ E.carrier}
  have hU : MeasurableSet U :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
  let g : Point → ℝ := fun p => 2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0)
  have hgc : Continuous g := by
    exact (continuous_const.mul (A.smooth.continuous.comp
      (((continuous_apply 0).comp continuous_position).prodMk
        ((continuous_apply 0).comp continuous_velocity)))).mul
      (hchi.continuous.comp ((continuous_apply 0).comp continuous_velocity))
  have hgn (p : Point) : 0 ≤ g p :=
    mul_nonneg (mul_nonneg (by norm_num)
      (hlam.trans_le (A.bounds _ _).1).le) (hn _).1
  have hgb (p : Point) : |g p| ≤ 2 * Lam := by
    rw [abs_of_nonneg (hgn p)]
    nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1,
      (A.bounds (p.position 0) (p.velocity 0)).2, (hn (p.velocity 0)).1,
      (hn (p.velocity 0)).2]
  have hi : Integrable g Γ := by
    apply Integrable.mono' (integrable_const (2 * Lam)) hgc.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simpa using hgb p
  have hind : Integrable (U.indicator (fun _p => (2 * lam))) Γ :=
    (integrable_const _).indicator hU
  have hlow : 2 * lam * (Γ U).toReal ≤ ∫ p, g p ∂Γ := by
    calc
      _ = ∫ p, U.indicator (fun _p => (2 * lam)) p ∂Γ := by
        rw [integral_indicator_const _ hU, Measure.real, smul_eq_mul]
        ring
      _ ≤ _ := integral_mono hind hi (fun p => by
        by_cases hp : p ∈ U
        · dsimp only [g]
          rw [indicator_of_mem hp, show chi (p.velocity 0) = 1 from
            h1 _ ⟨hp.1.le, hp.2.le⟩]
          nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1]
        · rw [indicator_of_notMem hp]
          exact hgn p)
  have hD : 0 ≤ 2 * (E.hi - E.lo) := by linarith [E.ordered]
  have hupper := capacity_diffusion_integral_le Phi chi
    hPhi hchi hn hsecond hD hd
  have hr : (Γ U).toReal ≤ (H.hi - H.lo) / lam * (E.hi - E.lo) := by
    have heq : ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam =
        (H.hi - H.lo) * (E.hi - E.lo) := by field_simp
    have hmul : (Γ U).toReal * lam ≤
        ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam := by
      rw [heq]
      change (∫ p, g p ∂Γ) ≤ _ at hupper
      nlinarith
    nlinarith
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top Γ U) (mul_nonneg (div_nonneg (sub_pos.mpr H.ordered).le hlam.le) (sub_pos.mpr E.ordered).le)).mpr hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

