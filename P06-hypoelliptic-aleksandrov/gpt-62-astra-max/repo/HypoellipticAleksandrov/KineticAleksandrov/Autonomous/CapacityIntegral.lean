module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import Mathlib.Tactic

/-! # Integral control from the genuine bounded strip Green identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The integral of a velocity diffusion test is bounded by its oscillation on the strip. -/
theorem capacity_diffusion_integral_le
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (Phi chi : ℝ → ℝ)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (_hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hn : ∀ v, 0 ≤ chi v ∧ chi v ≤ 1)
    (hsecond : ∀ v, deriv (deriv Phi) v = 2 * chi v)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ v, |deriv Phi v| ≤ D) :
    (∫ p, 2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0)
      ∂stripGreen hlam hLam A H T e) ≤ D * (H.hi - H.lo) := by
  let phi : Point → ℝ := fun p => Phi (p.velocity 0)
  let Ω := stripExit hlam hLam A H T e
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
  have hid := strip_identity_bounded_smooth hlam hLam A H T e phi
    (capacity_velocity_smooth hPhi) (by
      refine ⟨|Phi (e.1.velocity 0)| + D * (H.hi - H.lo) + 2 * Lam, ?_⟩
      intro p hv
      exact ⟨by dsimp only [phi]; linarith [hbound _ ⟨hv.1.le, hv.2.le⟩],
        by linarith [hsrc p, abs_nonneg (Phi (e.1.velocity 0)),
          mul_nonneg hD (sub_pos.mpr H.ordered).le]⟩)
  have hΩ : ∀ᵐ p ∂Ω, p.velocity 0 ∈ Icc H.lo H.hi := by
    filter_upwards [stripExitOfRealization_ae_closed_future hlam hLam A H _
      (stripEvolution_spec hlam hLam A H) T e] with p hp'
    exact hp'.2.2
  have hi : Integrable phi Ω := by
    apply Integrable.mono' (integrable_const
      (|Phi (e.1.velocity 0)| + D * (H.hi - H.lo)))
      (hPhi.continuous.comp ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable
    filter_upwards [hΩ] with p hp'
    exact hbound _ hp'
  have hupper : (∫ p, phi p ∂Ω) ≤ Phi (e.1.velocity 0) + D * (H.hi - H.lo) := by
    calc
      _ ≤ ∫ _p, Phi (e.1.velocity 0) + D * (H.hi - H.lo) ∂Ω :=
        integral_mono_ae hi (integrable_const _) (by
          filter_upwards [hΩ] with p hp'
          linarith [le_abs_self (Phi (p.velocity 0) - Phi (e.1.velocity 0)), hdiff _ hp'])
      _ = _ := by simp
  rw [(funext hop)] at hid
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
