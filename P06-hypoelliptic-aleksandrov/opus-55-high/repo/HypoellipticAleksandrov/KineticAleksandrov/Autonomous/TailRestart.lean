module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal

/-! # Physical restart identity for the actual active all-time Green family -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- The strict one-pole tail is exactly the enlarged Green mixture of surviving terminal mass. -/
theorem active_tail_restart_identity_strict
     (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t < p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  classical
  let H := c.activeInterval
  let E := stripEvolution hH hLE hlam hLam A H
  let ep := densityClockPole c e he
  let nu := E.2.fiberKernel (intervalDomain_measurable H) e.time (e.time + t)
    (le_add_of_nonneg_right ht) (stripPoleState H ⊤ ep)
  let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
  have hh := tailRestart_green_identity A H E
    (stripEvolution_spec hH hLE hlam hLam A H) ep t ht
  change (stripGreenOfKernel H E.2 ⊤ ep).restrict _ =
    (nu.map (activeRestartPoint H _)).bind K
  rw [nested_bind_map nu _ (measurable_activeRestartPoint H _) K K.measurable]
  refine hh.trans ?_
  congr 1
  funext a
  have ha : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active :=
    (tailRestartPole H (e.time + t) a).2.2
  change _ = (if hv : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A H ⊤
      (densityClockPole c (activeRestartPoint H (e.time + t) a) hv) else 0)
  aesop

/-- A one-pole Green measure assigns zero mass to each exact physical time slice. -/
theorem active_green_time_slice_null
     (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (s : ℝ) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      {p | p.time = s} = 0 := by
  have hh := stripGreen_timeMarginal hH hLE hlam hLam A c.activeInterval ⊤
    (densityClockPole c e he) _ (measurableSet_singleton s)
  simp_all

/-- Including the restart-time endpoint does not change the Green restart identity. -/
theorem active_tail_restart_identity
     (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t ≤ p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  rw [← active_tail_restart_identity_strict]
  apply Measure.restrict_congr_set
  have hn : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he), p.time ≠ e.time + t := by
    rw [ae_iff]
    simpa only [not_not] using
      active_green_time_slice_null hH hLE hlam hLam A c e he _
  filter_upwards [hn] with p hp
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
