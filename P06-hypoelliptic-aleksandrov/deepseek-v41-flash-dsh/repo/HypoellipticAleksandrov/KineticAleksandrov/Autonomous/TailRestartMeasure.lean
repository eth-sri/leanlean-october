module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Survival
import Mathlib.Tactic

/-! # The actual remaining terminal measure for a tail restart

Source: companion paper, Corollary 8.4 (restarted tail). The measure is placed on
the absolute restart-time slice and retains every interior active velocity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- Put a native terminal state on its physical absolute-time slice. -/
def activeRestartPoint (H : Interval) (s : ℝ)
    (w : EvolutionState (intervalDomain H) (fun _ => 0) s) : Point :=
  ⟨s, w.1.2, w.1.1⟩

/-- Restoring physical coordinates on a fixed time slice is measurable. -/
theorem measurable_activeRestartPoint (H : Interval) (s : ℝ) :
    Measurable (activeRestartPoint H s) := (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_fst.comp measurable_subtype_coe)))
section
variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t)

/-- The surviving terminal measure, restored to the source's physical spacetime coordinates. -/
def activeRestartMeasure
     : Measure Point :=
  ((stripEvolution hH hLE hlam hLam A c.activeInterval).2.fiberKernel
    (intervalDomain_measurable c.activeInterval) e.time (e.time + t)
    (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)).map
      (activeRestartPoint c.activeInterval (e.time + t))

/-- The mass of the remaining terminal measure is exactly the surviving killed mass. -/
theorem activeRestartMeasure_mass
     :
    activeRestartMeasure hH hLE hlam hLam A c e he t ht univ =
      ENNReal.ofReal (activeSurvivingMass hH hLE hlam hLam A c e he t ht) := by
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  let z := stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  have hmass := stripSurvivingMass_eq_kernel_mass A c.activeInterval E
    (stripEvolution_spec hH hLE hlam hLam A c.activeInterval)
    e.time (e.time + t) (le_add_of_nonneg_right ht) z
  change (Measure.map (activeRestartPoint c.activeInterval (e.time + t))
    (E.2.fiberKernel (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)) univ =
    ENNReal.ofReal (stripSurvivingMass c.activeInterval E
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)
  rw [Measure.map_apply (measurable_activeRestartPoint _ _) MeasurableSet.univ,
    preimage_univ, hmass]
  exact (ENNReal.ofReal_toReal
    ((E.2.fiberKernel_mass_le_one (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z).trans_lt
        ENNReal.one_lt_top).ne).symm
end

/-- Remaining terminal mass obeys the source uniform exponential decay. -/
theorem activeRestartMeasure_mass_exp
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
      activeRestartMeasure hH hLE hlam hLam A c e he t ht univ ≤
        ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2)) := by
  obtain ⟨C, c₀, hC, hc₀, hb⟩ := active_survival_exp hH hLE hlam hLam
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c e he t ht
  rw [activeRestartMeasure_mass]
  exact ENNReal.ofReal_le_ofReal (hb A c e he t ht)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
