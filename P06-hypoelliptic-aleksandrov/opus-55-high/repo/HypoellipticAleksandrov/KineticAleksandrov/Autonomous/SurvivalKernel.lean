module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance

/-! # Remaining killed mass and its monotonicity

Source: companion paper, Corollary 8.4 (survival decay). Remaining mass uses the actual
uniquely characterized killed operator, with absolute times and interior states.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- Remaining mass of the actual killed evolution between two ordered absolute times. -/
def stripSurvivingMass (H : Interval) (E : StripEvolution H) (s t : ℝ) (hst : s ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) : ℝ :=
  E.1 s t hst 1 z

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)

/-- Remaining mass is the real mass of the native killed terminal kernel. -/
theorem stripSurvivingMass_eq_kernel_mass 
    (hE : IsStripEvolution A H E) (s t : ℝ) (hst : s ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s t hst z =
      (E.2.fiberKernel (intervalDomain_measurable H) s t hst z univ).toReal := by
  rw [stripSurvivingMass, hE.2.1]
  aesop

/-- Sub-Markov positivity bounds every killed survival mass between zero and one. -/
theorem stripSurvivingMass_bounds 
    (hE : IsStripEvolution A H E) (s t : ℝ) (hst : s ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    0 ≤ stripSurvivingMass H E s t hst z ∧ stripSurvivingMass H E s t hst z ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [stripSurvivingMass_eq_kernel_mass A H E hE]
    positivity
  · exact realizes_contraction _
      _ _ E.1 E.2 hE s t hst z

/-- Killed evolution preserves pointwise order of bounded Borel terminal data. -/
theorem stripEvolution_apply_mono 
    (hE : IsStripEvolution A H E) (s t : ℝ) (hst : s ≤ t)
    (f g : BoundedBorel (EvolutionState (intervalDomain H) (fun _ => 0) t))
    (hfg : f ≤ g) : E.1 s t hst f ≤ E.1 s t hst g := by
  intro z
  have : IsFiniteMeasure _ :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H) s t hst z).trans_lt
      ENNReal.one_lt_top⟩
  rw [hE.2.1, hE.2.1]
  exact integral_mono (boundedBorel_integrable f _) (boundedBorel_integrable g _) hfg

/-- Composition and contraction make remaining mass nonincreasing in the terminal time. -/
theorem stripSurvivingMass_antitone 
    (hE : IsStripEvolution A H E) (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      stripSurvivingMass H E s t hst z := by
  have hc := realizes_composition _
    _ _ E.1 E.2 hE s t u hst htu
  have hm := stripEvolution_apply_mono A H E hE s t hst _ 1
    (realizes_contraction _
      _ _ E.1 E.2 hE t u htu)
  change E.1 s u _ 1 z ≤ E.1 s t hst 1 z
  aesop

/-- A uniform later survival bound multiplies the surviving mass at the restart time. -/
theorem stripSurvivingMass_le_mul_of_later_bound 
    (hE : IsStripEvolution A H E) (s t u k : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (hk : ∀ w, E.1 t u htu 1 w ≤ k)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      k * stripSurvivingMass H E s t hst z := by
  have : IsFiniteMeasure _ :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H) s t hst z).trans_lt
      ENNReal.one_lt_top⟩
  have hc := realizes_composition _
    _ _ E.1 E.2 hE s t u hst htu
  change E.1 s u _ 1 z ≤ k * E.1 s t hst 1 z
  rw [hc]
  change E.1 s t hst _ z ≤ k * E.1 s t hst 1 z
  rw [hE.2.1, hE.2.1]
  have hm := integral_mono (boundedBorel_integrable _ _)
    (integrable_const (μ := E.2.fiberKernel _ s t hst z) k) hk
  simpa only [BoundedBorel.one_apply, integral_const, smul_eq_mul,
    mul_one, one_mul, mul_comm] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
