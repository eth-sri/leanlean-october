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

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (s t : ℝ) (hst : s ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s)

include E hst z in
/-- Remaining mass of the actual killed evolution between two ordered absolute times. -/
def stripSurvivingMass : ℝ :=
  E.1 s t hst 1 z

include hE in
/-- Remaining mass is the real mass of the native killed terminal kernel. -/
theorem stripSurvivingMass_eq_kernel_mass :
    stripSurvivingMass H E s t hst z =
      (E.2.fiberKernel (intervalDomain_measurable H) s t hst z univ).toReal := by
  rw [stripSurvivingMass, hE.2.1 s t hst z 1]
  simp [measureReal_def]

include hE in
/-- Sub-Markov positivity bounds every killed survival mass between zero and one. -/
theorem stripSurvivingMass_bounds :
    0 ≤ stripSurvivingMass H E s t hst z ∧ stripSurvivingMass H E s t hst z ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [stripSurvivingMass_eq_kernel_mass A H E hE]
    exact ENNReal.toReal_nonneg
  · apply realizes_contraction <;> assumption

include hE in
/-- Killed evolution preserves pointwise order of bounded Borel terminal data. -/
theorem stripEvolution_apply_mono
    (f g : BoundedBorel (EvolutionState (intervalDomain H) (fun _ => 0) t))
    (hfg : f ≤ g) : E.1 s t hst f ≤ E.1 s t hst g := by
  intro z
  have : IsFiniteMeasure (E.2.fiberKernel (intervalDomain_measurable H) s t hst z) :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H) s t hst z).trans_lt
      ENNReal.one_lt_top⟩
  rw [hE.2.1 s t hst z f, hE.2.1 s t hst z g]
  exact integral_mono (boundedBorel_integrable f _) (boundedBorel_integrable g _) hfg

include hE in
/-- Composition and contraction make remaining mass nonincreasing in the terminal time. -/
theorem stripSurvivingMass_antitone (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      stripSurvivingMass H E s t hst z := by
  have hc := realizes_composition (intervalDomain_measurable H)
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE s t u hst htu
  have hm := stripEvolution_apply_mono A H E hE s t hst (E.1 t u htu 1) 1
    (realizes_contraction (intervalDomain_measurable H)
      (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE t u htu)
  change E.1 s u (hst.trans htu) 1 z ≤ E.1 s t hst 1 z
  rw [hc]
  apply hm

end

/-- A uniform later survival bound multiplies the surviving mass at the restart time. -/
theorem stripSurvivingMass_le_mul_of_later_bound {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (s t u k : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (hk : ∀ w, E.1 t u htu 1 w ≤ k)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      k * stripSurvivingMass H E s t hst z := by
  have : IsFiniteMeasure (E.2.fiberKernel (intervalDomain_measurable H) s t hst z) :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H) s t hst z).trans_lt
      ENNReal.one_lt_top⟩
  have hc := realizes_composition (intervalDomain_measurable H)
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE s t u hst htu
  change E.1 s u (hst.trans htu) 1 z ≤ k * E.1 s t hst 1 z
  rw [hc]
  change E.1 s t hst (E.1 t u htu 1) z ≤ k * E.1 s t hst 1 z
  rw [hE.2.1 s t hst z (E.1 t u htu 1), hE.2.1 s t hst z 1]
  have hm := integral_mono (boundedBorel_integrable (E.1 t u htu 1) _)
    (integrable_const (μ := E.2.fiberKernel (intervalDomain_measurable H) s t hst z) k) hk
  simpa [mul_comm] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
