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

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)

variable (s t : ℝ) (hst : s ≤ t)

section
variable (z : EvolutionState (intervalDomain H) (fun _ => 0) s)

include hE
/-- Remaining mass is the real mass of the native killed terminal kernel. -/
theorem stripSurvivingMass_eq_kernel_mass
     :
    stripSurvivingMass H E s t hst z =
      (E.2.fiberKernel (intervalDomain_measurable H) s t hst z univ).toReal := by
  rw [stripSurvivingMass, hE.2.1 s t hst z 1]
  simp only [BoundedBorel.one_apply, integral_const, smul_eq_mul, mul_one,
    measureReal_def]

/-- Sub-Markov positivity bounds every killed survival mass between zero and one. -/
theorem stripSurvivingMass_bounds
     :
    0 ≤ stripSurvivingMass H E s t hst z ∧ stripSurvivingMass H E s t hst z ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [stripSurvivingMass_eq_kernel_mass A H E hE]
    exact ENNReal.toReal_nonneg
  · exact realizes_contraction _
      _ _ E.1 E.2 hE s t hst z
end


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
theorem stripSurvivingMass_antitone  (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      stripSurvivingMass H E s t hst z := by
  have hc := realizes_composition _
    _ _ E.1 E.2 hE s t u hst htu
  have hm := stripEvolution_apply_mono A H E hE s t hst (E.1 t u htu 1) 1
    (realizes_contraction _
      _ _ E.1 E.2 hE t u htu)
  change E.1 s u (hst.trans htu) 1 z ≤ E.1 s t hst 1 z
  rw [hc]
  exact hm z

include hE in
/-- A uniform later survival bound multiplies the surviving mass at the restart time. -/
theorem stripSurvivingMass_le_mul_of_later_bound  (s t u k : ℝ) (hst : s ≤ t) (htu : t ≤ u)
    (hk : ∀ w, E.1 t u htu 1 w ≤ k)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s u (hst.trans htu) z ≤
      k * stripSurvivingMass H E s t hst z := by
  let sharedTerm_48c102af3b := ((E.1 t u htu 1))
  have : IsFiniteMeasure (E.2.fiberKernel (intervalDomain_measurable H) s t hst z) :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H) s t hst z).trans_lt
      ENNReal.one_lt_top⟩
  have hc := realizes_composition _
    _ _ E.1 E.2 hE s t u hst htu
  change E.1 s u (hst.trans htu) 1 z ≤ k * E.1 s t hst 1 z
  rw [hc]
  change E.1 s t hst sharedTerm_48c102af3b z ≤ k * E.1 s t hst 1 z
  rw [hE.2.1 s t hst z sharedTerm_48c102af3b, hE.2.1 s t hst z 1]
  have hm := integral_mono (boundedBorel_integrable sharedTerm_48c102af3b _)
    (integrable_const (μ := E.2.fiberKernel (intervalDomain_measurable H) s t hst z) k) hk
  simpa only [BoundedBorel.one_apply, integral_const, smul_eq_mul, mul_comm, one_mul] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
