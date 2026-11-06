module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationWeak

/-! # Weak calculus for Borel correctors

The supplied C112 solution has a genuine weak equation for each smooth approximating
coefficient, with its classical residual as source. This is integration by parts,
without a homogeneous-corrector premise.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Evolution SectionTwo TheoremA Occupation

/-- Integration by parts for the classical residual of a smooth coefficient. -/
alias borelCorrector_classical_weak := localRepresentation_classical_weak

/-- The physical whole-space signed potential, with the required coordinate swap. -/
def borelCorrectorPotential {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (T : ℝ) (F : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  duhamelPotential K T (F ∘ sectionTwoPoint) (sectionTwoPoint P)

/-- Bounded whole-space physical sources satisfy the signed weak equation. -/
theorem borelCorrectorPotential_weak {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
    (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ P, |F P| ≤ M) :
    IsKineticWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (evolutionPastOpenCylinder (wholeSpace d) (fun _ => (0 : PDE.Vec d)) T)
      (borelCorrectorPotential K T F ∘ sectionTwoPoint)
      (fun Q => -F (sectionTwoPoint Q)) := by
  have heq : borelCorrectorPotential K T F ∘ sectionTwoPoint =
      duhamelPotential K T (F ∘ sectionTwoPoint) := by
    funext Q
    simp only [borelCorrectorPotential, Function.comp_apply]
    rw [sectionTwoPoint_involutive Q]
  rw [heq]
  obtain ⟨hsm, hsym, _⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  exact duhamel_bounded_isKineticWeakTransportedSolution (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (zIndependentCoefficient B) (identityDrift d)
    S K hreal hsm hsym (identityDrift_smooth d) (F ∘ sectionTwoPoint)
    (hF.comp (continuous_sectionTwoPoint d).measurable) M hM (fun Q => hFb _) T

/-- Opposite genuine weak sources cancel; this is internal weak-equation calculus. -/
alias borelCorrector_weak_cancel := localRepresentation_weak_cancel

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
