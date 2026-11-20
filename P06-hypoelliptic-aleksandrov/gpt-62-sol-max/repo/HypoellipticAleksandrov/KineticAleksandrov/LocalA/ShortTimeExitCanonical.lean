module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-! # The canonical ball kernel and its actual parabolic marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic SectionTwo Set MeasureTheory

/-- The valid query corresponding to physical starting and terminal times. -/
def ballEvolutionQuery {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0) :=
  evolutionQueryOfState _ _ P.1.time T.1 T.2.le (ballStartState P)

section
variable {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (B : CoefficientField d)
  (hB : IsSectionTwoCoefficient lam Lam B) (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
include hd lam Lam B hB hR

/-- The physical ball transition is the master measure at its literal valid query.
Terminal states retain the evolution coordinate order (velocity, position). -/
def ballTransition
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    Measure (EvolutionAmbientState d) :=
  (localBallKernel hd B hB v₀ hR).master (ballEvolutionQuery P T)

/-- The actual uniquely chosen ball kernel inherits the proved full marginal bundle. -/
theorem localBallKernel_marginal :
    HasParabolicMarginalBundle (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet (zIndependentCoefficient B)
      (localBallKernel hd B hB v₀ hR) := 
  ((exists_terminalEvolution_of_classical.timeVelocity hd (localBall_admissible v₀ hR) B hB).clauses
    (localBallEvolution_realizes hd B hB v₀ hR)).2.2

end

/-- First marginal mass equals joint terminal mass at every physical starting position. -/
theorem ballTransition_mass_eq_marginal
    {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    (ballTransition hd B hB v₀ hR P T).real univ =
      (parabolicMarginalKernel (localBallKernel hd B hB v₀ hR)
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
        ⟨P.1.velocity, by simpa only [movingDomain_ball_zero] using P.2⟩).real univ := by
  let K := localBallKernel hd B hB v₀ hR
  let hD := (PDE.isOpen_euclideanBall v₀ R).measurableSet
  obtain ⟨Q, hfirst, _⟩ := localBallKernel_marginal hd B hB v₀ hR
    (fun _ _ _ _ => rfl)
  rw [Measure.real, Measure.real, hfirst _ _ _ _ P.1.position]
  have hm := K.map_fiberFirstMarginal_eq_firstMarginal hD P.1.time T.1 T.2.le
    (ballStartState P)
  have huniv := congrArg (fun μ : Measure (PDE.Vec d) => μ univ) hm
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ, K.firstMarginal_apply _ _ MeasurableSet.univ] at huniv
  exact congrArg ENNReal.toReal huniv.symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
