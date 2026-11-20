module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
import Mathlib.Tactic

/-! # Summing the enlarged-strip quadratic identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ)
include hs hT

/-- Entrance support gives an integrable quadratic with its exact source lower bound. -/
theorem enlargedQuadratic_entrance_lower_integral :
    5 * c.r ^ 2 / 16 *
      (enlargedVisitEntrance A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂enlargedVisitEntrance A c J s T P n := 
  visitQuadratic_integral_lower_of_entrance_support c _
    ((enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono fun _ hp => hp.2.2)

/-- Terminal mixtures at the observation horizon are finite for each finite entrance. -/
theorem enlarged_terminalPiece_isFiniteMeasure :
    IsFiniteMeasure ((enlargedVisitEntrance A c J s T P n).bind
      (enlargedActiveTerminalFamily A c J T)) := by
  rw [enlargedActiveTerminal_bind_eq_restrict A c J T _
    ((enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono
      fun _ hp => hp.2.1)]
  infer_instance

end

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (hJ : closure c.active ⊆ J.carrier)
include hs hT hJ

/-- The terminal contribution has the quadratic maximum times its actual terminal mass. -/
theorem enlargedQuadratic_exit_integral_le_terminal_mass (n : ℕ) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel A (visitActiveUnion c J) T ∘ₘ
        enlargedVisitEntrance A c J s T P n)) ≤
    9 * c.r ^ 2 / 16 *
      (((enlargedVisitEntrance A c J s T P n).bind
        (enlargedActiveTerminalFamily A c J T)) univ).toReal := by
  let mu := enlargedVisitEntrance A c J s T P n
  have ht := (enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono
    fun _ hp => hp.2.1
  have : IsFiniteMeasure (mu.bind
      (enlargedActiveTerminalFamily A c J T)) :=
    enlarged_terminalPiece_isFiniteMeasure A c J s T P hs hT n
  have hi := (enlargedQuadratic_integrable_exit A c J T mu).restrict
    (s := {q | q.time = T})
  rw [← enlargedActiveTerminal_bind_eq_restrict A c J T mu ht] at hi
  rw [enlargedQuadratic_exit_integral_eq_terminal A c J T hJ mu ht]
  have h := integral_mono_ae hi (integrable_const (9 * c.r ^ 2 / 16))
    (Filter.Eventually.of_forall fun q => visitQuadratic_le c (q.velocity 0))
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/-- The exact quadratic count inequality for the canonical finite active pieces. -/
theorem enlargedQuadratic_partial_mass_bound (N : ℕ) :
    5 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (enlargedVisitEntrance A c J s T P n univ).toReal) ≤
    9 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (((enlargedVisitEntrance A c J s T P n).bind
          (enlargedActiveTerminalFamily A c J T)) univ).toReal) +
    2 * Lam *
      (∑ n ∈ Finset.range N,
        (enlargedActivePiece A c J s T P n univ).toReal) := by
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => by
    have : IsFiniteMeasure (enlargedActivePiece A c J s T P n) :=
      enlargedActivePiece_isFiniteMeasure A c J s T P hs hT n
    exact (enlargedQuadratic_entrance_lower_integral
      A c J s T P hs hT n).trans
        ((enlargedQuadratic_entrance_green_identity
          A c J s T P hs hT hJ n).le.trans
            (add_le_add (enlargedQuadratic_exit_integral_le_terminal_mass
              A c J s T P hs hT hJ n)
                (visitCoefficient_integral_le A
                  (enlargedActivePiece A c J s T P n)))))
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
