module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassGreen

/-! # Summing the enlarged-strip quadratic identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/- Entrance support gives an integrable quadratic with its exact source lower bound. -/
theorem enlarged_terminalPiece_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    IsFiniteMeasure ((enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) := by
  rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T _
    ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
      fun _ hp => hp.2.1)]
  infer_instance

/- The terminal contribution has the quadratic maximum times its actual terminal mass. -/
theorem enlargedQuadratic_exit_integral_le_terminal_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ
        enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)) ≤
    9 * c.r ^ 2 / 16 *
      (((enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
        (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) univ).toReal := by
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J s T P n
  have ht := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
    fun _ hp => hp.2.1
  have : IsFiniteMeasure (mu.bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) :=
    enlarged_terminalPiece_isFiniteMeasure hH hLE hlam hLam A c J s T P hs hT n
  have hi := (enlargedQuadratic_integrable_exit hH hLE hlam hLam A c J T mu).restrict
    (s := {q | q.time = T})
  rw [← enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T mu ht] at hi
  have _h_xinl_0 : (∫ q, visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu)) =
    ∫ q, visitQuadratic c (q.velocity 0)
      ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T) := by
    rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T mu ht]
    symm
    rw [← integral_indicator (isClosed_eq continuous_time continuous_const).measurableSet]
    apply integral_congr_ae
    filter_upwards [enlargedActiveExit_ae_quadratic_zero_or_terminal
      hH hLE hlam hLam A c J T hJ mu] with q hq
    rcases hq with hq | hq
    · simp only [Set.indicator, mem_ofPred_eq, hq, ite_true]
    · by_cases htq : q.time = T
      · simp only [Set.indicator, mem_ofPred_eq, htq, ite_true]
      · simp only [Set.indicator, mem_ofPred_eq, htq, ite_false, hq]
  rw [_h_xinl_0]
  have h := integral_mono_ae hi (integrable_const (9 * c.r ^ 2 / 16))
    (Filter.Eventually.of_forall fun q => visitQuadratic_le c (q.velocity 0))
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/- The exact quadratic count inequality for the canonical finite active pieces. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
