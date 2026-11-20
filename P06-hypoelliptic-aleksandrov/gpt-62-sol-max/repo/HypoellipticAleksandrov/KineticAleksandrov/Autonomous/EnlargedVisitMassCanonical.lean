module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # Unconditional canonical enlarged count from the enlarged recursion results -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T : ℝ)
  (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2) (hbar : |c.vbar| = 2 * c.r)
  (hJ : closure c.active ⊆ J.carrier) (hvel : P.velocity 0 ∈ closure c.entrance)
include R hR hT hTR hbar hJ hvel

/-- The actual enlarged count has the source horizon bound independently of the outer interval. -/
theorem enlargedVisitStarts_mass_le :
    enlargedVisitStarts A c J P.time (P.time + T) P univ ≤
      ENNReal.ofReal (enlargedVisitMassConstant lam Lam * (1 + R / c.r)) := by
  have hPT : P.time < P.time + T := by linarith
  have hv : P.velocity 0 ∈ J.carrier :=
    hJ (subset_closure (_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hvel))
  have hLn : 0 ≤ Lam := A.positive.le.trans A.ordered
  have hlam := A.positive
  have hr := c.positive
  have hsqrt : Real.sqrt T ≤ R := by
    have h := Real.sqrt_le_sqrt hTR
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hR] at h
    exact h
  have hscale : (64 * c.r / lam) * Real.sqrt (2 * Lam * T) ≤
      (64 * c.r / lam) * (Real.sqrt (2 * Lam) * R) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) (by positivity)
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  let mu := enlargedVisitEntrance A c J P.time (P.time + T) P
  have hm := enlargedQuadratic_partial_mass_bound A c J
    P.time (P.time + T) P le_rfl hPT hJ N
  let tm := fun n => (mu n).bind
    (enlargedActiveTerminalFamily A c J (P.time + T))
  have : ∀ n, IsFiniteMeasure (tm n) := fun n =>
    enlarged_terminalPiece_isFiniteMeasure A c J P.time (P.time + T)
      P le_rfl hPT n
  have hmTerminal := enlarged_active_terminal_mass_le_one A c J
    P.time (P.time + T) P ⟨le_rfl, hPT, hv⟩ hJ N
  have he := ENNReal.toReal_mono ENNReal.one_ne_top hmTerminal
  change ((∑ n ∈ Finset.range N, tm n) univ).toReal ≤ (1 : ENNReal).toReal at he
  rw [visit_partial_real_mass tm N univ MeasurableSet.univ, ENNReal.toReal_one] at he
  have ho := (enlargedActivePiece_partial_capacity_of_domination
    A c J T P hT hbar N (enlarged_active_occupation_le_fullspace
      A c J T hT P hv N)).trans hscale
  have hnum := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ 2 * Lam)))
  have heq : 2 * Lam * ((64 * c.r / lam) * (Real.sqrt (2 * Lam) * R)) =
      (128 * Lam / lam * Real.sqrt (2 * Lam)) * R * c.r := by ring
  rw [mul_one, heq] at hnum
  have hbound := enlarged_mass_arithmetic hr hR.le
    (by positivity : 0 ≤ 128 * Lam / lam * Real.sqrt (2 * Lam)) hnum
  rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hbound
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) ?_).mpr hbound
  exact mul_nonneg (enlargedVisitMassConstant_pos A.positive A.ordered).le (by positivity)

/-- The canonical total enlarged visit count is finite, including the initial atom. -/
theorem enlargedVisitStarts_isFiniteMeasure :
    IsFiniteMeasure (enlargedVisitStarts A c J P.time (P.time + T) P) :=
  ⟨(enlargedVisitStarts_mass_le A c J R T P
    hR hT hTR hbar hJ hvel).trans_lt ENNReal.ofReal_lt_top⟩

end

/-- Every canonical observed visit count is finite, with an arbitrary positive horizon. -/
theorem visitsFromZero_isFiniteMeasure {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hT : 0 < T) (hvel : P.velocity 0 ∈ closure c.entrance) :
    IsFiniteMeasure (visitsFromZero A c J T P) :=
  enlargedVisitStarts_isFiniteMeasure A c J (1 + T) T P
    (by linarith) hT (by nlinarith) hbar hJ hvel

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
