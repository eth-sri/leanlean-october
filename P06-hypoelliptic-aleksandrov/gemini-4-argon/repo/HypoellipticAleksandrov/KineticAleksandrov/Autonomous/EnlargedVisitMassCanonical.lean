module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
import Mathlib.Tactic

/-! # Unconditional canonical enlarged count from the enlarged recursion results -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open ProbabilityTheory

/- The actual enlarged count has the source horizon bound independently of the outer interval. -/
theorem enlargedVisitStarts_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T )
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hvel : P.velocity 0 ∈ closure c.entrance) :
    enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P univ ≤
      ENNReal.ofReal (enlargedVisitMassConstant lam Lam * (1 + R / c.r)) := by
  have hPT : P.time < P.time + T := by linarith
  have hv :=
    hJ (subset_closure (enlarged_closedEntrance_subset_active c hvel))
  have hLn := hlam.le.trans hLam
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
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  have hm : 5 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n univ).toReal) ≤
    9 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (((enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).bind
          (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + T))) univ).toReal) +
    2 * Lam *
      (∑ n ∈ Finset.range N,
        (enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n univ).toReal) := by
    let s := P.time
    let T := (P.time + T)
    have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => by
      have : IsFiniteMeasure (enlargedActivePiece hH hLE hlam hLam A c J s T P n) :=
        enlargedActivePiece_isFiniteMeasure hH hLE hlam hLam A c J s T P le_rfl hPT n
      have _h_xinl_0 : 5 * c.r ^ 2 / 16 *
      (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n := by
          have hm := enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P le_rfl hPT n
          have hi : Integrable (fun p => visitQuadratic c (p.velocity 0))
              (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) := by
            apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
              (((visitQuadratic_smooth c).continuous.comp
                ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
            filter_upwards [hm] with p hp
            change ‖visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
            rw [Real.norm_eq_abs, abs_of_nonneg
              ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
                (visitQuadratic_entrance_lower c hp.2.2))]
            exact visitQuadratic_le c _
          have h := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16)) hi
            (hm.mono fun _ hp => visitQuadratic_entrance_lower c hp.2.2)
          simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

        /- Terminal mixtures at the observation horizon are finite for each finite entrance. -/
      exact _h_xinl_0.trans
          ((enlargedQuadratic_entrance_green_identity
            hH hLE hlam hLam A c J s T P le_rfl hPT hJ n).le.trans
              (add_le_add (enlargedQuadratic_exit_integral_le_terminal_mass
                hH hLE hlam hLam A c J s T P le_rfl hPT hJ n)
                  (visitCoefficient_integral_le hlam A
                    (enlargedActivePiece hH hLE hlam hLam A c J s T P n)))))
    simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h
  let tm := fun n => (mu n).bind
    (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + T))
  have : ∀ n, IsFiniteMeasure (tm n) := fun n =>
    enlarged_terminalPiece_isFiniteMeasure hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT n
  have hmTerminal := enlarged_active_terminal_mass_le_one hH hLE hlam hLam A c J
    P.time (P.time + T) P ⟨le_rfl, hPT, hv⟩ hJ N
  have he := ENNReal.toReal_mono ENNReal.one_ne_top hmTerminal
  change ((∑ n ∈ Finset.range N, tm n) univ).toReal ≤ (1 : ENNReal).toReal at he
  rw [visit_partial_real_mass tm N univ MeasurableSet.univ, ENNReal.toReal_one] at he
  have ho := (enlargedActivePiece_partial_capacity_of_domination
    hH hLE hlam hLam A c J T P hT hbar N (enlarged_active_occupation_le_fullspace
      hH hLE hlam hLam A c J T hT P hv N)).trans hscale
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
  exact mul_nonneg (enlargedVisitMassConstant_pos hlam hLam).le (by positivity)


/- The canonical total enlarged visit count is finite, including the initial atom. -/
theorem enlargedVisitStarts_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T )
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hvel : P.velocity 0 ∈ closure c.entrance) :
    IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P) :=
  ⟨(enlargedVisitStarts_mass_le hH hLE hlam hLam A c J R T P
    hR hT hTR hbar hJ hvel).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
