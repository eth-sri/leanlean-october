module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit

/-! # The endpoint-inclusive cumulative localized Green identity -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped Classical

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock)

/-- The all-time active occupation has no atom on a fixed time slice. -/
theorem positionStartGreen_ae_time_ne
     (p : Point)
    (hv : p.velocity 0 ∈ c.active) (b : ℝ) :
    ∀ᵐ q ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c p hv), q.time ≠ b := by
  rw [ae_iff]
  simpa only [not_not] using enlarged_stripGreen_time_slice_zero
    hH hLE hlam hLam A c.activeInterval (densityClockPole c p hv) b

/-- The cumulative identity retains a start exactly at `b` as a zero-duration terminal atom. -/
theorem positionStartQuadratic_cumulative_identity
     (J : Interval) (Y b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (p : Point) (hv : p.velocity 0 ∈ c.active) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    ({q : Point | q.time ≤ b}.indicator f) p =
      (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
      ∫ q in {q : Point | q.time ≤ b}, forwardScalarOperator A.a f q
        ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
  dsimp only
  let G := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv)
  have hvJ : p.velocity 0 ∈ (visitActiveUnion c J).carrier := by
    rw [visitActiveUnion_carrier]
    exact ⟨hv, hJ (subset_closure hv)⟩
  by_cases ht : p.time < b
  · rw [indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from ht.le)]
    have hi := positionStartQuadratic_terminal_identity
      hH hLE hlam hLam A c J Y b hc hJ p hv ht
    dsimp only at hi
    rw [positionStartGreen_eq_restrict hH hLE hlam hLam A c J b hJ p hv ht] at hi

    rw [Measure.restrict_congr_set (by
        filter_upwards [positionStartGreen_ae_time_ne hH hLE hlam hLam A c p hv b] with q hq
        exact propext (lt_iff_le_and_ne.trans (and_iff_left hq)))] at hi
    exact hi
  · have hbp  := le_of_not_gt ht
    have hz : G.restrict {q : Point | q.time ≤ b} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      have hn  :=
        (stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
          (densityClockPole c p hv)).mono fun q hq => not_le_of_gt (hbp.trans_lt hq.1)
      rw [ae_iff] at hn
      simpa only [not_not] using hn
    change _ = _ - ∫ q, _ ∂G.restrict {q : Point | q.time ≤ b}
    rw [hz, integral_zero_measure, sub_zero]
    by_cases he : p.time = b
    · simp_all [Point, enlargedActiveTerminalFamily]
    · rw [indicator_of_notMem (show p ∉ {q : Point | q.time ≤ b} from
        fun h => he (le_antisymm h hbp))]

      have hE : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
          0 := by
        change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else
          (0 : Measure Point)) = 0
        rw [dite_eq_right (fun h => ht h.1)]
      unfold enlargedActiveTerminalFamily
      rw [ite_eq_right (fun h => he h.1), hE, Measure.restrict_zero, integral_zero_measure]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
