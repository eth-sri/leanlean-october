module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit

/-! # The endpoint-inclusive cumulative localized Green identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped Classical

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (Y b : ℝ) (hc : |c.vbar| = 2 * c.r)
    (hJ : closure c.active ⊆ J.carrier) (p : Point) (hv : p.velocity 0 ∈ c.active)

/-- The all-time active occupation has no atom on a fixed time slice. -/
theorem positionStartGreen_ae_time_ne (b : ℝ) :
    ∀ᵐ q ∂stripGreen hlam hLam A c.activeInterval ⊤
      (densityClockPole c p hv), q.time ≠ b := by
  rw [ae_iff]
  simpa using enlarged_stripGreen_time_slice_zero
    hlam hLam A c.activeInterval (densityClockPole c p hv) b

include hc hJ in
/-- The cumulative identity retains a start exactly at `b` as a zero-duration terminal atom. -/
theorem positionStartQuadratic_cumulative_identity :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    ({q : Point | q.time ≤ b}.indicator f) p =
      (∫ q, f q ∂enlargedActiveTerminalFamily hlam hLam A c J b p) -
      ∫ q in {q : Point | q.time ≤ b}, forwardScalarOperator A.a f q
        ∂stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
  dsimp only
  let G := stripGreen hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv)
  have hvJ : p.velocity 0 ∈ (visitActiveUnion c J).carrier := by
    rw [visitActiveUnion_carrier]
    exact ⟨hv, hJ (subset_closure hv)⟩
  by_cases ht : p.time < b
  · rw [indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from ht.le)]
    have hi := positionStartQuadratic_terminal_identity
      hlam hLam A c J Y b hc hJ p hv ht
    dsimp only at hi
    rw [positionStartGreen_eq_restrict hlam hLam A c J b hJ p hv ht] at hi
    have hs : {q : Point | q.time < b} =ᵐ[G] {q | q.time ≤ b} := by
      filter_upwards [positionStartGreen_ae_time_ne hlam hLam A c p hv b] with q hq
      exact propext (lt_iff_le_and_ne.trans (and_iff_left hq))
    rw [Measure.restrict_congr_set hs] at hi
    exact hi
  · have hbp := le_of_not_gt ht
    have hz : G.restrict {q : Point | q.time ≤ b} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      have hn :=
        (stripGreen_infinite_ae_future_carrier hlam hLam A c.activeInterval
          (densityClockPole c p hv)).mono fun q hq => not_le_of_gt (hbp.trans_lt hq.1)
      rw [ae_iff] at hn
      simpa using hn
    rw [hz, integral_zero_measure, sub_zero]
    by_cases he : p.time = b
    · rw [indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from he.le)]
      unfold enlargedActiveTerminalFamily
      rw [ite_eq_left ⟨he, hvJ⟩, integral_dirac]
    · rw [indicator_of_notMem (show p ∉ {q : Point | q.time ≤ b} from
        fun h => he (le_antisymm h hbp))]
      have hp : p ∉ enlargedVisitPoleSet (visitActiveUnion c J) b := fun h => ht h.1
      have hE : enlargedVisitExitKernel hlam hLam A (visitActiveUnion c J) b p =
          0 := by
        change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else
          0) = 0
        rw [dite_eq_right hp]
      unfold enlargedActiveTerminalFamily
      simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
