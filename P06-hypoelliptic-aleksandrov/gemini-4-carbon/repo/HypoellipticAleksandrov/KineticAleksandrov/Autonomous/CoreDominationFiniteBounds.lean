module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The actual Green kernels satisfy the source's finite alternating identity. -/
theorem visitAlternating_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let GA := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let GO := visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P
    GO P = visitInitialGreen P (visitEntranceInterval c) GW +
      ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N := by
  apply alternating_green_of_nested_splitting
  · exact (visitInitial_nested hH hLE hlam hLam A c J s T hT P hP).1
  · intro n
    exact (visitEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).1
  · intro n
    exact (visitOutgoing_nested hH hLE hlam hLam A c J s T hT P n).1



/-- Positive terms of a finite alternating identity are bounded by the original measure. -/
theorem visit_positive_partial_le (mu initial remainder : Measure Point)
    (active waiting : ℕ → Measure Point) (N : ℕ)
    (h : mu = initial + ∑ n ∈ Finset.range N, (active n + waiting n) + remainder) :
    ∑ n ∈ Finset.range N, active n ≤ mu := by
  intro B
  rw [h]
  simp
  calc
    _ ≤ ∑ n ∈ Finset.range N, (active n B + waiting n B) :=
      Finset.sum_le_sum (fun n _ => le_add_of_nonneg_right zero_le)
    _ ≤ initial B + ∑ n ∈ Finset.range N, (active n B + waiting n B) :=
      le_add_of_nonneg_left zero_le
    _ ≤ _ := le_add_of_nonneg_right zero_le

/-- The actual active Green occupations in any finite visit sum are dominated by the outer Green. -/
theorem visitActiveGreen_partial_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n ≤
          visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P :=
  visit_positive_partial_le _ _ _ _ _ N
    (visitAlternating_green hH hLE hlam hLam A c J s T hT P hP N)

/-- Active outer-face exits in any finite visit sum are dominated by the outer exit. -/
theorem visitActiveExit_partial_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
          (finiteUnionExitSet J.toFiniteUnion s T) ≤
            visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T P  := by
  have visitAlternating_exit :
    let EW := visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let EO := visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    EO P = visitInitialExit P (visitEntranceInterval c) outer EW +
      ∑ n ∈ Finset.range N,
        (((visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T) ∘ₘ gamma n).restrict outer + (EW ∘ₘ (visitOutgoingPiece hH hLE hlam hLam A c J s T P) n).restrict outer) +
          EO ∘ₘ gamma N := by
    apply alternating_exit_of_nested_splitting
    · exact (visitInitial_nested hH hLE hlam hLam A c J s T hT P hP).2
    · intro n
      exact (visitEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).2
    · intro n
      exact (visitOutgoing_nested hH hLE hlam hLam A c J s T hT P n).2
  exact visit_positive_partial_le _ _ _ _ _ N
    (visitAlternating_exit)

/-- Finite sums of finite measures evaluate in real mass by summing their real masses. -/
theorem visit_partial_real_mass (mu : ℕ → Measure Point) [∀ n, IsFiniteMeasure (mu n)]
    (N : ℕ) (B : Set Point) (_hB : MeasurableSet B) :
    ((∑ n ∈ Finset.range N, mu n) B).toReal = ∑ n ∈ Finset.range N, (mu n B).toReal := by
  rw [Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun n _ => measure_ne_top (mu n) B)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

