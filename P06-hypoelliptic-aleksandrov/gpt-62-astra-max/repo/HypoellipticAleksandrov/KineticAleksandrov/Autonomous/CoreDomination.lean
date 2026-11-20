module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationEnlarged

/-! # The cylinder core domination and continuation conclusions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

/-- The original cylinder strip Green is dominated on the core by the actual visit Green measure. -/
theorem core_green_le_visitGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP)).restrict
        {q | q.velocity 0 ∈ c.core} := by
  have hp := visitCylinderStart_mem Z0 R hR P hP
  have hd := visitOuterGreen_core_domination hH hLE hlam hLam A c
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) P hp
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A _ _ _ P hp] at hd
  exact hd

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
