module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCylinderCount

/-! # The cylinder core domination and continuation conclusions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

/-- The original cylinder strip Green is dominated on the core by the actual visit Green measure. -/
theorem core_green_le_visitGreen
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (enlargedActiveGreen A c
      (visitStartsQ A c Z0 R hR P hP)).restrict
        {q | q.velocity 0 ∈ c.core} := by
  have hp := visitCylinderStart_mem Z0 R hR P hP
  have hd := visitOuterGreen_core_domination A c
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) P hp
  rw [visitOuterGreen_eq_strip A _ _ _ P hp] at hd
  exact hd

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
