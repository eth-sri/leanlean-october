module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The velocity interval of the forward cylinder. -/
def capacityCylinderInterval (Z0 : Point) (R : ℝ) (hR : 0 < R) : Interval :=
  ⟨Z0.velocity 0 - R, Z0.velocity 0 + R, by linarith⟩

/-- Every forward-cylinder point is an interior pole of its velocity strip. -/
def capacityCylinderPole (Z0 P : Point) (R : ℝ) (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z0 R hR) :
    StripPole (capacityCylinderInterval Z0 R hR) (↑(Z0.time + R ^ 2) : WithTop ℝ) := by
  refine ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, ?_⟩
  have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hP.2.2.1
  have hc := (PDE.abs_apply_le_vecEuclideanNorm (P.velocity - Z0.velocity) 0).trans_lt hn
  simp only [Pi.sub_apply] at hc
  obtain ⟨hl, hu⟩ := abs_lt.mp hc
  change Z0.velocity 0 - R < P.velocity 0 ∧ P.velocity 0 < Z0.velocity 0 + R
  constructor <;> linarith

/-- Exact velocity slices have zero mass in the forward-cylinder velocity strip. -/
theorem cylinder_strip_velocity_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z0 P : Point) (R : ℝ) (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z0 R hR) (v : ℝ) :
    stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP) {p | p.velocity 0 = v} = 0  := by
  have stripGreen_velocity_slice_zero (H : Interval) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
      stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 = v} = 0 := by
    let Γ := stripGreen hH hLE hlam hLam A H T e
    have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
    let S : Set Point := {p | p.velocity 0 = v}
    let C : ℝ := (H.hi - H.lo) / lam
    have hC : 0 < C := div_pos (sub_pos.mpr H.ordered) hlam
    by_contra hz
    have hm :=
      ENNReal.toReal_pos (by simpa using hz) (measure_ne_top Γ S)
    let d := (Γ S).toReal / (4 * C)
    have hd : 0 < d := div_pos hm (by positivity)
    let E : Interval := ⟨v - d, v + d, by linarith⟩
    have hsub : S ⊆ {p | p.velocity 0 ∈ E.carrier} := by
      intro p hp
      change p.velocity 0 = v at hp
      change v - d < p.velocity 0 ∧ p.velocity 0 < v + d
      rw [hp]
      constructor <;> linarith
    have hcap := (measure_mono hsub).trans (strip_capacity hH hLE hlam hLam A H T e E)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
    rw [ENNReal.toReal_ofReal (by
      exact mul_nonneg hC.le (by linarith))] at hr
    change (Γ S).toReal ≤ C * ((v + d) - (v - d)) at hr
    have he : C * ((v + d) - (v - d)) = (Γ S).toReal / 2 := by
      dsimp only [d]
      field_simp
      ring
    rw [he] at hr
    linarith
  exact stripGreen_velocity_slice_zero (capacityCylinderInterval Z0 R hR)
    (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

