module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity
import Mathlib.Tactic

/-! # No velocity atoms in the actual killed Green measure -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Capacity implies that every exact velocity slice has zero occupation mass. -/
theorem stripGreen_velocity_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (v : ℝ) :
    stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 = v} = 0 := by
  let Γ := stripGreen hH hLE hlam hLam A H T e
  have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
  let S : Set Point := {p | p.velocity 0 = v}
  let C  := (H.hi - H.lo) / lam
  have hC : 0 < C := div_pos (sub_pos.mpr H.ordered) hlam
  by_contra hz
  have hm : 0 < (Γ S).toReal :=
    ENNReal.toReal_pos (by omega) (measure_ne_top Γ S)
  let d := (Γ S).toReal / (4 * C)
  have hd : 0 < d := div_pos hm (by positivity)
  let E : Interval := ⟨v - d, v + d, by linarith⟩
  have hsub : S ⊆ {p | p.velocity 0 ∈ E.carrier} := by
    intro p hp
    change p.velocity 0 = v at hp
    change v - d < p.velocity 0 ∧ p.velocity 0 < v + d
    simp_all
  have hcap := (measure_mono hsub).trans (strip_capacity hH hLE hlam hLam A H T e E)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
  rw [ENNReal.toReal_ofReal (by
    exact mul_nonneg hC.le (by linarith))] at hr
  have he : C * ((v + d) - (v - d)) = (Γ S).toReal / 2 := by
    grind
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
