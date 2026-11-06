module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
import Mathlib.Tactic

/-! # Uniform localized generator bound for the position-start test -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The source localized quadratic has a uniform generator bound on the active interval. -/
theorem positionStartQuadratic_operator_bound {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (Y : ℝ) (p : Point),
      |c.vbar| = 2 * c.r → p.velocity 0 ∈ c.active →
      |forwardScalarOperator A.a
        (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
          visitQuadratic c (q.velocity 0)) p| ≤
        C * (box 4 c.r Y).indicator (fun _ => (1 : ℝ)) (p.position 0, p.velocity 0) := by
  obtain ⟨D, hD, hd⟩ := positionStartCutoff_deriv_bound
  refine ⟨2 * Lam + 27 * D / 16, by linarith, ?_⟩
  intro A c Y p hc hv
  have hr := c.positive
  let chi := positionStartCutoff Y c.r c.positive
  have hchi := (positionStartCutoff_properties Y c.r c.positive).1
  have h01 := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
  have hq0 := visitQuadratic_nonneg c (subset_closure hv)
  have hq := visitQuadratic_le c (p.velocity 0)
  have hva : |p.velocity 0| ≤ 3 * c.r := by
    have hh := (c.active_abs_bounds hv).2
    linarith
  have ha0 : 0 ≤ A.a (p.position 0) (p.velocity 0) :=
    hlam.le.trans (A.bounds _ _).1
  have ha := (A.bounds (p.position 0) (p.velocity 0)).2
  rw [positionStartQuadratic_operator c chi hchi]
  by_cases hp : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hp]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_mul, abs_mul, abs_of_nonneg ha0,
      abs_of_nonneg h01.1]
    have hfirst : |p.velocity 0| * |deriv chi (p.position 0)| *
        visitQuadratic c (p.velocity 0) ≤
        (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) := by
      apply mul_le_mul (mul_le_mul hva (hd Y c.r c.positive _)
        (abs_nonneg _) (by positivity)) hq hq0 (by positivity)
    have hsecond : 2 * A.a (p.position 0) (p.velocity 0) * chi (p.position 0) ≤
        2 * Lam := by
      have h := mul_le_mul_of_nonneg_left h01.2 (by positivity :
        0 ≤ 2 * A.a _ _)
      linarith
    have he : (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) = 27 * D / 16 := by
      field_simp [c.positive.ne']
      ring
    linarith
  · rw [indicator_of_notMem hp]
    have hnot : p.position 0 ∉ tsupport chi := by
      intro hx
      have hh := positionStartCutoff_tsupport Y c.r c.positive hx
      apply hp
      change |p.position 0 - Y| ≤ 4 * c.r ^ 3 ∧ |p.velocity 0| ≤ 4 * c.r
      grind
    rw [image_eq_zero_of_notMem_tsupport hnot, deriv_of_notMem_tsupport hnot]
    simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
