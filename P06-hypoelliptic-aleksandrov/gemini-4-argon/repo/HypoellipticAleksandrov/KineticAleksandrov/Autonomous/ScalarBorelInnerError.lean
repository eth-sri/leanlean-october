module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelConvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated

/-! # The autonomous scalar coefficient defect on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/- The literal scalar Hessian contraction defect; the classical solution stays fixed. -/
def scalarBorelError (C a : ℝ → ℝ → ℝ) (H : Point → ℝ) (P : Point) : ℝ :=
  |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P|

/- The autonomous operator difference is exactly the negative scalar contraction. -/
theorem scalar_borel_error_bound {lam Lam } (hlam : 0 < lam)
    {C a } (hC : ∀ x v, lam ≤ C x v ∧ C x v ≤ Lam)
    (ha : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (H : Point → ℝ) (P : Point) :
    scalarBorelError C a H P ≤ 2 * Lam * |H P| := by
  change |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hl := hC (P.position 0) (P.velocity 0)
  have hr := ha (P.position 0) (P.velocity 0)
  apply abs_le.mpr
  constructor <;> linarith

/- For a fixed compact set and continuous Hessian, the scalar defect vanishes in Lp. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
