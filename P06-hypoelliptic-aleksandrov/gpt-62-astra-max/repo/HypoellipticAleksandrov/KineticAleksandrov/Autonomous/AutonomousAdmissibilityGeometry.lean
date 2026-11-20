module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.ClassicalAdmissibility
import Mathlib.Tactic

/-! # The autonomous lift and smooth-near test regularity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory
open scoped MatrixOrder

/-- The scalar autonomous lift is Borel on the literal kinetic carrier. -/
theorem autonomous_lift_measurable {a : ℝ → ℝ → ℝ}
    (ha : Measurable (Function.uncurry a)) :
    Measurable (fullKineticCoefficientAt (autonomousCoefficient a)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact ha.comp (((continuous_apply 0).comp continuous_position).measurable.prodMk
    (((continuous_apply 0).comp continuous_velocity).measurable))

/-- The one-dimensional lift is symmetric at every point. -/
theorem autonomous_lift_symm (a : ℝ → ℝ → ℝ) (P : Point) :
    (fullKineticCoefficientAt (autonomousCoefficient a) P).IsSymm := by
  ext i j
  rfl

/-- The scalar range gives pointwise matrix ellipticity without an exceptional set. -/
theorem autonomous_lift_elliptic {a : ℝ → ℝ → ℝ} {lam Lam : ℝ}
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (P : Point) :
    lam • (1 : PDE.Mat 1) ≤ fullKineticCoefficientAt (autonomousCoefficient a) P ∧
      fullKineticCoefficientAt (autonomousCoefficient a) P ≤ Lam • (1 : PDE.Mat 1) := by
  have he : fullKineticCoefficientAt (autonomousCoefficient a) P =
      a (P.position 0) (P.velocity 0) • (1 : PDE.Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [fullKineticCoefficientAt, autonomousCoefficient]
  rw [he]
  have hI : (0 : PDE.Mat 1) ≤ 1 :=
    Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
  exact ⟨smul_le_smul_of_nonneg_right (hb _ _).1 hI,
    smul_le_smul_of_nonneg_right (hb _ _).2 hI⟩

theorem fullElliptic_of_bounds {lam Lam : ℝ} {a : ℝ → ℝ → ℝ}
    (hm : Measurable (Function.uncurry a)) (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) :
    FullElliptic lam Lam (autonomousCoefficient a) :=
  ⟨autonomous_lift_measurable hm, autonomous_lift_symm a,
    Filter.Eventually.of_forall fun P => (autonomous_lift_elliptic hb P).1,
    Filter.Eventually.of_forall fun P => (autonomous_lift_elliptic hb P).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
