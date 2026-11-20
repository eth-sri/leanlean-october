module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum

/-!
# Coefficient fields and ellipticity

This module fixes the curried time--velocity coefficient convention and the
Mathlib Loewner-order ellipticity predicates.  It also proves the matrix-level
positive-definiteness and determinant consequences of a positive lower bound.
-/

@[expose] public section

open scoped BigOperators ContDiff MatrixOrder Matrix.Norms.Elementwise
open Matrix
open MeasureTheory

namespace HypoellipticAleksandrov

/-- The product measurable-space structure on finite real matrices used for coefficient fields. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance

/-- A real matrix-valued coefficient field, curried in time and velocity. -/
abbrev CoefficientField (d : ℕ) := ℝ → PDE.Vec d → PDE.Mat d

section
variable {d : ℕ} (lam : ℝ) (Lam : ℝ) (A : CoefficientField d)

include A in
/-- Evaluates a curried coefficient field at a time--velocity pair. -/
def coefficientAt (z : ℝ × PDE.Vec d) : PDE.Mat d :=
  A z.1 z.2

include A in
/-- A coefficient field is Borel measurable on time--velocity space. -/
def IsBorelCoefficient : Prop :=
  Measurable (coefficientAt A)

include A in
/-- A coefficient field is continuous on time--velocity space. -/
def IsContinuousCoefficient : Prop :=
  Continuous (coefficientAt A)

include A in
/-- A coefficient field is smooth on time--velocity space. -/
def IsSmoothCoefficient : Prop :=
  ContDiff ℝ ∞ (coefficientAt A)

include A in
/-- Every coefficient matrix is symmetric. -/
def IsSymmetricCoefficient : Prop :=
  ∀ t v, (A t v).IsSymm

include lam A in
/-- A pointwise lower Loewner ellipticity bound. -/
def HasLowerEllipticity : Prop :=
  ∀ t v, lam • (1 : PDE.Mat d) ≤ A t v

include Lam A in
/-- A pointwise upper Loewner ellipticity bound. -/
def HasUpperEllipticity : Prop :=
  ∀ t v, A t v ≤ Lam • (1 : PDE.Mat d)

include lam A in
/-- An almost-everywhere lower Loewner ellipticity bound for product volume. -/
def HasLowerEllipticityAE : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), lam • (1 : PDE.Mat d) ≤ coefficientAt A z

include Lam A in
/-- An almost-everywhere upper Loewner ellipticity bound for product volume. -/
def HasUpperEllipticityAE : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), coefficientAt A z ≤ Lam • (1 : PDE.Mat d)

end

section
variable {d : ℕ} {lam : ℝ} {A : PDE.Mat d} (hlam : 0 < lam) (hA : A.IsSymm)
    (hlo : lam • (1 : PDE.Mat d) ≤ A)

include hlo in
/-- A Loewner lower bound, with no sign condition on `lam`, gives the
corresponding coordinate quadratic lower bound. -/
theorem vecDot_mulVec_lower_of_loewner (x : PDE.Vec d) :
    lam * PDE.vecNormSq x ≤ PDE.vecDot x (A *ᵥ x) := by
  have hquad := (Matrix.le_iff.mp hlo).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  exact sub_nonneg.mp hquad

include hlam in
/-- A positive lower Loewner bound makes a real matrix positive definite. -/
theorem posDef_of_loewner_lower (hA : lam • (1 : PDE.Mat d) ≤ A) : A.PosDef := by
  have hsplit : A = lam • 1 + (A - lam • 1) := by
    abel
  rw [hsplit]
  exact (Matrix.PosDef.one.smul hlam).add_posSemidef (Matrix.le_iff.mp hA)

include hlam hlo in
/-- A positive lower Loewner bound gives the sharp determinant lower bound. -/
theorem det_lower_of_loewner : lam ^ d ≤ A.det := by
  classical
  have hA := posDef_of_loewner_lower hlam hlo
  have heigen : ∀ i : Fin d, lam ≤ hA.isHermitian.eigenvalues i := by
    intro i
    have hnonneg := (Matrix.le_iff.mp hlo).dotProduct_mulVec_nonneg (⇑(hA.isHermitian.eigenvectorBasis i))
    rw [dotProduct_comm] at hnonneg
    have hsub : 0 ≤ hA.isHermitian.eigenvalues i - lam := by
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hA.isHermitian.mulVec_eigenvectorBasis, sub_dotProduct, smul_dotProduct,
        ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, hA.isHermitian.eigenvectorBasis.orthonormal.1 i,
        smul_eq_mul] at hnonneg
      norm_num at hnonneg
      exact sub_nonneg.mpr hnonneg
    exact sub_nonneg.mp hsub
  calc
    lam ^ d = ∏ _i : Fin d, lam := by simp
    _ ≤ ∏ i : Fin d, hA.isHermitian.eigenvalues i :=
      Finset.prod_le_prod₀
        (fun _ _ => hlam.le)
        (fun i _ => heigen i)
    _ = A.det := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues]
      simp

end

namespace HasLowerEllipticity

/-- A positive pointwise lower ellipticity bound gives pointwise positive definiteness. -/
theorem posDef {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    (h : HasLowerEllipticity lam A) (hlam : 0 < lam) (t : ℝ) (v : PDE.Vec d) :
    (A t v).PosDef :=
  posDef_of_loewner_lower hlam (h t v)

end HasLowerEllipticity

end HypoellipticAleksandrov
