module

public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryManifold.CayleyCharts
public import GS.Frobenius
public import Mathlib.Data.Complex.BigOperators
public import GS.Unitary.Factorization
public import Mathlib.Topology.Algebra.MulAction
public import GS.CompactFibres
public import GS.OverlapGeometry.HorizontalModel
public import GS.Unitary.Permutations
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Implicit

@[expose] public section


/-!
# The surjective derivative of the dephasing constraints

The anchor constraints are applied to the actual full-unitary Cayley chart.
Explicit row and column phase generators provide a right inverse for their
derivative. No regularity assumption about squared entry moduli is used.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (q : ℕ)
abbrev FullUnitary := BlockU (fun _ : Fin q => 0)
abbrev FullSkewModel := Model (fun _ : Fin q => 0)
end

abbrev AnchorCoordinates (o : Fin q) :=
  (Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)

def fullUnitary (Q : CMat q) (hQ : Unitary Q) : FullUnitary q :=
  ⟨Q, (by tauto), hQ⟩

/-- Imaginary parts of the independent anchor ratios. -/
def anchorImag (Q : CMat q) (o : Fin q) : CMat q →L[ℝ] AnchorCoordinates o :=
  LinearMap.toContinuousLinearMap
    { toFun A := (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im)
      map_add' A B := by ext <;> simp [add_div]
      map_smul' r A := by ext <;> simp [Complex.real_smul, mul_div_assoc] }

section
variable (Q : FullUnitary q) (o : Fin q)
def anchorConstraints (x : FullSkewModel q) :
    AnchorCoordinates o := anchorImag Q.val o (chartInv Q x)

@[simp] theorem anchorConstraints_zero (hQ : AnchorNonzero Q.val Q.val o) : anchorConstraints Q o 0 = 0 := by
  ext j <;> simp [anchorConstraints, anchorImag, div_self (hQ.1 j).1, div_self (hQ.2 _).1]

def anchorDerivative :
    FullSkewModel q →L[ℝ] AnchorCoordinates o :=
  (anchorImag Q.val o).comp (fderiv ℝ (chartInv Q) 0)

theorem anchorConstraints_hasStrictFDerivAt :
    HasStrictFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  ((anchorImag Q.val o).contDiff.comp (chartInv_smooth Q)).contDiffAt.hasStrictFDerivAt'
    (((anchorImag Q.val o).hasFDerivAt).comp 0 ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt) (by simp)

end

theorem anchorDerivative_range (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    LinearMap.range (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun ⟨a, c⟩ => ?_
  let D : (Fin q → ℝ) → CMat q := fun a => diagonal fun i => (a i : ℂ) * Complex.I
  have hD (a) : IsSkewHermitian (D a) := by unfold IsSkewHermitian; simp [D]
  let b : Fin q → ℝ := fun j => if hj : j = o then 0 else c ⟨j, hj⟩ - a o
  refine ⟨⟨(-1/2:ℝ) • (Q.valᴴ * D a * Q.val + D b), by tauto, skewHermitian_real_smul _
    (skewHermitian_add (by simpa using conjugate_skewHermitian Q.valᴴ (D a) (hD a)) (hD b))⟩, ?_⟩
  change anchorImag Q.val o (fderiv ℝ (chartInv Q) 0 _) = _
  rw [chartInv_fderiv_zero]
  change anchorImag Q.val o ((-2 : ℝ) • (Q.val * ((-1 / 2 : ℝ) • (Q.valᴴ * D a * Q.val + D b)))) = _
  rw [Matrix.mul_smul, smul_smul, Matrix.mul_add]
  norm_num [← Matrix.mul_assoc, Q.property.2.2]
  ext j
  · simp [anchorImag, D, b, mul_div_cancel_right₀ _ (hQ.1 j).1]
  · simp [anchorImag, D, b, j.2, mul_div_cancel_right₀ _ (hQ.2 j.val).1, mul_div_cancel_left₀ _ (hQ.2 j.val).1]

end GS.UnitaryLocalModel
