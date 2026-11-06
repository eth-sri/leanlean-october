
import GS.UnitaryLocalModel.Dephasing
import GS.UnitaryManifold.LocalProduct
import Mathlib.Analysis.Calculus.Implicit



/-!
# The surjective derivative of the dephasing constraints

The anchor constraints are applied to the actual full-unitary Cayley chart.
Explicit row and column phase generators provide a right inverse for their
derivative. No regularity assumption about squared entry moduli is used.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryManifold
namespace GS.UnitaryLocalModel

variable (Q A : CMat q)

variable (o : Fin q)

abbrev FullUnitary (q : ℕ) := BlockU (fun _ : Fin q => 0)
abbrev FullSkewModel (q : ℕ) := Model (fun _ : Fin q => 0)
abbrev AnchorCoordinates  :=
  (Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)

def fullUnitary  (hQ : Unitary Q) : FullUnitary q :=
  ⟨Q, (by tauto), hQ⟩

/-- Imaginary parts of the independent anchor ratios. -/
def anchorImagLinear   : CMat q →ₗ[ℝ] AnchorCoordinates o where
  toFun A := (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im)
  map_add' A B := by ext <;> simp_all [add_div,Complex.add_im]
  map_smul' r A := by ext <;> simp_all [mul_div_assoc,Complex.mul_im,Complex.real_smul]

def anchorImag   : CMat q →L[ℝ] AnchorCoordinates o :=
  (anchorImagLinear Q o).toContinuousLinearMap




variable (Q : FullUnitary q) (o : Fin q)
def anchorConstraints (x : FullSkewModel q) :
    AnchorCoordinates o := anchorImag Q.val o (chartInv Q x)

theorem anchorConstraints_smooth :
    ContDiff ℝ ⊤ (anchorConstraints Q o) :=
  (anchorImag Q.val o).contDiff.comp (chartInv_smooth Q)

@[simp] theorem anchorConstraints_zero (hQ : AnchorNonzero Q.val Q.val o) : anchorConstraints Q o 0 = 0 := by
  simp_all [anchorConstraints,anchorImag,anchorImagLinear,AnchorNonzero,funext_iff]


def anchorDerivative :
    FullSkewModel q →L[ℝ] AnchorCoordinates o :=
  (anchorImag Q.val o).comp (fderiv ℝ (chartInv Q) 0)

theorem anchorConstraints_hasFDerivAt :
    HasFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  ((anchorImag Q.val o).hasFDerivAt).comp 0
    ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt

theorem anchorConstraints_hasStrictFDerivAt :
    HasStrictFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  (anchorConstraints_smooth Q o).contDiffAt.hasStrictFDerivAt'
    (anchorConstraints_hasFDerivAt Q o) (by simp)

/-- Infinitesimal diagonal phases. -/
def phaseDiagonal (a : Fin q → ℝ) := Matrix.diagonal (fun i => (a i : ℂ) * Complex.I)

theorem phaseDiagonal_skew (a : Fin q → ℝ) : IsSkewHermitian (phaseDiagonal a) := by
  simp_all [GS.IsSkewHermitian, GS.UnitaryLocalModel.phaseDiagonal]

/-- A Cayley coordinate whose velocity is the prescribed row/column phase variation. -/
def phaseCoordinate (a b : Fin q → ℝ) : FullSkewModel q :=
  ⟨(-1 / 2 : ℝ) • (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal b),
    (by tauto),
    skewAdjoint.smul_mem _ ((skewAdjoint _).add_mem
      (skewAdjoint.conjugate' (phaseDiagonal_skew a) Q.val)
      (phaseDiagonal_skew b))⟩

theorem phaseCoordinate_velocity (a b : Fin q → ℝ) :
    fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a b) =
      phaseDiagonal a * Q.val + Q.val * phaseDiagonal b := by
  rw [chartInv_fderiv_zero]
  change (-2 : ℝ) • (Q.val * ((-1 / 2 : ℝ) •
    (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal b))) = _
  rw [Matrix.mul_smul, smul_smul]
  norm_num
  rw [Matrix.mul_add]
  congr 1
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

theorem phaseCoordinate_constraints (hQ : AnchorNonzero Q.val Q.val o) (a : Fin q → ℝ) (b : zeroAnchorSpace o) :
    anchorDerivative Q o (phaseCoordinate Q a b.val) = phaseConstraintMap o (a,b) := by
  change anchorImag Q.val o (fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a b.val)) = _
  rw [phaseCoordinate_velocity]
  have hb : b.val o = 0 := b.property
  apply Prod.ext
  · funext i
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal b.val) i o) / Q.val i o).im = a i
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, hb,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    rw [mul_div_cancel_right₀ _ (hQ.1 i).1]
    simp
  · funext j
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal b.val) o j.val) /
      Q.val o j.val).im = a o + b.val j.val
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [add_div, mul_div_cancel_right₀ _ (hQ.2 j.val).1,
      mul_div_cancel_left₀ _ (hQ.2 j.val).1]
    simp

/-- Surjectivity is proved by explicit phase directions, not assumed. -/
theorem anchorDerivative_surjective (hQ : AnchorNonzero Q.val Q.val o) : Function.Surjective (anchorDerivative Q o) := by
  intro y
  obtain ⟨⟨a,b⟩, hab⟩ := phaseConstraintMap_surjective o y
  exact ⟨phaseCoordinate Q a b.val, (phaseCoordinate_constraints Q o hQ a b).trans hab⟩

theorem anchorDerivative_range (hQ : AnchorNonzero Q.val Q.val o) : LinearMap.range (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o) = ⊤ :=
  LinearMap.range_eq_top.mpr (anchorDerivative_surjective Q o hQ)

end GS.UnitaryLocalModel
