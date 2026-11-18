module

public import GS.UnitaryManifold.BlockGroup
public import GS.Unitary.Frobenius
public import GS.Unitary.Factorization
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two-sided action, its orbit, and smooth ambient matrix operations

This is an actual mathlib MulAction and ContinuousSMul, not an orbit-shaped
existential definition. ContDiff below is in ambient matrix coordinates.
It does not assert a charted-space structure on BlockU or on its orbit.

All smoothness statements use real scalar coordinates.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ}

instance factorMulAction (block₁ block₂ : Fin n → ℕ) :
    MulAction (FactorGroup block₁ block₂) (CMat n) where
  smul g X := g.1.val * X * g.2.valᴴ
  one_smul X := by
    change ((1 : CMat n) * X) * (1 : CMat n)ᴴ = X
    simp
  mul_smul g h X := by
    change ((g.1.val * h.1.val) * X) * (g.2.val * h.2.val)ᴴ =
      (g.1.val * ((h.1.val * X) * h.2.valᴴ)) * g.2.valᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X : CMat n) :
    g • X = (g.1 : CMat n) * X * (g.2 : CMat n)ᴴ := rfl

instance factorContinuousSMul (block₁ block₂ : Fin n → ℕ) :
    ContinuousSMul (FactorGroup block₁ block₂) (CMat n) where
  continuous_smul := by
    change Continuous (fun p : FactorGroup block₁ block₂ × CMat n =>
      p.1.1.val * p.2 * p.1.2.valᴴ)
    exact continuous_matrix_product
      (continuous_matrix_product
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (continuous_matrix_conjTranspose
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))

/-- The concrete orbit map. P may be any matrix for this definition. -/
def orbitMap (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    FactorGroup block₁ block₂ → CMat n := fun g => g • P

theorem continuous_orbitMap (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    Continuous (orbitMap block₁ block₂ P) := by
  exact continuous_id.smul continuous_const

theorem orbit_eq_range (block₁ block₂ : Fin n → ℕ) (P : CMat n) :
    MulAction.orbit (FactorGroup block₁ block₂) P =
      Set.range (orbitMap block₁ block₂ P) := rfl

theorem action_cFrobInner {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : CMat n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y := by
  change cFrobInner (g.1.val * X * g.2.valᴴ)
    (g.1.val * Y * g.2.valᴴ) = _
  rw [cFrobInner_right_unitary _ g.2.property.2.conjTranspose,
    cFrobInner_left_unitary _ g.1.property.2]

/-- A fixed group element is a linear equivalence of the ambient matrix space.
No assertion about an inappropriate default matrix norm is made. -/
def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : CMat n ≃ₗ[ℝ] CMat n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Smooth multiplication written componentwise so it uses the ordinary
finite-product matrix norm, not an assumed operator-norm inner product. -/
theorem smooth_matrix_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → CMat n} (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum; intro k _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

end GS.UnitaryManifold
