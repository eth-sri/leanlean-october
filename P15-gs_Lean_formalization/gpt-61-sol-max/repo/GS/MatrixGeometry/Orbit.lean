import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Factors

import GS.LieAction.CompactQuotient
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular



/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InSharedA2Unitary` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}

variable (P X : KMat 𝕜 n)

variable (g : Factors right left)

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InSharedA2Unitary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : KMat 𝕜 n) : Prop :=
  ∃ L R : KMat 𝕜 n, SharedUnitaryFactor b₂ τ₂ L ∧
    SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.MatrixBase.product2 L P R

instance factorsMulAction (right left : Pattern 𝕜 n) :
    MulAction (Factors right left) (KMat 𝕜 n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : KMat 𝕜 n) * X * (1 : KMat 𝕜 n)ᴴ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) *
        (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply  (X : KMat 𝕜 n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern 𝕜 n) :
    ContinuousSMul (Factors right left) (KMat 𝕜 n) where
  continuous_smul := by simp_rw [action_apply]; fun_prop [Factor.matrix]

def orbitMap (right left : Pattern 𝕜 n) (P : KMat 𝕜 n) : Factors right left → KMat 𝕜 n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern 𝕜 n) (P : KMat 𝕜 n) :=
  ↥(MulAction.orbit (Factors right left) P)

theorem continuous_orbitMap  : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared  :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InSharedA2Unitary right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    simpa only [action_apply, Factor.matrix, Factor.ofMatrix, Matrix.conjTranspose_conjTranspose,
      GS.MatrixBase.product2] using hX.symm

theorem orbit_set_eq_inShared  :
    MulAction.orbit (Factors right left) P =
      {X | InSharedA2Unitary right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern 𝕜 n) (P : KMat 𝕜 n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit  :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit  :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩





theorem action_cFrobInner  (X Y : KMat 𝕜 n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y :=
by
  change cFrobInner (Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ)
    (Factor.matrix g.1 * Y * (Factor.matrix g.2)ᴴ) = _
  rw [cFrobInner_right_unitary _ (Factor.matrix_unitary g.2).conjTranspose,
    cFrobInner_left_unitary _ (Factor.matrix_unitary g.1)]

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv  : KMat 𝕜 n ≃ₗ[ℝ] KMat 𝕜 n :=
  { toFun X := g • X
    invFun X := g⁻¹ • X
    left_inv X := inv_smul_smul g X
    right_inv X := smul_inv_smul g X
    map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' a X := by simp [] }



/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap  :
    IsOpenMap (orbitMapToOrbit right left P) := by
  letI : CompactSpace (MatrixOrbit right left P) :=
    Function.Surjective.compactSpace (continuous_orbitMapToOrbit P) (surjective_orbitMapToOrbit P)
  letI : ContinuousSMul (Factors right left) (MatrixOrbit right left P) :=
    Topology.IsInducing.subtypeVal.continuousSMul continuous_id rfl
  exact isOpenMap_smul_of_sigmaCompact (⟨P,⟨1,one_smul _ _⟩⟩ : MatrixOrbit right left P)

end GS.MatrixGeometry
