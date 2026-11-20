module

public import GS.Shared.Factors

public import GS.Shared.Frobenius

public import Mathlib.GroupTheory.GroupAction.Quotient

public import Mathlib.Topology.Algebra.Group.Quotient

public import Mathlib.Topology.Algebra.Group.OpenMapping

public import Mathlib.Topology.Baire.LocallyCompactRegular

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared orthogonal or unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InSharedA2Unitary` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

set_option autoImplicit false

noncomputable section
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : ℕ} {right left : Pattern 𝕜 n}

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InSharedA2Unitary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : M 𝕜 n) : Prop :=
  ∃ L R : M 𝕜 n, SharedUnitaryFactor b₂ τ₂ L ∧
    SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.Shared.product2 L P R

instance factorsMulAction (right left : Pattern 𝕜 n) :
    MulAction (Factors right left) (M 𝕜 n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : M 𝕜 n) * X * (1 : M 𝕜 n)ᴴ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) *
        (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : M 𝕜 n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern 𝕜 n) :
    ContinuousSMul (Factors right left) (M 𝕜 n) where
  continuous_smul := by
    change Continuous (fun p : Factors right left × M 𝕜 n =>
      Factor.matrix p.1.1 * p.2 * (Factor.matrix p.1.2)ᴴ)
    fun_prop

abbrev MatrixOrbit (right left : Pattern 𝕜 n) (P : M 𝕜 n) :=
  ↥(MulAction.orbit (Factors right left) P)

theorem orbit_iff_inShared (P X : M 𝕜 n) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InSharedA2Unitary right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, rfl⟩
    exact ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), by
      simp [product2]⟩

theorem orbit_set_eq_inShared (P : M 𝕜 n) :
    MulAction.orbit (Factors right left) P =
      {X | InSharedA2Unitary right.size left.size right.label left.label P X} := by
  grind [orbit_iff_inShared]

def orbitMapToOrbit (right left : Pattern 𝕜 n) (P : M 𝕜 n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : M 𝕜 n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_id.smul continuous_const).subtype_mk _

theorem surjective_orbitMapToOrbit (P : M 𝕜 n) :
    Function.Surjective (orbitMapToOrbit right left P) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

def actionLinearEquiv (g : Factors right left) : M 𝕜 n ≃ₗ[ℝ] M 𝕜 n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp

instance orbitContinuousSMul (P : M 𝕜 n) : ContinuousSMul (Factors right left) (MatrixOrbit right left P) :=
  ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

theorem orbitMapToOrbit_isOpenMap (P : M 𝕜 n) :
    IsOpenMap (orbitMapToOrbit right left P) := by
  have : CompactSpace (MatrixOrbit right left P) :=
    Function.Surjective.compactSpace (continuous_orbitMapToOrbit P) (surjective_orbitMapToOrbit P)
  exact isOpenMap_smul_of_sigmaCompact (G := Factors right left)
    (⟨P, MulAction.mem_orbit_self P⟩ : MatrixOrbit right left P)

end GS.Shared
