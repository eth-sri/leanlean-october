module

public import GS.Isometric.Layers
public import GS.Isometric.Metric
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The shared matrix family as a compact homogeneous space

The action is L X R*, with actual shared unitary factors and conjugate transpose R*.
Its orbit is
exactly the previously defined `InOrbit` family.  Compactness gives a
homeomorphism from the genuine stabilizer quotient to the matrix subspace;
the orbit map is an open quotient map, also with continuous stabilizers.

These are topological statements.  They do not identify a smooth quotient or
replace the missing shared-orbit atlas by an assumed manifold structure.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Layer 𝕜 n}

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InOrbit (right left : Layer 𝕜 n) (P X : Square 𝕜 n) : Prop :=
  ∃ L R : Square 𝕜 n, SharedFactor left L ∧
    SharedFactor right R ∧ X = product₂ L P R

instance factorsMulAction (right left : Layer 𝕜 n) :
    MulAction (Factors right left) (Square 𝕜 n) where
  smul g X := Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ
  one_smul X := by
    change (1 : Square 𝕜 n) * X * (1 : Square 𝕜 n)ᴴ = X
    simp
  mul_smul g h X := by
    change (Factor.matrix g.1 * Factor.matrix h.1) * X *
      (Factor.matrix g.2 * Factor.matrix h.2)ᴴ =
      Factor.matrix g.1 * (Factor.matrix h.1 * X * (Factor.matrix h.2)ᴴ) *
        (Factor.matrix g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : Factors right left) (X : Square 𝕜 n) :
    g • X = Factor.matrix g.1 * X * (Factor.matrix g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Layer 𝕜 n) :
    ContinuousSMul (Factors right left) (Square 𝕜 n) where
  continuous_smul := by
    simp
    fun_prop

def orbitMap (right left : Layer 𝕜 n) (P : Square 𝕜 n) : Factors right left → Square 𝕜 n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Layer 𝕜 n) (P : Square 𝕜 n) :=
  ↥(MulAction.orbit (Factors right left) P)

theorem continuous_orbitMap (P : Square 𝕜 n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : Square 𝕜 n) :
    X ∈ MulAction.orbit (Factors right left) P ↔
      InOrbit right left P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Factor.matrix g.1, (Factor.matrix g.2)ᴴ, Factor.matrix_shared g.1,
      shared_factor_conjTranspose (Factor.matrix_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(Factor.ofMatrix L hL, Factor.ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    change L * P * (Rᴴ)ᴴ = X; simpa [product₂] using hX.symm

theorem orbit_set_eq_inShared (P : Square 𝕜 n) :
    MulAction.orbit (Factors right left) P =
      {X | InOrbit right left P X} := by
  ext X
  apply orbit_iff_inShared

def orbitMapToOrbit (right left : Layer 𝕜 n) (P : Square 𝕜 n) :
    Factors right left → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩

theorem continuous_orbitMapToOrbit (P : Square 𝕜 n) :
    Continuous (orbitMapToOrbit right left P) :=
  (continuous_orbitMap P).subtype_mk _

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : Factors right left) : Square 𝕜 n ≃ₗ[ℝ] Square 𝕜 n where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  map_add' _ _ := by simp [Matrix.add_mul, Matrix.mul_add]
  map_smul' _ _ := by simp [Matrix.smul_mul, Matrix.mul_smul]

/-- Orbit-stabilizer is a homeomorphism: the quotient is compact and the
matrix image Hausdorff. Thus the orbit map is open in the inherited topology. -/
theorem orbitMapToOrbit_isOpenMap (P : Square 𝕜 n) : IsOpenMap (orbitMapToOrbit right left P) := by
  let e := (MulAction.orbitEquivQuotientStabilizer (Factors right left) P).symm
  have he : Continuous e := continuous_coinduced_dom.2 (continuous_orbitMapToOrbit P)
  exact he.homeoOfEquivCompactToT2.isOpenMap.comp QuotientGroup.isOpenMap_coe

end GS.Isometric
