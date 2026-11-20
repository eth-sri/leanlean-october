module

public import GS.Shared.Orbit

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factor-independent infinitesimal directions for shared layers

The point map (A,B) |-> A X + X B is defined directly from X.  Conjugation
closure of the tied generator spaces identifies its range with the old
factor-coordinate formula for every valid factorization.  Thus the range
and the set of realized tied-factor velocities do not depend on that choice.

`pointDirections` is deliberately not called a tangent bundle.  The full
shared-orbit atlas and identification with its manifold differential are
constructed in the later atlas and tangent-bridge modules.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix ContinuousLinearMap
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : ℕ} {right left : Pattern 𝕜 n}

abbrev PairGenerator (right left : Pattern 𝕜 n) := Generator left × Generator right

/-- The differential at zero of the left/right Cayley parametrization. -/
def orbitDerivative (right left : Pattern 𝕜 n) (X : M 𝕜 n) :
    PairGenerator right left →L[ℝ] M 𝕜 n :=
  (-2 : ℝ) • ((mulCLM.flip X ∘L (sharedSkewSpace left.size left.label).subtypeL ∘L fst ℝ _ _) -
    (mulCLM X ∘L (sharedSkewSpace right.size right.label).subtypeL ∘L snd ℝ _ _))

@[simp] theorem orbitDerivative_apply (X : M 𝕜 n) (v : PairGenerator right left) :
    orbitDerivative right left X v = (-2 : ℝ) • (v.1.val * X - X * v.2.val) := rfl

def pointDirections (right left : Pattern 𝕜 n) (X : M 𝕜 n) : Submodule ℝ (M 𝕜 n) :=
  (orbitDerivative right left X).range

def SharedDirections (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : M 𝕜 n) : Prop :=
  ∃ A B : M 𝕜 n, A ∈ sharedSkewSpace b₂ τ₂ ∧ B ∈ sharedSkewSpace b₁ τ₁ ∧ Z = A * X + X * B

theorem mem_pointDirections_iff (X Y : M 𝕜 n) :
    Y ∈ pointDirections right left X ↔ SharedDirections right.size left.size right.label left.label X Y := by
  constructor
  · rintro ⟨⟨A, B⟩, rfl⟩
    refine ⟨(-2 : ℝ) • A.val, (2 : ℝ) • B.val,
      Submodule.smul_mem _ _ A.property, Submodule.smul_mem _ _ B.property, ?_⟩
    simp [orbitDerivative_apply, sub_eq_add_neg]
  · rintro ⟨A, B, hA, hB, rfl⟩
    refine ⟨((-1/2 : ℝ) • (⟨A,hA⟩ : Generator left),
      (1/2 : ℝ) • (⟨B,hB⟩ : Generator right)), ?_⟩
    norm_num [smul_sub, smul_smul, sub_eq_add_neg]

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : M 𝕜 n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, B, hA, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, R * B * Rᴴ, sharedSkew_conjugate left.divides hL hA,
    sharedSkew_conjugate right.divides hR hB, ?_⟩
  change L * Y * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) + (L * X * Rᴴ) * (R * B * Rᴴ)
  have hLu : Unitary L := hL.2.1
  have hRu : Unitary R := hR.2.1
  grind [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hLu.adjoint_mul_cancel, hRu.adjoint_mul_cancel]

theorem action_pointDirections (g : Factors right left) (X : M 𝕜 n) :
    (pointDirections right left X).map (actionLinearEquiv g).toLinearMap =
      pointDirections right left (g • X) := by
  ext Y
  rw [Submodule.mem_map_equiv]
  change g⁻¹ • Y ∈ pointDirections right left X ↔ _
  grind [smul_inv_smul, action_mem_pointDirections, inv_smul_smul]

end GS.Shared
