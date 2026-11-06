module

public import GS.Shared.MinimumNormLift

@[expose] public section


/-!
# Equivariance of the minimum-physical-norm shared lift

Both spatial generators transform by unitary conjugation. This preserves
the actual tied generator spaces, their physical Frobenius pairing, and the
synthesis kernel. Uniqueness of the horizontal lift then proves equivariance
without choosing a section of the orbit map.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- Conjugation acts separately on the two full shared generator matrices. -/
def generatorAction (g : Factors right left) :
    PairGenerator right left →ₗ[ℝ] PairGenerator right left where
  toFun v :=
    (⟨Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᴴ,
      sharedSkew_conjugate left.positive left.divides (Factor.matrix_shared g.1) v.1.property⟩,
     ⟨Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᴴ,
      sharedSkew_conjugate right.positive right.divides (Factor.matrix_shared g.2) v.2.property⟩)
  map_add' v w := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' a v := by
    simp

section
variable (g : Factors right left) (v : PairGenerator right left)
@[simp] theorem generatorAction_left :
    (generatorAction g v).1.val = Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᴴ := rfl

@[simp] theorem generatorAction_right :
    (generatorAction g v).2.val = Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᴴ := rfl

end

section
variable (g : Factors right left)
@[simp] theorem generatorAction_inverse (v : PairGenerator right left) :
    generatorAction g⁻¹ (generatorAction g v) = v := by
  have := g.1.matrix_unitary
  have := g.2.matrix_unitary
  apply Prod.ext <;> apply Subtype.ext <;> simp_all [Factor.matrix, ← Matrix.mul_assoc, Uni, Matrix.star_eq_conjTranspose] <;> simp_all [Matrix.mul_assoc]

@[simp] theorem generatorAction_inverse_right (v : PairGenerator right left) :
    generatorAction g (generatorAction g⁻¹ v) = v := by
  simpa only [inv_inv] using generatorAction_inverse g⁻¹ v

/-- Intertwining of the actual point-based synthesis maps. -/
theorem pointMap_generatorAction (X : 𝕄)
    (v : PairGenerator right left) :
    pointMap right left (g • X) (generatorAction g v) =
      g • pointMap right left X v := by
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hl : (L * v.1.val * Lᴴ) * (L * X * Rᴴ) = L * (v.1.val * X) * Rᴴ := by
    calc
      _ = L * v.1.val * (Lᴴ * L) * X * Rᴴ := by grind
      _ = _ := by rw [(Factor.matrix_unitary g.1).1]; grind
  have hr : (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (X * v.2.val) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * v.2.val * Rᴴ := by grind
      _ = _ := by rw [(Factor.matrix_unitary g.2).1]; grind
  change (L * v.1.val * Lᴴ) * (L * X * Rᴴ) +
    (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (v.1.val * X + X * v.2.val) * Rᴴ
  rw [hl, hr, Matrix.mul_add, Matrix.add_mul]

theorem generatorInner_action (v w : PairGenerator right left) :
    generatorInner (generatorAction g v) (generatorAction g w) = generatorInner v w := by
  simp only [generatorInner, generatorAction_left, generatorAction_right,
    frob_unitary (Factor.matrix_unitary g.1) (Factor.matrix_unitary g.1),
    frob_unitary (Factor.matrix_unitary g.2) (Factor.matrix_unitary g.2)]

theorem generatorAction_horizontal (X : 𝕄)
    (v : PairGenerator right left) (hv : IsHorizontal X v) :
    IsHorizontal (g • X) (generatorAction g v) := by
  intro k hk
  have hb : pointMap right left X (generatorAction g⁻¹ k) = 0 := by
    have he := pointMap_generatorAction g⁻¹ (g • X) k
    rw [inv_smul_smul, hk] at he
    simp_all
  calc
    generatorInner (generatorAction g v) k =
        generatorInner (generatorAction g v) (generatorAction g (generatorAction g⁻¹ k)) := by
          simp
    _ = generatorInner v (generatorAction g⁻¹ k) := generatorInner_action g v _
    _ = 0 := hv _ hb

/-- The selected lift is independent of all choices made in its existence proof. -/
theorem minimumNormLift_equivariant (X Z : 𝕄) :
    minimumNormLift right left (g • X) (g • Z) =
      generatorAction g (minimumNormLift right left X Z) := by
  symm
  apply minimumNormLift_unique
  · rw [pointMap_generatorAction, minimumNormLift_synthesis, pointProjection_equivariant]
  · exact generatorAction_horizontal g X _ (minimumNormLift_horizontal X Z)

/-- Every representative gives the same lift at the same matrix point. -/
theorem minimumNormLift_factor_formula (P Z : 𝕄) :
    minimumNormLift right left (g • P) Z =
      generatorAction g (minimumNormLift right left P (g⁻¹ • Z)) := by
  simpa only [smul_inv_smul] using minimumNormLift_equivariant g P (g⁻¹ • Z)

end

end GS.Shared
