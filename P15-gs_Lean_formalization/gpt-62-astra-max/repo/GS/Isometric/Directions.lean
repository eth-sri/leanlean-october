module

public import GS.Isometric.Orbit
public import GS.Isometric.Products

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
open Matrix GS
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Layer 𝕜 n}

abbrev PairGenerator (right left : Layer 𝕜 n) := Generator left × Generator right

/-- Differential of the left/right action: the second factor acts by its inverse. -/
def pointMap (right left : Layer 𝕜 n) (X : Square 𝕜 n) :
    PairGenerator right left →ₗ[ℝ] Square 𝕜 n where
  toFun v := v.1.val * X - X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X - X * (a • v.2.val) =
      a • (v.1.val * X - X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

def pointDirections (right left : Layer 𝕜 n) (X : Square 𝕜 n) : Submodule ℝ (Square 𝕜 n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : Square 𝕜 n) :
    Y ∈ pointDirections right left X ↔
      ∃ A B, A ∈ skewSpace left ∧ B ∈ skewSpace right ∧ Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, -B.val,A.property, (skewSpace right).neg_mem B.property, by simpa [pointMap,sub_eq_add_neg] using h.symm⟩
  · rintro ⟨A, B, hA, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨-B, (skewSpace right).neg_mem hB⟩), by simpa [pointMap] using h.symm⟩

/-- The two infinitesimal generators transform by conjugation. -/
lemma action_mem_pointDirections (g : Factors right left) (X Y : Square 𝕜 n)
    (hy : Y ∈ pointDirections right left X) : g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A,B,a,b,rfl⟩ := (mem_pointDirections_iff ..).1 hy
  apply (mem_pointDirections_iff ..).2
  exact ⟨_,_,sharedSkew_conjugate g.1.matrix_shared a,sharedSkew_conjugate g.2.matrix_shared b, by
    simp [mul_assoc,mul_add,add_mul,g.1.matrix_unitary.star_cancel,g.2.matrix_unitary.star_cancel]⟩
end GS.Isometric
