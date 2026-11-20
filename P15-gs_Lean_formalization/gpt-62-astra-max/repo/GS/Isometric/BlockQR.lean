module

public import GS.Isometric.Blocks
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Prod.Lex

@[expose] public section

/-! Ordinary QR in block lexicographic order. For invertible inputs, the
unitary factor respects the original blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Matrix InnerProductSpace
namespace GS.Isometric
variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [LinearOrder ι]

private theorem qr (A : Matrix ι ι 𝕜) : ∃ U T, IsU U ∧ T.BlockTriangular id ∧ A = U*T := by
  letI := LocallyFiniteOrderBot.ofIic ι (fun i => Finset.univ.filter (· ≤ i)) (by simp)
  let f (j : ι) := WithLp.toLp 2 (A.col j)
  have dim : Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by simp
  let e := gramSchmidtOrthonormalBasis dim f
  let b := EuclideanSpace.basisFun ι 𝕜
  refine ⟨b.toBasis.toMatrix e, (fun i j => e.repr (f j) i),
    b.toMatrix_orthonormalBasis_mem_unitary e, fun {_ _} hij => gramSchmidtOrthonormalBasis_inv_triangular' dim f hij, ?_⟩
  ext i j
  simpa only [Matrix.mul_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, b, EuclideanSpace.basisFun_inner] using!
    (e.sum_inner_mul_inner (b i) (f j)).symm

lemma support_of_triangular {n} {b : Fin n → ℕ} {U : Square 𝕜 n} (u : IsU U) (t : U.BlockTriangular b) : Support b U := by
  letI : Invertible U := ⟨Uᴴ,u.1,u.2⟩
  have ht := Matrix.blockTriangular_inv_of_blockTriangular t
  rw [inv_eq_left_inv u.1] at ht
  intro i j h
  rcases lt_or_gt_of_ne h with h | h
  · simpa using ht h
  · exact t h

/-- Sort first by the physical block, then by the requested label. The
ordinary triangular factor and its inverse preserve the block filtration.
The unitary triangular factor is therefore block diagonal. -/
theorem sortedQR {n} {α : Type*} [LinearOrder α] {b : Fin n → ℕ}
    (order : Fin n → α) {A : Square 𝕜 n} (hA : Support b A) (inv : IsUnit A) :
    ∃ U T, Support b U ∧ IsU U ∧ T.BlockTriangular order ∧ A = U*T := by
  letI := LinearOrder.lift' (fun i : Fin n => toLex (b i,toLex (order i,i.val)))
    (fun _ _ h => Fin.ext (congrArg (fun x => (ofLex (ofLex x).2).2) h))
  obtain ⟨U,T,u,t,e⟩ := qr A
  have hu : IsU U := by convert! u
  letI := (isUnit_of_mul_isUnit_right (e ▸ inv)).invertible
  have ht : T.BlockTriangular b := fun {_ _} h => t (Prod.Lex.left _ _ h)
  have hU : Support b U := support_of_triangular hu (by
    have := (show A.BlockTriangular b from fun {_ _} h => hA _ _ h.ne').mul (blockTriangular_inv_of_blockTriangular ht)
    simpa [e,mul_inv_cancel_right_of_invertible] using! this)
  have eT : Uᴴ*A = T := by simp [e,hu.star_cancel]
  have hT := eT ▸ hU.conjTranspose.mul hA
  refine ⟨U,T,hU,hu,fun {i j} hij => ?_,e⟩
  by_cases h : b i = b j
  · apply t; change Prod.Lex _ _ (b j,_) (b i,_); rw [h]; exact Prod.Lex.right _ (Prod.Lex.left _ _ hij)
  · exact hT i j h
end GS.Isometric
