module

public import GS.NonmanifoldCompletion.BlockRealization
public import GS.UnitaryCS.Square

@[expose] public section


/-!
# The square CS decomposition in the original scalar shuffle coordinates

Over any `RCLike` field, three scalar GS factors of sizes `p, 2, p`, with the
specified scalar perfect shuffle and its adjoint, exhaust the unitary group.
No positivity assumption on `p` or singular-value genericity is required.
-/

noncomputable section
open Matrix GS.NonmanifoldCompletion GS.Shared
namespace GS.UnitaryCS
variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_two_iff {p : ℕ} {M : Matrix (Fin (2*p)) (Fin (2*p)) 𝕜} :
    (∃ B₁ B₂ B₃, Supp (fun i : Fin (2*p) => i.val / p) B₁ ∧ Supp (fun i : Fin (2*p) => i.val / 2) B₂ ∧
      Supp (fun i : Fin (2*p) => i.val / p) B₃ ∧ IsUnitary B₁ ∧ IsUnitary B₂ ∧ IsUnitary B₃ ∧
      M = B₃ * (perm (scalarShuffle 2 p))ᴴ * B₂ * perm (scalarShuffle 2 p) * B₁) ↔ IsUnitary M := by
  have hP := perm_uni (𝕜 := 𝕜) (scalarShuffle 2 p)
  refine ⟨fun ⟨_, _, _, _, _, _, h₁, h₂, h₃, he⟩ => he ▸ (((h₃.mul hP.conjTranspose).mul h₂).mul hP).mul h₁,
    fun hM => ?_⟩
  let e := finProdFinEquiv.symm.trans (twoProdSumEquiv p)
  have hB (A B : Matrix (Fin p) (Fin p) 𝕜) : Supp (fun i : Fin (2*p) => i.val / p) (pullMatrix e (fromBlocks A 0 0 B)) := by
    change Supp _ (flattenBlocks (pullMatrix (twoProdSumEquiv p) _))
    convert flatten_blockDiagonal ![A,B] using 2
    ext ⟨a,i⟩ ⟨b,j⟩
    fin_cases a <;> fin_cases b <;> simp [pullMatrix, twoProdSumEquiv, blockMatrix]
  obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hfactor⟩ :=
    exists_square_cs _ (pullMatrix_unitary e.symm hM)
  refine ⟨_, _, _, hB V₁ V₂, ?_, hB U₁ U₂, pullMatrix_unitary _ (split_unitary hV₁ hV₂),
    (hP.mul (pullMatrix_unitary e (csMatrix_unitary c s fun i => (hcs i).2.2))).mul
      hP.conjTranspose, pullMatrix_unitary _ (split_unitary hU₁ hU₂), ?_⟩
  · intro i j hij
    have := shuffle_block_label ((scalarShuffle 2 p).symm i)
    have := shuffle_block_label ((scalarShuffle 2 p).symm j)
    simp
    simp only [e, pullMatrix, Equiv.trans_apply]
    generalize finProdFinEquiv.symm ((scalarShuffle 2 p).symm i) = x at *
    generalize finProdFinEquiv.symm ((scalarShuffle 2 p).symm j) = y at *
    obtain ⟨a,u⟩ := x
    obtain ⟨b,v⟩ := y
    fin_cases a <;> fin_cases b <;> simp [twoProdSumEquiv, csMatrix, diagonal_apply] <;> grind
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (perm (scalarShuffle 2 p))ᴴ, hP.1,
    Matrix.one_mul, ← pullMatrix_mul]
  rw [← Matrix.mul_assoc, ← split, ← split, ← hfactor]
  ext i j
  simp [pullMatrix]

end GS.UnitaryCS
