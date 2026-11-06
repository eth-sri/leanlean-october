import GS.NonmanifoldCompletion.SpectralTwo
import GS.MatrixBlocks
namespace GS.NonmanifoldCompletion
export GS.MatrixBlocks (pullMatrix pullMatrix_mul flattenBlocks flattenBlocks_apply flattenBlocks_mul flat_block_label flatten_blockDiagonal blockMatrix blockMatrix_mul blockMatrix_one centralPair centralPair_as_blocks shuffledMiddle shuffle_block_label shuffledMiddle_blockDiagonal)
alias pullMatrix_orthogonal := GS.MatrixBlocks.pullMatrix_unitary
alias blockMatrix_transpose := GS.MatrixBlocks.blockMatrix_conjTranspose
alias blockMatrix_orthogonal := GS.MatrixBlocks.blockMatrix_unitary
alias centralPair_orthogonal := GS.MatrixBlocks.centralPair_unitary
theorem diagTwo_eq_generic (a b : ℝ) : diagTwo a b = GS.MatrixBlocks.diagTwo a b := by
  ext i j
  fin_cases i,j <;> simp [diagTwo, GS.MatrixBlocks.diagTwo]
theorem small_block_sandwich {q : ℕ} (U V : Fin q → Mat 2) (A B : Mat q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i,a) (j,b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b  := by simp_all [GS.MatrixBlocks.small_block_sandwich,diagTwo_eq_generic]

export GS.MatrixBlocks (block_sandwich_mem_localFamily)
end GS.NonmanifoldCompletion
