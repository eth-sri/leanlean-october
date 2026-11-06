import GS.MatrixBlocks
import GS.MatrixCS.Square
import GS.MatrixFactor.Factorization
import GS.OriginalLocalModel

open Matrix GS.MatrixBase GS.MatrixFactor
namespace GS.MatrixCS
variable {𝕜 : Type} [RCLike 𝕜]

def twoProdSumEquiv (p : ℕ) : (Fin 2 × Fin p) ≃ (Fin p ⊕ Fin p) :=
  (finTwoEquiv.prodCongr (Equiv.refl _)).trans (Equiv.boolProdEquivSum _)

def sumEquiv (p : ℕ) : Fin (2*p) ≃ (Fin p ⊕ Fin p) :=
  finProdFinEquiv.symm.trans (twoProdSumEquiv p)

def squareFlatten (A : SumMat 𝕜 p) : KMat 𝕜 (2*p) :=
  A.submatrix (sumEquiv p) (sumEquiv p)

theorem squareFlatten_unitary {A : SumMat 𝕜 p} (hA : Unitary A) :
    Unitary (squareFlatten A) := Unitary.submatrix (sumEquiv p) hA

theorem squareFlatten_mul (A B : SumMat 𝕜 p) :
    squareFlatten (A*B) = squareFlatten A * squareFlatten B := (Matrix.submatrix_mul_equiv A B (sumEquiv p) (sumEquiv p) (sumEquiv p)).symm

theorem squareFlatten_split_blockDiagonal (A B : KMat 𝕜 p) :
    CBlockDiagonal p (squareFlatten (fromBlocks A 0 0 B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  have hi : i.val / p = x.1.val := rfl
  have hj : j.val / p = y.1.val := rfl
  change (fromBlocks A 0 0 B) (twoProdSumEquiv p x) (twoProdSumEquiv p y) = 0
  rcases x with ⟨a,u⟩; rcases y with ⟨b,v⟩
  fin_cases a,b <;> simp_all [twoProdSumEquiv,finTwoEquiv]


theorem shuffled_square_cs_blockDiagonal (c s : Fin p → ℝ) :
    CBlockDiagonal 2 (cPermMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p) * squareFlatten (csMatrix c s) *
      (cPermMatrix  (GS.scalarShuffle 2 p))ᴴ : KMat 𝕜 (2*p)) := by
  intro i j hij
  let σ := GS.scalarShuffle 2 p
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := GS.MatrixBlocks.shuffle_block_label (σ.symm i)
    have hj := GS.MatrixBlocks.shuffle_block_label (σ.symm j)
    simp only [σ,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  rw [cPerm_conjugate_apply]
  change (csMatrix c s : SumMat 𝕜 p)
    (twoProdSumEquiv p x) (twoProdSumEquiv p y) = 0
  rcases x with ⟨a,u⟩; rcases y with ⟨b,v⟩
  change u ≠ v at hxy
  fin_cases a,b <;> simp [csMatrix, twoProdSumEquiv, finTwoEquiv, hxy]

theorem unitary_mem_scalar_three_factor {M : KMat 𝕜 (2*p)} (hM : Unitary M) :
    CInA3Unitary p 2 p (cPermMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p))
      (cPermMatrix  (GS.scalarShuffle 2 p))ᴴ M := by
  let e := sumEquiv p
  let Q := M.submatrix e.symm e.symm
  have hQ : Unitary Q := Unitary.submatrix e.symm hM
  obtain ⟨U₁,U₂,V₁,V₂,c,s,hU₁,hU₂,hV₁,hV₂,hcs,hfactor⟩ := exists_square_cs Q hQ
  let L := squareFlatten (split U₁ U₂)
  let R := squareFlatten (split V₁ V₂)
  let K := squareFlatten (csMatrix c s : SumMat 𝕜 p)
  let P : KMat 𝕜 (2*p) := cPermMatrix  (GS.scalarShuffle 2 p)
  have hP : GS.MatrixBase.Unitary P := cPerm_unitary _
  have hK : GS.MatrixBase.Unitary K := squareFlatten_unitary (csMatrix_unitary c s (fun i => (hcs i).2.2))
  have he : squareFlatten Q = M := by
    ext i j; change M (e.symm (e i)) (e.symm (e j)) = M i j; simp
  refine ⟨R, P*K*Pᴴ, L, squareFlatten_split_blockDiagonal _ _,
    shuffled_square_cs_blockDiagonal c s, squareFlatten_split_blockDiagonal _ _,
    squareFlatten_unitary (split_unitary hV₁ hV₂),
    (hP.mul hK).mul hP.conjTranspose, squareFlatten_unitary (split_unitary hU₁ hU₂), ?_⟩
  rw [← he, hfactor, squareFlatten_mul, squareFlatten_mul]
  change L*K*R = L*Pᴴ*(P*K*Pᴴ)*P*R
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P, hP.1, Matrix.one_mul]

theorem scalar_exhaustion {M : KMat 𝕜 (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (𝕜 := 𝕜) (GS.scalarShuffle 2 p))
      (cPermMatrix  (GS.scalarShuffle 2 p))ᴴ M ↔ GS.MatrixBase.Unitary M :=
by
  constructor
  · rintro ⟨B₁,B₂,B₃,_,_,_,h₁,h₂,h₃,rfl⟩
    exact (((h₃.mul (cPerm_unitary _).conjTranspose).mul h₂).mul
      (cPerm_unitary _)).mul h₁
  · exact unitary_mem_scalar_three_factor

end GS.MatrixCS
