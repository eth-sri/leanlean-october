import GS.MatrixBlocks
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

import GS.M4Necessary
import GS.Unitary.RealEmbedding

variable {n : ℕ}



/-!
# Unitary four-factor insufficiency

The exact real counterexample remains a counterexample when arbitrary complex
unitary blocks are permitted. This does not follow merely from its real
nonfactorization: we prove the determinant-modulus obstruction for all complex
unitary factors, then transfer the exact real certificate through ℝ → ℂ.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryGeometry

variable (b₁ b₂ b₃ b₄ : ℕ)

def product4 (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4  (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary  (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end GS.UnitaryGeometry

namespace GS.UnitaryFour
open GS.UnitaryGeometry

def P : CMat 6 := ofRealMatrix GS.M4.P
open GS.M4 (cell detBlock)

def normDetBlock (A : CMat 6) (i j : Fin 3) : ℝ := ‖detBlock A i j‖

def determinantObstruction (A : CMat 6) : Prop :=
  let d := normDetBlock A
  (1-d 0 2*d 1 0/d 2 1)*(1-d 0 2*d 2 1/d 1 0) ≥ d 0 0*d 2 2/d 1 1

def block2 (A : CMat 6) (i j : Fin 3) : CMat 2 := A.submatrix (cell i) (cell j)

abbrev assemble := @GS.M4.blocks6 ℂ _

theorem block_diagonal_decompose (A : CMat 6) (hA : CBlockDiagonal 2 A) :
    A = assemble (fun i => block2 A i i) := by
  ext i j
  fin_cases i,j <;>
    simp [assemble,GS.M4.blocks6,Fin.divNat,Fin.modNat,block2,cell] <;> apply hA <;> decide

theorem block2_unitary (A : CMat 6) (hA : CBlockDiagonal 2 A)
    (ho : Unitary A) (r : Fin 3) : Unitary (block2 A r r) := by
  have he : block2 A r r = GS.MatrixBlocks.flatBlocks (k := 3) (b := 2) A r := by
    ext i j
    simp [block2,cell,GS.MatrixBlocks.flatBlocks,finProdFinEquiv,Nat.add_comm]
  rw [he]
  exact GS.MatrixBlocks.flatBlocks_unitary (k := 3) (b := 2) A hA ho r

/-- The entry-modulus identities hold for all complex unitary 2×2 blocks. -/
theorem unitary2_norm (W : CMat 2) (hW : Unitary W) :
    ‖W 1 0‖=‖W 0 1‖ ∧ ‖W 1 1‖=‖W 0 0‖ ∧ ‖W 0 0‖^2+‖W 0 1‖^2=1 := by
  have hc (i : Fin 2) : ‖W 0 i‖^2 + ‖W 1 i‖^2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using congrArg Complex.re (congrFun (congrFun hW.1 i) i)
  have hr0 : ‖W 0 0‖^2 + ‖W 0 1‖^2 = 1 := by
    simp only [Complex.sq_norm]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.normSq_apply] using congrArg Complex.re (congrFun (congrFun hW.2 0) 0)
  refine ⟨?_, ?_, hr0⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith only [hc 0, hr0]
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    linarith only [hc 1, hr0]

set_option maxHeartbeats 4000000 in
/-- Universal necessity for the precise m=4 class in the manuscript. -/
theorem necessaryCondition (A : CMat 6) (h : CInA4Unitary 2 2 2 2 P P P A)
    (hden : normDetBlock A 2 1 * normDetBlock A 1 0 * normDetBlock A 1 1 ≠ 0) :
    determinantObstruction A := by
  rcases h with ⟨B₁,B₂,B₃,B₄,hb₁,hb₂,hb₃,hb₄,ho₁,ho₂,ho₃,ho₄,he⟩
  let C₀ := P*B₃*P*B₂*P
  have he' : A=B₄*C₀*B₁ := by
    rw [he]
    simp only [GS.UnitaryGeometry.product4,C₀,Matrix.mul_assoc]
  have hd : normDetBlock A=normDetBlock C₀ := by
    funext i j
    rw [he']
    have hblock : block2 (B₄*C₀*B₁) i j =
        block2 B₄ i i * block2 C₀ i j * block2 B₁ j j := by
      generalize C₀ = C
      rw [block_diagonal_decompose B₄ hb₄,block_diagonal_decompose B₁ hb₁]
      ext a b
      fin_cases i,j,a,b <;>
        simp [block2,cell,assemble,GS.M4.blocks6,Fin.divNat,Fin.modNat,
          Matrix.mul_apply,Fin.sum_univ_succ]
    change ‖(block2 (B₄*C₀*B₁) i j).det‖ = ‖(block2 C₀ i j).det‖
    rw [hblock,Matrix.det_mul,Matrix.det_mul,norm_mul,norm_mul,
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (block2_unitary B₄ hb₄ ho₄ i)),
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (block2_unitary B₁ hb₁ ho₁ j))]
    simp
  unfold determinantObstruction
  rw [hd] at hden ⊢
  let W := fun i => block2 B₃ i i
  let Y := fun i => block2 B₂ i i
  have hw i := unitary2_norm (W i) (block2_unitary B₃ hb₃ ho₃ i)
  have hy i := unitary2_norm (Y i) (block2_unitary B₂ hb₂ ho₂ i)
  have ht : normDetBlock C₀ = GS.M4.canonicalDetTable
      (fun i => ‖W i 0 0‖) (fun i => ‖W i 0 1‖)
      (fun i => ‖Y i 0 0‖) (fun i => ‖Y i 0 1‖) := by
    dsimp only [C₀]
    rw [block_diagonal_decompose B₂ hb₂,block_diagonal_decompose B₃ hb₃]
    change normDetBlock (P*assemble W*P*assemble Y*P) = _

    ext i j
    fin_cases i,j <;>
      norm_num [normDetBlock,detBlock,Matrix.det_fin_two,Matrix.submatrix_apply,cell,P,GS.M4.P,ofRealMatrix,assemble,
        GS.M4.blocks6,Fin.divNat,Fin.modNat,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals
      conv_lhs => arg 1; ring_nf
    all_goals
      simp [GS.M4.canonicalDetTable,
        fun i => (hw i).1,fun i => (hw i).2.1,
        fun i => (hy i).1,fun i => (hy i).2.1] <;> ring

  rw [ht] at hden ⊢
  apply GS.M4.canonical_obstruction _ _ _ _ _ _ hden
  · intro i; exact (hw i).2.2
  · intro i; exact (hy i).2.2

end GS.UnitaryFour
