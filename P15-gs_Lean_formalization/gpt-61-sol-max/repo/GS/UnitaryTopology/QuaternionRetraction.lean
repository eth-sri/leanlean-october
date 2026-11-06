
import GS.UnitaryLocalModel.RankCone
import GS.NonmanifoldObstruction.ProductSphere
open GS.MatrixBase



/-!
# A Clifford contraction of the real three-row rank-one cone

For a width divisible by four, two orthogonal anticommuting complex structures
give a linear contraction onto the column space. Its squared Euclidean norm
equals the Frobenius square on rank-one matrices. The first-row section is an
exact right inverse. In particular the contraction has no additional zeros.
-/
open GS.UnitaryLocalModel GS.NonmanifoldObstruction
namespace GS.UnitaryTopology

abbrev RankThreeCone (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin 3) κ ℝ // W.rank ≤ 1}

def rankThreeZero {κ : Type*} [Fintype κ] : RankThreeCone κ := ⟨0,by simp⟩

def quaternionContraction {r : ℕ} (W : Matrix (Fin 3) (Fin r × Fin 4) ℝ) :
    Fin r × Fin 4 → ℝ := fun j =>
  ![W 0 (j.1,0)-W 1 (j.1,1)-W 2 (j.1,2),
    W 0 (j.1,1)+W 1 (j.1,0)+W 2 (j.1,3),
    W 0 (j.1,2)-W 1 (j.1,3)+W 2 (j.1,0),
    W 0 (j.1,3)+W 1 (j.1,2)-W 2 (j.1,1)] j.2

theorem continuous_quaternionContraction (r : ℕ) :
    Continuous (@quaternionContraction r) := by fun_prop [quaternionContraction]

theorem quaternionContraction_preserves_square {r : ℕ}
    (W : RankThreeCone (Fin r × Fin 4)) :
    vectorSq (quaternionContraction W.val) = cFrobSq W.val := by
  obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one W.val W.property
  rw [← hz,frobSq_sphereOuter hu]
  simp only [vectorSq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := congrArg (fun x : ℝ => x * (∑ a : Fin 4, z (j,a)^2)) hu
  norm_num [quaternionContraction,sphereOuter,Fin.sum_univ_succ] at hm ⊢
  nlinarith only [hm]

def firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℝ) :
    RankThreeCone κ :=
  ⟨sphereOuter (fun i => if i=0 then 1 else 0) z,rank_sphereOuter_le_one _ _⟩

@[simp] theorem quaternionContraction_section {r : ℕ} (z : Fin r × Fin 4 → ℝ) :
    quaternionContraction (firstRowSection z).val = z := by
  funext j
  rcases j with ⟨j,a⟩
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  fin_cases a <;> norm_num [quaternionContraction,firstRowSection,sphereOuter,h20]

theorem quaternionContraction_zero_iff {r : ℕ} (W : RankThreeCone (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankThreeZero := by
  constructor
  · intro he
    have hs := quaternionContraction_preserves_square W
    rw [he] at hs
    have hW  := by simpa [vectorSq] using hs.symm
    exact Subtype.ext ((cFrobSq_eq_zero_iff W.val).mp hW)
  · rintro rfl
    funext j
    rcases j with ⟨j,a⟩
    fin_cases a <;> norm_num [quaternionContraction,rankThreeZero]

end GS.UnitaryTopology
