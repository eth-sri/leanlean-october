module

public import GS.UnitaryLocalModel.RankCone
public import GS.NonmanifoldObstruction.ProductSphere

@[expose] public section


/-!
# A Clifford contraction of the real three-row rank-one cone

For a width divisible by four, two orthogonal anticommuting complex structures
give a linear contraction onto the column space. Its squared Euclidean norm
equals the Frobenius square on rank-one matrices. The first-row section is an
exact right inverse. In particular the contraction has no additional zeros.
-/
noncomputable section
open Matrix GS GS.UnitaryLocalModel GS.NonmanifoldObstruction
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
    Continuous (@quaternionContraction r) := by
  unfold quaternionContraction; fun_prop

section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
def firstRowSection (z : κ → ℝ) :
    RankThreeCone κ :=
  ⟨sphereOuter (fun i => if i=0 then 1 else 0) z,rank_sphereOuter_le_one _ _⟩

theorem continuous_firstRowSection :
    Continuous (@firstRowSection κ _ _) := by
  unfold firstRowSection sphereOuter; fun_prop

@[simp] theorem firstRowSection_zero :
    firstRowSection (0 : κ → ℝ) = rankThreeZero := by
  ext i j
  simp [firstRowSection,sphereOuter,rankThreeZero]

end

section
variable {r : ℕ}
@[simp] theorem quaternionContraction_section (z : Fin r × Fin 4 → ℝ) :
    quaternionContraction (firstRowSection z).val = z := by
  funext ⟨j,a⟩
  fin_cases a <;> norm_num [quaternionContraction,firstRowSection,sphereOuter,show (2 : Fin 3) ≠ 0 by decide]

theorem quaternionContraction_zero_iff (W : RankThreeCone (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankThreeZero := by
  refine ⟨fun he => Subtype.ext ((frobSq_eq_zero_iff W.val).mp ?_), ?_⟩
  · obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one W.val W.property
    rw [← hz] at he ⊢
    simp only [frobSq_sphereOuter hu, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h : (∑ a : Fin 4, quaternionContraction (sphereOuter u z) (j,a)^2) =
        (u 0^2+u 1^2+u 2^2) * (∑ a : Fin 4, z (j,a)^2) := by
      norm_num [quaternionContraction,sphereOuter,Fin.sum_univ_succ,
        show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
      ring
    rw [← one_mul (∑ a, _), ← hu, ← h, he]
    simp
  · rintro rfl
    ext ⟨j,a⟩
    fin_cases a <;> norm_num [quaternionContraction,rankThreeZero]

end

end GS.UnitaryTopology
