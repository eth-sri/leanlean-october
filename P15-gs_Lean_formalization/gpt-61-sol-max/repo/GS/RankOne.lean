import Mathlib.Tactic
import GS.Results.CellRank
import GS.Frobenius
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field
open GS.MatrixBase
open Matrix
namespace GS.RankOne
variable {ι κ : Type*} [Fintype ι]

theorem nonzero {u : ι → ℝ} (hu : ∑ i, u i ^ 2 = 1) : u ≠ 0 := by aesop

theorem zero_iff {u : ι → ℝ} (hu : ∑ i, u i ^ 2 = 1) (z : κ → ℝ) :
    vecMulVec u z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Function.ne_iff.mp (nonzero hu)
    funext j
    exact (mul_eq_zero.mp (congrFun (congrFun h i) j)).resolve_left hi
  · aesop (add norm [vecMulVec])

theorem col_sq {u : ι → ℝ} (hu : ∑ i, u i ^ 2 = 1) (z : κ → ℝ) (j : κ) :
    ∑ i, (vecMulVec u z i j)^2 = z j ^ 2 := by
  simp only [vecMulVec_apply, mul_pow, ← Finset.sum_mul, hu, one_mul]

theorem frobSq_outer [Fintype κ] {u : ι → ℝ} (hu : ∑ i, u i ^ 2 = 1) (z : κ → ℝ) :
    cFrobSq (vecMulVec u z) = ∑ j, z j ^ 2 := by
  simp only [cFrobSq,cFrobInner,star_trivial,RCLike.re_to_real,← pow_two]
  rw [Finset.sum_comm]
  simp [col_sq hu]

theorem unique_of_column {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : ∑ i, u i ^ 2 = 1) (h : vecMulVec u z = vecMulVec v w)
    (j : κ) (hz : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have huv : u = v := by
    funext i
    exact mul_right_cancel₀ hz (by simpa [vecMulVec,← hj] using congrFun (congrFun h i) j)
  refine ⟨huv, ?_⟩
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (nonzero hu)
  funext k
  exact mul_left_cancel₀ hi (by simpa [vecMulVec,← huv] using congrFun (congrFun h i) k)

theorem fibres {u v : ι → ℝ} {z w : κ → ℝ}
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    vecMulVec u z = vecMulVec v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · grind [zero_iff]
  simp only [hz, false_and, false_or]
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
    have he : z j ^ 2 = w j ^ 2 := by rw [← col_sq hu z j,h,col_sq hv]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · exact Or.inl (unique_of_column hu h j hj he)
    · right
      apply unique_of_column hu (v := -v) (w := -w) ?_ j hj he
      simpa [vecMulVec,neg_mul_neg] using h
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> ext i j <;> simp [vecMulVec]

theorem exists_outer [Fintype κ] (W : Matrix ι κ ℝ) (hW : W.rank ≤ 1) :
    ∃ u z, vecMulVec u z = W := by
  obtain ⟨U,V,h⟩ := (Results.CellRank.rank_le_card_iff_factorization (τ := Fin 1) W).mp (by simpa using hW)
  refine ⟨fun i => U i 0, fun j => V 0 j, ?_⟩
  ext i j
  simpa [Matrix.mul_apply,vecMulVec] using congrFun (congrFun h.symm i) j



theorem exists_unit_outer [Fintype κ] (i₀ : ι) (W : Matrix ι κ ℝ) (hW : W.rank ≤ 1) :
    ∃ u : ι → ℝ, (∑ i, u i ^ 2 = 1) ∧ ∃ z : κ → ℝ, vecMulVec u z = W := by
  classical
  obtain ⟨u,z,rfl⟩ := exists_outer W hW
  by_cases hu : u = 0
  · subst u
    exact ⟨Pi.single i₀ 1, by simp [Pi.single_apply], 0, by simp_all [vecMulVec]⟩
  let r := Real.sqrt (∑ i, u i ^ 2)
  have hs : 0 < ∑ i, u i ^ 2 := by simp_all [symm,funext_iff,Finset.sum_nonneg,Finset.sum_sq_eq_zero_iff,sq_nonneg,lt_of_le_of_ne]
  refine ⟨fun i => u i / r, ?_, fun j => r * z j, ?_⟩
  · simp only [div_pow,← Finset.sum_div]
    rw [Real.sq_sqrt hs.le]
    exact div_self (ne_of_gt hs)
  · grind [vecMulVec]
end GS.RankOne
