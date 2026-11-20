module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatrixClass

@[expose] public noncomputable section

/-! Scalar bounds in the restriction order are exact integer-sized rank bounds. The matrix exponent is the infimum of the finite block ratios. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation
namespace TensorResource
variable {K : Type*} [CommSemiring K] {X Y Z : Type}
variable {I U V W : Type} [Fintype I] [DecidableEq I] [Fintype U] [Fintype V] [Fintype W]

/-- Block-diagonal maps compare the direct sums coordinate by coordinate. -/
private theorem direct_mono {T : I → Tensor K X Y Z} {S : I → Tensor K U V W} (h : ∀ i, IsRestriction (T i) (S i)) :
    IsRestriction (Tensor.directSum T) (Tensor.directSum S) := by
  choose f g l e using h
  let block {A B : Type} (f : I → A → B → K) (p : I × A) (q : I × B) := if p.1 = q.1 then f p.1 p.2 q.2 else 0
  refine ⟨block f, block g, block l, ?_⟩
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, block, Fintype.sum_prod_type, ite_mul, mul_ite, ite_and]
  split_ifs <;> simp_all [Tensor.restrict]

theorem classOf_scalarTensor (I : Type) [Fintype I] [DecidableEq I] :
    classOf (scalarTensor (K := K) I) = scalars (Fintype.card I) := by
  tensor_relabel Fintype.equivFin I
  funext; simp [Tensor.pullback, scalarTensor]

theorem classOf_copies [Fintype X] [Fintype Y] [Fintype Z] (T : I → Tensor K X Y Z) {b : TensorClass K}
    (h : ∀ i, classOf (T i) = b) : classOf (Tensor.directSum T) = scalars (Fintype.card I) * b := by
  induction b using Quotient.inductionOn with | h a =>
  rw [← classOf_scalarTensor]
  trans classOf (Tensor.directSum fun _ : I => a.coeff)
  · apply le_antisymm <;> apply (classOf_le_iff ..).mpr <;> apply direct_mono <;> intro i
    · exact (h i).le
    · exact (h i).ge
  · apply congrArg classOf; funext; simp [Tensor.directSum, scalarTensor, Tensor.product, ite_mul]

theorem restrict_diag (f : X → I → K) (g : Y → I → K) (h : Z → I → K) :
    Tensor.restrict f g h (scalarTensor I) = fun x y z => ∑ i, f x i * g y i * h z i := by
  ext; simp [Tensor.restrict, scalarTensor, ite_and]

open scoped Classical

/-- One slice per pair of input coordinates bounds every tensor class. -/
theorem finite_bound (a : TensorClass K) : ∃ n : ℕ, a ≤ scalars n := by
  refine Quotient.inductionOn a fun T => ⟨Fintype.card (T.X × T.Y),?_⟩
  rw [← classOf_scalarTensor]
  refine ⟨fun x i => if i.1=x then 1 else 0, fun y i => if i.2=y then 1 else 0, fun z i => T.coeff i.1 i.2 z, ?_⟩
  simp [restrict_diag, Fintype.sum_prod_type]

def rank (a : TensorClass K) := Nat.find (finite_bound a)

theorem le_rank (a : TensorClass K) : a ≤ scalars (rank a) := Nat.find_spec (finite_bound a)

theorem scheme_of_le [Fintype X] [Fintype Y] [Fintype Z] {T : Tensor K X Y Z} {r : ℕ}
    (hr : classOf T ≤ scalars r) : Tensor.RankAtMost T r := by
  obtain ⟨f,g,h,e⟩ : IsRestriction T (scalarTensor (Fin r)) := by
    exact hr
  exact ⟨Function.swap f, Function.swap g, Function.swap h, fun x y z => congrArg (fun S => S x y z) (e.trans (restrict_diag ..))⟩

end TensorResource

open TensorResource
variable {K : Type*} [CommSemiring K]

abbrev exactMatrixRank (K : Type*) [CommSemiring K] (n : ℕ) := rank (matrixClass (K := K) n)

/-- The finite block ratios defining the exact rank exponent. -/
def exactRankExponentSet (K : Type*) [CommSemiring K] : Set ℝ :=
  {t | ∃ n : ℕ, 2 ≤ n ∧ t = Real.logb n (exactMatrixRank K n)}

def exactRankExponent (K : Type*) [CommSemiring K] := sInf (exactRankExponentSet K)

private theorem block_exists : (exactRankExponentSet K).Nonempty := ⟨_, 2, le_rfl, rfl⟩

variable [Nontrivial K]

/-- The output flattening has a square identity minor. -/
theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank K n := by
  let j : Fin n := ⟨0,hn⟩
  obtain ⟨a,b,c,h⟩ := scheme_of_le (le_rank (classOf (squareTensor K n)))
  let L : Matrix (Fin n × Fin n) _ K := fun x q => a q (x.2,j) * b q (j,x.1)
  have he : L * Matrix.of c = 1 := by
    funext x y
    exact (h (x.2,j) (j,x.1) y).symm.trans (by simp [squareTensor, Matrix.one_apply, Prod.ext_iff, eq_comm])
  simpa [he, sq, exactMatrixRank, matrixClass] using (L.rank_mul_le_left (Matrix.of c)).trans L.rank_le_card_width

private theorem rank_pos {n : ℕ} (hn : 0 < n) : (0:ℝ) < exactMatrixRank K n := by
  exact_mod_cast (pow_pos hn 2).trans_le (exactMatrixRank_lower hn)

private theorem block_lower : 2 ∈ lowerBounds (exactRankExponentSet K) := by
  rintro _ ⟨n,hn,rfl⟩
  apply (Real.le_logb_iff_rpow_le (by exact_mod_cast hn) (rank_pos (by omega))).mpr
  rw [Real.rpow_two]; exact_mod_cast exactMatrixRank_lower (by omega)

theorem exactRankExponent_lower : 2 ≤ exactRankExponent K := le_csInf block_exists block_lower

/-- At every positive size the tensor rank dominates the infimal power. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n:ℝ)^exactRankExponent K ≤ exactMatrixRank K n := by
  by_cases h : 2 ≤ n
  · apply (Real.le_logb_iff_rpow_le (by exact_mod_cast h) (rank_pos hn)).mp
    exact csInf_le ⟨2,block_lower⟩ ⟨n,h,rfl⟩
  · obtain rfl : n = 1 := by omega
    simpa using (Nat.cast_le (α := ℝ)).mpr (exactMatrixRank_lower hn)

/-- Every threshold strictly above the infimum is met by a finite exact scheme. -/
theorem finite_blocks {t : ℝ} (h : exactRankExponent K < t) : ∃ n r : ℕ, 2 ≤ n ∧
    (r:ℝ) ≤ (n:ℝ)^t ∧ Tensor.RankAtMost (squareTensor K n) r := by
  obtain ⟨_, ⟨n,hn,rfl⟩,hlt⟩ := exists_lt_of_csInf_lt block_exists h
  exact ⟨n,_,hn,((Real.logb_lt_iff_lt_rpow (by exact_mod_cast hn) (rank_pos (by omega))).mp hlt).le,scheme_of_le (le_rank _)⟩

end OAI.MatrixMultiplication.AuxiliarySeparation
