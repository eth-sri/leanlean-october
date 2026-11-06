module

public import GS.Frobenius
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.FunProp

@[expose] public section


/-!
# The algebra of the original fibre proof

This file retains the manuscript's unit-circle/rank-one parameterization.
No alternative polar-logarithm parameterization is substituted.
It does not identify a neighbourhood of the matrix family with this model;
that analytic/topological bridge is listed as an outstanding goal.

-/

noncomputable section
open Matrix
namespace GS

abbrev CircleVector := Fin 2 → ℝ

def OnCircle (u : CircleVector) : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

def outer {κ : Type*} (u : CircleVector) (z : κ → ℝ) : Matrix (Fin 2) κ ℝ :=
  fun i j => u i * z j

theorem onCircle_has_nonzero {u : CircleVector} (hu : OnCircle u) : ∃ i, u i ≠ 0 := by
  by_contra! h
  simp [OnCircle, h] at hu

section
variable {κ : Type*}
theorem outer_simultaneous_neg (u : CircleVector) (z : κ → ℝ) :
    outer (-u) (-z) = outer u z := by
  ext i j
  simp [outer]

theorem outer_zero_iff {u : CircleVector} (hu : OnCircle u) (z : κ → ℝ) :
    outer u z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; ext; simp [outer]⟩
  obtain ⟨i,hi⟩ := onCircle_has_nonzero hu
  funext j
  simpa [outer, hi] using congrFun (congrFun h i) j

theorem outer_col_sq {u : CircleVector} (hu : OnCircle u)
    (z : κ → ℝ) (j : κ) :
    outer u z 0 j ^ 2 + outer u z 1 j ^ 2 = z j ^ 2 := by
  simp only [outer, mul_pow, ← add_mul]
  rw [hu, one_mul]

/-- The circle variable does not change the squared Frobenius radius. -/
theorem frobSq_outer [Fintype κ] {u : CircleVector}
    (hu : OnCircle u) (z : κ → ℝ) :
    frobSq (outer u z) = ∑ j, z j ^ 2 := by
  simp only [frobSq, frobInner, Fin.sum_univ_two, ← Finset.sum_add_distrib, ← pow_two, outer_col_sq hu]

end

section
variable {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
/-- Equality plus one equal nonzero column coefficient fixes both factors. -/
theorem outer_unique_of_column (hu : OnCircle u) (h : outer u z = outer v w)
    (j : κ) (hzj : z j ≠ 0) (hj : z j = w j) : u = v ∧ z = w := by
  have h i k : u i * z k = v i * w k := congrFun (congrFun h i) k
  obtain ⟨i,hi⟩ := onCircle_has_nonzero hu
  have huv : u = v := funext fun i => by grind [h i j]
  exact ⟨huv, funext fun k => by grind [h i k]⟩

/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem outer_fibres (hu : OnCircle u) (hv : OnCircle v) :
    outer u z = outer v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  by_cases hz : z = 0
  · subst z
    rw [(outer_zero_iff hu 0).mpr rfl, eq_comm, outer_zero_iff hv]
    grind
  simp only [hz, false_and, false_or]
  refine ⟨fun h => ?_, by rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [outer_simultaneous_neg]⟩
  obtain ⟨j,hj⟩ : ∃ j, z j ≠ 0 := by by_contra! hn; exact hz (funext hn)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← outer_col_sq hu z j, h, outer_col_sq hv w j] : z j ^ 2 = w j ^ 2) with hp | hp
  · exact .inl (outer_unique_of_column hu h j hj hp)
  · exact .inr (outer_unique_of_column hu (h.trans (outer_simultaneous_neg v w).symm) j hj hp)

end

def T (u : CircleVector) : Mat 2 := !![u 0, u 1; u 1, -u 0]

theorem continuous_T : Continuous T :=
  continuous_pi fun i => continuous_pi fun j => by fin_cases i <;> fin_cases j <;> simp [T] <;> fun_prop

theorem T_orthogonal {u : CircleVector} (hu : OnCircle u) : Orthogonal (T u) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_succ] <;> dsimp [OnCircle] at hu <;> nlinarith [hu]

section
variable (a b : ℝ) (u : CircleVector)
def middleBlock : Mat 2 :=
  ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • T u

theorem middleBlock_swap :
    middleBlock b a (-u) = middleBlock a b u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [middleBlock,T] <;> ring

end

theorem middleBlock_equal (a : ℝ) (u : CircleVector) :
    middleBlock a a u = a • (1 : Mat 2) := by
  simp [middleBlock]

theorem middleBlock_trace (a b : ℝ) (u : CircleVector) :
    middleBlock a b u 0 0 + middleBlock a b u 1 1 = a + b := by
  simp [middleBlock,T]
  ring

/-- The sign argument at the scalar-difference level, used in the fibre proof. -/
theorem middleBlock_eq_sum_and_difference
    (a b a' b' : ℝ) (u v : CircleVector)
    (h : middleBlock a b u = middleBlock a' b' v) :
    a+b=a'+b' ∧ (a-b) • T u = (a'-b') • T v := by
  have hs : a+b=a'+b' := by
    rw [← middleBlock_trace a b u, h, middleBlock_trace]
  refine ⟨hs, ?_⟩
  ext i j
  have := congrFun (congrFun h i) j
  simp [middleBlock] at this ⊢
  grind

/-- The parameter map lands in the actual determinantal cone, expressed with
mathlib's matrix rank (not only by the vanishing of displayed minors). -/
theorem rank_outer_le_one [Fintype κ] [DecidableEq κ]
    (u : CircleVector) (z : κ → ℝ) : Matrix.rank (outer u z) ≤ 1 :=
  Matrix.rank_vecMulVec_le u z

end GS
