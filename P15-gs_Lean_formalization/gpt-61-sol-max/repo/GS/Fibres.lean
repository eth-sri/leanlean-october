
import GS.Frobenius
import GS.RankOne
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
open GS.MatrixBase



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

variable (a b : ℝ)

variable (u : CircleVector)

def OnCircle  : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

def outer {κ : Type*} (u : CircleVector) (z : κ → ℝ) : Matrix (Fin 2) κ ℝ := fun i j => u i * z j






/-- The circle variable does not change the squared Frobenius radius. -/
theorem frobSq_outer {κ : Type*} [Fintype κ] {u : CircleVector}
    (hu : OnCircle u) (z : κ → ℝ) :
    cFrobSq (outer u z) = ∑ j, z j ^ 2 := RankOne.frobSq_outer (by aesop) z


/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem outer_fibres {κ : Type*} {u v : CircleVector} {z w : κ → ℝ}
    (hu : OnCircle u) (hv : OnCircle v) :
    outer u z = outer v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := RankOne.fibres (by aesop)
    (by aesop)

def T  : Mat 2 := !![u 0, u 1; u 1, -u 0]

theorem continuous_T : Continuous T := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i,j <;> simp [T] <;> fun_prop

theorem T_transpose  : (T u)ᵀ = T u := by
  ext i j
  fin_cases i,j <;> rfl

theorem T_sq {u : CircleVector} (hu : OnCircle u) : T u * T u = 1 := by
  ext i j
  fin_cases i,j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    dsimp [OnCircle] at hu <;> nlinarith [hu]

theorem T_orthogonal {u : CircleVector} (hu : OnCircle u) : Orthogonal (T u) := by
  constructor <;> rw [T_transpose, T_sq hu]

def middleBlock   : Mat 2 :=
  ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • T u

theorem middleBlock_swap   :
    middleBlock b a (-u) = middleBlock a b u := by
  ext i j
  fin_cases i,j <;> simp [middleBlock,T] <;> ring

theorem middleBlock_equal   :
    middleBlock a a u = a • (1 : Mat 2) := by simp_all [middleBlock]

theorem middleBlock_trace   :
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
  have he := congrFun (congrFun h i) j
  change ((a+b)/2) * (1 : Mat 2) i j + ((a-b)/2) * T u i j =
    ((a'+b')/2) * (1 : Mat 2) i j + ((a'-b')/2) * T v i j at he
  change (a-b) * T u i j = (a'-b') * T v i j
  rw [hs] at he
  linarith

/-- The parameter map lands in the actual determinantal cone, expressed with
mathlib's matrix rank (not only by the vanishing of displayed minors). -/
theorem rank_outer_le_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : CircleVector) (z : κ → ℝ) : Matrix.rank (outer u z) ≤ 1 := Matrix.rank_vecMulVec_le _ _


end GS
