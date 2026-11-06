
import GS.NonmanifoldCompletion.OriginalMembership
import GS.NonmanifoldCompletion.BaseFibreGauges
import GS.NonmanifoldCompletion.LocalAngles
import GS.NonmanifoldCompletion.SmallLogarithms



/-!
# Constructing the original ell,r,c,z,u coordinates near a normalized factor tuple

All sign gauges are fixed diagonal orthogonal matrices. Small angles are
obtained from LocalAngles and small logarithms from SmallLogarithms. The
right angle is anchored at coordinate zero exactly as in originalK.

-/
open Matrix
namespace GS.NonmanifoldCompletion

variable (C : Mat 2)

/-- Conjugating the fixed reflection gives T(u) for an actual unit vector u. -/
theorem conjugate_reflection_coordinates  (hC : Orthogonal C) :
    ∃ u : CircleVector, OnCircle u ∧
      ∀ a b : ℝ, middleBlock a b u = Cᵀ * diagTwo a b * C := by
  let F := diagTwo 1 (-1)
  have hF := T_orthogonal (u := ![1,0]) (by norm_num [OnCircle])
  let K := Cᵀ*F*C
  have hK : Orthogonal K := (hC.transpose.mul hF).mul hC
  have hs : Kᵀ=K := by aesop (add norm [Matrix.mul_assoc])
  have htrace : K 1 1 = -K 0 0 := by
    have hh : Matrix.trace K = 0 := by
      
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hC.2, Matrix.one_mul]
      simp [F, diagTwo, Matrix.trace, Fin.sum_univ_two]
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hh
  let u := ![K 0 0,K 0 1]
  have he : T u = K := by
    ext i j
    fin_cases i,j <;> simp [T,u,htrace]
    exact (congrFun (congrFun hs 0) 1).symm
  have hu : OnCircle u := by
    have hh := congrFun (congrFun hK.2 0) 0
    simpa [OnCircle,u,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two,
      Matrix.one_apply,pow_two] using hh
  refine ⟨u,hu,?_⟩
  intro a b
  rw [diagTwo_scalar]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hC.1]
  change ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • T u =
    ((a+b)/2) • (1 : Mat 2) + ((a-b)/2) • K
  rw [he]




end GS.NonmanifoldCompletion
