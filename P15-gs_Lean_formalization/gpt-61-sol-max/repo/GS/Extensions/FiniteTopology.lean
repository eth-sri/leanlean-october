import Mathlib.Topology.Algebra.Star.Unitary

import GS.OriginalLocalModel
open GS.MatrixBase



/-!
# Finite-dimensional topology used by the original fibre proof

The argument uses coordinatewise compact intervals, not an identification of
mathlib's default matrix norm with the Frobenius norm.
-/

namespace GS.Extensions
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem continuous_frobSq : Continuous (fun A : Matrix ι κ ℝ => cFrobSq A) := by
  simp only [cFrobSq,cFrobInner,star_trivial,RCLike.re_to_real]
  fun_prop

 theorem entry_sq_le_frobSq (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    A i j ^ 2 ≤ cFrobSq A := by

  have h₁ :=
    Finset.single_le_sum (fun l _ => mul_self_nonneg (A i l)) (Finset.mem_univ j)
  have h₂ : (∑ l, A i l * A i l) ≤ ∑ r, ∑ l, A r l * A r l :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg (A r l)))
      (Finset.mem_univ i)
  simpa only [cFrobSq, cFrobInner,star_trivial,RCLike.re_to_real, pow_two] using h₁.trans h₂

 theorem abs_entry_le_of_frobSq_le {A : Matrix ι κ ℝ} {η : ℝ}
    (h : cFrobSq A ≤ η^2) (i : ι) (j : κ) : |A i j| ≤ |η| := sq_le_sq.mp ((entry_sq_le_frobSq A i j).trans h)


 theorem onCircle_abs_le_one {u : CircleVector} (hu : OnCircle u) (i : Fin 2) :
    |u i| ≤ 1 := by
  rw [← sq_le_one_iff₀ (abs_nonneg _), sq_abs]
  change u 0 ^ 2 + u 1 ^ 2 = 1 at hu
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;>
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

 

 

 theorem isClosed_originalK (q : ℕ) (η : ℝ) : IsClosed (originalK q η) := by
  simp only [originalK, OnCircle, IsSkew, Set.setOf_and, Set.setOf_forall]
  repeat' first
    | apply IsClosed.inter
    | apply isClosed_iInter; intro i
  all_goals first
    | (apply isClosed_le
       · exact continuous_frobSq.comp (by fun_prop)
       · fun_prop)
    | (apply isClosed_le <;> fun_prop)
    | (apply isClosed_eq <;> fun_prop)

/-- Actual compactness of the manuscript's parameter set, including its skew
constraints, Frobenius bounds, anchored right angle and circle. No compactness
or norm-equivalence hypothesis is passed to this theorem. -/
 theorem isCompact_originalK (q : ℕ) (η : ℝ) : IsCompact (originalK q η) := by
  refine (isCompact_closedBall (0 : OriginalParameters q) (|η|+1)).of_isClosed_subset
    (isClosed_originalK q η) ?_
  rintro ⟨ell,r,c,z,u⟩ ⟨hell,hr,_,_,_,hcn,hzn,hu⟩
  have hη : η ≤ |η|+1 := by grind
  have hab : |η| ≤ |η|+1 := by linarith
  have hone : 1 ≤ |η|+1 := by aesop
  simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Matrix.norm_def,
    pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ |η|+1), Real.norm_eq_abs] using
    And.intro (fun i => (hell i).trans hη)
      ⟨fun i => (hr i).trans hη,
       fun i j => (abs_entry_le_of_frobSq_le hcn i j).trans hab,
       fun i j => (abs_entry_le_of_frobSq_le hzn i j).trans hab,
       fun i => (onCircle_abs_le_one hu i).trans hone⟩


end GS.Extensions
