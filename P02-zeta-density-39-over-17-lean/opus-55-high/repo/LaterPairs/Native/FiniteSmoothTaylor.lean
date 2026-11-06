module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                        
                                                                     

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

section
variable {f : ℝ → ℝ}
include f
theorem contDiffAt_iteratedDeriv_finite {x : ℝ} {n j : ℕ}
    (hf : ContDiffAt ℝ (n+j) f x) :
    ContDiffAt ℝ n (iteratedDeriv j f) x := by
  induction j generalizing n with
  | zero => simpa only [Nat.cast_zero,add_zero,iteratedDeriv_zero] using hf
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hh : ContDiffAt ℝ ((n+1)+j) f x := by
        simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ,add_assoc,add_comm,add_left_comm]
          using hf
      exact (ih hh).derivWithin (by simp)

theorem taylorWithinEval_uIcc_eq_finiteTaylorPolynomial_finite {a x : ℝ} {n : ℕ} (hax : a ≠ x)
    (hf : ContDiffAt ℝ n f a) :
    taylorWithinEval f n (uIcc a x) a x = finiteTaylorPolynomial f n a x := by
  pm_5051 hu a x hax
  pm_8037
  intro j hj
  have hjn : j ≤ n := by have ht := Finset.mem_range.mp hj; omega
  have hjn' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hjn
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le hjn') left_mem_uIcc,
    iteratedDerivWithin_univ]

theorem abs_finiteTaylorPolynomial_remainder_le_finite {a x M : ℝ} (n : ℕ)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ (n+1) f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (n+1) f y| ≤ M) :
    |f x-finiteTaylorPolynomial f n a x| ≤
      M*|x-a|^(n+1)/(n+1).factorial := by
  pm_1618
  · obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      (fun z hz => (hf z hz).contDiffWithinAt)
    rw [taylorWithinEval_uIcc_eq_finiteTaylorPolynomial_finite hax
      ((hf a left_mem_uIcc).of_le (by simp))] at he
    pm_1617

theorem abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le_finite {a x M : ℝ} {j Q : ℕ} (hj : j ≤ Q)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ (Q+1) f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) :
    |iteratedDeriv j (fun y => f y-finiteTaylorPolynomial f Q a y) x| ≤
      M*|x-a|^(Q+1-j) := by
  pm_1620
  have hjQ : (j : WithTop ℕ∞) ≤ Q+1 := by exact_mod_cast (by omega : j ≤ Q+1)
  have hjtop : (j : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [iteratedDeriv_fun_sub ((hf x right_mem_uIcc).of_le hjQ)
    ((finiteTaylorPolynomial_contDiff f Q a).contDiffAt.of_le hjtop),
    iteratedDeriv_finiteTaylorPolynomial f a hj]
  have hf' (y : ℝ) (hy : y ∈ uIcc a x) :
      ContDiffAt ℝ (((Q-j+1)+j : ℕ) : WithTop ℕ∞) f y := by
    rw [show Q-j+1+j = Q+1 by omega]
    simpa only [Nat.cast_add,Nat.cast_one] using hf y hy
  have h := abs_finiteTaylorPolynomial_remainder_le_finite
    (f := iteratedDeriv j f) (a := a) (x := x) (M := M) (Q-j)
    (fun y hy => by
      have ht := contDiffAt_iteratedDeriv_finite (n := Q-j+1) (j := j)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hf' y hy)
      simpa only [Nat.cast_add,Nat.cast_one] using ht) ?_
  pm_1619
end

end TaoTrudgianYang2025
