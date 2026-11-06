module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Calculus for the explicit Euclidean norm on raw vectors

This file records the first derivatives of `PDE.vecNormSq` and
`PDE.vecEuclideanNorm`.  These are the explicit finite-coordinate Euclidean
functions on `PDE.Vec`; no norm inherited from a type-class instance is used.
-/

@[expose] public section

namespace HypoellipticAleksandrov

noncomputable section

open scoped BigOperators

variable {d : ℕ}

/-- The continuous linear functional `w ↦ 2 (z · w)`. -/
def vecNormSqFDeriv  (z : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, (2 * z i) • ContinuousLinearMap.proj i

@[simp]
theorem vecNormSqFDeriv_apply  (z w : PDE.Vec d) :
    vecNormSqFDeriv z w = 2 * PDE.vecDot z w := by
  classical
  unfold vecNormSqFDeriv PDE.vecDot
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

variable (z : PDE.Vec d)

/-- The squared explicit Euclidean norm has derivative `w ↦ 2 (z · w)`. -/
theorem hasFDerivAt_vecNormSq   :
    HasFDerivAt PDE.vecNormSq (vecNormSqFDeriv z) z := by
  classical
  have hd : DifferentiableAt ℝ PDE.vecNormSq z := by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop
  convert hd.hasFDerivAt using 1
  ext w
  rw [vecNormSqFDeriv_apply]
  unfold PDE.vecNormSq PDE.vecDot
  rw [fderiv_fun_sum fun i _ => by fun_prop]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv]
  simp only [ContinuousLinearMap.proj_apply]
  ring





end

end HypoellipticAleksandrov
