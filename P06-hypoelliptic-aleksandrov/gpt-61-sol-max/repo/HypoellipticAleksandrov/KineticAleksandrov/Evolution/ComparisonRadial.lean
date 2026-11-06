module

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivatives of radial functions

Functions of the form `y ↦ Ψ(|y - m|²)` of a native vector, together with their
gradients, Hessians, and the time derivative along a moving centre `m(σ)`.  Working with
the squared distance `|y - m|²` avoids square roots until the explicit barrier is
written down.  These formulas supply the growth barrier `Φ` of
Proposition 2.1 and the collar barrier `w(d)` of
Proposition 2.1.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Filter Matrix
open scoped Topology

variable {n : ℕ}

variable (m x : PDE.Vec n)

/-- The squared distance to a fixed centre has the expected derivative. -/
theorem hasFDerivAt_vecNormSq_sub   :
    HasFDerivAt (fun y  => PDE.vecNormSq (y - m))
      (∑ i, (2 * (x i - m i)) • (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ)) x := by
  have hfun : (fun y  => PDE.vecNormSq (y - m)) =
      fun y => ∑ i, (y i - m i) ^ 2 := by
    funext y
    rw [PDE.vecNormSq_eq_sum_sq]
    rfl
  rw [hfun]
  apply HasFDerivAt.fun_sum
  intro i _
  have h1 : HasFDerivAt (fun y : PDE.Vec n => y i - m i)
      (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ) x :=
    (hasFDerivAt_apply i x).sub_const (m i)

  convert (h1.pow 2) using 1
  simp

/-- Evaluation of the derivative of the squared distance on a basis vector. -/
theorem normSqGradCLM_apply_basisVec   (i : Fin n) :
    (∑ k, (2 * (x k - m k)) • (ContinuousLinearMap.proj k : PDE.Vec n →L[ℝ] ℝ))
      (PDE.basisVec i) = 2 * (x i - m i) := by
  simp [PDE.basisVec_apply]

variable {Ψ : ℝ → ℝ}

variable {m x : PDE.Vec n}

/-- Gradient of a function of the squared distance. -/
theorem classicalGradient_comp_vecNormSq_sub
    (hΨ : DifferentiableAt ℝ Ψ (PDE.vecNormSq (x - m))) :
    PDE.classicalGradient (fun y => Ψ (PDE.vecNormSq (y - m))) x =
      fun i => 2 * deriv Ψ (PDE.vecNormSq (x - m)) * (x i - m i) := by
  have h : HasFDerivAt (fun y => Ψ (PDE.vecNormSq (y - m)))
      (deriv Ψ (PDE.vecNormSq (x - m)) • (∑ i, (2 * (x i - m i)) •
        (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ))) x :=
    hΨ.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_vecNormSq_sub m x)
  ext i
  rw [PDE.classicalGradient_apply, h.fderiv]
  simp only [_root_.smul_apply, normSqGradCLM_apply_basisVec, smul_eq_mul]
  ring

section
variable (hΨ : ContDiffAt ℝ 2 Ψ (PDE.vecNormSq (x - m)))

include hΨ
/-- Hessian of a function of the squared distance. -/
theorem sliceHessian_comp_vecNormSq_sub
     (i j : Fin n) :
    sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x i j =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * (x i - m i) * (x j - m j) +
        (if i = j then 2 * deriv Ψ (PDE.vecNormSq (x - m)) else 0) := by
  set S : PDE.Vec n → ℝ := fun y => PDE.vecNormSq (y - m) with hS




  have hΨ2 : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) (S x)) (S x) := by

    exact (((hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasDerivAt
  have hgrad : ((PDE.classicalGradient (fun y => Ψ (S y)))) =ᶠ[𝓝 x]
      fun y => fun k => 2 * deriv Ψ (S y) * (y k - m k) := by
    filter_upwards [((show Continuous S by
        have : S = fun y => ∑ i, (y i - m i) ^ 2 := by
          funext y
          simp only [hS]
          rw [PDE.vecNormSq_eq_sum_sq]
          rfl
        rw [this]
        fun_prop).continuousAt.eventually (hΨ.eventually (by norm_num)))] with y hy
    exact classicalGradient_comp_vecNormSq_sub (hy.differentiableAt (by norm_num))
  have hfj : ∀ k : Fin n, ∃ L : PDE.Vec n →L[ℝ] ℝ,
      HasFDerivAt (fun y : PDE.Vec n => 2 * deriv Ψ (S y) * (y k - m k)) L x ∧
        ∀ i : Fin n, L (PDE.basisVec i) =
          4 * deriv (deriv Ψ) (S x) * (x i - m i) * (x k - m k) +
            (if i = k then 2 * deriv Ψ (S x) else 0) := by
    intro k



    refine ⟨_, (((hΨ2.comp_hasFDerivAt x (hasFDerivAt_vecNormSq_sub m x)).const_mul 2).mul ((hasFDerivAt_apply k x).sub_const (m k))), ?_⟩
    intro i
    simp only [_root_.add_apply, _root_.smul_apply, normSqGradCLM_apply_basisVec, smul_eq_mul,
      ContinuousLinearMap.proj_apply, PDE.basisVec_apply]
    by_cases h : i = k
    · subst h; simp; ring
    · have h' : k ≠ i := fun e => h e.symm
      simp [h, h']; ring
  choose L hL hLe using hfj

  unfold sliceHessian
  rw [hgrad.fderiv_eq]
  rw [fderiv_pi (fun k => (hL k).differentiableAt)]
  simp only [ContinuousLinearMap.pi_apply]
  rw [(hL j).fderiv, hLe j i]

/-- Contraction of a matrix with the Hessian of a function of the squared distance. -/
theorem matrixContraction_sliceHessian_comp_vecNormSq_sub
      (A : PDE.Mat n) :
    matrixContraction A (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x) =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * dotProduct (x - m) (A.mulVec (x - m)) +
        2 * deriv Ψ (PDE.vecNormSq (x - m)) * A.trace := by
  let sharedTerm_5084ec2959 := (2 * deriv Ψ (PDE.vecNormSq (x - m)))
  unfold matrixContraction
  simp_rw [sliceHessian_comp_vecNormSq_sub hΨ]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · simp only [Matrix.trace, Matrix.diag, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
      A i i * (sharedTerm_5084ec2959) =
        sharedTerm_5084ec2959 * A i i)]
    rw [← Finset.mul_sum]

/-- The Laplacian of a function of the squared distance. -/
theorem sum_diag_sliceHessian_comp_vecNormSq_sub
     :
    ∑ i, sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x i i =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * PDE.vecNormSq (x - m) +
        2 * n * deriv Ψ (PDE.vecNormSq (x - m)) := by
  simp_rw [sliceHessian_comp_vecNormSq_sub hΨ]
  simp only [ite_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [PDE.vecNormSq_eq_sum_sq, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    ring
  · ring
end


/-- Time derivative of a function of the squared distance to a moving centre. -/
theorem hasDerivAt_comp_vecNormSq_sub_moving   {m : ℝ → PDE.Vec n}
    {m' : PDE.Vec n} {σ : ℝ} (y : PDE.Vec n) (hm : HasDerivAt m m' σ)
    (hΨ : DifferentiableAt ℝ Ψ (PDE.vecNormSq (y - m σ))) :
    HasDerivAt (fun t => Ψ (PDE.vecNormSq (y - m t)))
      (deriv Ψ (PDE.vecNormSq (y - m σ)) * (-2 * ∑ i, (y i - m σ i) * m' i)) σ := by




  have e : (-2 * ∑ i, (y i - m σ i) * m' i) = (((∑ i, 2 * (y i - m σ i) * (-(m' i))))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e]
  exact (hΨ.hasDerivAt.comp σ (by
      have hfun : (fun t => PDE.vecNormSq (y - m t)) = fun t => ∑ i, (y i - m t i) ^ 2 := by
        funext t
        rw [PDE.vecNormSq_eq_sum_sq]
        rfl
      rw [hfun]
      exact HasDerivAt.fun_sum (fun i _ => (show ∀ i : Fin n, HasDerivAt (fun t => (y i - m t i) ^ 2)
      (2 * (y i - m σ i) * (-(m' i))) σ by
          intro i

          have h2 := (((hasDerivAt_pi.1 hm) i).const_sub (y i)).pow 2
          convert h2 using 1
          norm_num) i)))

end HypoellipticAleksandrov.KineticAleksandrov
