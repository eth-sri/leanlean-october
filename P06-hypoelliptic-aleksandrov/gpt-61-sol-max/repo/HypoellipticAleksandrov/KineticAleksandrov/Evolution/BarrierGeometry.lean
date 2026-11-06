module

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonMoving
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
import Mathlib.Tactic.Linarith



/-!
# Geometry of the moving ball

Facts about `movingDomain (euclideanBall c r₀) γ σ`, the ball of radius `r₀` centred at
`γ(σ) + c`, and about Lipschitz and piecewise `C¹` curves, used by the collar barrier of
(A.1).
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set
open scoped Topology

variable {n : ℕ}

variable {c : PDE.Vec n} {r₀ : ℝ} {γ : ℝ → PDE.Vec n} {σ : ℝ} {y : PDE.Vec n}

/-- Membership in the moving ball: the centre of the ball at time `σ` is `γ σ + c`. -/
theorem mem_movingDomain_euclideanBall_iff   :
    y ∈ movingDomain (PDE.euclideanBall c r₀) γ σ ↔
      PDE.vecNormSq (y - (γ σ + c)) < r₀ ^ 2 := by
  rw [mem_movingDomain_iff]
  change PDE.vecNormSq (y - γ σ - c) < r₀ ^ 2 ↔ _
  rw [sub_sub]

/-- Points of the closure of the moving ball have squared distance at most `r₀²`. -/
theorem vecNormSq_le_of_mem_closure_movingDomain
    (hy : y ∈ closure (movingDomain (PDE.euclideanBall c r₀) γ σ)) :
    PDE.vecNormSq (y - (γ σ + c)) ≤ r₀ ^ 2 := (closure_minimal (fun ⦃y⦄ hy => LT.lt.le (mem_movingDomain_euclideanBall_iff.mp hy))
  (isClosed_le
    (Eq.mpr
      (id
        (congrArg (fun _a => Continuous _a)
          (funext fun y =>
            Eq.mpr
              (id (congrArg (fun _a => _a = ∑ i, (y i - (γ σ + c) i) ^ 2) (PDE.vecNormSq_eq_sum_sq (y - (γ σ + c)))))
              (Eq.refl (∑ i, (y - (γ σ + c)) i ^ 2)))))
      (continuous_finsetSum Finset.univ fun i a =>
        Continuous.comp' (Continuous.fun_pow continuous_id' 2)
          (Continuous.fun_sub (continuous_apply i) continuous_const)))
    continuous_const)
  hy)

/-- Frontier points of the moving ball lie on the sphere. -/
theorem vecNormSq_eq_of_mem_frontier_movingDomain
    (hy : y ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ σ)) :
    PDE.vecNormSq (y - (γ σ + c)) = r₀ ^ 2 := by

  rw [(isOpen_movingDomain (PDE.isOpen_euclideanBall c r₀) σ).frontier_eq] at hy

  have h2  := fun h =>
    hy.2 (mem_movingDomain_euclideanBall_iff.mpr h)
  exact le_antisymm (vecNormSq_le_of_mem_closure_movingDomain hy.1) (not_lt.mp h2)

variable {γ : ℝ → PDE.Vec n}

/-- A Euclidean-Lipschitz curve has derivative of Euclidean norm at most the Lipschitz
constant. -/
theorem vecEuclideanNorm_le_of_hasDerivAt_lipschitz
    {γ' : PDE.Vec n} {σ Lγ : ℝ} (hLγ : 0 ≤ Lγ) (hγ : HasDerivAt γ γ' σ)
    (hL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|) :
    PDE.vecEuclideanNorm γ' ≤ Lγ := by


  have hbound := (show HasDerivAt (fun x => PDE.vecDot γ' (γ x)) (PDE.vecDot γ' γ') σ by
      unfold PDE.vecDot
      exact HasDerivAt.fun_sum (fun i _ => ((hasDerivAt_pi.1 hγ) i).const_mul (γ' i))).le_of_lip' (mul_nonneg (PDE.vecEuclideanNorm_nonneg _) hLγ) (by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : PDE.vecDot γ' (γ x) - PDE.vecDot γ' (γ σ) = PDE.vecDot γ' (γ x - γ σ) := by
        unfold PDE.vecDot
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by simp [mul_sub])
      rw [h1, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |PDE.vecDot γ' (γ x - γ σ)| ≤
            PDE.vecEuclideanNorm γ' * PDE.vecEuclideanNorm (γ x - γ σ) :=
              PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
        _ ≤ PDE.vecEuclideanNorm γ' * (Lγ * |x - σ|) :=
              mul_le_mul_of_nonneg_left (hL x σ) (PDE.vecEuclideanNorm_nonneg _)
        _ = (PDE.vecEuclideanNorm γ' * Lγ) * |x - σ| := by ring)
  rw [Real.norm_eq_abs] at hbound
  have hsq : PDE.vecDot γ' γ' = PDE.vecEuclideanNorm γ' ^ 2 := by
    rw [PDE.vecEuclideanNorm_sq]
    rfl
  rw [hsq, abs_of_nonneg (sq_nonneg _)] at hbound
  nlinarith

/-- A continuous piecewise `C¹` curve is differentiable at the interior points of the
pieces of a partition of a compact interval. -/
theorem exists_partition_differentiableAt
    (hγ : IsContinuousPiecewiseC1 γ) {a b : ℝ} (hab : a < b) :
    ∃ N : ℕ, ∃ t : Fin (N + 2) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last (N + 1)) = b ∧
      ∀ i : Fin (N + 1), ∀ σ ∈ Ioo (t i.castSucc) (t i.succ), DifferentiableAt ℝ γ σ := by
  obtain ⟨N, t, ht, h0, hl, hpiece⟩ := hγ.2 a b hab
  refine ⟨N, t, ht, h0, hl, fun i σ hσ => ?_⟩

  exact ((hpiece i).differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hσ.1 hσ.2)

end HypoellipticAleksandrov.KineticAleksandrov
