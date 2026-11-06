module

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonMoving
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Geometry of the moving ball

Facts about `movingDomain (euclideanBall c r₀) γ σ`, the ball of radius `r₀` centred at
`γ(σ) + c`, and about Lipschitz and piecewise `C¹` curves, used by the collar barrier of
(A.1).
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Filter Set
open scoped Topology

variable {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ} {γ : ℝ → PDE.Vec n} {σ : ℝ} {y : PDE.Vec n}

/-- Membership in the moving ball: the centre of the ball at time `σ` is `γ σ + c`. -/
theorem mem_movingDomain_euclideanBall_iff  :
    y ∈ movingDomain (PDE.euclideanBall c r₀) γ σ ↔
      PDE.vecNormSq (y - (γ σ + c)) < r₀ ^ 2 := by
  rw [mem_movingDomain_iff]
  change PDE.vecNormSq _ < r₀ ^ 2 ↔ _
  ring

/-- Points of the closure of the moving ball have squared distance at most `r₀²`. -/
theorem vecNormSq_le_of_mem_closure_movingDomain 
    (hy : y ∈ closure (movingDomain (PDE.euclideanBall c r₀) γ σ)) :
    PDE.vecNormSq (y - (γ σ + c)) ≤ r₀ ^ 2 := by
  have hcl : IsClosed {y : PDE.Vec n | PDE.vecNormSq (y - (γ σ + c)) ≤ r₀ ^ 2} := by
    have hc : Continuous (fun y : PDE.Vec n => PDE.vecNormSq (y - (γ σ + c))) := by
      have : (fun y : PDE.Vec n => PDE.vecNormSq (y - (γ σ + c))) =
          fun y => ∑ i, (y i - (γ σ + c) i) ^ 2 := by
        funext y
        rw [PDE.vecNormSq_eq_sum_sq]
        rfl
      rw [this]
      fun_prop
    exact isClosed_le hc continuous_const
  have hsub : movingDomain (PDE.euclideanBall c r₀) γ σ ⊆
      {y : PDE.Vec n | PDE.vecNormSq (y - (γ σ + c)) ≤ r₀ ^ 2} := by
    intro y hy
    exact (mem_movingDomain_euclideanBall_iff.mp hy).le
  exact closure_minimal hsub hcl hy

/-- Frontier points of the moving ball lie on the sphere. -/
theorem vecNormSq_eq_of_mem_frontier_movingDomain 
    (hy : y ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ σ)) :
    PDE.vecNormSq (y - (γ σ + c)) = r₀ ^ 2 := by
  have hopen : IsOpen (movingDomain _ γ σ) :=
    isOpen_movingDomain (PDE.isOpen_euclideanBall c r₀) σ
  rw [hopen.frontier_eq] at hy
  have h1 := vecNormSq_le_of_mem_closure_movingDomain hy.1
  have h2 : ¬ PDE.vecNormSq _ < r₀ ^ 2 := fun h =>
    hy.2 (mem_movingDomain_euclideanBall_iff.mpr h)
  linarith

/-- A Euclidean-Lipschitz curve has derivative of Euclidean norm at most the Lipschitz
constant. -/
theorem vecEuclideanNorm_le_of_hasDerivAt_lipschitz 
    {γ' : PDE.Vec n} {σ Lγ : ℝ} (hLγ : 0 ≤ Lγ) (hγ : HasDerivAt γ γ' σ)
    (hL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|) :
    PDE.vecEuclideanNorm γ' ≤ Lγ := by
  have hφ : HasDerivAt (fun x => PDE.vecDot γ' (γ x)) (PDE.vecDot γ' γ') σ := HasDerivAt.fun_sum (fun i _ => ((hasDerivAt_pi.1 hγ) i).const_mul _)
  have hlip : ∀ᶠ x in 𝓝 σ, ‖PDE.vecDot γ' (γ x) - PDE.vecDot γ' (γ σ)‖ ≤
      (PDE.vecEuclideanNorm γ' * Lγ) * ‖x - σ‖ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : PDE.vecDot γ' (γ x) - PDE.vecDot γ' (γ σ) = PDE.vecDot γ' (γ x - γ σ) := by
      unfold PDE.vecDot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp [mul_sub])
    rw [h1]
    calc |PDE.vecDot γ' _| ≤
          PDE.vecEuclideanNorm γ' * PDE.vecEuclideanNorm _ :=
            PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ PDE.vecEuclideanNorm γ' * (Lγ * |x - σ|) :=
            mul_le_mul_of_nonneg_left (hL x σ) (PDE.vecEuclideanNorm_nonneg _)
      _ = (PDE.vecEuclideanNorm γ' * Lγ) * |x - σ| := by ring
  have hbound := hφ.le_of_lip' (mul_nonneg (PDE.vecEuclideanNorm_nonneg _) hLγ) hlip
  rw [Real.norm_eq_abs] at hbound
  have hsq : PDE.vecDot γ' γ' = PDE.vecEuclideanNorm γ' ^ 2 := by
    rw [PDE.vecEuclideanNorm_sq]
    rfl
  rw [hsq, abs_of_nonneg (sq_nonneg _)] at hbound
  by_cases h0 : PDE.vecEuclideanNorm γ' = 0
  · simp_all
  · nlinarith

/-- A continuous piecewise `C¹` curve is differentiable at the interior points of the
pieces of a partition of a compact interval. -/
theorem exists_partition_differentiableAt 
    (hγ : IsContinuousPiecewiseC1 γ) {a b : ℝ} (hab : a < b) :
    ∃ N : ℕ, ∃ t : Fin (N + 2) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last (N + 1)) = b ∧
      ∀ i : Fin (N + 1), ∀ σ ∈ Ioo (t i.castSucc) (t i.succ), DifferentiableAt ℝ γ σ := by
  obtain ⟨N, t, ht, h0, hl, hpiece⟩ := hγ.2 a b hab
  refine ⟨N, t, ht, h0, hl, fun i σ hσ => ?_⟩
  have h1 : DifferentiableOn ℝ γ _ :=
    (hpiece i).differentiableOn (by norm_num)
  exact h1.differentiableAt (Icc_mem_nhds hσ.1 hσ.2)

end HypoellipticAleksandrov.KineticAleksandrov
