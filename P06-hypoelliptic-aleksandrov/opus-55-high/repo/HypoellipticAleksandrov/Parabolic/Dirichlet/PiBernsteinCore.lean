module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.FiniteFunctionProductSum
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Product Bernstein approximation core

This module defines product Bernstein approximations on finite unit cubes and proves their
positivity, total-mass, product-metric, and summed-variance identities.
-/

@[expose] public section

open scoped BigOperators Topology unitInterval

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section PiBernstein

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

/-- The product Bernstein grid on the unit cube. -/
def piBernsteinGrid {d n : ℕ} (k : Fin d → Fin (n + 1)) : Fin d → I :=
  fun i => bernstein.z (k i)

/-- The scalar product Bernstein basis on the unit cube. -/
def piBernsteinBasis {d : ℕ} (n : ℕ) (k : Fin d → Fin (n + 1)) :
    C(Fin d → I, ℝ) :=
  ∏ i : Fin d, (bernstein n (k i)).comp
    ⟨fun x => x i, continuous_apply i⟩

/-- The product Bernstein approximation of a continuous map on the unit cube. -/
def piBernsteinApproximation {d : ℕ} (n : ℕ) (f : C(Fin d → I, E)) :
    C(Fin d → I, E) :=
  ∑ k : Fin d → Fin (n + 1),
    piBernsteinBasis n k • ContinuousMap.const (Fin d → I) (f (piBernsteinGrid k))

variable {d n : ℕ} (k : Fin d → Fin (n + 1)) (x : Fin d → I)

/-- Failure of a product-metric proximity test bounds the summed squared displacement below. -/
theorem sq_le_sum_sq_sub_of_not_dist_lt_piBernsteinGrid
     (δ : ℝ)
    (hδ : 0 ≤ δ) (hfar : ¬ dist (piBernsteinGrid k) x < δ) :
    δ ^ 2 ≤ ∑ i : Fin d,
      ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2 := by
  rcases hδ.eq_or_lt with rfl | hδpos
  · norm_num
    positivity
  · rw [dist_pi_lt_iff hδpos] at hfar
    push_neg at hfar
    obtain ⟨i, hi⟩ := hfar
    calc
      δ ^ 2 ≤ dist _ _ ^ 2 := by nlinarith
      _ = ((x i) - (piBernsteinGrid k i : ℝ)) ^ 2 := by
        rw [Subtype.dist_eq, Real.dist_eq]
        grind
      _ ≤ ∑ j : Fin d,
          ((x j) - (piBernsteinGrid k j : ℝ)) ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg
          ((x j) - (piBernsteinGrid k j : ℝ))) (Finset.mem_univ i)

/-- Every product Bernstein weight is nonnegative. -/
theorem piBernsteinBasis_nonneg  :
    0 ≤ piBernsteinBasis n k x := by
  simp only [piBernsteinBasis, ContinuousMap.prod_apply]
  exact Finset.prod_nonneg fun _ _ => bernstein_nonneg

/-- Product Bernstein weights have total mass one, including in dimension zero. -/
theorem sum_piBernsteinBasis  :
    (∑ k : Fin d → Fin (n + 1), piBernsteinBasis n k x) = 1 := by
  classical
  simp only [piBernsteinBasis, ContinuousMap.prod_apply]
  calc
    (∑ k : Fin d → Fin _, ∏ i : Fin d, bernstein n _ _) =
        ∏ i : Fin d, ∑ j : Fin _, bernstein n j _ := by
      symm
      exact Fintype.prod_sum _
    _ = 1 := by simp

/-- The summed squared coordinate displacement has the product Bernstein variance. -/
theorem sum_sq_sub_piBernsteinGrid_mul_piBernsteinBasis
     (hn : n ≠ 0) (x : Fin d → I) :
    (∑ k : Fin d → Fin (n + 1),
        (∑ i : Fin d, ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) *
          piBernsteinBasis n k x) =
      ∑ i : Fin d, (x i : ℝ) * (1 - (x i : ℝ)) / n := by
  classical
  simp only [piBernsteinBasis, ContinuousMap.prod_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ k : Fin d → Fin _,
      ((x i) - (bernstein.z _)) ^ 2 *
        ∏ j : Fin d, bernstein n _ _) = _
  rw [Fintype.sum_apply_mul_prod i
    (fun a : Fin _ => ((x i) - (bernstein.z a : ℝ)) ^ 2)
    (fun j (a : Fin _) => bernstein n a _)]
  rw [bernstein.variance hn]
  simp

end PiBernstein

end HypoellipticAleksandrov.Parabolic.Dirichlet
