module

public import RoughRegime.HolderModulus

@[expose] public section

/-! Ordered coordinate derivatives control genuine multilinear operator norms. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.Model

lemma euclidean_coordinate_decomposition {d : ℕ} (x : Covariate d) :
    x = ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ) := by
  classical
  ext j
  simp [Pi.single_apply]

section
variable {d q : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)

theorem multilinear_coordinate_expansion 
    v :
    L v = ∑ σ : Fin q → Fin d, (∏ i, v i (σ i)) *
      L (fun i => EuclideanSpace.single (σ i) 1) := by
  classical
  have hv : v = fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ) := by
    funext i
    exact euclidean_coordinate_decomposition (v i)
  conv_lhs => rw [hv]
  change L.toMultilinearMap (fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ)) = _
  rw [L.toMultilinearMap.map_sum]
  simp only [L.toMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem multilinear_norm_le_coordinate_bound 
    H (hH : 0 ≤ H)
    (hb : ∀ σ : Fin q → Fin d, |L (fun i => EuclideanSpace.single (σ i) 1)| ≤ H) :
    ‖L‖ ≤ d ^ q * H := by
  classical
  apply L.opNorm_le_bound (by positivity)
  intro v
  rw [multilinear_coordinate_expansion]
  calc
    _ ≤ ∑ σ : Fin q → Fin d,
        ‖(∏ i, v i (σ i)) * L (fun i => EuclideanSpace.single (σ i) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin q → Fin d, (∏ i, ‖v i‖) * H := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Real.norm_eq_abs, Finset.abs_prod]
      apply mul_le_mul _ (hb σ) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      grind only [Finset.prod_le_prod₀, abs_nonneg, Real.norm_eq_abs, PiLp.norm_apply_le]
    _ = ((d : ℝ) ^ q * H) * ∏ i, ‖v i‖ := by simp; ring
end


theorem holderBall_iteratedFDerivWithin_modulus {d } f
    t H (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    x y (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ‖iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y‖ ≤
      d ^ holderOrder t * H * ‖x - y‖ ^ holderExponent t := by
  have hbound := multilinear_norm_le_coordinate_bound
    (iteratedFDerivWithin ℝ (holderOrder t) f (cube d) x -
      iteratedFDerivWithin ℝ (holderOrder t) f (cube d) y)
    (H * ‖x - y‖ ^ holderExponent t) (by positivity) (fun σ => by
      solve_by_elim [holderBall_coordinate_modulus])
  simpa only [mul_assoc] using hbound

end RoughRegime.Model
