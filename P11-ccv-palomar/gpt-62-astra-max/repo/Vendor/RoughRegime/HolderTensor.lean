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

variable {d q : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)

theorem multilinear_coordinate_expansion
    (v : Fin q → Covariate d) :
    L v = ∑ σ : Fin q → Fin d, (∏ i, v i (σ i)) *
      L (fun i => EuclideanSpace.single (σ i) 1) := by
  classical
  have hv : v = fun i => ∑ j, v i j • EuclideanSpace.single j 1 := by
    funext i
    exact euclidean_coordinate_decomposition (v i)
  conv_lhs => rw [hv]
  change L.toMultilinearMap _ = _
  rw [L.toMultilinearMap.map_sum]
  simp only [L.toMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem multilinear_norm_le_coordinate_bound
    (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ σ : Fin q → Fin d, |L (fun i => EuclideanSpace.single (σ i) 1)| ≤ H) :
    ‖L‖ ≤ d ^ q * H := by
  classical
  apply L.opNorm_le_bound (by positivity)
  intro v
  rw [multilinear_coordinate_expansion]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ _σ, (∏ i, ‖v i‖) * H := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Real.norm_eq_abs, Finset.abs_prod]
      apply mul_le_mul _ (hb σ) (abs_nonneg _) (by positivity)
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => PiLp.norm_apply_le (v i) (σ i))
    _ = _ := by simp; ring

theorem holderBall_iteratedFDerivWithin_modulus {f : Covariate d → ℝ}
    {t H : ℝ} (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
    {x y : Covariate d} (hx : x ∈ cube d) (hy : y ∈ cube d) :
    let within := iteratedFDerivWithin ℝ (holderOrder t) f (cube d)
    ‖within x -
      within y‖ ≤
      d ^ holderOrder t * H * ‖x - y‖ ^ holderExponent t := by
  intro within
  have hbound := multilinear_norm_le_coordinate_bound
    (within x -
      within y)
    (H * ‖x - y‖ ^ holderExponent t) (by positivity) (fun σ => holderBall_coordinate_modulus hH hf σ hx hy)
  bound

end RoughRegime.Model
