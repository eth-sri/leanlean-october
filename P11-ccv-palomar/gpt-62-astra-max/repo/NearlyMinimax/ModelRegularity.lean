module

public import NearlyMinimax.Model
public import NearlyMinimax.Projection

@[expose] public section

open Set Matrix
open scoped BigOperators ENNReal

namespace NearlyMinimax

section
variable {d : ℕ} {U : Set (Covariate d)} {F : Covariate d → ℝ} {ℓ : ℕ} {α H : ℝ} (x : Covariate d)
    (G : Covariate d → ℝ) (hH : 0 ≤ H) (hNorm : holderNorm U F ℓ α ≤ ENNReal.ofReal H)
    (γ : Fin d → Fin (ℓ + 1))

theorem multiPartial_zero_index (F : Covariate d → ℝ) :
    multiPartial F (fun _ => 0) = F := by
  simp [multiPartial, (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl))]

theorem euclideanNorm_eq_sqrt_energy :
    euclideanNorm x = Real.sqrt (projectionEnergy x) := by
  grind [euclideanNorm, projectionEnergy, dotProduct]

theorem euclideanNorm_eq_zero_iff :
    euclideanNorm x = 0 ↔ x = 0 := by
  rw [euclideanNorm_eq_sqrt_energy, Real.sqrt_eq_zero (projectionEnergy_nonneg x)]
  exact dotProduct_self_eq_zero

theorem euclideanNorm_pos_of_ne_zero {x : Covariate d} (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  have hnonneg : 0 ≤ euclideanNorm x := by unfold euclideanNorm; positivity
  have hne : euclideanNorm x ≠ 0 := fun hz => hx ((euclideanNorm_eq_zero_iff x).mp hz)
  positivity

/-- The model's actual Hölder seminorm gives its pointwise modulus,
using precisely the Euclidean distance in the manuscript. -/
theorem holderSeminorm_pointwise_bound (α H : ℝ) (hH : 0 ≤ H)
    (hseminorm : holderSeminorm U G α ≤ ENNReal.ofReal H)
    {x y : Covariate d} (hx : x ∈ U) (hy : y ∈ U) :
    |G x - G y| ≤ H * euclideanNorm (x - y) ^ α := by
  by_cases hxy : x = y
  · subst y
    simp
    exact mul_nonneg hH (Real.rpow_nonneg (Real.sqrt_nonneg _) α)
  · have hraw : ENNReal.ofReal
        (|G x - G y| / euclideanNorm (x - y) ^ α) ≤ holderSeminorm U G α := by
      apply le_iSup_of_le (⟨x, hx⟩)
      apply le_iSup_of_le (⟨y, hy⟩)
      bound
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (euclideanNorm_pos_of_ne_zero (sub_ne_zero.mpr hxy)) α)).mp ((ENNReal.ofReal_le_ofReal_iff hH).mp (hraw.trans hseminorm))

include hH hNorm in
/-- Every mixed partial counted in the model norm has the stated
uniform pointwise bound on the extension domain. -/
theorem holderNorm_derivative_bound (hγ : (∑ i, (γ i).val) ≤ ℓ)
    {x : Covariate d} (hx : x ∈ U) :
    |multiPartial F (fun i => (γ i).val) x| ≤ H := by
  have hpoint  := le_iSup (fun z : U => ENNReal.ofReal |multiPartial F (fun i => (γ i).val) z|) ⟨x, hx⟩
  have hterm : derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤
      holderNorm U F ℓ α := by
    apply le_trans _ (le_add_right le_rfl)
    have ht := Finset.single_le_sum
      (fun δ _ => (bot_le : 0 ≤
        if (∑ i, (δ i).val) ≤ ℓ then derivativeSup U (multiPartial F (fun i => (δ i).val)) else 0))
      (Finset.mem_univ γ)
    bound
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp ((hpoint.trans hterm).trans hNorm)

include hH hNorm in
/-- The highest-order mixed partials counted by the model norm inherit
the actual Hölder modulus, without replacing the paper's norm. -/
theorem holderNorm_top_derivative_modulus (hγ : (∑ i, (γ i).val) = ℓ)
    {x y : Covariate d} (hx : x ∈ U) (hy : y ∈ U) :
    |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
      H * euclideanNorm (x - y) ^ α := by
  apply holderSeminorm_pointwise_bound _ α H hH _ hx hy
  apply le_trans _ hNorm
  apply le_trans _ (le_add_left le_rfl)
  apply le_iSup_of_le γ
  bound

end

variable {d : ℕ}

/-- The paper's actual admissibility norm bounds the regression values
uniformly on the design cube for every smoothness order. -/
theorem admissible_regression_value_bound {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    {x : Covariate d} (hx : x ∈ unitCube d) : |θ.regression x| ≤ C.holderBound := by
  rcases hθ with ⟨_, _, _, _, ⟨F, hcube, _, hNorm⟩, _, _, _⟩
  have hb := holderNorm_derivative_bound
    C.holderBound_pos.le hNorm (fun _ => 0) (by simp) (C.cube_subset hx)
  simpa only [Fin.val_zero, multiPartial_zero_index, hcube x hx] using hb

/-- A cube of side length `h` has Euclidean diameter at most `sqrt(d) h`. -/
theorem euclideanNorm_le_coordinate_radius {x : Covariate d}
    {h : ℝ} (hh : 0 ≤ h) (hx : ∀ i, |x i| ≤ h) :
    euclideanNorm x ≤ Real.sqrt d * h := by
  rw [euclideanNorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hh, ?_⟩
  rw [mul_pow]
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using (sq_le_sq₀ (abs_nonneg _) hh).mpr (hx i)
    _ = _ := by simp

/-- Each coordinate is bounded by the manuscript's Euclidean norm. -/
@[bound] theorem abs_coordinate_le_euclideanNorm {d : ℕ} (v : Covariate d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  simpa only [Real.sqrt_sq_eq_abs, euclideanNorm] using Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

end NearlyMinimax
