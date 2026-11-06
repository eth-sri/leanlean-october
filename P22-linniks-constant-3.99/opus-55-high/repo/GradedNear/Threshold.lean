module

public import Mathlib

/-!
# The threshold form (paper Proposition 8.8)

If `(Σ a_j v_j)_+² ≤ Σ D_j a_j² + d (Σ a_j)²` for all `a ≥ 0`, with every `D_j > 0` and `d > 0`,
then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ² / d`.

This is the direction "quadratic ⇒ threshold".
The threshold is a zero of the continuous scalar function `t ↦ d Σ_j (v_j - t)_+ / D_j - t` on
`[0, b]`, found by the intermediate value theorem; the test vector
`a_j = (v_j - t)_+ / D_j` then turns the quadratic hypothesis into the threshold bound.
-/

@[expose] public section

namespace GradedNear

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] (v D : ι → ℝ) (d : ℝ)
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hq : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt d ∧
      ∑ j, (max 0 (v j - τ)) ^ 2 / D j ≤ 1 - τ ^ 2 / d := by
  have hb : 0 ≤ d * ∑ i, max 0 (v i) / D i :=
    mul_nonneg hd.le (Finset.sum_nonneg fun i _ => div_nonneg (le_max_left ..) (hD i).le)
  have hf : Continuous fun t => d * ∑ i, max 0 (v i - t) / D i - t := by fun_prop
  obtain ⟨t, ht, hft⟩ : (0 : ℝ) ∈ _ '' _ := intermediate_value_Icc' hb hf.continuousOn ⟨by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => div_le_div_of_nonneg_right
        (max_le_max_left 0 (by linarith : v i - d * ∑ i, max 0 (v i) / D i ≤ v i)) (hD i).le
      nlinarith, by grind⟩
  set a := fun i => max 0 (v i - t) / D i
  have ha i : 0 ≤ a i := div_nonneg (le_max_left ..) (hD i).le
  have hc i : a i * v i = D i * a i ^ 2 + t * a i ∧ max 0 (v i - t) ^ 2 / D i = D i * a i ^ 2 := by grind
  have hS := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hD i).le (sq_nonneg (a i))
  have h1 := hq a ha
  have ht' : t = d * ∑ i, a i := by grind
  simp only [(hc _).1, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  rw [ht', max_eq_right (by nlinarith)] at h1
  have h2 : t ^ 2 / d = d * (∑ i, a i) ^ 2 := by grind
  refine ⟨t, ht.1, Real.le_sqrt_of_sq_le ?_, ?_⟩
  · exact (div_le_one hd).1 (by nlinarith)
  · simp only [(hc _).2]
    nlinarith

end GradedNear
