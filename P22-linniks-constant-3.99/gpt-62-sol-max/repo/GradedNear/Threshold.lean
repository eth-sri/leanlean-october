module

public import Mathlib

/-!
# The threshold form (paper Proposition 8.8)

If `(Σ a_j v_j)_+² ≤ Σ D_j a_j² + d (Σ a_j)²` for all `a ≥ 0`, with every `D_j > 0` and `d > 0`,
then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ² / d`.

The threshold is a zero of the continuous scalar function `t ↦ d Σ_j (v_j - t)_+ / D_j - t` on
`[0, b]`, found by the intermediate value theorem; the test vector
`a_j = (v_j - t)_+ / D_j` then turns the quadratic hypothesis into the threshold bound.
-/

@[expose] public section

namespace GradedNear

scoped notation "ThresholdForm[" j "; " v ", " D "; " d "]" =>
  ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt d ∧
    ∑ j, (max 0 (v - τ)) ^ 2 / D ≤ 1 - τ ^ 2 / d

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] (v D : ι → ℝ) (d : ℝ)
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hq : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    ThresholdForm[j; v j, D j; d] := by
  let a (t : ℝ) (i : ι) := max 0 (v i - t) / D i
  let b := d * ∑ i, a 0 i
  let f (t : ℝ) := (∑ i, a t i) - t / d
  have ha t i : 0 ≤ a t i := div_nonneg (le_max_left _ _) (hD i).le
  have hb : 0 ≤ b := mul_nonneg hd.le (Finset.sum_nonneg fun i _ => ha 0 i)
  have hfb : f b ≤ 0 := by
    rw [sub_nonpos, mul_div_cancel_left₀ _ hd.ne']
    unfold a
    gcongr with i
    exact (hD i).le
  have hf : Continuous f := by dsimp [f, a]; fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hb hf.continuousOn
    ⟨hfb, by simpa [f] using (Finset.sum_nonneg fun i _ => ha 0 i)⟩
  have hfix := sub_eq_zero.mp he
  have hterm i : a t i * v i = (max 0 (v i - t)) ^ 2 / D i + t * a t i := by
    simp only [a, max_def]
    split <;> ring
  let Q := (∑ i, (max 0 (v i - t)) ^ 2 / D i) + t ^ 2 / d
  have hdot : (∑ i, a t i * v i) = Q := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfix]
    ring
  have hs : 0 ≤ ∑ i, (max 0 (v i - t)) ^ 2 / D i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hD i).le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have H := hq (a t) (ha t)
  simp_rw [hdot, max_eq_right hQ, hfix] at H
  have h1 : Q ≤ 1 := by
    suffices Q ^ 2 ≤ Q by nlinarith
    convert H using 2
    · simp only [a, ← mul_div_assoc, pow_two]
      congr with i
      field_simp [(hD i).ne']
    · field_simp
  dsimp [Q] at h1
  exact ⟨t, ht.1, Real.le_sqrt_of_sq_le ((div_le_one hd).1 (by linarith)), by linarith⟩

end GradedNear
