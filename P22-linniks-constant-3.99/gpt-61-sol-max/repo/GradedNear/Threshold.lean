import GradedNear.Tactics

import GradedNear.Defs

/-!
# The threshold form (paper Proposition 8.8)

If `(Σ a_j v_j)_+² ≤ Σ D_j a_j² + d (Σ a_j)²` for all `a ≥ 0`, with every `D_j > 0` and `d > 0`,
then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ² / d`.

The threshold is a zero of the continuous scalar function `t ↦ d Σ_j (v_j - t)_+ / D_j - t` on
`[0, b]`, found by the intermediate value theorem; the test vector
`a_j = (v_j - t)_+ / D_j` then turns the quadratic hypothesis into the threshold bound.
-/

namespace GradedNear

open Finset

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] {v D : ι → ℝ} {d : ℝ}
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hquad : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
       max 0 (∑ j, a j * v j) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    NearThreshold d (j => v j, D j) := by
  let p (x : ℝ) := max 0 x
  let R (a : ι → ℝ) := ∑ i, D i * a i ^ 2 + d * (∑ i, a i) ^ 2
  let b := d * ∑ i, p (v i) / D i
  let f (t : ℝ) := d * ∑ i, p (v i - t) / D i - t
  have hb : 0 ≤ b := by
    bound
  have hf : Continuous f := by fun_prop (disch := grind)
  have hf₀ : 0 ≤ f 0 := by bound

  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hb hf.continuousOn ⟨ by
    have hp : ∑ i, p (v i - b) / D i ≤ ∑ i, p (v i) / D i := by
      bound
    nlinarith
   , hf₀⟩
  let a (i : ι) := p (v i - t) / D i
  have ha i : 0 ≤ a i := by bound

  have hcoord i : a i * v i = D i * a i ^ 2 + t * a i := by

    grind
  have hdot : ∑ i, a i * v i = R a := by
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]

    grind
  have hres₁ : R a ≤ 1 := by
    have hq := hquad a ha
    rw [hdot] at hq
    nlinarith [le_max_left 0 (R a), le_max_right 0 (R a)]
  have hcost : t ^ 2 / d + ∑ i, p (v i - t) ^ 2 / D i = R a := by

    have he : ∀ i, p (v i - t) ^ 2 / D i = D i * a i ^ 2 := by grind
    simp_rw [he]
    grind


  refine ⟨t, ht.1, Real.le_sqrt_of_sq_le ((div_le_one hd).1
    ((le_add_of_nonneg_right (sum_nonneg fun i _ =>
      div_nonneg (sq_nonneg _) (hD i).le)).trans (hcost.symm ▸ hres₁))
  ), ?_⟩
  linarith

end GradedNear
