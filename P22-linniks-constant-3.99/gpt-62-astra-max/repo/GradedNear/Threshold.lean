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

/-- Threshold form (T), with squared radius `d` and per-entry feature and diagonal `(v,D)`. -/
scoped macro "HasThreshold[" d:term "] " j:ident " ↦ " "(" v:term ", " D:term ")" : term =>
  `(∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt $d ∧ ∑ $j:ident, (max 0 ($v - τ))^2 / $D ≤ 1 - τ^2 / $d)

/-- Decreasing a feature (or making it nonpositive), increasing a diagonal,
or increasing the squared radius preserves the same threshold witness. -/
lemma threshold_weaken {ι : Type*} [Fintype ι] {v v' D D' : ι → ℝ} {d d' : ℝ}
    (hD : ∀ j, 0 < D j) (hDD : ∀ j, D j ≤ D' j) (hv : ∀ j, v' j ≤ v j ∨ v' j ≤ 0)
    (hd : 0 < d) (hdd : d ≤ d') : (HasThreshold[d] j ↦ (v j, D j)) → HasThreshold[d'] j ↦ (v' j, D' j) := by
  rintro ⟨τ, hτ, hb, h⟩
  refine ⟨τ, hτ, hb.trans (Real.sqrt_le_sqrt hdd), (Finset.sum_le_sum fun j _ => ?_).trans (h.trans ?_)⟩
  · have := hv j; bound
  · gcongr

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] (v D : ι → ℝ) (d : ℝ)
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hq : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    HasThreshold[d] j ↦ (v j, D j) := by
  let p t i := max 0 (v i - t)
  let a t i := p t i / D i
  let f t := d * ∑ i, a t i
  have ha t i : 0 ≤ a t i := div_nonneg (le_max_left ..) (hD i).le
  have hb : 0 ≤ f 0 := mul_nonneg hd.le (Finset.sum_nonneg fun i _ => ha 0 i)
  obtain ⟨t, ht, hft⟩ := exists_mem_Icc_isFixedPt (f := f) (by dsimp [f,a,p]; fun_prop) hb hb (by
    dsimp [f,a,p]; gcongr with i <;> first | positivity | linarith [hD i])
  have hfix : d * (∑ i, a t i) = t := hft
  let c := ∑ i, p t i^2 / D i
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hD i).le
  have h := hq (a t) (ha t)
  have hdiag : ∑ i, D i * a t i^2 = c := by
    apply Finset.sum_congr rfl; intro i _; dsimp [a]; field_simp
  have hdot : ∑ i, a t i * v i = c + t * ∑ i, a t i := by
    dsimp [c]; rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [a,p]; field_simp; rcases le_total 0 (v i - t) with h | h
    · rw [max_eq_right h]; ring
    · simp [max_eq_left h]
  have hval : c + t^2/d ≤ 1 := by
    have e : t^2/d = d * (∑ i, a t i)^2 := by nth_rw 1 [← hfix]; field_simp
    have e' : t * (∑ i, a t i) = d * (∑ i, a t i)^2 := by linear_combination (∑ i, a t i) * -hfix
    rw [hdot, hdiag, e', max_eq_right (by positivity)] at h
    nlinarith
  exact ⟨t, ht.1, Real.le_sqrt_of_sq_le ((div_le_one hd).mp (by linarith)), by linarith⟩

end GradedNear
