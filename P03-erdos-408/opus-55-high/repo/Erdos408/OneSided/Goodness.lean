module

public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Lift
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Good ratios

PD Lemma 3.2 (`blueprint/one_sided_type_ii.md` §5.3): for fixed lists, the ratios
`r ∈ [0, 1]` failing either good-state test have measure at most `exp(-L^{a₋}/4)`, uniformly
in the lists and the varying data.

* For a nonzero integer `N`, the set of `r ∈ [0, 1]` with `‖N r‖ ≤ δ` lies within `δ / |N|`
  of the `2|N| + 1` points `k / N`, so it has measure at most `6δ`.
* Test (i). There are at most `M^K` omission products `D` and at most `Y^{0.2}` integers `l`.
  For the integer `N = l D ≥ 1`, the bad set has measure at most `6 Y^{-0.7}`. The total is
  at most `6 M^K Y^{-0.5}`.
* Test (ii). Fix `I` with `i_* = max I`. For each fresh draw `T`, the ratios at which some
  pair of distinct trial integers `DZ ≠ D'Z'` violates the separation have measure at most
  `#pairs · 600 exp(-L^{a_{i_*}})`. The trial integers number at most
  `M^K exp(2K L^{a_{i_*} - g})`, by the gap (B6). Averaging over `T` (total probability one)
  and applying Markov's inequality at the threshold `exp(-L^{a_{i_*}}/4)` gives
  `600 M^{2K} exp(4K L^{a_{i_*} - g} - (3/4) L^{a_{i_*}})` for each of the `2^K` sets `I`.
* Uniformity. Both totals are at most `exp(-L^{a₋}/4)/2` once `L^g ≥ 32K` and
  `L^{a₋} ≥ 8(K + 2K L^{0.01} + 600)`, using `M ≤ exp(L^{0.01})`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset

variable {K : ℕ}

/-! ### Small circle distances -/

/-! ### Test (i) -/

/-! ### Test (ii) -/

/-- The fresh draws have total probability one when every band has positive mass. -/
theorem sum_freshWeight {x : ℝ} {d : Data K} (I : Finset (Fin K))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) :
    ∑ T ∈ freshDraws x d I, freshWeight x d I T = 1 := by
  unfold freshDraws freshWeight
  simp_rw [prod_filter]
  have h := prod_univ_sum (fun i => if i ∈ I then {1} else band x (d.a i))
    fun i (q : ℕ) => if i ∉ I then 1 / ((q : ℝ) * harmonicMass (band x (d.a i))) else 1
  beta_reduce at h
  rw [← h]
  refine prod_eq_one fun i _ => ?_
  by_cases hi : i ∈ I
  · simp_all
  · simp only [hi, ite_false, not_false_eq_true, ite_true]
    -- `∑_{q ∈ 𝒫_i} 1 / (q V_i) = V_i / V_i`
    rw [sum_congr rfl fun (q : ℕ) _ => (div_div (1 : ℝ) (q : ℝ) _).symm, ← sum_div]
    exact div_self (hV i).ne'

/-- A fresh draw has nonnegative probability. -/
theorem freshWeight_nonneg {x : ℝ} {d : Data K} (I : Finset (Fin K))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (T : Fin K → ℕ) :
    0 ≤ freshWeight x d I T :=
  prod_nonneg fun i _ => div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (by grind))

/-- With `i_* = max I`, the selections number at most `exp(2 L^{a_{i_*} - g})^K`: every
selected group lies at least `g` below `i_*`, by the gap (B6). -/
theorem card_selections_le {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hL : 1 ≤ Real.log x) {I : Finset (Fin K)}
    (hI : I.Nonempty) :
    ((selections x d I (I.max' hI)).card : ℝ) ≤
      Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) ^ K := by
  unfold selections
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ j, ((if j ∈ I.erase (I.max' hI) then band x (d.a j) else {1}).card : ℝ)
      ≤ ∏ _j : Fin K, Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) := by
        refine prod_le_prod₀ (by simp) fun j _ => ?_
        split_ifs with hj
        · -- `j < i_*`, so `a_j ≤ a_{i_*} - g`
          have hlt : j < I.max' hI :=
            lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase hj)) (ne_of_mem_erase hj)
          have hgap := hd.gap _ _ hlt
          exact (card_band_le _ _).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) zero_le_two))
        · rw [card_singleton, Nat.cast_one]
          exact Real.one_le_exp (by positivity)
    _ = Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) ^ K := by
        simp

/-! ### Both tests -/

end Erdos408.OneSided
