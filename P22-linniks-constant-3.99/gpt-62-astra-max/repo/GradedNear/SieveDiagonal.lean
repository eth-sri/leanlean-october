module

public import GradedNear.SieveAbel
public import GradedNear.Basic

/-!
# (B) The diagonal of the sieve part: Graham's estimate and partial summation

From `Σ_{n ≤ N} ν_V(n) = N / log V + O(N / log² V)` (`GrahamEstimate`), partial summation gives
`Σ_{A ≤ n ≤ B} (log n / n) ν_V(n) ≤ (log² B - log² A) / (2 log V) + O((log² B + 1) / log² V)`
for `V₀ ≤ V ≤ A ≤ B`.

Apply the Abel bound on real endpoints with `s = 1`. Only the upper half
of Graham's estimate is needed to majorize all the prefixes, including the
one starting at the lower end of the cell.
-/

@[expose] public section

namespace GradedNear

open Finset Real Set

open Filter Topology

/-- On any fixed logarithmic cell the normalized diagonal is eventually below its
main term plus `ε`. In the bound from partial summation the error coefficients
contain an extra inverse power of `log q`. -/
theorem sieve_diagonal (hGr : GrahamEstimate) {t u v ε : ℝ}
    (hv : 0 < v) (hvt : v ≤ t) (htu : t ≤ u) (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop,
    ∑ n ∈ cell q t u, log n / n * sieveNu ((q:ℝ)^v) n ≤ ((u^2-t^2)/(2*v) + ε)*log q := by
  obtain ⟨c, V₀, hGr⟩ := hGr
  let Δ := (u^2-t^2)/2
  have lim := ((log_level_atTop.const_div_atTop (|c|/v^2)).const_add (1/v)).mul ((log_level_atTop.const_div_atTop (2*u)).add_const Δ)
  simp only [add_zero, zero_add] at lim
  filter_upwards [eventually_ge_atTop 2, ((tendsto_rpow_atTop hv).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max V₀ (exp 1)),
    lim.eventually_le_const (lt_add_of_pos_right _ hε)] with q hq hv₀ herr
  let V := (q:ℝ)^v
  let A := (q:ℝ)^t
  let B := (q:ℝ)^u
  have hq1 : (1:ℝ) ≤ q := by bound
  have hℓ := log_q_pos hq
  have hV : V ≤ A := rpow_le_rpow_of_exponent_le hq1 hvt
  have hab : A ≤ B := rpow_le_rpow_of_exponent_le hq1 htu
  obtain ⟨hv₀, he⟩ := max_le_iff.mp hv₀
  let K := 1/log V + |c|/log V^2
  have hLV := log_le_log (exp_pos 1) he
  rw [log_exp] at hLV
  have hA : 1 ≤ A := (one_le_exp (by norm_num)).trans (he.trans hV)
  have hu x (hx : x ∈ Set.Icc A B) : ‖prefixSum (fun n => (sieveNu V n : ℂ)) A x‖ ≤ K*x := by
    rw [prefixSum, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ => sq_nonneg _)]
    have hx0 := zero_lt_one.trans_le (hA.trans hx.1)
    have hh := (abs_le.mp (hGr V x hv₀ (hV.trans hx.1))).2
    apply (sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (Nat.one_le_ceil_iff.mpr (by positivity)) le_rfl)
      (fun i _ _ => sq_nonneg _)).trans
    grw [le_abs_self c] at hh
    simpa only [K, add_mul, div_mul_eq_mul_div, one_mul, add_comm] using sub_le_iff_le_add.mp hh
  have H := wt_bound hA hab (by positivity) hu (s := 1) (by simp)
  have eq (n : ℕ) : wt 1 n * (sieveNu V n : ℂ) = ((log n/n*sieveNu V n : ℝ) : ℂ) := by simp [wt, Complex.cpow_neg_one, div_eq_mul_inv]
  simp only [prefixSum, eq, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, norm_one, one_mul] at H
  apply (le_abs_self _).trans H |>.trans
  apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right herr hℓ.le) |>.trans_eq ?_
  · dsimp [K,V,A,B,Δ]; simp_rw [log_rpow (by positivity : 0 < (q:ℝ))]; field_simp
  · dsimp [Δ]; ring

end GradedNear
