module

public import GradedNear.SieveMajorant
public import GradedNear.Bookkeeping
public import GradedNear.SieveOffDiagonal


/-!
# The sieve part of the second Cauchy–Schwarz factor

`𝓛⁻¹ Σ_{n ≤ N} (Λ(n)/n) H(t_n) |Y_n|² ≤ Σ_j S(δ_j) a_j² + ε (Σ a)²` for all large `q`, where
`S(δ) = Σ_k h_k e^{-2δ t_k} (t_{k+1}² - t_k²)/(2 λ_k)` is the sieve part of `D(δ)`.
-/

@[expose] public section

open Complex Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

noncomputable section

namespace GradedNear

open NearData

/-- The sieve part of `D(δ)`. -/
def sieveDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D.m,
    D.h k * Real.exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

private lemma mem_sieveInterval {q n : ℕ} (hq : 2 ≤ q) {t u : ℝ} :
    n ∈ sieveInterval q t u ↔ 1 ≤ n ∧ t ≤ tn q n ∧ tn q n < u := by
  simp only [sieveInterval, mem_realIco]
  exact and_congr_right fun hn => by simp only [← not_le, ← le_tn_iff hq hn]

/-- The sieve part of the second Cauchy–Schwarz factor, summed over the cells. -/
theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
      (∀ j, |E.γ j| ≤ Real.log q / 3) → (∀ j, E.δ j ∈ D.Δ) →
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Ioc 0 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  classical
  let t k := D.t k
  let u k := D.t (k + 1)
  let v k := D.level k
  let M k := (u k ^ 2 - t k ^ 2) / (2 * v k)
  let R k := (2 * u k - t k) / v k
  let H := ∑ k ∈ range D.m, D.h k
  have hH : 0 ≤ H := sum_nonneg fun k hk => hD.h_nonneg k (mem_range.mp hk)
  let r := ε / (2 * (1 + H))
  have hr : 0 < r := by dsimp [r]; positivity
  have hbound : H * (r + r) ≤ ε := by
    dsimp [r]
    field_simp
    nlinarith
  have ht k (hk : k < D.m) : 1 / 3 + 2 * D.ε' < t k := by
    exact hD.t_zero.trans_le ((strictMonoOn_Iic_of_lt_succ hD.t_lt).monotoneOn (by simp) hk.le k.zero_le)
  obtain ⟨CB, V₀, hGr⟩ := hGr
  have hv k (hk : k < D.m) : 0 < v k ∧ v k < t k := by
    dsimp [v, t, NearData.level]
    constructor <;> linarith [ht k hk, hD.ε'_pos]
  let Bnd k (q : ℕ) := (1 + CB / v k / Real.log q) * (M k + R k / Real.log q)
  have hBnd k : Tendsto (Bnd k) atTop (𝓝 (M k)) := by
    simpa [Bnd] using ((tendsto_const_nhds (x := 1)).add (tendsto_div_log_nat (CB / v k))).mul
      ((tendsto_const_nhds (x := M k)).add (tendsto_div_log_nat (R k)))
  have hPow k (hk : k < D.m) : Tendsto (fun q : ℕ => u k * (q : ℝ) ^ (v k - t k)) atTop (𝓝 0) := by
    simpa [neg_sub] using ((tendsto_rpow_neg_atTop (sub_pos.mpr (hv k hk).2)).comp
      tendsto_natCast_atTop_atTop).const_mul (u k)
  have hcells := (eventually_all_finset (range D.m)).mpr fun k hk =>
    let h := mem_range.mp hk
    (sieve_offdiag hBur hD.ε'_pos (ht k h) (hD.t_lt k h).le hr).and <|
      ((hBnd k).eventually_le_const (lt_add_of_pos_right _ hr)).and <|
      ((hPow k h).eventually_le_const hr).and <|
      ((tendsto_rpow_atTop (hv k h).1).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max V₀ 2)
  filter_upwards [eventually_ge_atTop 2, hcells,
    tendsto_log_nat_atTop.eventually_ge_atTop (2 * ∑ δ ∈ D.Δ, δ)] with q hq hcells hΔsum
  intro ι _ E hγ hΔ hinj a ha N
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (by omega)
  have hq0 := zero_lt_one.trans_le hq1
  let L := Real.log q
  have hℓ := log_q_pos hq
  have hδ j := hD.Δ_nonneg _ (hΔ j)
  have hβ j k : E.δ j + E.δ k ≤ L := by
    linarith [single_le_sum hD.Δ_nonneg (hΔ j), single_le_sum hD.Δ_nonneg (hΔ k)]
  have hτ j k : |E.γ j - E.γ k| ≤ L := by
    linarith [abs_sub (E.γ j) (E.γ k), hγ j, hγ k]
  let e (j : ι) (k : ℕ) := Real.exp (-(E.δ j * t k))
  let w (n : ℕ) := Λ n / n * ‖Yn E a n‖ ^ 2
  let aSumSq := (∑ j, a j) ^ 2
  simp_rw [mul_right_comm (Λ _ / _), NearData.sieveH]
  change (∑ n ∈ Ioc 0 N, w n * _) / L ≤ _
  simp_rw [mul_sum, sum_comm (s := Ioc 0 N), mul_ite, mul_zero]
  rw [sum_div]
  calc
    _ ≤ ∑ k ∈ range D.m, D.h k * ((∑ j, e j k ^ 2 * M k * a j ^ 2) + (r + r) * aSumSq) := by
      refine sum_le_sum fun k hk => ?_
      rw [← sum_filter]
      simp_rw [mul_comm _ (D.h k), ← mul_sum, mul_div_assoc]
      by_cases hh : D.h k = 0
      · simp [hh]
      have hk' := mem_range.mp hk
      refine mul_le_mul_of_nonneg_left ?_ (hD.h_nonneg k hk')
      let C := sieveInterval q (t k) (u k)
      have hsub : (Ioc 0 N).filter (fun n => t k ≤ tn q n ∧ tn q n < u k) ⊆ C := by
        grind [mem_sieveInterval hq]
      refine (div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
        by dsimp [w]; positivity) hℓ.le).trans ?_
      obtain ⟨hoff, hBnd', hPow', hcut⟩ := hcells k hk
      obtain ⟨hcut, hV2⟩ := max_le_iff.mp hcut
      let V := (q : ℝ) ^ v k
      let A := (q : ℝ) ^ t k
      let B := (q : ℝ) ^ u k
      let W := sieveWeight V
      have hV : 1 < V := one_lt_two.trans_le hV2
      have hk₀ := (hv k hk').1.le.trans (hv k hk').2.le
      have hd : (∑ n ∈ C, W n) / L ≤ M k + r := by
        have hVA : V ≤ A := Real.rpow_le_rpow_of_exponent_le hq1 (hv k hk').2.le
        have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le hq1 (hD.t_lt k hk').le
        let K := 1 / Real.log V + CB / Real.log V ^ 2
        have hS t (ht : V ≤ t) : ∑ n ∈ Icc 1 ⌊t⌋₊, sieveNu V n ≤ K * t := by
          have H := (le_abs_self _).trans (hGr V t hcut ht)
          dsimp [K, sieveNu]
          linear_combination H
        have H := wt_sum_norm_le (E := K) 1 (by simp) (fun n => (sieveNu V n : ℂ)) (hV.le.trans hVA) hAB ?_
        · have hw n : wt 1 n = ((Real.log n / n : ℝ) : ℂ) := by
            push_cast
            simp [wt, cpow_neg, div_eq_mul_inv]
          have H' := (le_abs_self _).trans (by simpa only [hw, ← ofReal_mul, ← ofReal_sum,
            norm_real, Real.norm_eq_abs, norm_one, one_mul] using H)
          refine (div_le_div_of_nonneg_right H' hℓ.le).trans ?_
          simp only [K, V, A, B, Real.log_rpow hq0]
          convert hBnd' using 1
          dsimp [Bnd, M, R, L]
          field_simp [hℓ.ne', (hv k hk').1.ne']
          ring
        · intro t ht
          rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ => sieveNu_nonneg V n)]
          refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 ⌊t⌋₊) ?_
            (fun n _ _ => sieveNu_nonneg V n)).trans (hS t (hVA.trans ht.1))
          grind [mem_realIco, Nat.le_floor]
      have hp : (∑ n ∈ C, smallPrimeWeight V n / n) / L ≤ r := by
        refine (div_le_div_of_nonneg_right (small_primepow_sum (V := V) (A := A) (B := B)
          (by positivity) (by positivity) (Real.one_le_rpow hq1 (hk₀.trans (hD.t_lt k hk').le))) hℓ.le).trans ?_
        convert hPow' using 1
        simp only [V, A, B, Real.log_rpow hq0, Real.rpow_sub hq0]
        field_simp [hℓ.ne']
      have hW n : 0 ≤ W n := mul_nonneg (by positivity) (sieveNu_nonneg V n)
      have he j : e j k ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hδ j])
      have hb j n (hn : n ∈ C) : ‖phase E j n‖ ≤ e j k := by
        simp [phase, phaseWeight, e, norm_exp, -Complex.natCast_log, neg_mul]
        grw [(E.χ j).norm_le_one n, one_mul]
        gcongr
        · exact hδ j
        · exact ((mem_sieveInterval hq).mp hn).2.1
      have hY n (hn : n ∈ C) : ‖Yn E a n‖ ^ 2 ≤ aSumSq := by
        unfold Yn aSumSq
        grw [norm_sum_le]
        gcongr with j
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j)]
        exact mul_le_of_le_one_right (ha j) ((hb j n hn).trans (he j))
      have hmain : (∑ n ∈ C, W n * ‖Yn E a n‖ ^ 2) / L ≤
          ∑ j, e j k ^ 2 * M k * a j ^ 2 + r * aSumSq := by
        rw [weighted_Yn]
        let K j l := (∑ n ∈ C, (W n : ℂ) * (phase E j n * conj (phase E l n))).re / L
        have H := quadratic_rows K (fun _ _ => 0) a (fun j => e j k ^ 2 * M k) r ha
          (fun _ _ => le_rfl) (fun _ _ => rfl) ?_
        · simpa only [K, sum_const_zero, add_zero] using H
        · intro j l
          by_cases hlj : l = j
          · subst l
            simp only [ite_true, add_zero, K, Complex.re_sum, Complex.re_ofReal_mul, Complex.mul_conj,
              Complex.ofReal_re, Complex.normSq_eq_norm_sq]
            calc
              _ ≤ (∑ n ∈ C, W n * e j k ^ 2) / L := by
                gcongr with n hn
                · exact hW n
                · exact hb j n hn
              _ ≤ _ := by
                rw [← sum_mul, ← div_mul_eq_mul_div, mul_comm _ (e j k ^ 2)]
                have he₀ : 0 ≤ e j k := (Real.exp_pos _).le
                grw [hd]
                nlinarith only [mul_le_of_le_one_left hr.le (pow_le_one₀ he₀ (he j) (n := 2))]
          · have H := hoff _ (fun h => Ne.symm hlj (hinj ⟨k, hk', hh⟩ (mul_inv_eq_one.mp h))) _ _
              (add_nonneg (hδ j) (hδ l)) (hβ j l) (hτ j l)
            simpa only [K, hlj, ite_false, zero_add, add_zero, phase_pair, W, C, V, v, u, t, NearData.level] using
              (div_le_div_of_nonneg_right (Complex.re_le_norm _) hℓ.le).trans H
      calc
        _ ≤ (∑ n ∈ C, (W n * ‖Yn E a n‖ ^ 2 + smallPrimeWeight V n / n * aSumSq)) / L := by
          gcongr with n hn
          dsimp only [w, W, sieveWeight]
          have := smallPrimeWeight_nonneg V n
          grw [vonMangoldt_le_sieve hV n, add_div, add_mul]
          rw [div_mul_eq_mul_div (Real.log n)]
          gcongr
          exact hY n hn
        _ ≤ _ := by
          rw [sum_add_distrib, add_div, ← sum_mul, ← div_mul_eq_mul_div]
          grw [hmain, hp]
          linarith only
    _ ≤ _ := by
      simp only [mul_add, sum_add_distrib]
      refine add_le_add ?_ ?_
      · simp only [sieveDiag, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
        simp only [e, M, t, u, v, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_neg]
        ring_nf; exact le_rfl
      · simp only [← mul_assoc, ← sum_mul]
        gcongr

end GradedNear
