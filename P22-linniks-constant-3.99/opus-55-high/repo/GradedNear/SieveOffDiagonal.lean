module

public import GradedNear.SieveBasic
public import GradedNear.BurgessReduction

/-!
# (C) The off-diagonal of the sieve part: Burgess's bound and Abel summation

For a non-principal `ψ` mod `q`, a cell `[q^t, q^{t'})` with `t > 1/3 + 2ε'`, and the level
`V = q^{(t - 1/3)/2 - ε'}`, open `ν_V(n) = Σ_{d,e ≤ V} ψ_d ψ_e [d ∣ n][e ∣ n]`. Each inner sum
runs over `m ≥ M₀ = q^t/[d,e] ≥ q^{1/3 + 2ε'}`. Abel summation against the pointwise Burgess
bound `|Σ_{M₀ ≤ m ≤ u} ψ(m)| ≪ u^{2/3} q^{1/9 + ε}`, together with
`Σ_{d,e ≤ V} [d,e]^{-2/3} ≪ V^{2/3}`, gives a total of `≪ (log q)^2 q^{ε - 2ε'/3}`.

Formalized route: the sum over `Ico ⌈q^t⌉ ⌈q^{t'}⌉` is rewritten over `Ioc a b`; the square is
opened over `d, e ≤ ⌊V⌋` (`sum_sieveNu_mul`); each inner sum over multiples of `l = [d,e]` is
handled by discrete summation by parts in `n` (`sum_Ioc_by_parts`), with partial sums bounded
by Burgess for any length (`burgess_any_length`, `norm_sum_Ioc_dvd_le`) and
`|W(n) - W(n+1)| ≤ (1 + |s| log(n+1))/n²` from the mean value theorem (`norm_wt_sub_le`),
which gives `≪ q^{1/9+ε} l^{-2/3} (q^t)^{-1/3} (1 + log q)^3` (`norm_T_le`). The lcm sum is
bounded by `9 V^{2/3} (1 + log V)` (`lcm_sum_le`). With `ε = ε'/3` the total is
`≪ (1 + log q)^4 q^{-ε'/3} ≪ q^{-ε'/6}`, so `κ = ε'/6` and `q₀ = 2`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.Moebius

namespace GradedNear

/-! ### The Selberg weights -/

/-- The weights satisfy `|ψ_d| ≤ 1`. -/
lemma abs_grahamWeight_le_one (V : ℝ) (d : ℕ) : |grahamWeight V d| ≤ 1 := by
  unfold grahamWeight
  split_ifs with h
  · rcases d.eq_zero_or_pos with rfl | hd
    · simp
    have hd1 : (1:ℝ) ≤ d := mod_cast hd
    have h1 := Real.log_nonneg ((one_le_div (by positivity)).2 h)
    rw [abs_div, abs_mul, abs_of_nonneg h1, abs_of_nonneg (Real.log_nonneg (hd1.trans h))]
    exact div_le_one_of_le₀ ((mul_le_of_le_one_left h1 (by exact_mod_cast
      ArithmeticFunction.abs_moebius_le_one)).trans (Real.log_le_log (by bound)
        (div_le_self (by linarith) hd1))) (Real.log_nonneg (hd1.trans h))
  · simp

/-! ### Summation by parts -/

/-- Discrete summation by parts, with partial sums `P(x) = Σ_{a < k ≤ x} f(k)`. -/
lemma sum_Ioc_by_parts (f W : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, f n * W n =
      (∑ k ∈ Finset.Ioc a b, f k) * W (b + 1) +
        ∑ n ∈ Finset.Ioc a b, (∑ k ∈ Finset.Ioc a n, f k) * (W n - W (n + 1)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : a ≤ b
    · simp only [Finset.sum_Ioc_succ_top hab, ih]
      ring
    · simp_all

/-- A harmonic-sum bound. -/
lemma sum_Ioc_inv_le (a b : ℕ) : ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n ≤ 1 + Real.log b := by
  refine le_trans ?_ (harmonic_le_one_add_log b)
  simp only [harmonic_eq_sum_Icc, one_div]
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp at hx ⊢; omega)
    (fun _ _ _ => by positivity)

/-! ### The weight `W(n) = log n · n^{-s}` -/

/-- The weight `W(n) = log n · n^{-s}`. -/
noncomputable def wt (s : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) * (n : ℂ) ^ (-s)

/-- `|W(n)| ≤ log n / n` for `Re s ≥ 1`. -/
lemma norm_wt_le (s : ℂ) (hs : 1 ≤ s.re) (n : ℕ) : ‖wt s n‖ ≤ Real.log n / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt]
  rw [wt, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n), div_eq_mul_inv, neg_re,
    ← Real.rpow_neg_one]
  gcongr
  exact_mod_cast hn

/-- `W(n) = G(log n)` with `G(u) = u e^{-su}`. -/
lemma wt_eq_exp (s : ℂ) {n : ℕ} (hn : 0 < n) :
    wt s n = (Real.log n : ℂ) * cexp ((Real.log n : ℂ) * (-s)) := by
  rw [wt, Complex.cpow_def_of_ne_zero (mod_cast hn.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]

/-- `|W(n) - W(n+1)| ≤ (1 + |s| log(n+1)) / n²` for `Re s ≥ 1`, by the mean value theorem
applied to `G(u) = u e^{-su}` on `[log n, log(n+1)]`. -/
lemma norm_wt_sub_le (s : ℂ) (hs : 1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖wt s n - wt s (n + 1)‖ ≤ (1 + ‖s‖ * Real.log (n + 1)) / (n : ℝ) ^ 2 := by
  have hn0 : (0:ℝ) < n := mod_cast hn
  have hu : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hn0 (by linarith)
  have hu0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hC : 0 ≤ 1 + ‖s‖ * Real.log (n + 1) := by have := hu0.trans hu; positivity
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => (u : ℂ) * cexp ((u : ℂ) * (-s)))
    (C := (1 + ‖s‖ * Real.log (n + 1)) / n)
    (f' := fun u => cexp ((u : ℂ) * (-s)) * (1 - u * s))
    (fun u _ => by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := ofRealCLM.hasDerivAt
      convert (h1.mul (h1.mul_const (-s)).cexp).hasDerivWithinAt using 1
      ring) ?_ (convex_Icc ..) (Set.left_mem_Icc.2 hu) (Set.right_mem_Icc.2 hu)
  · rw [wt_eq_exp s hn, wt_eq_exp s n.succ_pos, Nat.cast_succ, norm_sub_rev]
    refine key.trans ?_
    have h := Real.log_le_sub_one_of_pos (x := ((n:ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) hn0.ne', add_div, div_self hn0.ne'] at h
    grw [Real.norm_of_nonneg (by linarith), h]
    exact (by ring : _ = _).le
  · rintro u ⟨h0, h1⟩
    rw [norm_mul, Complex.norm_exp, div_eq_mul_inv, mul_comm]
    refine mul_le_mul ((norm_sub_le ..).trans ?_) ?_ (by positivity) hC
    · simp [abs_of_nonneg (hu0.trans h0)]
      nlinarith [norm_nonneg s]
    · rw [← Real.exp_log hn0, ← Real.exp_neg, Real.exp_le_exp]
      simp
      nlinarith

/-! ### The bound for one pair `(d, e)` -/

/-- `(x/l)^{2/3} ≤ l^{-2/3} c^{-1/3} x` for `0 < c ≤ x`. -/
lemma rpow_two_thirds_div_le {x l c : ℝ} (hc : 0 < c) (hcx : c ≤ x) (hl : 0 < l) :
    (x / l) ^ ((2 : ℝ) / 3) ≤ l ^ (-((2 : ℝ) / 3)) * c ^ (-((1 : ℝ) / 3)) * x := by
  have hx : 0 < x := lt_of_lt_of_le hc hcx
  rw [Real.div_rpow hx.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le,
    show x ^ ((2 : ℝ) / 3) = x * x ^ (-((1 : ℝ) / 3)) by
      rw [← Real.rpow_one_add' hx.le (by norm_num)]; norm_num]
  have := Real.rpow_le_rpow_of_nonpos hc hcx (show -((1 : ℝ) / 3) ≤ 0 by norm_num)
  grw [this]
  grind

/-- Partial sums of `χ` over the multiples of `l` in `(a, x]`, from Burgess's bound. -/
lemma norm_sum_Ioc_dvd_le {q : ℕ} (χ : DirichletCharacter ℂ q) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3))
    {l : ℕ} (hl : 0 < l) (a x : ℕ) :
    ‖∑ k ∈ Finset.Ioc a x, (if l ∣ k then χ k else 0)‖ ≤
      K * ((x : ℝ) / l) ^ ((2 : ℝ) / 3) := by
  rw [← Finset.sum_filter, sum_filter_dvd_Ioc _ hl]
  simp only [Nat.cast_mul, map_mul, ← Finset.mul_sum, norm_mul]
  grw [χ.norm_le_one, one_mul]
  rcases le_or_gt (a / l) (x / l) with hax | hax
  · obtain ⟨H, hH⟩ := Nat.exists_eq_add_of_le hax
    rw [hH]
    refine (h ..).trans ?_
    gcongr
    exact (Nat.cast_le.2 (hH ▸ Nat.le_add_left _ _ : H ≤ x / l)).trans Nat.cast_div_le
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp
    positivity

/-- The inner sum for one `l = [d, e]`: by summation by parts against the partial sums,
`|Σ_{a < n ≤ b, l ∣ n} χ(n) W(n)| ≤ K l^{-2/3} (a+1)^{-1/3} Λ`, where
`Λ = log(b+1) + (1 + |s| log(b+1))(1 + log(b+1))`. -/
lemma norm_T_le {q : ℕ} (χ : DirichletCharacter ℂ q) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3))
    (s : ℂ) (hs : 1 ≤ s.re) {l : ℕ} (hl : 0 < l) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ioc a b, (if l ∣ n then χ n * wt s n else 0)‖ ≤
      K * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * (Real.log (b + 1) +
        (1 + ‖s‖ * Real.log (b + 1)) * (1 + Real.log (b + 1))) * (l : ℝ) ^ (-((2 : ℝ) / 3)) := by
  set E := K * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3))
  set L := Real.log ((b : ℝ) + 1)
  have hE0 : 0 ≤ E := by positivity
  have hL0 : 0 ≤ L := Real.log_nonneg (by simp)
  simp only [← ite_zero_mul]
  rw [sum_Ioc_by_parts]
  have hkey : ∀ x : ℕ, a < x → ‖∑ k ∈ Finset.Ioc a x, if l ∣ k then χ k else 0‖ ≤ E * x :=
    fun x hx => by
      grw [norm_sum_Ioc_dvd_le χ hK h hl a x, rpow_two_thirds_div_le (c := a + 1) (by positivity) (mod_cast hx) (mod_cast hl)]
      grind
  rcases le_or_gt b a with hab | hab
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp
    positivity
  calc _ ≤ E * L + ∑ n ∈ Finset.Ioc a b, E * (1 + ‖s‖ * L) * (1 / (n : ℝ)) := by
        refine (norm_add_le ..).trans (add_le_add ?_ ((norm_sum_le ..).trans
          (Finset.sum_le_sum fun n hn => ?_)))
        · grw [norm_mul, hkey b hab, show ‖wt s (b + 1)‖ ≤ L / (b + 1) by simpa using norm_wt_le s hs (b + 1)]
          field_simp
          nlinarith
        · rw [Finset.mem_Ioc] at hn
          grw [norm_mul, hkey n hn.1, norm_wt_sub_le s hs (by omega)]
          field_simp
          simp only [L]
          gcongr
          exact_mod_cast hn.2
    _ ≤ E * L + E * (1 + ‖s‖ * L) * (1 + L) := by
        grw [← Finset.mul_sum, sum_Ioc_inv_le a b]
        simp only [L]; gcongr; exacts [mod_cast hab.pos, by linarith]
    _ = _ := by ring

/-! ### The lcm sum -/

/-- `Σ_{j ≤ Y} j^{-2/3} ≤ 3 Y^{1/3}`, by comparison with the integral. -/
lemma sum_rpow_neg_two_thirds_le (Y : ℕ) :
    ∑ j ∈ Finset.Ioc 0 Y, (j : ℝ) ^ (-((2 : ℝ) / 3)) ≤ 3 * (Y : ℝ) ^ ((1 : ℝ) / 3) := by
  have := AntitoneOn.sum_le_integral_of_integrableOn (x₀ := 0) (a := Y)
    (f := fun x : ℝ => x ^ (-((2 : ℝ) / 3)))
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num))
    ((integrableOn_Icc_iff_integrableOn_Ioc (by simp)).2 (by
      simpa [intervalIntegrable_iff_integrableOn_Ioc_of_le] using
        intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := -((2 : ℝ) / 3)) (by norm_num)))
  simp only [zero_add] at this
  rw [integral_rpow (by norm_num), Finset.range_eq_Ico, Finset.sum_Ico_add'
    (fun j : ℕ => (j : ℝ) ^ (-((2 : ℝ) / 3))), Finset.Ico_add_one_add_one_eq_Ioc] at this
  norm_num at this
  linarith

/-- `[d, e]^{-2/3} = (d, e)^{2/3} d^{-2/3} e^{-2/3}`. -/
lemma lcm_rpow_eq {d e : ℕ} (hd : 0 < d) :
    ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) =
      ((Nat.gcd d e : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
        ((d : ℝ) ^ (-((2 : ℝ) / 3)) * (e : ℝ) ^ (-((2 : ℝ) / 3))) := by
  have hg : (0 : ℝ) < (Nat.gcd d e : ℕ) := mod_cast Nat.gcd_pos_of_pos_left e hd
  rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul,
    ← Nat.gcd_mul_lcm d e, Nat.cast_mul, Real.mul_rpow hg.le (Nat.cast_nonneg _), ← mul_assoc,
    ← Real.rpow_add hg]
  norm_num

/-- `Σ_{d ≤ K, g ∣ d} d^{-2/3} ≤ 3 K^{1/3} / g`. -/
lemma sum_dvd_rpow_le (K : ℕ) {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ Finset.Ioc 0 K, (if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0) ≤
      3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ := by
  have hg0 : (0 : ℝ) < g := mod_cast hg
  rw [← Finset.sum_filter, sum_filter_dvd_Ioc _ hg, Nat.zero_div]
  simp only [Nat.cast_mul, Real.mul_rpow hg0.le (Nat.cast_nonneg _), ← Finset.mul_sum]
  calc _ ≤ (g : ℝ) ^ (-((2 : ℝ) / 3)) * (3 * ((K : ℝ) / g) ^ ((1 : ℝ) / 3)) := by
        gcongr
        exact (sum_rpow_neg_two_thirds_le _).trans (by gcongr; exact Nat.cast_div_le)
    _ = _ := by
        rw [Real.div_rpow (Nat.cast_nonneg _) hg0.le, ← show (g : ℝ) ^ (-((2 : ℝ) / 3)) /
          (g : ℝ) ^ ((1 : ℝ) / 3) = (g : ℝ)⁻¹ by rw [← Real.rpow_sub hg0]; norm_num [Real.rpow_neg_one]]
        ring

/-- `Σ_{d, e ≤ K} [d, e]^{-2/3} ≤ 9 K^{2/3} (1 + log K)`. -/
lemma lcm_sum_le (K : ℕ) :
    ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤
      9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log K) := by
  set F : ℕ → ℕ → ℝ := fun g d => if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0
  have hF0 : ∀ g d, 0 ≤ F g d := fun g d => by positivity
  calc _ ≤ ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K,
        (g : ℝ) ^ ((2 : ℝ) / 3) * (F g d * F g e) := by
        gcongr with d hd e he
        rw [Finset.mem_Ioc] at hd he
        refine (Finset.single_le_sum (fun g _ => by have := hF0 g d; have := hF0 g e; positivity)
          (Finset.mem_Ioc.2
            ⟨Nat.gcd_pos_of_pos_left e hd.1, (Nat.gcd_le_left e hd.1).trans hd.2⟩)).trans_eq' ?_
        simp [F, lcm_rpow_eq hd.1, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ = ∑ g ∈ Finset.Ioc 0 K, (g : ℝ) ^ ((2 : ℝ) / 3) *
          ((∑ d ∈ Finset.Ioc 0 K, F g d) * (∑ e ∈ Finset.Ioc 0 K, F g e)) := by
        simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ ≤ ∑ g ∈ Finset.Ioc 0 K, (g : ℝ) * (3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹) ^ 2 := by
        gcongr with g hg
        · exact Real.rpow_le_self_of_one_le (mod_cast (Finset.mem_Ioc.1 hg).1) (by norm_num)
        · rw [sq]
          exact mul_self_le_mul_self (Finset.sum_nonneg fun d _ => hF0 g d)
            (sum_dvd_rpow_le K (Finset.mem_Ioc.1 hg).1)
    _ = 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * ∑ g ∈ Finset.Ioc 0 K, 1 / (g : ℝ) := by
        rw [Finset.mul_sum]
        rw [← show ((K : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (K : ℝ) ^ ((2 : ℝ) / 3) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num]
        grind
    _ ≤ _ := by
        gcongr
        exact sum_Ioc_inv_le 0 K

/-! ### Opening the square -/

/-- `Σ_{d ∣ n} ψ_d = Σ_{d ≤ ⌊V⌋} [d ∣ n] ψ_d` for `n ≠ 0`. -/
lemma sum_divisors_grahamWeight (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, grahamWeight V d =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, (if d ∣ n then grahamWeight V d else 0) := by
  rw [← Finset.sum_filter]
  refine (Finset.sum_subset (fun d hd => ?_) fun d hd hnot => ?_).symm
  · grind
  · simp only [Finset.mem_filter, Finset.mem_Ioc, not_and, Nat.dvd_of_mem_divisors hd] at hnot
    simp [grahamWeight, Nat.lt_of_floor_lt (not_le.1 fun h => hnot ⟨Nat.pos_of_mem_divisors hd, h⟩
      trivial)]

/-- Opening the square: if each sum over multiples of `l` is `≤ X l^{-2/3}`, then the
`ν_V`-weighted sum is `≤ 9 X ⌊V⌋^{2/3} (1 + log ⌊V⌋)`. -/
lemma norm_sum_sieveNu_le (V : ℝ) (a b : ℕ) (F : ℕ → ℂ) {X : ℝ}
    (h : ∀ l, 0 < l → ‖∑ n ∈ Finset.Ioc a b, if l ∣ n then F n else 0‖ ≤
      X * (l : ℝ) ^ (-((2 : ℝ) / 3))) :
    ‖∑ n ∈ Finset.Ioc a b, (sieveNu V n : ℂ) * F n‖ ≤
      X * (9 * (⌊V⌋₊ : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log ⌊V⌋₊)) := by
  have hX : 0 ≤ X := by simpa using (norm_nonneg _).trans (h 1 one_pos)
  rw [Finset.sum_congr rfl fun n hn => by
    rw [sieveNu, sum_divisors_grahamWeight V (by grind), sq, Finset.sum_mul_sum]]
  simp only [ite_zero_mul_ite_zero, ← Nat.lcm_dvd_iff, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum fun d hd => ?_).trans
    ((Finset.mul_sum ..).symm.trans_le (mul_le_mul_of_nonneg_left (lcm_sum_le _) hX)))
  rw [Finset.sum_comm, Finset.mul_sum]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun e he => ?_)
  simp only [↓apply_ite Complex.ofReal, Complex.ofReal_zero, ite_zero_mul, ← mul_ite_zero,
    ← Finset.mul_sum, norm_mul, Complex.norm_real]
  grw [Real.norm_eq_abs, abs_grahamWeight_le_one V d, Real.norm_eq_abs, abs_grahamWeight_le_one V e, one_mul, one_mul]
  simp_all

/-! ### Assembly -/

theorem sieve_offdiag (hBur : BurgessBound) {ε' tmax : ℝ} (hε' : 0 < ε') :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, 1 / 3 + 2 * ε' < t → t ≤ t' → t' ≤ tmax → 0 ≤ β → β ≤ 1 →
        |τ| ≤ Real.log q →
        ‖∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu ((q : ℝ) ^ ((t - 1 / 3) / 2 - ε')) n : ℂ) * ψ n * (Real.log n : ℂ) *
              (n : ℂ) ^ (-((1 + β : ℝ) + (τ : ℂ) * I))‖ ≤ C * (q : ℝ) ^ (-κ) := by
  obtain ⟨CB, hCB⟩ := hBur (ε' / 3) (by positivity)
  set c := max 1 tmax
  set M := 1 + 24 / ε'
  refine ⟨max CB 0 * (63 * (2 * c * M) ^ 4), ε' / 6, by positivity, by positivity, 2,
    fun q hq ψ hψ t t' β τ ht htt' ht'max hβ0 hβ1 hτ => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by norm_cast; omega
  have hq0 : (0 : ℝ) < q := by positivity
  have : NeZero q := ⟨by omega⟩
  have hc : 1 ≤ c := le_max_left ..
  have hct : tmax ≤ c := le_max_right ..
  set W := 2 * c * M * (q : ℝ) ^ (ε' / 24)
  have hlog : ∀ x : ℝ, 0 < x → x ≤ 2 * (q : ℝ) ^ c → 1 + Real.log x ≤ W := fun x hx hxq => by
    have h1 := Real.log_le_log hx hxq
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_rpow hq0] at h1
    have h2 : Real.log q ≤ 24 / ε' * (q : ℝ) ^ (ε' / 24) :=
      (Real.log_le_rpow_div hq0.le (show 0 < ε' / 24 by positivity)).trans_eq (by field_simp)
    have h3 := Real.one_le_rpow hq1 (show 0 ≤ ε' / 24 by positivity)
    have := Real.log_two_lt_d9
    nlinarith [Real.log_nonneg hq1]
  set V := (q : ℝ) ^ ((t - 1 / 3) / 2 - ε')
  have hV1 : 1 ≤ V := Real.one_le_rpow hq1 (by linarith)
  set s : ℂ := ((1 + β : ℝ) : ℂ) + (τ : ℂ) * I
  have hA := Nat.ceil_pos.2 (by positivity : (0 : ℝ) < (q : ℝ) ^ t)
  have hB := Nat.ceil_pos.2 (by positivity : (0 : ℝ) < (q : ℝ) ^ t')
  rw [show Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊ =
    Finset.Ioc (⌈(q : ℝ) ^ t⌉₊ - 1) (⌈(q : ℝ) ^ t'⌉₊ - 1) by grind]
  simp_rw [show ∀ n : ℕ, (sieveNu V n : ℂ) * ψ n * (Real.log n : ℂ) * (n : ℂ) ^ (-s) =
    (sieveNu V n : ℂ) * (ψ n * wt s n) from fun n => by grind [wt]]
  refine (norm_sum_sieveNu_le V _ _ _ fun l hl => norm_T_le ψ
    (K := max CB 0 * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3)) (by positivity)
    (char_bound_all ψ hψ fun N H _ hH1 hHq => (hCB q ψ hψ N H hH1 hHq).trans
      (by gcongr; exact le_max_left ..)) s (by simp [s]; linarith) hl ..).trans ?_
  simp only [Nat.cast_sub hA, Nat.cast_sub hB, Nat.cast_one, sub_add_cancel]
  have hL := hlog _ (by positivity) (show (⌈(q : ℝ) ^ t'⌉₊ : ℝ) ≤ 2 * (q : ℝ) ^ c by
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ t'),
      Real.one_le_rpow hq1 (by linarith : 0 ≤ t'),
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : t' ≤ c)])
  have hs : ‖s‖ ≤ 2 * W := by
    have := hlog q hq0 (by linarith [Real.self_le_rpow_of_one_le hq1 hc])
    refine (norm_add_le ..).trans ?_
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β)]
    grind
  calc _ ≤ max CB 0 * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * ((q : ℝ) ^ t) ^ (-((1 : ℝ) / 3)) *
        (7 * W ^ 3) * (9 * V ^ ((2 : ℝ) / 3) * W) := by
        gcongr _ * ?_ * ?_ * (_ * ?_ * ?_)
        · exact Real.rpow_le_rpow_of_nonpos (by positivity) (Nat.le_ceil _) (by norm_num)
        · have := Real.log_natCast_nonneg ⌈(q : ℝ) ^ t'⌉₊
          nlinarith [mul_le_mul (add_le_add_left (mul_le_mul hs (by linarith :
            Real.log ⌈(q : ℝ) ^ t'⌉₊ ≤ W) this (by linarith)) 1) hL (by linarith) (by nlinarith),
            mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith : 1 ≤ W) : 1 ≤ W ^ 2)
              (by positivity)]
        · gcongr
          grind [Nat.floor_le]
        · exact hlog _ (mod_cast Nat.floor_pos.2 hV1) ((Nat.floor_le (by positivity)).trans
            (by linarith [Real.rpow_le_rpow_of_exponent_le hq1 (show (t - 1 / 3) / 2 - ε' ≤ c by
              linarith)]))
    _ = _ := by
        rw [show (q : ℝ) ^ (-(ε' / 6)) = (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) *
          ((q : ℝ) ^ t) ^ (-((1 : ℝ) / 3)) * V ^ ((2 : ℝ) / 3) * ((q : ℝ) ^ (ε' / 24)) ^ 4 by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le,
            ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0, ← Real.rpow_add hq0,
            ← Real.rpow_add hq0]; ring_nf]
        ring

end GradedNear
