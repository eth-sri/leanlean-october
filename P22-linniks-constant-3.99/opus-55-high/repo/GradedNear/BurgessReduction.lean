module

public import GradedNear.Defs

/-!
# Burgess's bound: from the printed primitive statement to all non-principal characters

`GradedNear.BurgessBound` (in `GradedNear/Defs.lean`) is Burgess's bound with `r = 3` for every
non-principal Dirichlet character and every `N ≥ 0`. The printed source, [HB, Lemma 2.1, p. 7],
states it for primitive characters and `N ≥ 1` only. `BurgessPrimitive` (in `GradedNear/Defs.lean`)
states the printed form, and this file proves `BurgessPrimitive → BurgessBound`
(`burgessBound_of_primitive`), so that the hypothesis is a statement matching the print.

The reduction is the standard one. If `χ` mod `q` is induced by the primitive `χ*` mod `q*`, then
`χ(n) = χ*(n)` for `(n, q) = 1` and `χ(n) = 0` otherwise, and Möbius inversion gives
`Σ_{N < n ≤ N+H} χ(n) = Σ_{d ∣ q} μ(d) χ*(d) Σ_{⌊N/d⌋ < m ≤ ⌊(N+H)/d⌋} χ*(m)`.
Each inner sum has length at most `H`; complete periods of `χ*` are removed (they vanish since
`χ* ≠ 1`) and the interval is shifted by `q*`, which lands in the printed range `N ≥ 1`,
`1 ≤ H ≤ q*`. Finally `q* ≤ q` and the number of divisors costs `τ(q) ≪_ε q^ε`
(`card_divisors_le_rpow`, proved here).

References: [HB] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least
prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338 (Lemma 2.1 is on
p. 7 of the preprint `literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf`).
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GradedNear

/-! ## The divisor bound -/

/-- One prime-power factor of the divisor bound: `a + 1 ≤ M_p (p^ε)^a`. -/
private lemma divisor_factor_le {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : (2 : ℝ) ^ (1 / ε) ≤ K)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a : ℝ) + 1 ≤
      (if p < K then max 1 (1 / ((2 : ℝ) ^ ε - 1)) else 1) * ((p : ℝ) ^ ε) ^ a := by
  have hb1 : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hbp : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
    Real.rpow_le_rpow (by norm_num) (mod_cast hp.two_le) hε.le
  have key : ∀ M : ℝ, 1 ≤ M → 1 ≤ M * ((p : ℝ) ^ ε - 1) →
      (a : ℝ) + 1 ≤ M * ((p : ℝ) ^ ε) ^ a := fun M h1 h2 => by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) ^ ε - 1 by linarith) a
    rw [add_sub_cancel] at this
    nlinarith
  split_ifs with hpK
  · exact key _ (le_max_left ..) ((div_mul_cancel₀ (1 : ℝ) (by linarith)).symm.le.trans
      (mul_le_mul (le_max_right ..) (by linarith) (by linarith) (by positivity)))
  · refine key 1 le_rfl ?_
    calc (1 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε - 1 := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne']; norm_num
      _ ≤ _ := by
        rw [one_mul]; gcongr; exact hK.trans (mod_cast not_lt.1 hpK)

/-- The divisor bound `τ(n) ≪_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set K : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  set M : ℝ := max 1 (1 / ((2 : ℝ) ^ ε - 1))
  have hM1 : 1 ≤ M := le_max_left ..
  refine ⟨M ^ K, by positivity, fun n hn => ?_⟩
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    grind [Finset.prod_congr, Real.rpow_pow_comm, Nat.cast_nonneg]
  rw [Nat.card_divisors hn, hn']
  push_cast
  calc _ ≤ ∏ p ∈ n.primeFactors,
        ((if p < K then M else 1) * ((p : ℝ) ^ ε) ^ (n.factorization p)) :=
        prod_le_prod₀ (fun p _ => by positivity) fun p hp =>
          divisor_factor_le hε (Nat.le_ceil _) (Nat.prime_of_mem_primeFactors hp) _
    _ ≤ _ := by
      rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one, prod_const]
      gcongr
      exact (card_le_card fun p hp => mem_range.2 (mem_filter.1 hp).2).trans (card_range K).le

/-! ## Complete periods -/

/-- A sum over the multiples of `l` in `(a, b]`, after the substitution `k = l m`. -/
lemma sum_filter_dvd_Ioc {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 0 < l)
    (a b : ℕ) : ∑ k ∈ (Ioc a b).filter (l ∣ ·), f k = ∑ m ∈ Ioc (a / l) (b / l), f (l * m) := by
  rw [← sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hl h)]
  congr 1; ext n
  simp [mem_filter, mem_Ioc, mem_image, Nat.div_lt_iff_lt_mul hl, Nat.le_div_iff_mul_le hl]
  constructor
  · rintro ⟨h, m, rfl⟩; exact ⟨m, by grind, rfl⟩
  · grind [dvd_mul_right]

/-- A non-principal character sums to zero over any `q` consecutive integers. -/
lemma sum_Ioc_period_eq_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (a : ℕ) : ∑ n ∈ Ioc a (a + q), ψ n = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hψ]
  refine sum_nbij' (fun k : ℕ => (k : ZMod q)) (fun x => a + 1 + (x - (a + 1 : ℕ)).val)
    (by simp) (fun x _ => by grind) (fun k hk => ?_) (fun x _ => by simp) (by simp)
  rw [mem_Ioc] at hk
  rw [← Nat.cast_sub (by grind), ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Burgess-type bounds on intervals extend to all `N ≥ 0` and all lengths. -/
lemma char_bound_all {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {K : ℝ}
    (h : ∀ N H : ℕ, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Ioc N (N + H), ψ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3)) (N H : ℕ) :
    ‖∑ n ∈ Ioc N (N + H), ψ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  have := NeZero.pos q
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (h 1 1 le_rfl le_rfl NeZero.one_le)
  induction H using Nat.strong_induction_on generalizing N with
  | _ H ih =>
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    by_cases hHq : H ≤ q
    · have e1 := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right N q)
        (Nat.le_add_right (N + q) H)
      have e2 := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right N H)
        (Nat.le_add_right (N + H) q)
      rw [sum_Ioc_period_eq_zero ψ hψ, zero_add] at e1
      rw [sum_Ioc_period_eq_zero ψ hψ, add_zero, add_right_comm, ← e1] at e2
      exact e2 ▸ h _ H (by omega) hH hHq
    rw [← sum_Ioc_consecutive _ (by omega : N ≤ N + q) (by omega : N + q ≤ N + H),
      sum_Ioc_period_eq_zero ψ hψ, zero_add, show N + H = N + q + (H - q) by omega]
    exact (ih (H - q) (by omega) (N + q)).trans (by gcongr; exact_mod_cast Nat.sub_le H q)

/-! ## Reduction to the primitive character -/

/-- `Σ_{d ∣ m} μ(d) = [m = 1]`. -/
private lemma sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (μ d : ℂ) = if m = 1 then 1 else 0 := by
  have := congr($(ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ)) m)
  rw [ArithmeticFunction.coe_mul_zeta_apply] at this
  simpa [ArithmeticFunction.one_apply] using this

/-- Möbius inversion over the divisors of the level:
`Σ_{n ∈ s} χ(n) = Σ_{d ∣ q} μ(d) Σ_{n ∈ s, d ∣ n} χ*(n)`. -/
private lemma sum_eq_sum_divisors {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) :
    ∑ n ∈ s, χ n =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ n ∈ s.filter (d ∣ ·), χ.primitiveCharacter n := by
  have key : ∀ n : ℕ, χ n =
      ∑ d ∈ q.divisors, if d ∣ n then (μ d : ℂ) * χ.primitiveCharacter n else 0 := by
    intro n
    rw [← Finset.sum_filter, show q.divisors.filter (· ∣ n) = (Nat.gcd n q).divisors by
      ext d; simp [Nat.dvd_gcd_iff]; tauto, ← Finset.sum_mul, sum_moebius_divisors]
    by_cases h : n.Coprime q
    · simpa [h.gcd_eq_one] using (χ.primitiveCharacter_apply_of_isCoprime
        (Nat.isCoprime_iff_coprime.mpr h)).symm
    · rw [ite_eq_right (fun h' => h (Nat.coprime_iff_gcd_eq_one.mpr h')), zero_mul]
      exact χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])
  rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_comm]
  simp [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]

/-- **Burgess's bound for all non-principal characters** (`BurgessBound`, with `N ≥ 0`) follows
from the printed primitive statement [HB, Lemma 2.1, k = 3] (`BurgessPrimitive`). -/
theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hB (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂, hτ⟩ := card_divisors_le_rpow (show 0 < ε / 2 by positivity)
  refine ⟨max C₁ 0 * C₂, fun q χ hχ N H hH hHq => ?_⟩
  have : NeZero q := ⟨by omega⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : χ.primitiveCharacter ≠ 1 := fun h =>
    hχ (by rw [← χ.changeLevel_primitiveCharacter, h, map_one])
  have hcond : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  rw [sum_eq_sum_divisors (by omega)]
  refine (norm_sum_le ..).trans ((sum_le_sum (g := fun _ => max C₁ 0 *
    (q : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) * (H : ℝ) ^ ((2 : ℝ) / 3)) fun d hd => ?_).trans ?_)
  · have hd0 := Nat.pos_of_mem_divisors hd
    obtain ⟨L, hL⟩ : ∃ L, (N + H) / d = N / d + L :=
      ⟨_, (Nat.add_sub_cancel' (Nat.div_le_div_right (by omega))).symm⟩
    have hLH : L ≤ H := by
      have := Nat.div_le_div_right (c := d) (show N + H ≤ N + H * d by nlinarith)
      rw [Nat.add_mul_div_right N H hd0] at this
      omega
    rw [sum_filter_dvd_Ioc _ hd0, hL]
    simp only [Nat.cast_mul, map_mul, ← mul_sum, norm_mul]
    grw [χ.primitiveCharacter.norm_le_one, show ‖(μ d : ℂ)‖ ≤ 1 by simp; exact_mod_cast ArithmeticFunction.abs_moebius_le_one, one_mul, one_mul]
    refine (char_bound_all _ hψ1 (K := max C₁ 0 * (χ.conductor : ℝ) ^ ((1 : ℝ) / 9 + ε / 2)) (fun N H hN hH hHq => (hC₁ _ NeZero.one_le _
      χ.primitiveCharacter_isPrimitive N H hN hH hHq).trans ?_) ..).trans ?_
    · gcongr; exact le_max_left ..
    · gcongr
  · rw [sum_const, nsmul_eq_mul]
    calc _ ≤ (C₂ * (q : ℝ) ^ (ε / 2)) * _ := by gcongr; exact hτ q (by omega)
      _ = _ := by
        rw [show (1 : ℝ) / 9 + ε = ε / 2 + ((1 : ℝ) / 9 + ε / 2) by ring,
          Real.rpow_add (by norm_cast; omega : (0 : ℝ) < q) (ε / 2)]; ring

end GradedNear
