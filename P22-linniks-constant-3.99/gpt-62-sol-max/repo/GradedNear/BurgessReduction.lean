module

public import GradedNear.Basic

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

open Finset Filter
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GradedNear

/-! ## The divisor bound -/

/-- The divisor bound `τ(n) ≪_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (((tendsto_rpow_atTop hε).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
  let b := (2 : ℝ) ^ ε
  let M := max 1 (1 / (b - 1))
  let g (p : ℕ) := if p < K then M else 1
  have hM : 1 ≤ M := le_max_left _ _
  have hb := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε
  have hMb : 1 ≤ M * (b - 1) := (div_le_iff₀ (sub_pos.mpr hb)).mp (le_max_right _ _)
  have hp {p : ℕ} (hp : p.Prime) (a : ℕ) : (a : ℝ) + 1 ≤ g p * ((p : ℝ) ^ ε) ^ a := by
    let x := (p : ℝ) ^ ε
    have hbx : b ≤ x := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp.two_le) hε.le
    have hg : 1 ≤ g p := by unfold g; split <;> grind
    have hgx : 1 ≤ g p * (x - 1) := by
      unfold g
      split_ifs with h
      · exact hMb.trans (by gcongr)
      · have hx : 2 ≤ x := hK p (not_lt.mp h)
        linarith
    calc
      _ ≤ g p * (1 + a * (x - 1)) := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (sub_nonneg.mpr hgx)]
      _ ≤ _ := by gcongr; exact one_add_mul_sub_le_pow (by linarith) a
  refine ⟨M ^ K, by positivity, fun n hn => ?_⟩
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    exact prod_congr rfl fun p _ => (Real.rpow_pow_comm (by positivity) _ _).symm
  have hgK : ∏ p ∈ n.primeFactors, g p ≤ M ^ K := by
    simp only [g, prod_ite, prod_const_one, mul_one, prod_const]
    apply pow_le_pow_right₀ hM
    simpa using card_le_card (t := range K) (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
  rw [Nat.card_divisors hn, Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (g p * ((p : ℝ) ^ ε) ^ n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) fun p hm => by
        push_cast
        exact hp (Nat.prime_of_mem_primeFactors hm) _
    _ = (∏ p ∈ n.primeFactors, g p) * (n : ℝ) ^ ε := by rw [prod_mul_distrib, hn']
    _ ≤ _ := by gcongr

/-! ## Complete periods -/

/-- A non-principal character sums to zero over `q` consecutive integers. -/
private lemma sum_Ioc_period_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a : ℕ) : ∑ n ∈ Ioc a (a + q), χ n = 0 := by
  have hfin (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    let : CommRing (Fin q) := Fin.instCommRing q
    simpa only [Fin.cast_val_eq_self] using map_natCast (ZMod.finEquiv q) i.val
  rw [sum_Ioc_eq_range, Nat.add_sub_cancel_left, ← MulChar.sum_eq_zero_of_ne_one hχ,
    ← Equiv.sum_comp (Equiv.addRight ((a + 1 : ℕ) : ZMod q)) (fun z => χ z),
    ← (ZMod.finEquiv q).toEquiv.sum_comp,
    ← Fin.sum_univ_eq_sum_range (fun k => χ ((a + 1 + k : ℕ) : ZMod q))]
  simp [hfin, Nat.cast_add, add_assoc, add_left_comm, add_comm]

/-- The Burgess bound on short intervals starting at a positive integer bounds every interval:
remove the complete periods and shift the remainder by the modulus. -/
lemma char_sum_bound {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {K : ℝ} (h : ∀ N H : ℕ, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Ioc N (N + H), ψ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3)) :
    0 ≤ K ∧ ∀ a b : ℕ, ‖∑ n ∈ Ioc a b, ψ n‖ ≤ K * ((b - a : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (h 1 1 le_rfl le_rfl (NeZero.pos q))
  refine ⟨hK, fun a b => ?_⟩
  by_cases hab : b ≤ a
  · simp [Ioc_eq_empty (not_lt.mpr hab)]; positivity
  have hq := NeZero.pos q
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hab)
  rw [Nat.add_sub_cancel_left]
  clear hab
  induction l using Nat.strong_induction_on with
  | h l ih =>
    obtain rfl | hl := l.eq_zero_or_pos
    · simp
    by_cases hlq : l ≤ q
    · simpa only [sum_Ioc_eq_range, Nat.add_sub_cancel_left, Nat.cast_add, ZMod.natCast_self, add_zero] using h (a + q) l (by omega) hl hlq
    · have hc := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a (l - q))
        (Nat.le_add_right (a + (l - q)) q)
      rw [sum_Ioc_period_eq_zero ψ hψ, add_zero, add_assoc, Nat.sub_add_cancel (by omega : q ≤ l)] at hc
      grw [← hc, ih (l - q) (by omega)]
      gcongr; omega

/-! ## Reduction to the primitive character -/

/-- Möbius inversion over the divisors of the level:
`Σ_{n ∈ s} χ(n) = Σ_{d ∣ q} μ(d) Σ_{n ∈ s, d ∣ n} χ*(n)`. -/
private lemma sum_eq_sum_divisors {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) :
    ∑ n ∈ s, χ n =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ n ∈ s.filter (d ∣ ·), χ.primitiveCharacter n := by
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter]
  have hfilt : q.divisors.filter (· ∣ n) = (Nat.gcd n q).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, Nat.gcd_eq_zero_iff, hq, and_comm]
  have hm := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd n q))
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] at hm
  rw [hfilt, ← Finset.sum_mul, hm]
  simp only [← Nat.coprime_iff_gcd_eq_one, ite_mul]
  split_ifs with h
  · simpa using (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)).symm
  · simpa using χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])

/-- Substitution `n = d * m` in a character sum over multiples of `d`. -/
lemma sum_char_dvd {q : ℕ} (ψ : DirichletCharacter ℂ q) {d : ℕ} (hd : 0 < d) (a b : ℕ) :
    ∑ n ∈ (Ioc a b).filter (d ∣ ·), ψ n = ψ d * ∑ m ∈ Ioc (a / d) (b / d), ψ m := by
  rw [mul_sum]
  simp only [← map_mul, ← Nat.cast_mul]
  symm
  refine sum_nbij (fun m => d * m) ?_ (fun _ _ _ _ => Nat.eq_of_mul_eq_mul_left hd) ?_ (fun _ _ => rfl)
  · simp [mem_filter, mem_Ioc, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, mul_comm _ d]
  · intro k hk
    obtain ⟨hk, m, rfl⟩ : k ∈ Ioc a b ∧ d ∣ k := by simpa using hk
    exact ⟨m, by simpa [mem_Ioc, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, mul_comm _ d] using hk, rfl⟩

/-- **Burgess's bound for all non-principal characters** (`BurgessBound`, with `N ≥ 0`) follows
from the printed primitive statement [HB, Lemma 2.1, k = 3] (`BurgessPrimitive`). -/
theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  obtain ⟨C, hC⟩ := hB (ε / 2) (by positivity)
  obtain ⟨C₂, -, hτ⟩ := card_divisors_le_rpow (show 0 < ε / 2 by positivity)
  refine ⟨C * C₂, fun q χ hχ N H hH hHq => ?_⟩
  have hq : 0 < q := hH.trans hHq
  let : NeZero q := ⟨hq.ne'⟩
  let ψ := χ.primitiveCharacter
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : ψ ≠ 1 := fun e => hχ (by simp [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from e])
  let E := (1 : ℝ) / 9 + ε / 2
  obtain ⟨hK, hchar⟩ := char_sum_bound ψ hψ fun n l hn hl hlq =>
    hC _ (by exact NeZero.pos χ.conductor) ψ χ.primitiveCharacter_isPrimitive n l hn hl hlq
  have hC₀ := nonneg_of_mul_nonneg_left hK (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos χ.conductor)) E)
  let B := C * (q : ℝ) ^ E * (H : ℝ) ^ ((2 : ℝ) / 3)
  have hB : 0 ≤ B := by positivity
  rw [sum_eq_sum_divisors hq.ne']
  refine (norm_sum_le _ _).trans ((?_: _ ≤ (q.divisors.card : ℝ) * B).trans ?_)
  · rw [← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro d hd
    have hd' := Nat.pos_of_mem_divisors hd
    rw [sum_char_dvd _ hd', norm_mul, norm_mul]
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    grw [hμ, ψ.norm_le_one]
    simp only [one_mul]
    refine (hchar _ _).trans ?_
    dsimp [B, E]
    gcongr
    · exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    · exact_mod_cast (show (N + H) / d - N / d ≤ H by
        have h := Nat.div_le_div_right (c := d) (show N + H ≤ N + H * d by nlinarith)
        rw [Nat.add_mul_div_right N H hd'] at h
        omega)
  · refine (mul_le_mul_of_nonneg_right (hτ q hq.ne') hB).trans_eq ?_
    dsimp [B, E]
    rw [show (1 / 9 + ε) = ε / 2 + (1 / 9 + ε / 2) by ring,
      Real.rpow_add (by positivity : (0 : ℝ) < q) (ε / 2)]
    ring

end GradedNear
