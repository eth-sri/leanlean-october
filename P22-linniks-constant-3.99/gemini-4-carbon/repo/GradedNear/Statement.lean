module

public import GradedNear.Cert.Sound

@[expose] public section

open Filter Topology MeasureTheory Finset Real DirichletCharacter Asymptotics
open Complex (I)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ComplexConjugate

noncomputable section

namespace GradedNear


private lemma sum_Ioc_dvd {M : Type*} [AddCommMonoid M] (f : ℕ → M) {d} (hd : 0 < d) (a b : ℕ) :
    ∑ n ∈ (Ioc a b).filter (d ∣ ·), f n = ∑ m ∈ Ioc (a / d) (b / d), f (d * m) := by
  rw [← sum_image fun _ _ _ _ => Nat.eq_of_mul_eq_mul_left hd]; congr; ext
  simp [Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, dvd_def, mul_comm d]; aesop

private lemma char_sum_dvd_le {q} (hq : 0 < q) (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {K} (hK : 0 ≤ K)
    (h : ∀ N H, 1 ≤ N → 1 ≤ H → H ≤ q → ‖∑ n ∈ Ioc N (N + H), ψ n‖ ≤ K * H ^ (2 / 3 : ℝ))
    {d} (hd : 0 < d) (a b : ℕ) :
    ‖∑ n ∈ (Ioc a b).filter (d ∣ ·), ψ n‖ ≤ K * (b / d - a / d : ℕ) ^ (2 / 3 : ℝ) := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [sum_Ioc_dvd _ hd]; simp only [Nat.cast_mul, map_mul, ← mul_sum, norm_mul]
  rcases le_or_gt (b / d) (a / d) with hab | hab
  · rw [Ioc_eq_empty_of_le hab]; simp; positivity
  grw [ψ.norm_le_one _, one_mul]
  set H := b / d - a / d
  rw [show b / d = a / d + H by omega]
  generalize a / d = N; clear_value H; clear hab
  have hper a : ∑ n ∈ Ioc a (a + q), ψ n = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
      show a + (m + 1) + 1 - (a + 1) = m + 1 by omega,
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ => ψ ((a + 1 + i : ℕ) : ZMod (m + 1))) (m + 1)]
    simp only [Nat.cast_add]
    change ∑ x : ZMod (m + 1), ψ (a + 1 + (x.val : ℕ)) = 0
    simpa [add_assoc, ZMod.natCast_zmod_val] using
      (Equiv.sum_comp (Equiv.addLeft (↑a + 1 : ZMod (m + 1))) (ψ ·)).trans
        (MulChar.sum_eq_zero_of_ne_one hψ)
  induction H using Nat.strong_induction_on generalizing N with | _ H ih => ?_
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  by_cases hHq : H ≤ q
  · have e1 := sum_Ioc_consecutive (ψ ·) (Nat.le_add_right N H) (Nat.le_add_right _ q)
    have e2 := sum_Ioc_consecutive (ψ ·) (Nat.le_add_right N q) (Nat.le_add_right _ H)
    rw [hper, add_zero, add_right_comm] at e1; rw [hper, zero_add] at e2
    rw [e1.trans e2.symm]; exact h (N + q) H (by omega) hH hHq
  · rw [← sum_Ioc_consecutive (ψ ·) (Nat.le_add_right N q) (by omega), hper, zero_add,
      show N + H = N + q + (H - q) by omega]
    exact (ih (H - q) (by omega) (N + q)).trans (by gcongr; exact_mod_cast Nat.sub_le H q)

theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  set ε2 := ε / 2
  have hε2 : 0 < ε2 := half_pos hε
  obtain ⟨C₁, hC₁⟩ := hB ε2 hε2
  set K := ⌈(2 : ℝ) ^ (1 / ε2)⌉₊
  set M := max 1 (4 / ε2)
  have hτ (n : ℕ) (hn : n ≠ 0) : (#n.divisors : ℝ) ≤ M ^ K * (n : ℝ) ^ ε2 := by
    rw [Nat.card_divisors hn, show (n : ℝ) ^ ε2 = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε2 by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
      push_cast; exact (finsetProd_rpow _ _ (fun _ _ => by positivity) _).symm]
    push_cast
    refine (prod_le_prod₀ (g := fun p => (if p < K then M else 1) * ((p : ℝ) ^ n.factorization p) ^ ε2)
      (fun _ _ => by positivity) fun p hp => ?_).trans
      (by rw [prod_mul_distrib]; gcongr; rw [prod_ite, prod_const_one, mul_one, prod_const]
          exact pow_le_pow_right₀ (le_max_left _ _)
            ((card_le_card fun p hp => mem_range.2 (mem_filter.1 hp).2).trans_eq (card_range K)))
    set a := n.factorization p
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpK
    · have h1 : (a : ℝ) + 1 ≤ 4 * log ((p : ℝ) ^ a) := by
        rw [log_pow]; nlinarith [log_two_gt_d9, log_le_log two_pos hp2]
      grw [h1, log_le_rpow_div (by positivity) hε2]
      rw [div_eq_inv_mul, ← mul_assoc, ← div_eq_mul_inv]; gcongr; exact le_max_right 1 _
    · have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε2 := by
        simpa [← rpow_mul two_pos.le, inv_mul_cancel₀ hε2.ne'] using
          rpow_le_rpow (by positivity) ((Nat.le_ceil _).trans (show (K : ℝ) ≤ p by exact_mod_cast not_lt.1 hpK)) hε2.le
      grw [show (a : ℝ) + 1 ≤ 2 ^ a by exact_mod_cast Nat.lt_two_pow_self, h2]
      simp [rpow_pow_comm (by positivity : (0 : ℝ) ≤ p)]
  set C₁' := max C₁ 0
  refine ⟨C₁' * M ^ K, fun q χ hχ N H hH hHq => ?_⟩
  have hq1 : 1 ≤ q := hH.trans hHq
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have hc0 := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : χ.primitiveCharacter ≠ 1 := fun h =>
    hχ (by rw [← χ.changeLevel_primitiveCharacter, h, map_one])
  set B := C₁' * (q : ℝ) ^ ((1 : ℝ) / 9 + ε2) * (H : ℝ) ^ ((2 : ℝ) / 3)
  rw [show ∑ n ∈ Ioc N (N + H), χ n =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), χ.primitiveCharacter n by
    have key (n : ℕ) : χ n = ∑ d ∈ q.divisors, if d ∣ n then (μ d : ℂ) * χ.primitiveCharacter n else 0 := by
      rw [← sum_filter, show q.divisors.filter (· ∣ n) = (n.gcd q).divisors by
        ext; simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq0]; tauto, ← sum_mul, ← Int.cast_sum,
        show ∑ d ∈ (n.gcd q).divisors, μ d = if n.gcd q = 1 then 1 else 0 by
          simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using
            congrArg (fun f : ArithmeticFunction ℤ => f (n.gcd q)) ArithmeticFunction.moebius_mul_coe_zeta]
      by_cases hc : n.Coprime q
      · simp [Nat.coprime_iff_gcd_eq_one.1 hc]
        simpa using (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.2 hc)).symm
      · simp [mt Nat.coprime_iff_gcd_eq_one.2 hc, χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])]
    simp_rw [key]; rw [sum_comm]
    exact sum_congr rfl fun d _ => by rw [sum_filter, mul_sum]; simp [mul_ite]]
  grw [norm_sum_le, sum_le_sum (g := fun _ => B) fun d hd => (by
    have hd0 := Nat.pos_of_mem_divisors hd
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hcond : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq1 χ.conductor_dvd_level
    have hH' : ((N + H) / d - N / d : ℕ) ≤ (H : ℝ) := by
      have := Nat.div_le_div_right (c := d) (show N + H ≤ N + H * d by nlinarith)
      rw [Nat.add_mul_div_right N H hd0] at this; exact_mod_cast (by omega : (N + H) / d - N / d ≤ H)
    rw [norm_mul, Complex.norm_intCast]
    grw [hμ, one_mul, char_sum_dvd_le (K := C₁' * (χ.conductor : ℝ) ^ ((1 : ℝ) / 9 + ε2))
      hc0 _ hψ1 (by positivity)
      (fun n h hn hh hhq => (hC₁ _ hc0 _ χ.primitiveCharacter_isPrimitive n h hn hh hhq).trans
        (by gcongr; exact le_max_left _ _)) hd0 N (N + H)]
    dsimp [B]; gcongr), sum_const, nsmul_eq_mul, hτ q hq0]
  dsimp [B, ε2]
  rw [show (1 : ℝ) / 9 + ε = ε / 2 + ((1 : ℝ) / 9 + ε / 2) by ring, rpow_add (by exact_mod_cast hq1) (ε / 2)]
  exact le_of_eq (by ring)

private abbrev sieveNu V n := (∑ d ∈ Nat.divisors n, grahamWeight V d) ^ 2

private lemma lcm_sum_le (K : ℕ) :
    ∑ d ∈ Ioc 0 K, ∑ e ∈ Ioc 0 K, ((d.lcm e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤
      9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 + log K) := by
  have hsum23 (Y : ℕ) : ∑ j ∈ Ioc 0 Y, (j : ℝ) ^ (-((2 : ℝ) / 3)) ≤ 3 * (Y : ℝ) ^ ((1 : ℝ) / 3) := by
    induction Y with
    | zero => simp
    | succ Y ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le Y), Nat.cast_succ]
      set x := ((Y : ℝ) + 1) ^ ((1 : ℝ) / 3); set y := (Y : ℝ) ^ ((1 : ℝ) / 3)
      have hx0 : 0 < x := by positivity
      have hy0 : 0 ≤ y := by positivity
      have h1 : ((Y : ℝ) + 1) ^ (-((2 : ℝ) / 3)) = 1 / x ^ 2 := by
        dsimp [x]; rw [one_div, ← rpow_natCast, ← rpow_mul (by positivity), ← rpow_neg (by positivity)]; norm_num
      have h2 : x ^ 3 - y ^ 3 = 1 := by
        rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (by positivity), ← rpow_mul (Nat.cast_nonneg Y)]; norm_num
      rw [h1]; linarith [(div_le_iff₀ (sq_pos_of_pos hx0)).2 (by nlinarith [sq_nonneg (x - y)] : 1 ≤ 3 * (x - y) * x ^ 2)]
  let F g (d : ℕ) : ℝ := if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0
  have hF0 g d : 0 ≤ F g d := by dsimp [F]; split_ifs <;> positivity
  have hdvd g (hg : 0 < g) : ∑ d ∈ Ioc 0 K, F g d ≤ 3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ := by
    have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
    dsimp [F]; rw [← sum_filter, sum_Ioc_dvd _ hg, Nat.zero_div]
    simp only [Nat.cast_mul]
    rw [sum_congr rfl fun m _ => mul_rpow hg0.le (Nat.cast_nonneg m), ← mul_sum]
    grw [hsum23 _, Nat.cast_div_le]
    rw [div_rpow (Nat.cast_nonneg K) hg0.le, ← rpow_neg_one (g : ℝ),
      show (-1 : ℝ) = -((2 : ℝ) / 3) - 1 / 3 by norm_num, rpow_sub hg0]
    exact le_of_eq (by ring)
  let X (g d e : ℕ) := (g : ℝ) * (F g d * F g e)
  have hle d (hd : d ∈ Ioc 0 K) e (he : e ∈ Ioc 0 K) :
      ((d.lcm e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤ ∑ g ∈ Ioc 0 K, X g d e := by
    obtain ⟨hd0, hdK⟩ := mem_Ioc.1 hd; obtain ⟨he0, -⟩ := mem_Ioc.1 he
    have hg1 : (1 : ℝ) ≤ (d.gcd e : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left e hd0
    have hl : (0 : ℝ) < (d.lcm e : ℕ) := by exact_mod_cast Nat.lcm_pos hd0 he0
    refine (?_ : _ ≤ X (d.gcd e) d e).trans <| single_le_sum (f := fun g => X g d e)
      (fun g _ => mul_nonneg (by positivity) (mul_nonneg (hF0 g d) (hF0 g e)))
      (mem_Ioc.2 ⟨Nat.gcd_pos_of_pos_left e hd0, (Nat.gcd_le_left e hd0).trans hdK⟩)
    dsimp [X, F]; simp only [Nat.gcd_dvd_left, Nat.gcd_dvd_right, ↓reduceIte]
    rw [← mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg e),
      show (d : ℝ) * e = (d.gcd e : ℕ) * (d.lcm e : ℕ) by exact_mod_cast (Nat.gcd_mul_lcm d e).symm,
      mul_rpow (by linarith) hl.le, ← mul_assoc, ← rpow_one_add' (by linarith) (by norm_num)]
    exact le_mul_of_one_le_left (by positivity) (one_le_rpow hg1 (by norm_num))
  refine (sum_le_sum fun d hd => sum_le_sum fun e he => hle d hd e he).trans ?_
  rw [sum_congr rfl fun _ _ => sum_comm, sum_comm,
    sum_congr rfl fun g _ => show ∑ d ∈ Ioc 0 K, ∑ e ∈ Ioc 0 K, X g d e =
      (g : ℝ) * ((∑ d ∈ Ioc 0 K, F g d) * ∑ e ∈ Ioc 0 K, F g e) by
      dsimp [X]; rw [sum_congr rfl fun _ _ => (mul_sum _ _ _).symm, ← mul_sum, sum_mul_sum]]
  refine ((sum_le_sum (g := fun g : ℕ => 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 / (g : ℝ))) fun g hg => ?_).trans_eq
    (mul_sum _ _ _).symm).trans ?_
  · have hg1 := (mem_Ioc.1 hg).1
    refine (mul_le_mul_of_nonneg_left (mul_self_le_mul_self (sum_nonneg fun d _ => hF0 g d) (hdvd g hg1))
      (by positivity)).trans_eq ?_
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg1.ne'
    rw [show (2 : ℝ) / 3 = 1 / 3 + 1 / 3 by norm_num, rpow_add' (Nat.cast_nonneg K) (by norm_num)]
    field_simp; ring
  · gcongr
    exact (by rw [harmonic_eq_sum_Icc, show Ioc 0 K = Icc 1 K by ext; simp; omega]; push_cast; simp [one_div] :
      _ = (harmonic K : ℝ)).trans_le (harmonic_le_one_add_log K)

private lemma sieve_offdiag (hBur : BurgessBound) {ε' tmax : ℝ} (hε' : 0 < ε') :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, 1 / 3 + 2 * ε' < t → t ≤ t' → t' ≤ tmax → 0 ≤ β → β ≤ 1 → |τ| ≤ log q →
        ‖∑ n ∈ Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu ((q : ℝ) ^ ((t - 1 / 3) / 2 - ε')) n : ℂ) * ψ n * (log n : ℂ) *
              (n : ℂ) ^ (-((1 + β : ℝ) + (τ : ℂ) * I))‖ ≤ 1 := by
  obtain ⟨CB, hCB⟩ := hBur (ε' / 3) (by positivity)
  set C₀ := max CB 0
  set c₁ := max 1 tmax + 1
  have hc₁1 : 1 ≤ c₁ := by dsimp [c₁]; linarith [le_max_left 1 tmax]
  have hT0 : Tendsto (fun q : ℕ => 45 * C₀ * c₁ ^ 3 * (log q ^ (4 : ℝ) / (q : ℝ) ^ (ε' / 3)))
      atTop (𝓝 0) := by
    simpa using ((isLittleO_log_rpow_rpow_atTop 4 (by positivity : 0 < ε' / 3)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (45 * C₀ * c₁ ^ 3)
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop (⌈exp 1⌉₊ + 2)).and ((tendsto_order.1 hT0).2 1 one_pos)
  refine ⟨q₀, fun q hq ψ hψ t t' β τ ht htt' ht'max hβ0 hβ1 hτ => ?_⟩
  obtain ⟨hqe, hq1_lt⟩ := hq₀ q hq
  have hqpos : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hℓ1 : 1 ≤ log q := (le_log_iff_exp_le hq0).2
    ((Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈exp 1⌉₊ ≤ q)))
  set Kq := C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3)
  have hKq0 : 0 ≤ Kq := by positivity
  have hBurq {l} (hl : 0 < l) := char_sum_dvd_le hqpos ψ hψ hKq0
    (fun N H _ hH1 hHq => (hCB q ψ hψ N H hH1 hHq).trans (by dsimp [Kq]; gcongr; exact le_max_left _ _)) hl
  set s : ℂ := ((1 + β : ℝ) : ℂ) + τ * I
  have hs : 1 ≤ s.re := by dsimp [s]; simp; linarith
  have hsn : ‖s‖ ≤ 3 * log q :=
    (norm_add_le _ _).trans <| by
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        norm_eq_abs, norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + β)]; linarith
  set δ := (t - 1 / 3) / 2 - ε'
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  set V := (q : ℝ) ^ δ; set A := (q : ℝ) ^ t; set B := (q : ℝ) ^ t'
  have hV1 : 1 ≤ V := one_le_rpow hq1 hδ0.le
  have hA0 : 0 < A := rpow_pos_of_pos hq0 t
  have hB0 : 0 < B := rpow_pos_of_pos hq0 t'
  set a := ⌈A⌉₊ - 1; set b := ⌈B⌉₊ - 1
  have ha1 : (a : ℝ) + 1 = ⌈A⌉₊ := by
    dsimp [a]; rw [Nat.cast_sub (Nat.ceil_pos.2 hA0), Nat.cast_one, sub_add_cancel]
  have ha_ge : 1 ≤ a := Nat.le_sub_one_of_lt <| Nat.lt_ceil.2 <| by
    simpa using one_lt_rpow (show (1 : ℝ) < q by exact_mod_cast (by omega : 1 < q)) (show 0 < t by linarith)
  let f (t : ℝ) : ℂ := log t * Complex.exp (log t * (-s))
  have hgw (d : ℕ) : |grahamWeight V d| ≤ 1 := by
    unfold grahamWeight; rcases eq_or_ne d 0 with rfl | hd0 <;> split_ifs with h <;> try simp
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have h1 : 0 ≤ log (V / d) := log_nonneg ((le_div_iff₀ (by positivity)).2 (by linarith))
    rw [abs_div, abs_mul, abs_of_nonneg h1, abs_of_nonneg (log_nonneg hV1)]
    exact div_le_one_of_le₀
      ((mul_le_of_le_one_left h1 (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)).trans
        (log_le_log (by positivity) (div_le_self (by positivity) hd)))
      (log_nonneg hV1)
  rw [show Ico ⌈A⌉₊ ⌈B⌉₊ = Ioc a b by
      have := Nat.ceil_pos.2 hA0; have := Nat.ceil_pos.2 hB0
      ext n; simp only [mem_Ico, mem_Ioc, a, b]; omega,
    sum_congr rfl fun n hn => show _ = ∑ d ∈ Ioc 0 ⌊V⌋₊, ∑ e ∈ Ioc 0 ⌊V⌋₊,
        ↑(grahamWeight V d * grahamWeight V e) * (if d.lcm e ∣ n then ψ n * f n else 0) by
      have hdiv : ∑ d ∈ n.divisors, grahamWeight V d =
          ∑ d ∈ Ioc 0 ⌊V⌋₊, if d ∣ n then grahamWeight V d else 0 := by
        rw [← sum_filter]; symm
        refine sum_subset (fun d hd => Nat.mem_divisors.2 ⟨(mem_filter.1 hd).2, by have := (mem_Ioc.1 hn).1; omega⟩)
          fun d hd hnot => ?_
        unfold grahamWeight
        exact ite_eq_right fun hle => hnot (mem_filter.2
          ⟨mem_Ioc.2 ⟨Nat.pos_of_mem_divisors hd, Nat.le_floor hle⟩, Nat.dvd_of_mem_divisors hd⟩)
      have hn0 : (n : ℂ) ≠ 0 := by have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
      rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log,
        show (sieveNu V n : ℂ) * ψ n * log n * Complex.exp (log n * -s) = sieveNu V n * (ψ n * f n) by dsimp [f]; ring,
        sieveNu, hdiv, sq, sum_mul_sum, Complex.ofReal_sum, sum_mul]
      refine sum_congr rfl fun d _ => ?_
      rw [Complex.ofReal_sum, sum_mul]
      exact sum_congr rfl fun e _ => by
        by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff],
    sum_comm]
  simp_rw [sum_comm (s := Ioc a b), ← mul_sum]
  set L := log b
  have hL0 : 0 ≤ L := log_natCast_nonneg b
  set CT := Kq * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * ((2 + ‖s‖) * (1 + L) ^ 2)
  have hTle {l : ℕ} (hl : 0 < l) :
      ‖∑ n ∈ Ioc a b, (if l ∣ n then ψ n * f n else 0)‖ ≤ CT * (l : ℝ) ^ (-((2 : ℝ) / 3)) := by
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
    set E := Kq * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3))
    have hE0 : 0 ≤ E := by positivity
    rcases le_or_gt b a with hab | hab
    · rw [Ioc_eq_empty_of_le hab]; simp; positivity
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha_ge
    have hb0 : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hab
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    let c (n : ℕ) : ℂ := if a < n ∧ l ∣ n then ψ n else 0
    have heq m : ∑ k ∈ Icc 0 m, c k = ∑ k ∈ (Ioc a m).filter (l ∣ ·), ψ k := by
      rw [← sum_filter (p := fun k => a < k ∧ l ∣ k)]
      congr 1; ext; simp; omega
    have hS {t : ℝ} (ht : (a : ℝ) ≤ t) : ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ E * t := by
      rw [heq]
      by_cases htx : ⌊t⌋₊ ≤ a
      · simp [Ioc_eq_empty_of_le htx, mul_nonneg hE0 (ha0.le.trans ht)]
      have : 0 ≤ t := by linarith
      have hct : (a : ℝ) + 1 ≤ t := (show (a : ℝ) + 1 ≤ ⌊t⌋₊ by exact_mod_cast not_le.1 htx).trans (Nat.floor_le this)
      grw [hBurq hl a ⌊t⌋₊, (show ((⌊t⌋₊ / l - a / l : ℕ) : ℝ) ≤ (⌊t⌋₊ / l : ℕ) by exact_mod_cast Nat.sub_le _ _).trans
        (Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le this) hlpos.le))]
      rw [div_rpow (by linarith) hlpos.le, div_eq_mul_inv, ← rpow_neg hlpos.le,
        show (2 : ℝ) / 3 = 1 + -((1 : ℝ) / 3) by norm_num, rpow_add (by linarith), rpow_one]
      grw [rpow_le_rpow_of_nonpos (by positivity) hct (by norm_num)]
      exact le_of_eq (by dsimp [E]; ring)
    let f' (t : ℝ) : ℂ := Complex.exp (log t * (-s)) * (1 - log t * s) * (t⁻¹ : ℝ)
    have hdf {t : ℝ} (ht : t ≠ 0) : HasDerivAt f (f' t) t :=
      (((hasDerivAt_log ht).ofReal_comp.mul
        (((hasDerivAt_log ht).ofReal_comp.mul_const (-s)).cexp)).congr_deriv (by dsimp [f']; push_cast; field_simp; ring))
    have hnz : ∀ t ∈ Set.Icc (a : ℝ) b, t ≠ 0 := fun t ht => (ha0.trans_le ht.1).ne'
    have : ContinuousOn log (Set.Icc (a : ℝ) b) := continuousOn_log.mono fun t ht => hnz t ht
    have hint : IntegrableOn (deriv f) (Set.Icc (a : ℝ) b) :=
      (by fun_prop : ContinuousOn f' _).integrableOn_Icc.congr_fun
        (fun t ht => (hdf (hnz t ht)).deriv.symm) measurableSet_Icc
    have hAbel := sum_mul_eq_sub_sub_integral_mul' c hab.le
      (fun t ht => (hdf (hnz t ht)).differentiableAt) hint
    rw [show ∑ n ∈ Ioc a b, (if l ∣ n then ψ n * f n else 0) = ∑ n ∈ Ioc a b, f n * c n from
      sum_congr rfl fun n hn => by dsimp [c]; by_cases hd : l ∣ n <;> simp [hd, (mem_Ioc.1 hn).1, mul_comm],
      hAbel, heq a, Ioc_self, filter_empty, sum_empty, mul_zero, sub_zero,
      ← intervalIntegral.integral_of_le habR]
    have hexp_le {t : ℝ} (ht : (1 : ℝ) ≤ t) : exp (log t * -s.re) ≤ t⁻¹ :=
      (exp_le_exp.2 (show log t * -s.re ≤ -log t by nlinarith [log_nonneg ht])).trans_eq
        (by rw [exp_neg, exp_log (zero_lt_one.trans_le ht)])
    have hT1 : ‖f b * ∑ k ∈ Icc 0 b, c k‖ ≤ E * L := by
      have hSb := Nat.floor_natCast (R := ℝ) b ▸ hS habR
      dsimp [f]; rw [norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, Complex.neg_re,
        Complex.norm_real, norm_of_nonneg hL0]
      grw [hexp_le (by exact_mod_cast (ha_ge.trans hab.le)), hSb]
      exact le_of_eq (by dsimp [L]; field_simp)
    have hT2 : ‖∫ t in (a : ℝ)..b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ E * (1 + ‖s‖ * L) * L := by
      refine (intervalIntegral.norm_integral_le_of_norm_le habR ?_
        (((continuousOn_id.inv₀ hnz).intervalIntegrable_of_Icc habR).const_mul (E * (1 + ‖s‖ * L)))).trans ?_
      · refine Eventually.of_forall fun t ht => ?_
        have ht1 : (1 : ℝ) ≤ t := (show (1 : ℝ) ≤ a by exact_mod_cast ha_ge).trans ht.1.le
        have hlt : log t ≤ L := log_le_log (ha0.trans ht.1) ht.2
        rw [norm_mul, (hdf (ha0.trans ht.1).ne').deriv, norm_mul, norm_mul, Complex.norm_exp,
          Complex.re_ofReal_mul, Complex.neg_re, Complex.norm_real, norm_of_nonneg (by positivity : 0 ≤ t⁻¹)]
        have h1 : ‖1 - (log t : ℂ) * s‖ ≤ 1 + ‖s‖ * L :=
          (norm_sub_le _ _).trans (by rw [norm_one, norm_mul, Complex.norm_real, norm_of_nonneg (log_nonneg ht1), mul_comm]; gcongr)
        grw [hexp_le ht1, h1, hS ht.1.le]
        dsimp; have : t ≠ 0 := (ha0.trans ht.1).ne'; exact le_of_eq (by field_simp)
      · dsimp; rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hb0]
        exact mul_le_mul_of_nonneg_left (log_le_log (by positivity) (div_le_self hb0.le (by exact_mod_cast ha_ge)))
          (by positivity)
    refine (norm_sub_le _ _).trans ((add_le_add hT1 hT2).trans ?_)
    rw [show E * L + E * (1 + ‖s‖ * L) * L = E * (L + (1 + ‖s‖ * L) * L) by ring]
    exact (mul_le_mul_of_nonneg_left
      (show L + (1 + ‖s‖ * L) * L ≤ (2 + ‖s‖) * (1 + L) ^ 2 by
        nlinarith [norm_nonneg s, sq_nonneg L, mul_nonneg (norm_nonneg s) hL0]) hE0).trans_eq
      (by dsimp [CT, E]; ring)
  set K := ⌊V⌋₊
  have hlog_bd (m : ℕ) (hm : (m : ℝ) ≤ (q : ℝ) ^ max 1 tmax) : 1 + log m ≤ c₁ * log q := by
    have : log (m : ℝ) ≤ max 1 tmax * log q := by
      rcases eq_or_ne m 0 with rfl | hm0; · simp; positivity
      exact (log_le_log (by positivity) hm).trans_eq (log_rpow hq0 _)
    dsimp [c₁]; rw [add_one_mul]; linarith
  have hLle : 1 + L ≤ c₁ * log q := hlog_bd b ((Nat.lt_ceil.1 (Nat.sub_one_lt_of_le (Nat.ceil_pos.2 hB0) le_rfl)).le.trans
    (rpow_le_rpow_of_exponent_le hq1 (ht'max.trans (le_max_right 1 tmax))))
  have hΛ : (2 + ‖s‖) * (1 + L) ^ 2 ≤ 5 * c₁ ^ 2 * log q ^ 3 := by
    grw [show 2 + ‖s‖ ≤ 5 * log q by linarith, hLle]; exact le_of_eq (by ring)
  have hlogK : 1 + log (K : ℝ) ≤ c₁ * log q := hlog_bd K ((Nat.floor_le (by positivity)).trans
    (rpow_le_rpow_of_exponent_le hq1 (by dsimp [δ]; linarith [ht'max.trans (le_max_right 1 tmax)])))
  have hK23 : (K : ℝ) ^ ((2 : ℝ) / 3) ≤ V ^ ((2 : ℝ) / 3) :=
    rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) (by norm_num)
  have hA13 : ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) ≤ A ^ (-((1 : ℝ) / 3)) := by
    rw [ha1]; exact rpow_le_rpow_of_nonpos hA0 (Nat.le_ceil A) (by norm_num)
  have hexp : (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * A ^ (-((1 : ℝ) / 3)) * V ^ ((2 : ℝ) / 3) =
      ((q : ℝ) ^ (ε' / 3))⁻¹ := by
    dsimp [A, V, δ]
    rw [← rpow_mul hq0.le, ← rpow_mul hq0.le, ← rpow_add hq0, ← rpow_add hq0, ← rpow_neg hq0.le]
    congr 1; ring
  have : 0 ≤ CT := by positivity
  have : 0 ≤ 1 + log (K : ℝ) := by positivity
  refine ((norm_sum_le _ _).trans (sum_le_sum fun d hd => (norm_sum_le _ _).trans
    (sum_le_sum fun e he => (by
      rw [norm_mul, Complex.norm_real, norm_eq_abs, abs_mul]
      grw [hgw d, hgw e, one_mul, one_mul]
      exact hTle (Nat.lcm_pos (mem_Ioc.1 hd).1 (mem_Ioc.1 he).1) : _ ≤ CT * _)))).trans ?_
  simp_rw [← mul_sum]; grw [lcm_sum_le K]; dsimp [CT]; grw [hA13, hΛ, hK23, hlogK]
  refine (le_of_eq ?_).trans hq1_lt.le
  rw [rpow_ofNat _ 4, div_eq_mul_inv (log q ^ 4), ← hexp]; dsimp [Kq]; ring

private lemma sieve_diagonal (hGr : GrahamEstimate) :
    ∃ C V₀, ∀ V A B, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Icc ⌈A⌉₊ ⌊B⌋₊, log n / n * sieveNu V n ≤
        (log B ^ 2 - log A ^ 2) / (2 * log V) + C * (log B ^ 2 + 1) / log V ^ 2 := by
  obtain ⟨C₀, V₁, hC₀⟩ := hGr
  set C₁ := max C₀ 0
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  refine ⟨4 + 4 * C₁, max V₁ (exp 1), fun V A B hV hVA hAB => ?_⟩
  let ld t := log t / t
  have hd {t : ℝ} (ht : t ≠ 0) : HasDerivAt ld ((1 - log t) / t ^ 2) t :=
    ((hasDerivAt_log ht).div (hasDerivAt_id' (x := t)) ht).congr_deriv (by field_simp)
  have hV1 : V₁ ≤ V := (le_max_left _ _).trans hV
  have hVe : exp 1 ≤ V := (le_max_right _ _).trans hV
  have hV0 := (exp_pos 1).trans_le hVe
  have hA2 : 2 ≤ A := ((by linarith [add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ exp 1).trans hVe).trans hVA
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hL1 : 1 ≤ log V := by simpa using log_le_log (exp_pos 1) hVe
  have hLA : log V ≤ log A := log_le_log (by linarith) hVA
  have hlogAB : log A ≤ log B := log_le_log hA0 hAB
  set K := 1 / log V + C₁ / log V ^ 2
  have hS N (hN : V ≤ N) :
      N / log V - C₁ * N / log V ^ 2 ≤ ∑ n ∈ Icc 0 ⌊N⌋₊, sieveNu V n ∧
        ∑ n ∈ Icc 0 ⌊N⌋₊, sieveNu V n ≤ N * K := by
    have h := (hC₀ V N hV1 hN).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by linarith)) (sq_nonneg _))
    rw [Icc_eq_cons_Ioc (Nat.zero_le ⌊N⌋₊), sum_cons, ← Icc_add_one_left_eq_Ioc,
      show sieveNu V 0 = 0 by simp [sieveNu], zero_add]
    simp only [abs_le] at h; exact ⟨by linarith, by dsimp [K]; linarith [show N / log V + C₁ * N / log V ^ 2 = N * (1 / log V + C₁ / log V ^ 2) by ring]⟩
  have hnz : ∀ t ∈ Set.Icc A B, t ≠ 0 := fun t ht => (hA0.trans_le ht.1).ne'
  have : ContinuousOn log (Set.Icc A B) := continuousOn_log.mono fun t ht => hnz t ht
  have hcont_ld : ContinuousOn ld (Set.Icc A B) := by fun_prop
  have hint_d : IntegrableOn (deriv ld) (Set.Icc A B) :=
    ((by fun_prop : ContinuousOn (fun t => 1 - log t) (Set.Icc A B)).div (by fun_prop)
      fun t ht => pow_ne_zero 2 (hnz t ht)).integrableOn_Icc.congr_fun
      (fun t ht => (hd (hnz t ht)).deriv.symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul (sieveNu V) hA0.le hAB
    (fun t ht => (hd (hnz t ht)).differentiableAt) hint_d
  have hBt : ld B * ∑ k ∈ Icc 0 ⌊B⌋₊, sieveNu V k ≤ log B * K :=
    (mul_le_mul_of_nonneg_left (hS B (hVA.trans hAB)).2
      (div_nonneg (log_nonneg (by linarith)) hB0.le)).trans_eq (by field_simp)
  have hAt : log A / log V - C₁ * log A / log V ^ 2 ≤ ld A * ∑ k ∈ Icc 0 ⌊A⌋₊, sieveNu V k :=
    (by dsimp [ld]; field_simp : _ = ld A * (A / log V - C₁ * A / log V ^ 2)).trans_le
      (mul_le_mul_of_nonneg_left (hS A hVA).1 (div_nonneg (log_nonneg (by linarith)) hA0.le))
  have hE : ld ⌊A⌋₊ * sieveNu V ⌊A⌋₊ ≤ 2 * log A * K := by
    have hm : A / 2 ≤ ⌊A⌋₊ := by linarith [Nat.lt_floor_add_one A]
    have hnu : sieveNu V ⌊A⌋₊ ≤ A * K :=
      (single_le_sum (f := sieveNu V) (fun _ _ => sq_nonneg _)
        (mem_Icc.2 ⟨Nat.zero_le _, le_rfl⟩)).trans (hS A hVA).2
    have : 1 ≤ ⌊A⌋₊ := (Nat.one_le_floor_iff A).2 (by linarith)
    have : 0 ≤ log A := log_nonneg (by linarith)
    dsimp [ld]; grw [log_le_log (by positivity) (Nat.floor_le hA0.le), ← hm, hnu]; exact le_of_eq (by field_simp)
  have hint_eq : ∫ t in A..B, ld t = (log B ^ 2 - log A ^ 2) / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => log t ^ 2 / 2)
      (fun x hx => (((hasDerivAt_log (hA0.trans_le (Set.uIcc_of_le hAB ▸ hx).1).ne').pow 2).div_const 2).congr_deriv
        (by dsimp [ld]; field_simp))
      (hcont_ld.intervalIntegrable_of_Icc hAB)]
    ring
  have hI : -(∫ t in Set.Ioc A B, deriv ld t * ∑ k ∈ Icc 0 ⌊t⌋₊, sieveNu V k) ≤
      K * ((log B ^ 2 - log A ^ 2) / 2) := by
    rw [← intervalIntegral.integral_of_le hAB, ← intervalIntegral.integral_neg, ← hint_eq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hAB
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hAB).2 (integrableOn_mul_sum_Icc (m := 0) (sieveNu V) hA0.le hint_d)).neg
      ((hcont_ld.intervalIntegrable_of_Icc hAB).const_mul _) fun t ht => ?_
    have ht0 := hA0.trans_le ht.1
    have hlt1 : 1 ≤ log t := by simpa using log_le_log (exp_pos 1) (hVe.trans (hVA.trans ht.1))
    have := sum_nonneg fun i (_ : i ∈ Icc 0 ⌊t⌋₊) => sq_nonneg (∑ d ∈ i.divisors, grahamWeight V d)
    rw [(hd ht0.ne').deriv, show -((1 - log t) / t ^ 2 * ∑ k ∈ Icc 0 ⌊t⌋₊, sieveNu V k) =
      (log t - 1) * (∑ k ∈ Icc 0 ⌊t⌋₊, sieveNu V k) / t ^ 2 by ring]
    grw [show log t - 1 ≤ log t by linarith, (hS t (hVA.trans ht.1)).2]
    exact le_of_eq (by dsimp [ld]; have := ht0.ne'; field_simp)
  set a := log A; set b := log B; set L := log V
  refine ((sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (Nat.floor_le_ceil A) le_rfl)
      fun n _ _ => mul_nonneg (div_nonneg (log_natCast_nonneg n) (Nat.cast_nonneg n)) (sq_nonneg _)).trans
    (show _ ≤ 2 * a * K + b * K - (a / L - C₁ * a / L ^ 2) + K * ((b ^ 2 - a ^ 2) / 2) by
      rw [Icc_eq_cons_Ioc (Nat.floor_le_floor hAB), sum_cons]; dsimp [ld] at hAbel hE hBt hAt hI; linarith)).trans ?_
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 * L ^ 2)
  dsimp [K, L]; have : log V ≠ 0 := by linarith
  field_simp; rw [mul_div_cancel_left₀ _ this, mul_div_cancel_left₀ _ this]
  nlinarith [mul_le_mul (show a + b ≤ 2 * b by linarith) (hLA.trans hlogAB) (by linarith) (by linarith),
    mul_nonneg hC₁ (by nlinarith [sq_nonneg (b - 1), sq_nonneg b, sq_nonneg a] :
      0 ≤ 8 * (b ^ 2 + 1) - (6 * a + 2 * b + (b ^ 2 - a ^ 2)))]



private abbrev tn (q n : ℕ) := log n / log q

private lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < log q :=
  log_pos (by exact_mod_cast (by omega : 1 < q))

private lemma tn_nonneg (q n : ℕ) (hq : 2 ≤ q) : 0 ≤ tn q n :=
  div_nonneg (log_natCast_nonneg n) (log_q_pos hq).le

private lemma cpow_one_sub {q n : ℕ} (hn : 1 ≤ n) (σ γ : ℝ) :
    (n : ℂ) ^ (-(((1 - σ / log q : ℝ) : ℂ) + γ * I)) =
      ((1 / n * exp (σ * tn q n) : ℝ) : ℂ) * Complex.exp (-((γ * log n : ℝ) : ℂ) * I) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : n ≠ 0)), ← Complex.natCast_log,
    show (log n : ℂ) * -(((1 - σ / log q : ℝ) : ℂ) + γ * I) =
      ↑(-log n + σ * tn q n) + -((γ * log n : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, exp_add, exp_neg, exp_log hnp]
  push_cast; ring

private lemma le_tn_iff {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) {X : ℝ} :
    X ≤ tn q n ↔ (q : ℝ) ^ X ≤ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [tn, le_div_iff₀ (log_q_pos hq), ← log_rpow hq0, log_le_log_iff (rpow_pos_of_pos hq0 X) (by exact_mod_cast hn)]

private lemma tn_ge_of_gt {q n : ℕ} (hq : 2 ≤ q) {X : ℝ} (hn : ⌊(q : ℝ) ^ X⌋₊ < n) :
    X ≤ tn q n :=
  (le_tn_iff hq (by omega)).2 ((Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hn)).le

private lemma primeSum_eq_sum {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) {f : ℝ → ℝ}
    {X : ℝ} (hf : ∀ t, X ≤ t → f t = 0) (s : ℂ) :
    primeSum χ f s = ∑ n ∈ Icc 1 ⌊(q : ℝ) ^ X⌋₊, (Λ n : ℂ) * χ n * (n : ℂ) ^ (-s) * f (tn q n) := by
  refine tsum_eq_sum fun n hn => ?_
  rcases not_and_or.1 (by simpa only [mem_Icc] using hn) with h | h
  · obtain rfl : n = 0 := by omega
    simp
  · have h0 := hf _ (tn_ge_of_gt hq (not_le.1 h)); simp [h0]

private def ycomp {q ι} (E : Entries q ι) (a : ι → ℝ) (j : ι) (n : ℕ) : ℂ :=
  a j * (exp (-(E.δ j) * tn q n) * E.χ j n * Complex.exp (-((E.γ j * log n : ℝ) : ℂ) * I))

private abbrev Yn {q ι} [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ := ∑ j, ycomp E a j n

private abbrev cWeight (D : NearData) (q n : ℕ) := Λ n / n * exp (D.s * tn q n) * D.f (tn q n)

private lemma ycomp_pair_re {q ι} (E : Entries q ι) (a : ι → ℝ) (j k : ι) {n : ℕ} (hn : 1 ≤ n)
    (W σ₀ : ℝ) :
    W / n * exp (σ₀ * tn q n) * (ycomp E a j n * conj (ycomp E a k n)).re =
      a j * a k * ((W : ℂ) * (E.χ j * (E.χ k)⁻¹) n *
        (n : ℂ) ^ (-(((1 - (σ₀ - E.δ j - E.δ k) / log q : ℝ) : ℂ) + ↑(E.γ j - E.γ k) * I))).re := by
  have hχ : conj (E.χ k n) = (E.χ k)⁻¹ n := by rw [← MulChar.star_apply']; rfl
  have e1 : Complex.exp (-((E.γ j * log n : ℝ) : ℂ) * I) * Complex.exp (((E.γ k * log n : ℝ) : ℂ) * I) =
      Complex.exp (-(((E.γ j - E.γ k) * log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← Complex.re_ofReal_mul, ← Complex.re_ofReal_mul]; congr 1
  unfold ycomp
  rw [cpow_one_sub hn, ← e1, show σ₀ - E.δ j - E.δ k = σ₀ + -(E.δ j) + -(E.δ k) by ring]
  simp only [add_mul, exp_add, MulChar.coeToFun_mul, Pi.mul_apply, map_mul, ← Complex.exp_conj,
    map_neg, Complex.conj_ofReal, Complex.conj_I, hχ, mul_neg, neg_mul, neg_neg]
  push_cast; ring

private lemma norm_Yn_sq {q ι} [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (n : ℕ) :
    ‖Yn E a n‖ ^ 2 = ∑ j, ∑ k, (ycomp E a j n * conj (ycomp E a k n)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
    Yn, map_sum, sum_mul_sum]
  simp [Complex.re_sum]

private lemma eventually_loglog_ge K :
    ∃ q₀, ∀ q : ℕ, q₀ ≤ q → K ≤ √(log (log q)) ∧ K ≤ log (log q) ∧ 2 ≤ q := by
  obtain ⟨q₀, h⟩ := eventually_atTop.1 <|
    ((tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop
      (max (K ^ 2) K)).and (eventually_ge_atTop 2)
  refine ⟨q₀, fun q hq => ⟨?_, (le_max_right _ _).trans (h q hq).1, (h q hq).2⟩⟩
  exact (le_abs_self K).trans ((sqrt_sq_eq_abs K).symm.trans_le (sqrt_le_sqrt ((le_max_left _ _).trans (h q hq).1)))

private lemma laplace_re_conj g z :
    (laplace g (conj z)).re = (laplace g z).re := by
  rw [← Complex.conj_re (laplace g z)]; congr 1; unfold laplace; rw [← integral_conj]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [← Complex.exp_conj]

private abbrev sieveDiag (D : NearData) δ :=
  ∑ k ∈ range D.m, D.h k * exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

section
variable (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε)
include hD hε

private lemma first_factor_bound :
    ∃ q₀ : ℕ, ∀ q ≥ q₀,
      (∑ n ∈ Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n *
          (exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))) / log q ≤ D.IB + ε := by
  have hX := hD.f_cond.pos
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  let φ u := exp (2 * D.s * u) * D.f u ^ 2 / max (D.omega u) c
  have hφeq {u} (hu : 0 ≤ u) : exp (2 * D.s * u) * D.f u ^ 2 / D.omega u = φ u := by
    dsimp [φ]; by_cases hf : D.f u = 0; · simp [hf]
    · rw [max_eq_left (hcω u hu hf)]
  obtain ⟨M₀, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc 0 D.xf) (f := fun v => exp (2 * D.s * v) * D.f v ^ 2 / c)
    (by have : ContinuousOn D.f (Set.Icc 0 D.xf) := hD.f_cond.cont.mono Set.Icc_subset_Ici_self; fun_prop)
  set M := max M₀ 0
  have hbd {u} (hu : 0 ≤ u) : φ u ≤ M := by
    by_cases hux : u ≤ D.xf
    · dsimp [φ]; grw [← le_max_right (D.omega u) c]
      exact ((le_abs_self _).trans (norm_eq_abs _ ▸ hM0 u ⟨hu, hux⟩)).trans (le_max_left _ _)
    · simp [φ, hD.f_cond.vanish u (le_of_not_ge hux), M]
  let P : Finset ℝ := (range (D.m + 1)).image D.t
  have hcont u (hu : 0 < u) (huP : u ∉ P) : ContinuousAt φ u := by
    have hne k (hk : k ≤ D.m) : ∀ᶠ v in 𝓝 u, D.t k ≤ v ↔ D.t k ≤ u :=
      (lt_or_gt_of_ne fun h => huP (mem_image.2 ⟨k, mem_range.2 (by omega), h.symm⟩)).elim
        (fun h => Filter.mem_of_superset (Iio_mem_nhds h) fun _ hv => by simp [h.not_ge]; exact hv.out)
        (fun h => Filter.mem_of_superset (Ioi_mem_nhds h) fun _ hv => by simp [hv.out.le, h.le])
    have hf := hD.f_cond.cont.continuousAt (Ici_mem_nhds hu)
    have hg := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu)
    have hH : ContinuousAt D.sieveH u := tendsto_finsetSum _ fun k hk =>
      (continuousAt_const (y := if D.t k ≤ u ∧ u < D.t (k + 1) then D.h k else 0)).congr
        (((hne k (mem_range.1 hk).le).and (hne (k + 1) (mem_range.1 hk))).mono
          fun v ⟨h1, h2⟩ => by simp only [← not_le, h1, h2])
    exact ((by fun_prop : ContinuousAt (fun v => exp (2 * D.s * v)) u).mul (hf.pow 2)).div
      (((hg.mul (by fun_prop : ContinuousAt (fun v => exp (D.s₁ * v)) u)).add hH).max continuousAt_const)
      (hc.trans_le (le_max_right _ _)).ne'
  let cell (h : ℝ) (i : ℕ) := sSup (φ '' Set.Icc (i * h) ((i + 1) * h))
  let stepFn h t := cell h ⌊t / h⌋₊
  have hcell_spec {h : ℝ} (hh : 0 ≤ h) (i : ℕ) :
      0 ≤ cell h i ∧ cell h i ≤ M ∧ ∀ t ∈ Set.Icc ((i : ℝ) * h) ((i + 1) * h), φ t ≤ cell h i := by
    have hm : (i : ℝ) * h ∈ Set.Icc ((i : ℝ) * h) ((i + 1) * h) := ⟨le_rfl, by nlinarith⟩
    have hub : ∀ y ∈ φ '' Set.Icc ((i : ℝ) * h) ((i + 1) * h), y ≤ M := by
      rintro _ ⟨v, hv, rfl⟩; exact hbd ((by positivity : 0 ≤ (i : ℝ) * h).trans hv.1)
    have hle t ht := le_csSup ⟨M, hub⟩ ⟨t, ht, rfl⟩
    exact ⟨(div_nonneg (by positivity) (hc.le.trans (le_max_right _ _))).trans (hle _ hm),
      csSup_le ⟨_, _, hm, rfl⟩ hub, hle⟩
  have hstep {h} (hh : 0 ≤ h) : AEStronglyMeasurable (stepFn h) ∧ ∀ t, ‖stepFn h t‖ ≤ M :=
    ⟨((measurable_from_nat (f := cell h)).comp (measurable_id.div_const _).nat_floor).aestronglyMeasurable,
     fun t => (norm_of_nonneg (hcell_spec hh _).1).trans_le (hcell_spec hh _).2.1⟩
  have hdom : Tendsto (fun K : ℕ => ∫ t in 0..D.xf, stepFn (D.xf / K) t) atTop (𝓝 D.IB) := by
    rw [show D.IB = ∫ u in 0..D.xf, φ u by
      rw [intervalIntegral.integral_of_le hX.le, NearData.IB,
        setIntegral_congr_fun measurableSet_Ioi fun v hv => hφeq (Set.mem_Ioi.1 hv).le]
      exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self fun v hv => by
          simp [φ, hD.f_cond.vanish v (le_of_not_gt fun h => hv.2 ⟨hv.1, h.le⟩)]]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun K => (hstep (by positivity)).1.restrict)
      (Eventually.of_forall fun K => Eventually.of_forall fun t _ => (hstep (by positivity)).2 t)
      intervalIntegrable_const ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (P.finite_toSet.measure_zero _)] with t htP htI
    rw [Set.uIoc_of_le hX.le] at htI
    rw [Metric.tendsto_nhds]; intro η hη
    obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 (hcont t htI.1 htP) (η / 2) (half_pos hη)
    filter_upwards [eventually_gt_atTop 0,
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hδ)] with K hK0 hhδ
    have hh : 0 < D.xf / K := div_pos hX (Nat.cast_pos.2 hK0)
    have htmem : t ∈ Set.Icc ((⌊t / (D.xf / K)⌋₊ : ℝ) * (D.xf / K))
        ((⌊t / (D.xf / K)⌋₊ + 1) * (D.xf / K)) :=
      ⟨(le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg htI.1.le hh.le)),
       ((div_lt_iff₀ hh).1 (Nat.lt_floor_add_one _)).le⟩
    have hup : cell (D.xf / K) ⌊t / (D.xf / K)⌋₊ ≤ φ t + η / 2 :=
      csSup_le ⟨_, _, htmem, rfl⟩ <| by
        rintro _ ⟨v, hv, rfl⟩
        have hd : dist v t < δ := by
          rw [Real.dist_eq, abs_lt]; exact ⟨by nlinarith [hv.1, htmem.2], by nlinarith [hv.2, htmem.1]⟩
        linarith [(abs_lt.1 (Real.dist_eq _ _ ▸ hδφ hd)).2]
    dsimp only [stepFn]; rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [(hcell_spec hh.le _).2.2 t htmem], by linarith⟩
  obtain ⟨K, hK0, hKint⟩ :=
    ((eventually_gt_atTop 0).and ((tendsto_order.1 hdom).2 _ (lt_add_of_pos_right _ (half_pos hε)))).exists
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK0
  set h := D.xf / K
  have hh : 0 < h := div_pos hX hKR
  have hKh : (K : ℝ) * h = D.xf := mul_div_cancel₀ _ hKR.ne'
  rw [show ∫ t in 0..D.xf, stepFn (D.xf / K) t = ∑ i ∈ range K, cell h i * h by
    rw [show stepFn (D.xf / K) = stepFn h from rfl, ← hKh, show (0 : ℝ) = (0 : ℕ) * h by simp,
      ← intervalIntegral.sum_integral_adjacent_intervals (a := fun i => (i : ℝ) * h) fun j _ =>
        (intervalIntegrable_const (c := M)).mono_fun' (hstep hh.le).1.restrict (ae_of_all _ (hstep hh.le).2)]
    refine sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_of_le (by push_cast; nlinarith), integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo fun t ht => congrArg (cell h) <|
        (Nat.floor_eq_iff (div_nonneg ((by positivity : 0 ≤ (j : ℝ) * h).trans ht.1.le) hh.le)).2
          ⟨(le_div_iff₀ hh).2 ht.1.le, (div_lt_iff₀ hh).2 (by push_cast at ht; exact ht.2)⟩,
      setIntegral_const, Real.volume_real_Ioo, max_eq_left (by push_cast; nlinarith), smul_eq_mul]
    push_cast; ring] at hKint
  refine ⟨⌈exp (18 * K * M / ε)⌉₊ + 2, fun q hq => ?_⟩
  have hq1 : 1 < q := by omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hℓ : 0 < log q := log_pos hqR
  have hℓbig : 18 * K * M < ε * log q := by
    have : 18 * K * M / ε < log q := (lt_log_iff_exp_lt (by positivity)).2
      ((Nat.le_ceil _).trans_lt (by exact_mod_cast (by omega : ⌈exp (18 * K * M / ε)⌉₊ < q)))
    rw [div_lt_iff₀ hε] at this; linarith
  let ms (N : ℕ) := ∑ n ∈ Ioc 0 N, Λ n / n
  have hmert {a : ℝ} (ha : 0 ≤ a) :
      a * log q - 2 ≤ ms ⌊(q : ℝ) ^ a⌋₊ ∧ ms ⌊(q : ℝ) ^ a⌋₊ ≤ a * log q + 7 := by
    set x := (q : ℝ) ^ a; set N := ⌊x⌋₊
    have hx : 1 ≤ x := one_le_rpow hqR.le ha
    have hN : 1 ≤ N := Nat.le_floor (by simpa using hx)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog : ∑ n ∈ Ioc 0 N, log n = ∑ n ∈ Ioc 0 N, Λ n * (N / n : ℕ) := by
      simpa [ArithmeticFunction.log_apply, ArithmeticFunction.vonMangoldt_mul_zeta] using
        ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
    have hNms : (N : ℝ) * ms N = ∑ n ∈ Ioc 0 N, Λ n * (N / n) := by
      dsimp [ms]; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have hup : (N : ℝ) * ms N ≤ N * (log N + 7) := by
      have h1 : (N : ℝ) * ms N ≤ ∑ n ∈ Ioc 0 N, Λ n * (N / n : ℕ) + Chebyshev.psi N := by
        rw [hNms, Chebyshev.psi, Nat.floor_natCast, ← sum_add_distrib]
        exact sum_le_sum fun n _ => (mul_le_mul_of_nonneg_left
          (by simpa [Nat.floor_div_eq_div] using (Nat.lt_floor_add_one ((N : ℝ) / n)).le)
          ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_add_one _ _)
      have h2 : ∑ n ∈ Ioc 0 N, log n ≤ N * log N :=
        (sum_le_sum (g := fun _ => log N) fun n hn => log_le_log (by exact_mod_cast (mem_Ioc.1 hn).1)
          (by exact_mod_cast (mem_Ioc.1 hn).2)).trans_eq (by simp)
      nlinarith [Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hNR.le,
        log_le_sub_one_of_pos (x := 4) (by norm_num)]
    have hlog2 : a * log q ≤ log N + 1 := by
      have : x ≤ 2 * N := by linarith [Nat.lt_floor_add_one x, show (1 : ℝ) ≤ N by exact_mod_cast hN]
      linarith [log_rpow hq0 a, log_le_log (by positivity) this, log_mul two_ne_zero hNR.ne', log_two_lt_d9]
    exact ⟨by linarith [le_of_mul_le_mul_left (show (N : ℝ) * (log N - 1) ≤ N * ms N by
      linarith [le_sum_log_nat N, hlog, hNms, sum_le_sum (s := Ioc 0 N) fun n _ =>
        mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := N) (n := n)) (ArithmeticFunction.vonMangoldt_nonneg (n := n))]) hNR],
      by linarith [le_of_mul_le_mul_left hup hNR, log_le_log hNR (Nat.floor_le (by positivity)), log_rpow hq0 a]⟩
  have hpart (j : ℕ) : ∑ n ∈ Ioc 0 ⌊(q : ℝ) ^ ((j : ℝ) * h)⌋₊, Λ n / n * φ (tn q n) ≤
      (∑ i ∈ range j, cell h i * h) * log q + j * (9 * M) := by
    induction j with
    | zero => simp [show Ioc 0 1 = {1} from rfl]
    | succ j ih =>
      set aj := ⌊(q : ℝ) ^ ((j : ℝ) * h)⌋₊
      set bj := ⌊(q : ℝ) ^ (((j + 1 : ℕ) : ℝ) * h)⌋₊
      have hmF : aj ≤ bj := Nat.floor_le_floor (rpow_le_rpow_of_exponent_le hqR.le (by push_cast; nlinarith))
      rw [sum_range_succ, ← sum_Ioc_consecutive _ (Nat.zero_le _) hmF]
      obtain ⟨hc0, hcM, hcel⟩ := hcell_spec hh.le j
      have hle : ∑ n ∈ Ioc aj bj, Λ n / n * φ (tn q n) ≤ cell h j * ∑ n ∈ Ioc aj bj, Λ n / n := by
        rw [mul_sum]; refine sum_le_sum fun n hn => ?_
        obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le _).trans_lt hn1
        have h2 := (log_le_log hnR ((Nat.le_floor_iff (rpow_nonneg hq0.le _)).1 hn2)).trans_eq
          (log_rpow hq0 (((j + 1 : ℕ) : ℝ) * h))
        rw [mul_comm (cell h j)]
        exact mul_le_mul_of_nonneg_left
          (hcel _ ⟨tn_ge_of_gt hq1 hn1, by push_cast at h2; exact (div_le_iff₀ hℓ).2 h2⟩)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hnR.le)
      have hs : ∑ n ∈ Ioc aj bj, Λ n / n ≤ h * log q + 9 := by
        have h1 := (hmert (a := ((j + 1 : ℕ) : ℝ) * h) (by positivity)).2
        have h2 := (hmert (a := (j : ℝ) * h) (by positivity)).1
        dsimp [ms] at h1 h2; rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hmF] at h1
        linarith [show ((j + 1 : ℕ) : ℝ) * h * log q = j * h * log q + h * log q by push_cast; ring]
      rw [Nat.cast_add, Nat.cast_one]; nlinarith [mul_le_mul_of_nonneg_left hs hc0]
  have hK' := hpart K
  rw [hKh, show Ioc 0 ⌊(q : ℝ) ^ D.xf⌋₊ = Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊ by ext; simp; omega,
    sum_congr rfl fun n _ => by rw [← hφeq (tn_nonneg q n hq1)]] at hK'
  rw [div_le_iff₀ hℓ]; nlinarith [mul_lt_mul_of_pos_right hKint hℓ]

private lemma sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ T, 0 ≤ T → T ≤ log q / 3 →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a, (∀ j, 0 ≤ a j) → ∀ N,
        (∑ n ∈ Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  obtain ⟨CB, V₀, hdiagG⟩ := sieve_diagonal hGr
  obtain ⟨qC, hoffC⟩ := sieve_offdiag hBur (tmax := D.t D.m) hD.ε'_pos
  have htmono {k l : ℕ} (hkl : k ≤ l) : l ≤ D.m → D.t k ≤ D.t l :=
    Nat.le_induction (fun _ => le_rfl) (fun n _ ih hn => (ih (by omega)).trans (hD.t_lt n hn).le) l hkl
  have ht0k k (hk : k < D.m) : 1 / 3 + 2 * D.ε' < D.t k := hD.t_zero.trans_le (htmono (Nat.zero_le k) hk.le)
  have hlev_pos k (hk : k < D.m) : 0 < D.level k := by unfold NearData.level; linarith [ht0k k hk]
  have hlev_lt k (hk : k < D.m) : D.level k < D.t k := by unfold NearData.level; linarith [ht0k k hk, hD.ε'_pos]
  let main k := (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)
  let Mk k := |CB| * (D.t (k + 1) ^ 2 + 1) / D.level k ^ 2
  set Ctot := ∑ k ∈ range D.m, D.h k * (Mk k + 2)
  have hPkT : ∀ k ∈ range D.m, Tendsto (fun q : ℕ =>
      3 * D.t (k + 1) ^ 2 * (log q ^ (2 : ℝ) / (q : ℝ) ^ (D.t k - D.level k))) atTop (𝓝 0) := fun k hk => by
    simpa using ((isLittleO_log_rpow_rpow_atTop 2 (sub_pos.2 (hlev_lt k (mem_range.1 hk)))).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (3 * D.t (k + 1) ^ 2)
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.1 <|
    (((eventually_ge_atTop (max qC (⌈exp 3⌉₊ + 2))).and
        ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
          (max (Ctot / ε) (2 * ∑ δ ∈ D.Δ, δ)))).and
      (((Finset.eventually_all _).2 fun k hk => (tendsto_order.1 (hPkT k hk)).2 1 one_pos).and
        ((Finset.eventually_all _).2 fun k hk =>
          ((tendsto_rpow_atTop (hlev_pos k (mem_range.1 hk))).comp
            tendsto_natCast_atTop_atTop).eventually_ge_atTop V₀)))
  refine ⟨q₀, fun q hq T hT hTq ι _ E hγ hΔ hinj a ha N => ?_⟩
  obtain ⟨⟨hqC', hqL⟩, hqPk, hqV⟩ := hq₀ q hq
  dsimp only [Function.comp_apply] at hqL hqV
  have hq2 : 2 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hℓ3 : 3 ≤ log q := (le_log_iff_exp_le hq0).2 ((Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈exp 3⌉₊ ≤ q)))
  have hℓ : 0 < log q := by linarith
  have hδ (j : ι) : 0 ≤ E.δ j := hD.Δ_nonneg _ (hΔ j)
  have hyc (j : ι) (n : ℕ) : ‖ycomp E a j n‖ ≤ a j * exp (-(E.δ j) * tn q n) := by
    simp only [ycomp, norm_mul, Complex.norm_real, norm_of_nonneg (ha j), norm_of_nonneg (exp_pos _).le,
      ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
    have := ha j; grw [(E.χ j).norm_le_one n, mul_one]
  have hYn (n : ℕ) : ‖Yn E a n‖ ^ 2 ≤ (∑ j, a j) ^ 2 := by
    grw [Yn, norm_sum_le]
    refine pow_le_pow_left₀ (by positivity) (sum_le_sum fun j _ => (hyc j n).trans ?_) 2
    have := ha j; grw [exp_le_one_iff.2 (by nlinarith [hδ j, tn_nonneg q n hq2]), mul_one]
  rw [div_le_iff₀ hℓ, show ∑ n ∈ Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 =
      ∑ k ∈ range D.m, D.h k * ∑ n ∈ (Icc 1 N).filter (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)),
        Λ n / n * ‖Yn E a n‖ ^ 2 by
    unfold NearData.sieveH; simp_rw [mul_sum, sum_mul]; rw [sum_comm]
    exact sum_congr rfl fun k _ => by rw [sum_filter]; exact sum_congr rfl fun _ _ => by split_ifs <;> ring]
  refine ((sum_le_sum fun k hk => show _ ≤
      D.h k * (log q * ∑ j, exp (-2 * E.δ j * D.t k) * main k * a j ^ 2 + (Mk k + 2) * (∑ j, a j) ^ 2) by
    classical
    have hk' := mem_range.1 hk
    rcases eq_or_lt_of_le (hD.h_nonneg k hk') with hh0 | hhp
    · simp [← hh0]
    have hinj' := hinj ⟨k, hk', hhp.ne'⟩
    refine mul_le_mul_of_nonneg_left ?_ hhp.le
    set V := (q : ℝ) ^ D.level k; set A := (q : ℝ) ^ D.t k; set B := (q : ℝ) ^ D.t (k + 1)
    set Ck := Ico ⌈A⌉₊ ⌈B⌉₊
    refine (sum_le_sum_of_subset_of_nonneg (t := Ck)
      (fun n hn => by
        obtain ⟨⟨hn1, -⟩, ht1, ht2⟩ := by simpa only [mem_filter, mem_Icc] using hn
        exact mem_Ico.2 ⟨Nat.ceil_le.2 ((le_tn_iff hq2 hn1).1 ht1),
          Nat.lt_ceil.2 ((lt_iff_lt_of_le_iff_le (le_tn_iff hq2 hn1)).1 ht2)⟩)
      fun n _ _ => mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)) (sq_nonneg _)).trans ?_
    have hCk n (hn : n ∈ Ck) : 1 ≤ n ∧ D.t k ≤ tn q n := by
      have h1 : 1 ≤ n := lt_of_lt_of_le (Nat.ceil_pos.2 (rpow_pos_of_pos hq0 _)) (mem_Ico.1 hn).1
      exact ⟨h1, (le_tn_iff hq2 h1).2 (Nat.ceil_le.1 (mem_Ico.1 hn).1)⟩
    have hVpos : 1 < V := one_lt_rpow (by exact_mod_cast hq2) (hlev_pos k hk')
    have hVA : V ≤ A := rpow_le_rpow_of_exponent_le hq1 (hlev_lt k hk').le
    have hAB : A ≤ B := rpow_le_rpow_of_exponent_le hq1 (hD.t_lt k hk').le
    let pp (n : ℕ) := if IsPrimePow n ∧ (n.minFac : ℝ) ≤ V then Λ n else 0
    have step1 : ∑ n ∈ Ck, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
        ∑ n ∈ Ck, log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 + ∑ n ∈ Ck, pp n / n * ‖Yn E a n‖ ^ 2 := by
      rw [← sum_add_distrib]; refine sum_le_sum fun n hn => ?_
      have hnp : (0 : ℝ) < n := by exact_mod_cast (hCk n hn).1
      have hvM : Λ n ≤ log n * sieveNu V n + pp n := by
        have hprod : 0 ≤ log n * sieveNu V n := by positivity
        dsimp [pp]; by_cases hpp : IsPrimePow n
        · by_cases hmin : (n.minFac : ℝ) ≤ V
          · rw [ite_eq_left ⟨hpp, hmin⟩]; linarith
          · rw [ite_eq_right fun h => hmin h.2, add_zero]
            have h1 : ∑ d ∈ n.divisors, grahamWeight V d = 1 := by
              rw [sum_eq_single 1]
              · simp [grahamWeight, hVpos.le, (log_pos hVpos).ne']
              · intro d hd hd1
                have hle : (n.minFac : ℝ) ≤ d := by
                  exact_mod_cast Nat.minFac_le_of_dvd (by have := Nat.pos_of_mem_divisors hd; omega) (Nat.dvd_of_mem_divisors hd)
                simp [grahamWeight, show ¬(d : ℝ) ≤ V by linarith]
              · exact fun h => absurd (Nat.one_mem_divisors.2 hpp.ne_zero) h
            simpa [sieveNu, h1] using ArithmeticFunction.vonMangoldt_le_log
        · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp, hpp, hprod]
      grw [hvM]; exact le_of_eq (by ring)
    have step2 : ∑ n ∈ Ck, pp n / n * ‖Yn E a n‖ ^ 2 ≤ (∑ j, a j) ^ 2 := by
      have hppsum : ∑ n ∈ Ck, pp n / n ≤ 1 := by
        set S := Ck.filter fun n => IsPrimePow n ∧ (n.minFac : ℝ) ≤ V
        have hB1 : 1 ≤ log B := by rw [log_rpow hq0]; nlinarith [ht0k k hk', hD.t_lt k hk', hD.ε'_pos]
        have hcard : (#S : ℝ) ≤ 3 * V * log B := by
          have hc : #S ≤ #(Icc 1 ⌊V⌋₊ ×ˢ range (⌊2 * log B⌋₊ + 1)) :=
            (card_le_card fun n hn => by
              obtain ⟨hI, hpp, hmin⟩ := mem_filter.1 hn
              have h2B : (2 : ℝ) ^ n.factorization n.minFac ≤ B :=
                (show (2 : ℝ) ^ n.factorization n.minFac ≤ n by
                  exact_mod_cast (Nat.pow_le_pow_left (Nat.minFac_prime hpp.ne_one).two_le _).trans_eq hpp.minFac_pow_factorization_eq).trans
                  (Nat.lt_ceil.1 (mem_Ico.1 hI).2).le
              have hlog : (n.factorization n.minFac : ℝ) * log 2 ≤ log B := by
                simpa [log_pow] using log_le_log (by positivity) h2B
              exact mem_image.2 ⟨(n.minFac, n.factorization n.minFac),
                mem_product.2 ⟨mem_Icc.2 ⟨Nat.minFac_pos n, Nat.le_floor hmin⟩,
                  mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor (by nlinarith [log_two_gt_d9, Nat.cast_nonneg (α := ℝ) (n.factorization n.minFac)])))⟩,
                hpp.minFac_pow_factorization_eq⟩).trans (card_image_le (f := fun x => x.1 ^ x.2))
          grw [show (#S : ℝ) ≤ ⌊V⌋₊ * (⌊2 * log B⌋₊ + 1) by simpa using (Nat.cast_le (α := ℝ)).2 hc,
            Nat.floor_le (by positivity), Nat.floor_le (by positivity), show 2 * log B + 1 ≤ 3 * log B by linarith]
          exact le_of_eq (by ring)
        rw [show ∑ n ∈ Ck, pp n / n = ∑ n ∈ S, Λ n / n by
          rw [sum_filter]; exact sum_congr rfl fun _ _ => by dsimp [pp]; split_ifs <;> simp]
        refine (((sum_le_sum fun n hn => ?_).trans_eq (by simp : ∑ _ ∈ S, log B / A = #S * (log B / A))).trans
          (mul_le_mul_of_nonneg_right hcard (by positivity))).trans ?_
        · obtain ⟨hI, -⟩ := mem_filter.1 hn
          have hnA : A ≤ n := Nat.ceil_le.1 (mem_Ico.1 hI).1
          exact div_le_div₀ (by positivity)
            (ArithmeticFunction.vonMangoldt_le_log.trans
              (log_le_log (by exact_mod_cast (hCk n hI).1) (Nat.lt_ceil.1 (mem_Ico.1 hI).2).le))
            (by positivity) hnA
        · refine (?_ : _ = 3 * D.t (k + 1) ^ 2 * (log q ^ (2 : ℝ) / (q : ℝ) ^ (D.t k - D.level k))).trans_le (hqPk k hk).le
          rw [log_rpow hq0, rpow_ofNat _ 2, rpow_sub hq0]; dsimp [V, A]; field_simp
      refine ((sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hYn n)
        (div_nonneg (by dsimp [pp]; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]) (Nat.cast_nonneg n))).trans_eq
        (sum_mul _ _ _).symm).trans (mul_le_of_le_one_left (sq_nonneg _) hppsum)
    have hdiag : ∑ n ∈ Ck, log n / n * sieveNu V n ≤ log q * main k + Mk k := by
      refine (sum_le_sum_of_subset_of_nonneg
        (fun n hn => mem_Icc.2 ⟨(mem_Ico.1 hn).1, Nat.le_floor (Nat.lt_ceil.1 (mem_Ico.1 hn).2).le⟩)
        fun n _ _ => mul_nonneg (div_nonneg (log_natCast_nonneg n) (Nat.cast_nonneg n)) (sq_nonneg _)).trans
        ((hdiagG V A B (hqV k hk) hVA hAB).trans ?_)
      simp only [V, A, B, log_rpow hq0]
      have hlv := (hlev_pos k hk').ne'
      have e1 : ((D.t (k + 1) * log q) ^ 2 - (D.t k * log q) ^ 2) / (2 * (D.level k * log q)) =
          log q * main k := by dsimp [main]; field_simp
      have e2 : CB * ((D.t (k + 1) * log q) ^ 2 + 1) / (D.level k * log q) ^ 2 ≤ Mk k := by
        dsimp [Mk]
        grw [le_abs_self CB, show (D.t (k + 1) * log q) ^ 2 + 1 ≤ (D.t (k + 1) ^ 2 + 1) * log q ^ 2 by nlinarith]
        rw [mul_pow, ← mul_assoc, mul_div_mul_right _ _ (sq_pos_of_pos hℓ).ne']
      linarith
    let T j j' n := sieveNu V n * (log n / n * (ycomp E a j n * conj (ycomp E a j' n)).re)
    have hexpY : ∑ n ∈ Ck, log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 = ∑ j, ∑ j', ∑ n ∈ Ck, T j j' n := by
      simp_rw [norm_Yn_sq, mul_sum]; rw [sum_comm]
      exact sum_congr rfl fun j _ => by rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by dsimp [T]; ring
    have hM0 : 0 ≤ Mk k := by dsimp [Mk]; positivity
    have hdiagj (j : ι) : ∑ n ∈ Ck, T j j n ≤
        log q * (exp (-2 * E.δ j * D.t k) * main k * a j ^ 2) + Mk k * a j ^ 2 := by
      have hterm n (hn : n ∈ Ck) :
          T j j n ≤ (log n / n * sieveNu V n) * (a j ^ 2 * exp (-2 * E.δ j * D.t k)) := by
        have := ha j; dsimp [T]
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        grw [hyc j n, show -E.δ j * tn q n ≤ -E.δ j * D.t k by nlinarith [hδ j, (hCk n hn).2]]
        rw [mul_pow, ← exp_nat_mul]; push_cast; exact le_of_eq (by ring)
      have he1 : exp (-2 * E.δ j * D.t k) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hδ j, ht0k k hk', hD.ε'_pos])
      grw [sum_le_sum hterm, ← sum_mul, hdiag]
      nlinarith [mul_le_of_le_one_right (mul_nonneg hM0 (sq_nonneg (a j))) he1]
    have hoffj (j j' : ι) (hjj' : j ≠ j') : ∑ n ∈ Ck, T j j' n ≤ a j * a j' := by
      have hψ : E.χ j * (E.χ j')⁻¹ ≠ 1 := fun h => hjj' (hinj' (mul_inv_eq_one.1 h))
      have hb := hoffC q (by omega) _ hψ (D.t k) (D.t (k + 1)) ((E.δ j + E.δ j') / log q)
        (E.γ j - E.γ j') (ht0k k hk') (hD.t_lt k hk').le (htmono hk' le_rfl)
        (div_nonneg (add_nonneg (hδ j) (hδ j')) hℓ.le)
        ((div_le_one hℓ).2 (by linarith [single_le_sum hD.Δ_nonneg (hΔ j), single_le_sum hD.Δ_nonneg (hΔ j'), (le_max_right _ _).trans hqL]))
        (by linarith [abs_sub (E.γ j) (E.γ j'), hγ j, hγ j'])
      have hrw n (hn : n ∈ Ck) :
          T j j' n = a j * a j' * ((sieveNu V n : ℂ) * (E.χ j * (E.χ j')⁻¹) n * log n *
            (n : ℂ) ^ (-((1 + (E.δ j + E.δ j') / log q : ℝ) + ↑(E.γ j - E.γ j') * I))).re := by
        refine (show _ = (sieveNu V n * log n) / n * exp (0 * tn q n) * _ by dsimp [T]; simp; ring).trans
          ((ycomp_pair_re E a j j' (hCk n hn).1 _ 0).trans ?_)
        congr 2; rw [show (1 + (E.δ j + E.δ j') / log q : ℝ) = 1 - (0 - E.δ j - E.δ j') / log q by ring]
        push_cast; ring
      rw [sum_congr rfl hrw, ← mul_sum, ← Complex.re_sum]
      exact mul_le_of_le_one_right (mul_nonneg (ha j) (ha j')) ((Complex.re_le_norm _).trans hb)
    have step3 : ∑ n ∈ Ck, log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 ≤
        log q * ∑ j, exp (-2 * E.δ j * D.t k) * main k * a j ^ 2 + (Mk k + 1) * (∑ j, a j) ^ 2 := by
      rw [hexpY]
      refine (sum_le_sum fun j _ => sum_le_sum fun j' _ => show _ ≤
          (if j' = j then log q * (exp (-2 * E.δ j * D.t k) * main k * a j ^ 2) else 0) +
            (Mk k + 1) * (a j * a j') by
        by_cases h : j' = j
        · subst h; rw [ite_eq_left rfl]; nlinarith [hdiagj j', sq_nonneg (a j')]
        · rw [ite_eq_right h, zero_add]; nlinarith [hoffj j j' (Ne.symm h), mul_nonneg (ha j) (ha j')]).trans_eq ?_
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, ← mul_sum, sq, sum_mul_sum]
    linarith).trans_eq (show _ = (∑ j, sieveDiag D (E.δ j) * a j ^ 2) * log q + Ctot * (∑ j, a j) ^ 2 by
      simp_rw [mul_add (D.h _), sum_add_distrib, ← mul_assoc (D.h _), ← sum_mul]
      congr 1; simp only [mul_sum]; rw [sum_comm, sum_mul]
      exact sum_congr rfl fun j _ => by
        unfold sieveDiag; rw [sum_mul, sum_mul]; exact sum_congr rfl fun _ _ => by dsimp [main]; ring)).trans ?_
  have hCe : Ctot ≤ ε * log q := by
    have := (le_max_left _ _).trans hqL; rwa [div_le_iff₀ hε, mul_comm] at this
  nlinarith [sq_nonneg (∑ j, a j)]

end



section
open Set

private lemma lfunc_analytic {q} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (LFunction χ) univ ∧ LFunction χ 1 ≠ 0 :=
  ⟨Complex.analyticOnNhd_univ_iff_differentiable.2 (differentiable_LFunction hχ),
   LFunction_apply_one_ne_zero hχ⟩

private lemma lfunc_order_ne_top {q} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  obtain ⟨ha, h1⟩ := lfunc_analytic hχ
  exact ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1) (mem_univ ρ)
    (by simp [analyticOrderAt_eq_zero.2 (.inr h1)])

private lemma one_le_zmult {q} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have hne := analyticOrderAt_ne_zero.2 ⟨(lfunc_analytic hχ).1 ρ ⟨⟩, hρ⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h =>
    hne (by rw [← Nat.cast_analyticOrderNatAt (lfunc_order_ne_top hχ ρ), h]; rfl)

private lemma laplace_eq {f x₀ B} (hf : Condition1 f x₀ B) z :
    laplace f z = ∫ t in 0..x₀, f t * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hf.pos.le, laplace]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun t ht => by simp [hf.vanish t (le_of_not_gt fun h => ht.2 ⟨ht.1, h.le⟩)]

private lemma laplace_decay {f x₀ B} (hf : Condition1 f x₀ B) (X : ℝ) {ε} (hε : 0 < ε) :
    ∃ M > 0, ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| → ‖laplace f (x + Y * I)‖ ≤ ε := by
  have hx₀ := hf.pos
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 x₀) := hf.smooth.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hmid : x₀ / 2 ∈ Ioo 0 x₀ := ⟨by linarith, by linarith⟩
  set K := max (|deriv f (x₀ / 2)| + B * x₀) |deriv f x₀|
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (le_max_right _ _)
  have hK t (ht : t ∈ Ioc 0 x₀) : |deriv f t| ≤ K := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact le_max_right _ _
    · have hmv := (convex_Ioo 0 x₀).norm_image_sub_le_of_norm_deriv_le
        (fun s hs => (hd1.differentiableOn one_ne_zero s hs).differentiableAt (isOpen_Ioo.mem_nhds hs))
        (fun s hs => (norm_eq_abs _).trans_le (hf.bound s hs)) hmid ⟨ht.1, h⟩
      rw [norm_eq_abs, norm_eq_abs] at hmv
      refine le_trans ?_ (le_max_left _ _)
      nlinarith [abs_sub_abs_le_abs_sub (deriv f t) (deriv f (x₀ / 2)),
        abs_le.2 ⟨show -x₀ ≤ t - x₀ / 2 by linarith [ht.1], show t - x₀ / 2 ≤ x₀ by linarith⟩,
        (abs_nonneg _).trans (hf.bound _ hmid)]
  set C := |f 0| + K * exp (X * x₀) * x₀
  refine ⟨C / ε + 1, by positivity, fun x hx Y hY => ?_⟩
  set z : ℂ := x + Y * I
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (v := fun t : ℝ => Complex.exp (-(z * t))) (v' := fun t => Complex.exp (-(z * t)) * (-z)) (a := 0) (b := x₀)
    (uIcc_of_le hx₀.le ▸ Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self))
    (by fun_prop)
    (fun t ht => by
      rw [min_eq_left hx₀.le, max_eq_right hx₀.le] at ht
      exact ((hf.smooth.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt.ofReal_comp)
    (fun t _ => ((hasDerivAt_id t).ofReal_comp.const_mul z).neg.cexp.congr_deriv (by dsimp; ring))
    ((intervalIntegrable_const (c := K)).mono_fun'
      (Complex.measurable_ofReal.comp (measurable_deriv f)).aestronglyMeasurable
      (by rw [uIoc_of_le hx₀.le]; exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by simpa using hK t ht))
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
  simp_rw [Function.comp_apply, ← mul_assoc, intervalIntegral.integral_mul_const, ← laplace_eq hf, hf.vanish x₀ le_rfl] at hibp
  have hbd : ‖z‖ * ‖laplace f z‖ ≤ C := by
    rw [← norm_mul, show z * laplace f z = f 0 + ∫ t in 0..x₀, ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t)) by
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one, zero_sub] at hibp
      linear_combination -hibp]
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * exp (X * x₀))
      fun t ht => ?_).trans_eq (by simp [hx₀.le])
    rw [uIoc_of_le hx₀.le] at ht
    rw [norm_mul, Complex.norm_real, norm_eq_abs, Complex.norm_exp]
    grw [hK t ht, show (-(z * t)).re ≤ X * x₀ by simp [z]; nlinarith [hx.1, hx.2, ht.1, ht.2]]
  have hMz : C / ε + 1 ≤ ‖z‖ := hY.trans (by simpa [z] using Complex.abs_im_le_norm z)
  exact le_of_mul_le_mul_left
    (hbd.trans (by nlinarith [mul_le_mul_of_nonneg_right hMz hε.le, div_mul_cancel₀ C hε.ne']))
    (lt_of_lt_of_le (by positivity) hMz)

theorem response_lemma (hX32 : XylourisLemma32) {f : ℝ → ℝ} {x₀ B : ℝ}
    (hf1 : Condition1 f x₀ B) (hf2 : Condition2 f) σmax (K₀ : ℕ) {η} (hη : 0 < η) :
    ∃ M, 0 < M ∧ ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ q₀, ∀ q, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ, |σ| ≤ σmax → |γ| ≤ log q →
      ∀ Sz,
        (∀ ρ ∈ Sz, LFunction χ ρ = 0 ∧ ‖1 + γ * I - ρ‖ ≤ δ) →
        (∀ ρ, LFunction χ ρ = 0 → ‖1 + γ * I - ρ‖ ≤ δ →
          ρ ∉ Sz → (1 - ρ.re) * log q < σ → M ≤ |γ - ρ.im| * log q) →
        (∑ᶠ ρ ∈ {ρ | LFunction χ ρ = 0 ∧ ‖1 + γ * I - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * log q < σ},
          zmult χ ρ) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  set ε' := η / 2 / (K₀ + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax hε'
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge σmax
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩
  obtain ⟨hsq, -, hq2⟩ := hq₂ q (by omega)
  have hℓ := log_q_pos hq2
  set s : ℂ := ((1 - σ / log q : ℝ) : ℂ) + γ * I
  have hX := hq₁ q (by omega) χ hχ s
    ⟨by simpa [s, -Complex.natCast_log, abs_div, abs_of_pos hℓ] using div_le_div_of_nonneg_right (hσ.trans hsq) hℓ.le,
     by simpa [s, -Complex.natCast_log] using hγ⟩
  obtain ⟨ha, h1⟩ := lfunc_analytic hχ
  set Z := {ρ | ‖1 + s.im * I - ρ‖ ≤ δ ∧ LFunction χ ρ = 0}
  have hZfin : Z.Finite :=
    ((isCompact_closedBall (1 + s.im * I) δ).finite_sdiff_of_mem_codiscreteWithin
      (codiscreteWithin_mono (subset_univ _)
        ((ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
          fun h => h1 (h (mem_univ 1))))).subset
      fun ρ ⟨h1, h0⟩ => ⟨by rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm], by simp [h0]⟩
  let g ρ := zmult χ ρ * zeroTerm f q σ γ ρ
  have hzs : zeroSum χ f s δ = ∑ ρ ∈ hZfin.toFinset, g ρ := by
    rw [zeroSum, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine sum_congr rfl fun ρ _ => congrArg (zmult χ ρ * ·) ?_
    unfold zeroTerm; congr 2
    have := hℓ.ne'; apply Complex.ext <;> simp [s, -Complex.natCast_log]; field_simp; ring
  have hmem ρ : ρ ∈ hZfin.toFinset ↔ LFunction χ ρ = 0 ∧ ‖1 + γ * I - ρ‖ ≤ δ := by
    simp [Z, s, -Complex.natCast_log, and_comm]
  set T := hZfin.toFinset \ Sz
  let p (ρ : ℂ) := (1 - ρ.re) * log q < σ
  have hgood : 0 ≤ ∑ ρ ∈ T.filter (¬p ·), g ρ :=
    sum_nonneg fun ρ hρ => mul_nonneg (Nat.cast_nonneg _)
      (hf2.re_nonneg _ (by simp [-Complex.natCast_log]; linarith [(mem_filter.1 hρ).2]))
  have hadv : -(η / 2) ≤ ∑ ρ ∈ T.filter p, g ρ := by
    have hterm ρ (hρ : ρ ∈ T.filter p) : -ε' ≤ zeroTerm f q σ γ ρ := by
      obtain ⟨hT', hlt⟩ := mem_filter.1 hρ
      obtain ⟨hρZ, hρS⟩ := Finset.mem_sdiff.1 hT'
      obtain ⟨hL, hd⟩ := (hmem ρ).1 hρZ
      have hr1 : ρ.re < 1 := lt_of_not_ge fun h =>
        LFunction_ne_zero_of_one_le_re χ (.inl hχ) h hL
      have hb := hdecay ((1 - ρ.re) * log q - σ)
        ⟨by linarith [le_abs_self σ, mul_nonneg (sub_nonneg.2 hr1.le) hℓ.le], by linarith [abs_nonneg σ]⟩
        ((γ - ρ.im) * log q) (by simpa [abs_mul, abs_of_pos hℓ] using hsep ρ hL hd hρS hlt)
      unfold zeroTerm; linarith [neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hb)]
    have h1 : (∑ ρ ∈ T.filter p, zmult χ ρ) * (-ε') ≤ _ :=
      (sum_mul _ _ _).trans_le (sum_le_sum fun ρ hρ =>
        mul_le_mul_of_nonneg_left (hterm ρ hρ) (Nat.cast_nonneg _))
    have hK' : ∑ ρ ∈ T.filter p, zmult χ ρ ≤ K₀ :=
      (le_of_eq (by rw [← finsum_mem_coe_finset]; congr 1; ext; simp [T, hmem, p, and_assoc])).trans hK
    have : (K₀ : ℝ) * ε' ≤ η / 2 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hK' hε'.le]
  rw [responseAt, show (((1 - σ / log q : ℝ) : ℂ) + γ * I) = s from rfl, le_div_iff₀ hℓ]
  rw [hzs, ← sum_sdiff (fun ρ hρ => (hmem ρ).2 (hSz ρ hρ)), ← sum_filter_add_sum_filter_not T p] at hX
  dsimp [g] at hX hadv hgood; nlinarith

private lemma zeroTerm_at_height_le {f x₀ B} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) {q : ℕ} {σ γ hi ρ} (hγ : ρ.im = γ)
    (hhi : (1 - ρ.re) * log q ≤ hi) :
    (laplace f ↑(hi - σ)).re ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  have hreal (x : ℝ) : (laplace f x).re = ∫ t in 0..x₀, f t * exp (-(x * t)) := by
    rw [laplace_eq hf]
    have (t : ℝ) : (f t : ℂ) * Complex.exp (-((x : ℂ) * t)) = ↑(f t * exp (-(x * t))) := by
      rw [Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; ring_nf
    simp_rw [this, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hc (z : ℝ) : IntervalIntegrable (fun t => f t * exp (-(z * t))) volume 0 x₀ :=
    ((hf.cont.mono Icc_subset_Ici_self).mul (by fun_prop)).intervalIntegrable_of_Icc hf.pos.le
  rw [show zeroTerm f q σ γ ρ = (laplace f ↑((1 - ρ.re) * log q - σ)).re by
    simp [zeroTerm, hγ, -Complex.natCast_log], hreal, hreal]
  exact ⟨intervalIntegral.integral_mono_on hf.pos.le (hc _) (hc _) fun t ht =>
      mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith [ht.1])) (hf2.nonneg t ht.1),
    intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
      mul_nonneg (hf2.nonneg t ht.1) (exp_pos _).le⟩

section Entry
variable {q : ℕ} {ι : Type*} [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
  (E : Entries q ι) (Sz : ι → Finset ℂ)
include hD hf2

theorem keptBound_single η j (hχ : E.χ j ≠ 1) {ρ hi}
    (hS : Sz j = {ρ}) (hρ : LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * log q ≤ hi) :
    (laplace D.f ↑(hi - (D.s - E.δ j))).re - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound; rw [hS, sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith [one_le_zmult hχ hρ]

theorem keptBound_pair η j (hχ : E.χ j ≠ 1) {ρ ρ' hi}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : (1 - ρ.re) * log q ≤ hi)
    (hρ' : LFunction (E.χ j) ρ' = 0) (hleft : D.s - E.δ j ≤ (1 - ρ'.re) * log q) :
    (laplace D.f ↑(hi - (D.s - E.δ j))).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound; rw [hS, sum_pair hne]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have hz' : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' :=
    hf2.re_nonneg _ (by simp [-Complex.natCast_log]; linarith)
  nlinarith [one_le_zmult hχ hρ, one_le_zmult hχ hρ']

theorem keptBound_double η j {ρ hi}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * log q ≤ hi) :
    (laplace D.f ↑(hi - (D.s - E.δ j))).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound; rw [hS, sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith

theorem keptBound_pair_neg j (hχ : E.χ j ≠ 1) {ρ ρ' hi C}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * log q ≤ hi) (hρ' : LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ') :
    (laplace D.f ↑(hi - (D.s - E.δ j))).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ↑(hi - (D.s - E.δ j))).re - C - D.f 0 / 6 ≤ 0 := by
  unfold keptBound; rw [hS, sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have hm2 := one_le_zmult hχ hρ'
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ + zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ'
  · exact .inl (by nlinarith [mul_le_mul_of_nonneg_right hm hA0, mul_le_mul_of_nonneg_left hm2 hAB])
  · exact .inr (by linarith)

end Entry

lemma zeroTerm_conj f q σ γ ρ :
    zeroTerm f q σ (-γ) (conj ρ) = zeroTerm f q σ γ ρ := by
  unfold zeroTerm; rw [← laplace_re_conj]; congr 2; apply Complex.ext <;> simp [-Complex.natCast_log]; ring


end

section Threshold
variable (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
  (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
include hX31 hX32 hBur hGr hD

theorem graded_near_lemma
    {η} (hη : 0 < η) :
    ∃ q₀, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T, 0 ≤ T → T ≤ log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ a : _ → ℝ, (∀ j, 0 ≤ a j) →
          max 0 (∑ j, a j * response D E j) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2) := by
  have hIB := hD.IB_pos
  set ε := η / 2
  have hε : 0 < ε := half_pos hη
  set K : ℝ := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨qF, hqF⟩ := first_factor_bound D hD (ε := η * D.IB) (mul_pos hη hIB)
  obtain ⟨C, q₁, hC⟩ := hX31 D.g D.xg D.Bg hD.g_cond1
  obtain ⟨δ, hδ0, hδ1, q₂, hq₂⟩ := hX32 D.g D.xg D.Bg hD.g_cond1 (hD.g_cond2.nonneg 0 le_rfl) ε hε
  obtain ⟨q₃, hq₃⟩ := eventually_loglog_ge (max K (|C| / ε + 1))
  obtain ⟨qS, hqS⟩ := sieve_part_bound D hD hε hGr (burgessBound_of_primitive hBur)
  obtain ⟨c, hc, hωc⟩ := hD.omega_lb
  refine ⟨max (max (max qF q₁) (max q₂ q₃)) qS, fun q _ hq T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha => ?_⟩
  classical
  obtain ⟨hsq, hll, hq2⟩ := hq₃ q (by omega)
  have hℓ := log_q_pos hq2
  set Sf := Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊
  set N := max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊
  let w (n : ℕ) := Λ n / n * D.omega (tn q n)
  have hω0 {u : ℝ} (hu : 0 ≤ u) : 0 ≤ D.omega u :=
    add_nonneg (mul_nonneg (hD.g_cond2.nonneg u hu) (exp_pos _).le)
      (sum_nonneg fun k hk => by split_ifs; exacts [hD.h_nonneg k (mem_range.1 hk), le_rfl])
  have hw0 (n : ℕ) : 0 ≤ w n :=
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
      (hω0 (tn_nonneg q n hq2))
  let u (n : ℕ) := Λ n / n * (exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))
  have hu0 (n : ℕ) : 0 ≤ u n := mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    (div_nonneg (by positivity) (hω0 (tn_nonneg q n hq2)))
  have hcs : (∑ n ∈ Sf, |cWeight D q n| * ‖Yn E a n‖) ^ 2 ≤
      (∑ n ∈ Sf, u n) * (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) := by
    have key : ∀ n ∈ Sf, |cWeight D q n| * ‖Yn E a n‖ = √(u n) * (√(w n) * ‖Yn E a n‖) := fun n _ => by
      rw [← mul_assoc, ← sqrt_mul (hu0 n), ← sqrt_sq_eq_abs]; congr 2
      dsimp [cWeight, u, w]; by_cases hf : D.f (tn q n) = 0
      · simp [hf]
      · have := (hc.trans_le (hωc _ (tn_nonneg q n hq2) hf)).ne'
        rw [show 2 * D.s * tn q n = D.s * tn q n + D.s * tn q n by ring, exp_add]; field_simp
    rw [sum_congr rfl key]
    exact (sum_mul_sq_le_sq_mul_sq Sf _ _).trans_eq <| congrArg₂ (· * ·)
      (sum_congr rfl fun n _ => sq_sqrt (hu0 n))
      (sum_congr rfl fun n _ => by rw [mul_pow, sq_sqrt (hw0 n)])
  have hG : (∑ n ∈ Icc 1 N, Λ n / n * (D.g (tn q n) * exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2) / log q ≤
      ∑ j, (D.Dδ (E.δ j) - sieveDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
        (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
    set sjk := fun j k => (((1 - (D.s₁ - E.δ j - E.δ k) / log q : ℝ)) : ℂ) + ↑(E.γ j - E.γ k) * I
    rw [show ∑ n ∈ Icc 1 N, Λ n / n * (D.g (tn q n) * exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 =
        ∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk j k)).re by
      rw [← sum_subset (Icc_subset_Icc le_rfl (le_max_right _ _)) fun n hn hn' => by
        rw [hD.g_cond1.vanish _ (tn_ge_of_gt hq2 (not_le.1 fun h => hn' (mem_Icc.2 ⟨(mem_Icc.1 hn).1, h⟩)))]; simp]
      simp_rw [primeSum_eq_sum hq2 _ hD.g_cond1.vanish, Complex.re_sum, mul_sum, norm_Yn_sq, mul_sum]
      rw [sum_congr rfl fun n hn => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
        (by ring : _ = (Λ n * D.g (tn q n)) / n * exp (D.s₁ * tn q n) * _).trans
          ((ycomp_pair_re E a j k (mem_Icc.1 hn).1 _ D.s₁).trans
            (show _ = a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk j k) * D.g (tn q n)).re by
              dsimp only [sjk]; congr 2; push_cast; ring)), sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm, sum_div]
    simp_rw [sum_div, mul_div_assoc]
    let M j k := (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk j k)).re / log q
    let R j k := (laplace D.g (↑(-(D.s₁ - E.δ j - E.δ k)) + ↑((E.γ j - E.γ k) * log q) * I)).re
    have hreg (j k : ι) : LemmaRegion q (sjk j k) := by
      refine ⟨?_, by simp [sjk, -Complex.natCast_log]; linarith [abs_sub (E.γ j) (E.γ k), hγ j, hγ k]⟩
      have hσ : |D.s₁ - E.δ j - E.δ k| ≤ K := abs_le.2
        ⟨by linarith [neg_le_abs D.s₁, single_le_sum hD.Δ_nonneg (hΔ j), single_le_sum hD.Δ_nonneg (hΔ k)],
         by linarith [le_abs_self D.s₁, hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k),
           sum_nonneg fun δ hδ => hD.Δ_nonneg δ hδ]⟩
      simpa [sjk, -Complex.natCast_log, abs_div, abs_of_pos hℓ] using
        div_le_div_of_nonneg_right (hσ.trans ((le_max_left _ _).trans hsq)) hℓ.le
    have hsame (j k : ι) (hjk : E.χ j = E.χ k) : M j k ≤ R j k + ε := by
      have h1 : E.χ j * (E.χ k)⁻¹ = 1 := by rw [hjk, mul_inv_cancel]
      have hb := (Complex.re_le_norm _).trans (hC q (by omega) (sjk j k) (hreg j k))
      rw [Complex.sub_re, Complex.re_ofReal_mul] at hb
      have harg : (sjk j k - 1) * log q = ↑(-(D.s₁ - E.δ j - E.δ k)) + ↑((E.γ j - E.γ k) * log q) * I := by
        have := hℓ.ne'; apply Complex.ext <;> simp [sjk, -Complex.natCast_log]; field_simp; ring
      have hll2 : |C| / ε + 1 ≤ log (log q) := (le_max_right _ _).trans hll
      have hsm : C / log (log q) ≤ ε := (div_le_iff₀ (lt_of_lt_of_le (by positivity) hll2)).2
        (by nlinarith [le_abs_self C, div_mul_cancel₀ |C| hε.ne'])
      dsimp [M, R]; rw [h1, ← harg, div_le_iff₀ hℓ]; rw [mul_div_right_comm] at hb; nlinarith
    have hdiff (j k : ι) (hjk : E.χ j ≠ E.χ k) : M j k ≤ D.d₁ + ε := by
      have hψ : E.χ j * (E.χ k)⁻¹ ≠ 1 := fun h => hjk (mul_inv_eq_one.1 h)
      have hb := hq₂ q (by omega) _ hψ (sjk j k) (hreg j k)
      have hzs : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g (sjk j k) δ := by
        refine finsum_nonneg fun ρ => finsum_nonneg fun hρ =>
          mul_nonneg (Nat.cast_nonneg _) (hD.g_cond2.re_nonneg ((sjk j k - ρ) * ↑(log q)) ?_)
        have h1 := (Complex.abs_im_le_norm (1 + (sjk j k).im * I - ρ)).trans hρ.1
        simp [sjk, -Complex.natCast_log] at h1 ⊢
        rw [abs_sub_comm] at h1
        have hs := hsafe _ hψ ρ hρ.2 (by
          linarith [abs_sub_abs_le_abs_sub ρ.im (E.γ j - E.γ k), abs_sub (E.γ j) (E.γ k), hγ j, hγ k])
        exact mul_nonneg (by linarith [(div_le_div_of_nonneg_right
          (show D.s₁ - E.δ j - E.δ k ≤ D.s₁ by linarith [hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k)]) hℓ.le)]) hℓ.le
      dsimp [M]; unfold NearData.d₁; rw [div_le_iff₀ hℓ]; nlinarith
    let P j k := if k ≠ j ∧ E.χ k = E.χ j then max 0 (R j k - D.d₁) else 0
    have hRsymm (j k : ι) : R j k = R k j := by
      dsimp [R]; rw [← laplace_re_conj]; congr 2
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    have hPsymm (j k : ι) : P j k = P k j := by
      dsimp [P]; by_cases h1 : k = j <;> by_cases h2 : E.χ k = E.χ j <;> simp [h1, Ne.symm, h2, hRsymm j k]
    have hRjj (j : ι) : R j j = D.Dδ (E.δ j) - sieveDiag D (E.δ j) := by
      unfold NearData.Dδ; rw [add_sub_cancel_right]; dsimp [R, laplace]
      have (u : ℝ) : (D.g u : ℂ) * Complex.exp (-((↑(-(D.s₁ - E.δ j - E.δ j)) + ↑((E.γ j - E.γ j) * log q) * I) * u)) =
          ↑(D.g u * exp ((D.s₁ - 2 * E.δ j) * u)) := by
        rw [Complex.ofReal_mul (D.g u), Complex.ofReal_exp]; congr 2; push_cast; ring
      simp_rw [this, integral_complex_ofReal, Complex.ofReal_re]
    have hPe (j : ι) : ∑ k, P j k = pairExcess D E j := by
      unfold pairExcess sameCharOthers; rw [sum_filter]
      exact sum_congr rfl fun _ _ => by dsimp [P]; split_ifs <;> rfl
    refine (sum_le_sum fun j _ => sum_le_sum fun k _ => show a j * a k * M j k ≤
        a j * a k * (D.d₁ + ε) + (if k = j then (R j j - D.d₁) * a j ^ 2 else 0) +
          (a j ^ 2 * P j k + a k ^ 2 * P k j) / 2 by
      have : 0 ≤ P j k := by dsimp [P]; split_ifs <;> positivity
      have hp : a j * a k * P j k ≤ (a j ^ 2 * P j k + a k ^ 2 * P k j) / 2 := by
        rw [← hPsymm j k]; nlinarith [sq_nonneg (a j - a k)]
      have hM : M j k ≤ (D.d₁ + ε) + (if k = j then R j j - D.d₁ else 0) + P j k := by
        dsimp [P]; by_cases hkj : k = j
        · subst hkj; simp; linarith [hsame k k rfl]
        · by_cases hc : E.χ k = E.χ j
          · simp [hkj, hc]; linarith [hsame j k hc.symm, le_max_right 0 (R j k - D.d₁)]
          · simp [hkj, hc]; exact hdiff j k (Ne.symm hc)
      have hm := mul_le_mul_of_nonneg_left hM (mul_nonneg (ha j) (ha k))
      by_cases hkj : k = j
      · subst hkj; simp at hm ⊢; nlinarith
      · simp [hkj] at hm ⊢; linarith).trans_eq ?_
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, ← sum_div]
    rw [sum_comm (f := fun j k => a k ^ 2 * P k j), add_self_div_two,
      show ∑ j, ∑ k, a j * a k * (D.d₁ + ε) = (D.d₁ + ε) * (∑ j, a j) ^ 2 by
        rw [sq, sum_mul_sum, mul_sum]; exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring]
    simp_rw [← mul_sum, hPe, ← hRjj, add_mul, sum_add_distrib, mul_comm (a _ ^ 2)]; ring
  have hresp : max 0 (∑ j, a j * response D E j) ≤ (∑ n ∈ Sf, |cWeight D q n| * ‖Yn E a n‖) / log q :=
    max_le (div_nonneg (sum_nonneg fun _ _ => by positivity) hℓ.le) <| by
      have hj j : a j * response D E j =
          -(∑ n ∈ Sf, (cWeight D q n : ℂ) * ycomp E a j n).re / log q := by
        rw [response, primeSum_eq_sum hq2 _ hD.f_cond.vanish, ← mul_div_assoc, mul_neg,
          ← Complex.re_ofReal_mul, mul_sum]
        congr 3; refine sum_congr rfl fun n hn => ?_
        rw [cpow_one_sub (mem_Icc.1 hn).1,
          show (D.s - E.δ j) * tn q n = D.s * tn q n + -(E.δ j) * tn q n by ring, exp_add]
        dsimp [cWeight, ycomp]; push_cast; ring
      simp_rw [hj, ← sum_div, sum_neg_distrib, ← Complex.re_sum]
      rw [sum_comm]; simp only [← mul_sum]
      refine div_le_div_of_nonneg_right ((neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)) hℓ.le
      exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun n _ => by rw [norm_mul, Complex.norm_real, norm_eq_abs])
  grw [hresp, div_pow, hcs, sq (log ↑q), ← div_mul_div_comm]
  refine mul_le_mul (by linarith [hqF q (by omega)]) ?_
    (div_nonneg (sum_nonneg fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le) (by positivity)
  have hmono := sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc (le_refl 1) (le_max_left ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊))
    fun n _ _ => mul_nonneg (hw0 n) (sq_nonneg ‖Yn E a n‖)
  have hS := hqS q (by omega) T hT hTq ι E hγ hΔ hinj a ha N
  refine (div_le_div_of_nonneg_right hmono hℓ.le).trans ?_
  rw [show ∑ n ∈ Icc 1 N, w n * ‖Yn E a n‖ ^ 2 =
    ∑ n ∈ Icc 1 N, Λ n / n * (D.g (tn q n) * exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 +
      ∑ n ∈ Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by dsimp [w, NearData.omega]; ring, add_div]
  have hDsum : ∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 =
      ∑ j, (D.Dδ (E.δ j) - sieveDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
        ∑ j, sieveDiag D (E.δ j) * a j ^ 2 := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
  dsimp [ε] at hG hS; linarith



open Set
variable (hf2 : Condition2 D.f) (K₀ : ℕ)
include hf2

theorem graded_near_threshold {η} (hη : 0 < η) :
    ∃ M, 0 < M ∧ ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ q₀, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T, 0 ≤ T → T ≤ log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz,
          (∀ j, ∀ ρ ∈ Sz j, LFunction (E.χ j) ρ = 0 ∧ ‖1 + E.γ j * I - ρ‖ ≤ δ) →
          (∀ j ρ, LFunction (E.χ j) ρ = 0 → ‖1 + E.γ j * I - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ | LFunction (E.χ j) ρ = 0 ∧ ‖1 + E.γ j * I - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ Dn, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ, 0 ≤ τ ∧ τ ≤ √((D.d₁ + η) / Dn) ∧
              ∑ j, max 0 (keptBound D E Sz η j / √((1 + η) * D.IB * Dn) - τ) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨q₁, hq₁⟩ := graded_near_lemma hX31 hX32 hBur hGr D hD hη
  obtain ⟨M, hM, δ, hδ0, hδ1, q₂, hq₂⟩ :=
    response_lemma hX32 hD.f_cond hf2 (|D.s| + ∑ δ ∈ D.Δ, |δ|) K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂,
    fun q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK Dn hDn hDj => ?_⟩
  have hIB := hD.IB_pos
  set N := √((1 + η) * D.IB * Dn)
  have hN : 0 < N := sqrt_pos.2 (by positivity)
  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  let v j := keptBound D E Sz η j / N
  let Dg j := (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn
  set d := (D.d₁ + η) / Dn
  have hD : ∀ j, 0 < Dg j := fun j => div_pos (hDj j) hDn
  have hd : 0 < d := div_pos (by linarith) hDn
  let b := d * ∑ i, max 0 (v i) / Dg i
  let f t := d * (∑ i, max 0 (v i - t) / Dg i) - t
  have hb : 0 ≤ b := mul_nonneg hd.le (sum_nonneg fun i _ => div_nonneg (le_max_left _ _) (hD i).le)
  have hfb : f b ≤ 0 := by
    dsimp [f, b]; nlinarith [show ∑ i, max 0 (v i - b) / Dg i ≤ ∑ i, max 0 (v i) / Dg i from
      sum_le_sum fun i _ => by have := hD i; gcongr; linarith]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hb (by fun_prop : Continuous f).continuousOn
    ⟨hfb, by simpa [f, b] using hb⟩
  let a i := max 0 (v i - t) / Dg i
  have ha : ∀ i, 0 ≤ a i := fun i => div_nonneg (le_max_left _ _) (hD i).le
  have htfix : t = d * ∑ i, a i := by dsimp [f, a] at hft ⊢; linarith
  have hcoord i : a i * v i = Dg i * a i ^ 2 + t * a i := by
    have := (hD i).ne'; dsimp [a]; field_simp
    rcases le_total 0 (v i - t) with h | h; · rw [max_eq_right h]; ring
    · simp [h]
  set Q := ∑ i, Dg i * a i ^ 2 + d * (∑ i, a i) ^ 2
  have he i : max 0 (v i - t) ^ 2 / Dg i = Dg i * a i ^ 2 := by have := (hD i).ne'; dsimp [a]; field_simp
  have hcost : t ^ 2 / d + ∑ i, max 0 (v i - t) ^ 2 / Dg i = Q := by dsimp [Q]; simp_rw [he, htfix]; field_simp; ring
  have hsum0 : 0 ≤ ∑ i, max 0 (v i - t) ^ 2 / Dg i := sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hD i).le
  have : 0 ≤ Q := by rw [← hcost]; linarith [div_nonneg (sq_nonneg t) hd.le]
  have hNQ : N * Q ≤ max 0 (∑ j, a j * response D E j) := by
    have hdot : N * Q = ∑ i, a i * keptBound D E Sz η i := by
      rw [show Q = ∑ i, a i * v i by symm; simp_rw [hcoord, sum_add_distrib, ← mul_sum, htfix]; ring,
        mul_sum]
      exact sum_congr rfl fun i _ => by dsimp [v]; have := hN.ne'; field_simp
    exact hdot.trans_le <| le_max_of_le_right <| sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (hq₂ q (by omega) _ (hχ j) _ _
        ((abs_sub _ _).trans (add_le_add_right (single_le_sum (f := (|·|)) (fun _ _ => abs_nonneg _) (hΔ j)) _))
        (by linarith [hγ j, log_natCast_nonneg q]) _ (hSz j) (hsep j) (hK j)) (ha j)
  have hQ1 : Q ≤ 1 := by
    have hsq : (N * Q) ^ 2 ≤ N ^ 2 * Q := by
      grw [hNQ, hq₁ q (by omega) T hT0 hTl hsafe ι E hχ hγ hΔ hinj a ha]
      rw [sq_sqrt (by positivity : 0 ≤ (1 + η) * D.IB * Dn)]; dsimp [Q, Dg, d]
      have := hDn.ne'; simp_rw [div_mul_eq_mul_div, ← sum_div, ← add_div]; exact le_of_eq (by field_simp)
    rw [mul_pow] at hsq; nlinarith [le_of_mul_le_mul_left hsq (sq_pos_of_pos hN)]
  exact ⟨t, ht.1, le_sqrt_of_sq_le ((div_le_one hd).1 (by linarith)), by dsimp [v, Dg] at hcost; linarith⟩

theorem single_zero_threshold {η} (hη : 0 < η) :
    ∃ M, 0 < M ∧ ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ q₀, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T, 0 ≤ T → T ≤ log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ (ρ : _ → _) (hi : _ → _),
          (∀ j, LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            ‖1 + E.γ j * I - ρ j‖ ≤ δ ∧ (1 - (ρ j).re) * log q ≤ hi j) →
          (∀ j ρ', LFunction (E.χ j) ρ' = 0 → ‖1 + E.γ j * I - ρ'‖ ≤ δ → ρ' ≠ ρ j →
            (1 - ρ'.re) * log q < D.s - E.δ j → M ≤ |E.γ j - ρ'.im| * log q) →
          (∀ j, (∑ᶠ ρ' ∈ {ρ' | LFunction (E.χ j) ρ' = 0 ∧ ‖1 + E.γ j * I - ρ'‖ ≤ δ ∧
              ρ' ≠ ρ j ∧ (1 - ρ'.re) * log q < D.s - E.δ j}, zmult (E.χ j) ρ') ≤ K₀) →
          ∀ Dn, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ, 0 ≤ τ ∧ τ ≤ √((D.d₁ + η) / Dn) ∧
              ∑ j, max 0 (((laplace D.f ↑(hi j - (D.s - E.δ j))).re - D.f 0 / 6 - η) /
                  √((1 + η) * D.IB * Dn) - τ) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  gconvert graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη using 21 with
    M _ δ _ _ q₀ q _ _ T _ _ _ ι _ E hχ _ _ _ h
  intro ρ hi hρ hsep hK Dn hDn hDj
  obtain ⟨τ, hτ0, hτd, hT⟩ := h (fun j => {ρ j}) (by simp_all)
    (fun j ρ' h1 h2 h3 => hsep j ρ' h1 h2 (by simpa using h3)) (fun j => by simpa using hK j) Dn hDn hDj
  refine ⟨τ, hτ0, hτd, (sum_le_sum fun j _ => ?_).trans hT⟩
  have := hD.IB_pos; have := hDj j
  have := keptBound_single D hD hf2 E (fun j => {ρ j}) η j (hχ j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2
  gcongr

theorem builder_threshold {η} (hη : 0 < η) {Iu Du} (hIu : D.IB ≤ Iu) (hDu : 0 < Du) :
    ∃ M, 0 < M ∧ ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ q₀, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T, 0 ≤ T → T ≤ log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz,
          (∀ j, ∀ ρ ∈ Sz j, LFunction (E.χ j) ρ = 0 ∧ ‖1 + E.γ j * I - ρ‖ ≤ δ) →
          (∀ j ρ, LFunction (E.χ j) ρ = 0 → ‖1 + E.γ j * I - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ | LFunction (E.χ j) ρ = 0 ∧ ‖1 + E.γ j * I - ρ‖ ≤ δ ∧
              ρ ∉ Sz j ∧ (1 - ρ.re) * log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ r De : _ → _, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            (∀ j, D.Dδ (E.δ j) - D.d₁ + pairExcess D E j ≤ De j) →
            ∃ τ, 0 ≤ τ ∧ τ ≤ √((1 + η) * (D.d₁ / Du + η)) ∧
              ∑ j, max 0 (r j / √(Iu * Du) - η - τ) ^ 2 / ((1 + η) * De j / Du) ≤
                1 - τ ^ 2 / ((1 + η) * (D.d₁ / Du + η)) := by
  have hIB := hD.IB_pos
  set N := √(D.IB * Du)
  have hNpos : 0 < N := sqrt_pos.2 (by positivity)
  set η' := η * min 1 (min N Du)
  have hη'pos : 0 < η' := by positivity
  have hη'η : η' ≤ η := mul_le_of_le_one_right hη.le (min_le_left _ _)
  have hη'N : η' ≤ η * N := by dsimp [η']; grw [min_le_right, min_le_left]
  gconvert graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη'pos using 25 with
    M _ δ _ _ q₀ q _ _ T _ _ _ ι _ E _ _ _ _ Sz _ _ _ h
  intro r De hr hDj hDe
  have hDnpos : 0 < Du / (1 + η') := by positivity
  obtain ⟨τ, hτ0, hτd, hT⟩ := h (Du / (1 + η')) hDnpos hDj
  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  rw [show √((1 + η') * D.IB * (Du / (1 + η'))) = N from congrArg (√·) (by field_simp)] at hT
  have hdiv {x y} (hx : 0 ≤ x) (hxy : x ≤ y) : x / (Du / (1 + η')) ≤ (1 + η) * y / Du := by
    rw [div_div_eq_mul_div, mul_comm _ (1 + η')]; grw [hη'η, hxy]
  have hdle : (D.d₁ + η') / (Du / (1 + η')) ≤ (1 + η) * (D.d₁ / Du + η) :=
    (hdiv (y := D.d₁ + η * Du) (by positivity) (by
      have : η' ≤ η * Du := by dsimp [η']; grw [min_le_right, min_le_right]
      linarith)).trans_eq (by field_simp)
  refine ⟨τ, hτ0, hτd.trans (sqrt_le_sqrt hdle), (sum_le_sum fun j _ => Cert.term_le
    (by
      by_cases hr0 : r j ≤ 0
      · exact .inr (by grw [hr0]; simp [hη.le])
      · left; have := (not_le.1 hr0).le
        grw [← sqrt_le_sqrt (show D.IB * Du ≤ Iu * Du by gcongr), (hr j).resolve_right hr0,
          ← (div_le_iff₀ hNpos).2 hη'N]
        rw [← sub_div, show keptBound D E Sz 0 j - η' = keptBound D E Sz η' j by unfold keptBound; ring])
    hτ0 (div_pos (hDj j) hDnpos) (hdiv (hDj j).le (hDe j))).trans
    (hT.trans (by have := div_pos (by linarith : 0 < D.d₁ + η') hDnpos; grw [← hdle]))⟩

end Threshold


theorem zmult_conj {q} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a, conj (χ a) = χ a) ρ :
    zmult χ (conj ρ) = zmult χ ρ := by
  have hL := differentiable_LFunction hχ
  let cc (g : ℂ → ℂ) z := conj (g (conj z))
  have hcc {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) : AnalyticAt ℂ (cc g) (conj z₀) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt] at hg ⊢
    filter_upwards [(Complex.continuous_conj.tendsto (conj z₀)).eventually (by simpa using hg)] with z
      using differentiableAt_conj_conj_iff.2
  have heq : cc (LFunction χ) = LFunction χ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.2 fun z => differentiableAt_conj_conj_iff.2 (hL _)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.2 hL) (z₀ := 2) <|
      eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
        fun s hs => by
          dsimp [cc]
          rw [LFunction_eq_LSeries χ (by simpa using hs), LFunction_eq_LSeries χ hs, LSeries, LSeries, Complex.conj_tsum]
          refine tsum_congr fun n => ?_
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
              ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity), Complex.conj_natCast]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lfunc_order_ne_top hχ ρ)
  obtain ⟨g, hg, hg0, hfg⟩ := (hL.analyticAt ρ).analyticOrderAt_eq_natCast.1 hn.symm
  have hord : analyticOrderAt (LFunction χ) (conj ρ) = n := by
    rw [← heq]
    refine (hcc (hL.analyticAt ρ)).analyticOrderAt_eq_natCast.2 ⟨_, hcc hg, by simpa [cc] using hg0, ?_⟩
    filter_upwards [(Complex.continuous_conj.tendsto (conj ρ)).eventually (by simpa using hfg)] with z hz
      using by simp [cc, hz]
  simp [zmult, analyticOrderNatAt, hord, ← hn]

theorem keptBound_pair_neg_real {q} [NeZero q] {ι : Type*} (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) Sz j (hχ : E.χ j ≠ 1)
    (hreal : ∀ a, conj (E.χ j a) = E.χ j a) {ρ hi C}
    (hne : ρ ≠ conj ρ) (hS : Sz j = {ρ, conj ρ}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * log q ≤ hi) (hρ' : LFunction (E.χ j) (conj ρ) = 0)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) (conj ρ)) :
    (laplace D.f ↑(hi - (D.s - E.δ j))).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ↑(hi - (D.s - E.δ j))).re - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC

theorem pairExcess_eq_zero (D : NearData) (hD : D.Valid) (hg0 : 0 < D.g 0) :
    ∃ M, 0 < M ∧ ∀ {q} {ι : Type} [Fintype ι] (E : Entries q ι), (∀ j, E.δ j ∈ D.Δ) →
      ∀ j, (∀ k, k ≠ j → E.χ k = E.χ j → M ≤ |E.γ j - E.γ k| * log q) →
        pairExcess D E j = 0 := by
  classical
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 (|D.s₁| + 2 * ∑ δ ∈ D.Δ, δ)
    (show 0 < D.d₁ by unfold NearData.d₁; linarith)
  refine ⟨M, hM, fun {q} _ _ E hΔ j hsep => sum_eq_zero fun k hk => max_eq_left ?_⟩
  obtain ⟨hkj, hχ⟩ := (mem_filter.1 hk).2
  have h := hdec (-(D.s₁ - E.δ j - E.δ k))
    ⟨by linarith [le_abs_self D.s₁, hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k), sum_nonneg fun δ hδ => hD.Δ_nonneg δ hδ],
     by linarith [neg_le_abs D.s₁, single_le_sum hD.Δ_nonneg (hΔ j), single_le_sum hD.Δ_nonneg (hΔ k)]⟩
    ((E.γ j - E.γ k) * log q)
    (by simpa [abs_mul, abs_of_nonneg (log_natCast_nonneg _)] using hsep k hkj hχ)
  linarith [(Complex.re_le_norm _).trans h]

end GradedNear
