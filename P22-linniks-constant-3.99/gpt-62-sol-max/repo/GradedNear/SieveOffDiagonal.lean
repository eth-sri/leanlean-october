module

public import GradedNear.SieveBasic
public import GradedNear.Basic
public import GradedNear.BurgessReduction

/-!
# The off-diagonal sieve estimate

Open the Selberg square in the prefix sums, applying Burgess on each progression of multiples
of `[d,e]`. Apply Abel summation in logarithmic coordinates. Group pairs by their least common
multiple. A small power from the divisor bound and the logarithmic factors
are absorbed by the saving from the progression bounds.
-/

@[expose] public section

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace GradedNear

/-! ### The Selberg weights -/

/-- The weights satisfy `|ψ_d| ≤ 1`. -/
private lemma abs_grahamWeight_le_one (V : ℝ) {d : ℕ} (hd : 0 < d) : |grahamWeight V d| ≤ 1 := by
  unfold grahamWeight
  split_ifs with h
  · have hlog := Real.log_le_log (Nat.cast_pos.mpr hd) h
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hN := Real.log_natCast_nonneg d
    have hV := hN.trans hlog
    rw [Real.log_div ((Nat.cast_pos.mpr hd).trans_le h).ne' (by positivity), abs_div, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hlog), abs_of_nonneg hV]
    apply div_le_one_of_le₀ _ hV
    grw [hμ, one_mul, sub_le_self _ hN]; linarith
  · simp

/-! ### The lcm sum -/

private noncomputable def sievePairs (V : ℝ) := Ioc 0 ⌊V⌋₊ ×ˢ Ioc 0 ⌊V⌋₊

private noncomputable def lcmSum (V : ℝ) : ℝ :=
  ∑ p ∈ sievePairs V, (p.1.lcm p.2 : ℝ) ^ (-(2 / 3 : ℝ))

-- Group by lcm, then take out a power of the upper bound, leaving a summable series.
private lemma lcm_bound {ρ : ℝ} (hρ : 0 < ρ) : ∃ C : ℝ, ∀ V : ℝ, 0 < V →
    lcmSum V ≤ C * (V ^ 2) ^ (1 / 3 + ρ) := by
  obtain ⟨C, hC, hDiv⟩ := card_divisors_le_rpow (show 0 < ρ / 4 by positivity)
  let f (l : ℕ) := (l : ℝ) ^ (-(1 + ρ / 2))
  have hs : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨C ^ 2 * ∑' l, f l, fun V hV => ?_⟩
  let T := Ioc 0 (⌊V⌋₊ ^ 2)
  let lcm (p : ℕ × ℕ) := p.1.lcm p.2
  have hcut p (hp : p ∈ sievePairs V) : lcm p ∈ T := by
    obtain ⟨⟨ha, hb⟩, hc, hd⟩ := by simpa [sievePairs] using hp
    exact mem_Ioc.mpr ⟨Nat.lcm_pos ha hc, (Nat.lcm_le_mul ha hc).trans (by rw [sq]; gcongr)⟩
  rw [lcmSum, ← sum_fiberwise_of_maps_to' hcut (fun l => (l : ℝ) ^ (-(2 / 3 : ℝ)))]
  calc
    _ ≤ ∑ l ∈ T, C ^ 2 * (V ^ 2) ^ (1 / 3 + ρ) * f l := by
      refine sum_le_sum fun l hl => ?_
      obtain ⟨hl, hu⟩ := mem_Ioc.mp hl
      have hl' : (0 : ℝ) < l := by positivity
      have hcard : ((sievePairs V).filter (fun p => lcm p = l)).card ≤ l.divisors.card ^ 2 := by
        rw [sq, ← card_product]
        exact card_le_card fun p hp => by grind [Nat.dvd_lcm_left, Nat.dvd_lcm_right]
      simp only [sum_const, nsmul_eq_mul]
      grw [hcard, Nat.cast_pow, hDiv l hl.ne']
      calc
        _ = C ^ 2 * (l : ℝ) ^ (1 / 3 + ρ) * f l := by
          dsimp [f]
          rw [mul_pow, ← Real.rpow_mul_natCast hl'.le]
          simp only [mul_assoc, ← Real.rpow_add hl']
          push_cast; ring_nf
        _ ≤ _ := by
          gcongr
          exact (by exact_mod_cast hu : (l : ℝ) ≤ (⌊V⌋₊ : ℝ)^2).trans
            (by gcongr; exact Nat.floor_le hV.le)
    _ ≤ _ := by rw [← mul_sum]; grw [hs.sum_le_tsum _ (fun l _ => show 0 ≤ f l by dsimp [f]; positivity)]; rw [mul_right_comm]

/-! ### Opening the square -/

/-- `Σ_{d ∣ n} ψ_d = Σ_{d ≤ ⌊V⌋} [d ∣ n] ψ_d` for `n ≠ 0`. -/
lemma sum_divisors_grahamWeight (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, grahamWeight V d =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, (if d ∣ n then grahamWeight V d else 0) := by
  rw [← Finset.sum_filter]
  symm
  refine sum_subset (fun d hd => Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hn⟩)
    (fun d hd hnot => ?_)
  have hV : ⌊V⌋₊ < d := by grind [Nat.pos_of_mem_divisors, Nat.dvd_of_mem_divisors]
  simp [grahamWeight, (Nat.lt_of_floor_lt hV).not_ge]

/-- Opening the square and swapping the sums. -/
private lemma sum_sieveNu_mul (V : ℝ) (R : Finset ℕ) (hR : ∀ n ∈ R, n ≠ 0) (F : ℕ → ℂ) :
    ∑ n ∈ R, (sieveNu V n : ℂ) * F n =
      ∑ p ∈ sievePairs V, ((grahamWeight V p.1 * grahamWeight V p.2 : ℝ) : ℂ) *
        ∑ n ∈ R, (if Nat.lcm p.1 p.2 ∣ n then F n else 0) := by
  rw [sievePairs, sum_product]
  unfold sieveNu
  rw [sum_congr rfl (fun n hn => by rw [sum_divisors_grahamWeight V (hR n hn)])]
  simp_rw [sq, sum_mul_sum, ofReal_sum, sum_mul, mul_sum, sum_comm (s := R)]
  refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => sum_congr rfl fun n _ => ?_
  simp_rw [Nat.lcm_dvd_iff]
  split_ifs <;> simp_all

/-! ### Assembly -/

theorem sieve_offdiag (hBur : BurgessBound) {ε' t t' : ℝ} (hε' : 0 < ε')
    (ht : 1 / 3 + 2 * ε' < t) (htt' : t ≤ t') {r : ℝ} (hr : 0 < r) :
    ∀ᶠ q : ℕ in atTop, ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ δ τ : ℝ, 0 ≤ δ → δ ≤ Real.log q → |τ| ≤ Real.log q →
        ‖∑ n ∈ sieveInterval q t t',
          (sieveWeight ((q : ℝ) ^ ((t - 1 / 3) / 2 - ε')) n : ℂ) * phaseWeight ψ δ τ n‖ / Real.log q ≤ r := by
  let v := (t - 1 / 3) / 2 - ε'
  have hv : 0 < v := by dsimp [v]; linarith
  have ht₀ : 0 ≤ t' := by linarith
  obtain ⟨C, hC⟩ := hBur (ε' / 3) (by positivity)
  let u := ε' / (12 * v)
  obtain ⟨C', hDiv⟩ := lcm_bound (ρ := u) (by dsimp [u]; positivity)
  let G := (2 + 3 * t') * t' * C * C'
  have hlim : Tendsto (fun q : ℕ => G * (Real.log q ^ 3 / (q : ℝ) ^ (ε' / 6))) atTop (𝓝 0) := by
    simpa using (((isLittleO_log_rpow_rpow_atTop 3 (by positivity : 0 < ε' / 6)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop).const_mul G
  filter_upwards [eventually_ge_atTop 2, tendsto_log_nat_atTop.eventually_ge_atTop 1,
    hlim.eventually_le_const hr] with q hq hP hpow
  intro ψ hψ δ τ hδ₀ hδ₁ hτ
  have hℓ := log_q_pos hq
  have hβ₀ := div_nonneg hδ₀ hℓ.le
  let P := Real.log q
  have hq₁ : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (by omega)
  have hq₀ := zero_lt_one.trans_le hq₁
  let K := C * (q : ℝ) ^ (1 / 9 + ε' / 3)
  let : NeZero q := ⟨by omega⟩
  obtain ⟨hK, hBurq⟩ := char_sum_bound ψ hψ (K := K) fun N H _ hH hHq => hC q ψ hψ N H hH hHq
  let s := spectralPoint q (-δ) τ
  have hs' : ‖s‖ ≤ 3 * P := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_real, norm_mul, norm_I, mul_one, Real.norm_eq_abs, neg_div, sub_neg_eq_add,
      abs_of_nonneg (add_nonneg zero_le_one hβ₀)]
    linarith [(div_le_one hℓ).mpr hδ₁]
  let V := (q : ℝ) ^ v
  let A := (q : ℝ) ^ t
  let B := (q : ℝ) ^ t'
  have hA : 1 ≤ A := Real.one_le_rpow hq₁ (by linarith)
  have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le hq₁ htt'
  -- Burgess bounds the unweighted prefixes after opening the sieve square.
  let E := K * A ^ (-(1 / 3 : ℝ)) * lcmSum V
  let L := Real.log B
  let c (n : ℕ) := (sieveNu V n : ℂ) * ψ n
  have hAp : 0 < A := by linarith
  have hpref t (ht : t ∈ Set.Icc A B) : ‖∑ n ∈ realIco A t, c n‖ ≤ E * t := by
    have htp := hAp.trans_le ht.1
    have := Nat.ceil_pos.mpr htp
    dsimp only [c, realIco]
    rw [sum_sieveNu_mul V _ (by grind)]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ p ∈ sievePairs V, (K * A ^ (-(1 / 3 : ℝ)) * t) * (p.1.lcm p.2 : ℝ) ^ (-(2 / 3 : ℝ)) := by
        gcongr with p hp
        obtain ⟨hd, he⟩ := mem_product.mp hp
        let l := p.1.lcm p.2
        have hl : 0 < l := Nat.lcm_pos (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, ← sum_filter, sum_char_dvd ψ hl, norm_mul]
        grw [abs_grahamWeight_le_one V (mem_Ioc.mp hd).1, abs_grahamWeight_le_one V (mem_Ioc.mp he).1, ψ.norm_le_one]
        simp only [one_mul]
        have hdiv : ↑((⌈t⌉₊ - 1) / l - (⌈A⌉₊ - 1) / l : ℕ) ≤ t / l := by
          grw [Nat.sub_le, Nat.cast_div_le]
          gcongr
          exact (Nat.lt_ceil.mp (by omega)).le
        refine (hBurq _ _).trans ?_
        calc
          _ ≤ K * (t / l) ^ (2 / 3 : ℝ) := by gcongr
          _ ≤ _ := by
            rw [Real.div_rpow htp.le (by positivity), div_eq_mul_inv, ← Real.rpow_neg (by positivity),
              show (2 / 3 : ℝ) = -(1 / 3) + 1 by norm_num, Real.rpow_add htp, Real.rpow_one]
            grw [Real.rpow_le_rpow_of_nonpos hAp ht.1 (by norm_num : -(1 / 3 : ℝ) ≤ 0)]
            simp [l, mul_assoc]
      _ = _ := by simp only [E, lcmSum, ← mul_sum]; ring
  have hab := wt_sum_norm_le s (by simpa [s, neg_div] using hβ₀) c hA hAB hpref
  change ‖∑ n ∈ realIco A B, (sieveWeight V n : ℂ) * phaseWeight ψ δ τ n‖ / P ≤ _
  rw [sum_congr rfl (g := fun n => wt s n * c n) ?_]
  swap
  · intro n hn
    have H := phaseWeight_term ψ (mem_realIco.mp hn).1 0 δ τ
    simp only [zero_sub, zero_mul, Real.exp_zero, ofReal_div, ofReal_one, ofReal_natCast] at H
    dsimp [wt, c, s, sieveWeight]
    push_cast
    linear_combination -Complex.log (n : ℂ) * (sieveNu V n : ℂ) * H
  refine (div_le_self (norm_nonneg _) hP).trans (hab.trans ?_)
  have hΛ : L + (L - Real.log A + ‖s‖ * (L ^ 2 - Real.log A ^ 2) / 2) ≤ (2 + 3 * t') * t' * P ^ 3 := by
    grw [sub_le_self L (Real.log_nonneg hA), sub_le_self _ (sq_nonneg _), hs']
    rw [show L = t' * P from Real.log_rpow hq₀ t']
    nlinarith [mul_nonneg (mul_nonneg ht₀ hℓ.le) (sub_nonneg.mpr (one_le_pow₀ (n := 2) hP))]
  have hexp : (q : ℝ) ^ (1 / 9 + ε' / 3) * A ^ (-(1 / 3 : ℝ)) * (V ^ 2) ^ (1 / 3 + u) =
      (q : ℝ) ^ (-(ε' / 6)) := by
    dsimp [A, V]
    simp_rw [← Real.rpow_natCast_mul (Real.rpow_nonneg hq₀.le v), ← Real.rpow_mul hq₀.le,
      ← Real.rpow_add hq₀, Nat.cast_ofNat]
    congr 1
    grind
  have : 0 ≤ (2 + 3 * t') * t' * P ^ 3 := by positivity
  have hE : 0 ≤ E := by unfold E lcmSum; positivity
  grw [hΛ]
  unfold E
  grw [hDiv V (by dsimp [V]; positivity)]
  convert hpow using 1
  rw [div_eq_mul_inv (Real.log q ^ (3 : ℕ)), ← Real.rpow_neg hq₀.le, ← hexp]
  dsimp [G, K, P]; ring

end GradedNear
