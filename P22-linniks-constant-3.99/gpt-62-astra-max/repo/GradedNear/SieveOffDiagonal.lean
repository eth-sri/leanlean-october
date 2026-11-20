module

public import GradedNear.SieveAbel
public import GradedNear.Basic
public import GradedNear.BurgessReduction

/-!
# (C) The off-diagonal of the sieve part: Burgess's bound and Abel summation

Open the Selberg square over `d,e ≤ V`. On multiples of `l = lcm d e` the effective
Burgess length `n/l` is at least `X = q^(1/3 + 2ε')`. Thus the partial sums are bounded
by `K X^(-1/3) n/l`. Summation by parts against `log n · n^(-s)` and the reciprocal lcm
sum cost only powers of `log q`, which fit in the power saving from `X`.
-/

@[expose] public section

open Complex Finset Filter
open scoped ArithmeticFunction.Moebius

namespace GradedNear

-- The Burgess length exponent and its complementary power.
local notation "θ" => (2/3 : ℝ)
local notation "α" => (1/3 : ℝ)

/-! ### The Selberg weights -/

/-- On its support the logarithmic factor is between zero and one. -/
lemma weight_bound {V : ℝ} (hV : 0 ≤ V) {d : ℕ} (hd : d ∈ Ioc 0 ⌊V⌋₊) : |grahamWeight V d| ≤ 1 := by
  obtain ⟨hd,h⟩ := mem_Ioc.mp hd
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdV := (Nat.cast_le.mpr h).trans (Nat.floor_le hV)
  have hlog := Real.log_nonneg (hd'.trans hdV)
  have hsub := Real.log_le_log (by positivity) hdV
  rw [grahamWeight, ite_eq_left hdV, Real.log_div (by linarith) (by positivity), abs_div, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hsub), abs_of_nonneg hlog]
  apply div_le_one_of_le₀ _ hlog
  grw [show |(μ d : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)]
  all_goals linarith [Real.log_nonneg hd']

/-! ### Summation by parts -/

/-- A harmonic-sum bound. -/
lemma harmonic_bound {S : Finset ℕ} {b : ℕ} (h : S ⊆ Icc 1 b) :
    ∑ n ∈ S, (1 : ℝ) / n ≤ 1 + Real.log b :=
  (sum_le_sum_of_subset_of_nonneg h (by simp)).trans
    (by simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log b)

/-! ### The lcm sum -/

/-- Sending `(d,e)` to `((d,e), d/(d,e), e/(d,e))` injects the sum into a product
of three harmonic sums: the product of the three coordinates is `[d,e]`. -/
lemma lcm_harmonic (N : ℕ) : ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 N, (d.lcm e : ℝ)⁻¹ ≤
    (1 + Real.log N)^3 := by
  let S := Ioc 0 N
  let split (x : ℕ × ℕ) := (x.1.gcd x.2, x.1 / x.1.gcd x.2, x.2 / x.1.gcd x.2)
  let join (t : ℕ × ℕ × ℕ) := (t.2.1 * t.1, t.2.2 * t.1)
  have inv : Function.LeftInverse join split := fun (d,e) => by
    simp [join, split, Nat.div_mul_cancel, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
  have hdvd {d g : ℕ} (hd : d ∈ S) (hg : g ∣ d) : d/g ∈ S := by
    obtain ⟨hd, hm⟩ := mem_Ioc.mp hd
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hd hg) (Nat.pos_of_dvd_of_pos hg hd), (Nat.div_le_self ..).trans hm⟩
  rw [← sum_product']
  calc _ ≤ ∑ t ∈ S ×ˢ (S ×ˢ S), (1/t.1 : ℝ) * (1/t.2.1 * (1/t.2.2)) := by
          apply sum_le_sum_of_injOn split inv.injective.injOn _ _ (by bound)
          · rintro _ hx; obtain ⟨⟨d,e⟩, hp, rfl⟩ := mem_image.mp hx
            obtain ⟨hd, he⟩ := mem_product.mp hp
            exact mem_product.mpr ⟨mem_Ioc.mpr ⟨Nat.gcd_pos_of_pos_left _ (mem_Ioc.mp hd).1,
              (Nat.gcd_le_left _ (mem_Ioc.mp hd).1).trans (mem_Ioc.mp hd).2⟩,
              mem_product.mpr ⟨hdvd hd (Nat.gcd_dvd_left ..), hdvd he (Nat.gcd_dvd_right ..)⟩⟩
          · rintro ⟨d,e⟩ _; 
            rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc _ (Nat.gcd_dvd_right d e)]
            simp [← mul_inv, ← Nat.cast_mul]
            rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)]
       _ ≤ _ := by
          simp_rw [sum_product, ← mul_sum, ← sum_mul]
          have h := harmonic_bound (show S ⊆ Icc 1 N from fun _ h => h)
          rw [pow_succ, sq, mul_assoc]; gcongr

/-! ### Opening the square -/

/-- `Σ_{d ∣ n} ψ_d = Σ_{d ≤ ⌊V⌋} [d ∣ n] ψ_d` for `n ≠ 0`. -/
lemma sum_divisors_grahamWeight (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, grahamWeight V d =
      ∑ d ∈ Ioc 0 ⌊V⌋₊, (if d ∣ n then grahamWeight V d else 0) := by
  rw [← sum_filter]
  symm
  apply sum_subset
  · intro d hd
    aesop
  · intro d hd hnot
    exact ite_eq_right fun h => hnot (mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_floor h⟩, Nat.dvd_of_mem_divisors hd⟩)

/-- Opening the square and swapping the sums. -/
lemma sum_sieveNu_mul (V : ℝ) (R : Finset ℕ) (hR : ∀ n ∈ R, n ≠ 0) (F : ℕ → ℂ) :
    ∑ n ∈ R, (sieveNu V n : ℂ) * F n =
      ∑ d ∈ Ioc 0 ⌊V⌋₊, ∑ e ∈ Ioc 0 ⌊V⌋₊,
        ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ R, (if Nat.lcm d e ∣ n then F n else 0) := by
  simp_rw [mul_sum]; rw [sum_comm_cycle]
  refine sum_congr rfl fun n hn => ?_
  rw [sum_divisors_grahamWeight V (hR n hn), sq]
  simp_rw [ofReal_mul, ofReal_sum, sum_mul_sum, sum_mul]
  refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff]

/-! ### Assembly -/

/-- Open the sieve *in the partial sum*. All pairs benefit from the same lower
bound `X` on the effective Burgess length `x/l`; summing `1/l` costs at most `R³`. -/
lemma sieve_partial {q : ℕ} {χ : DirichletCharacter ℂ q} {K X V R : ℝ} (hK : 0 ≤ K)
    (h : CharBound χ K) (hX : 0 < X) (hV : 0 ≤ V) {A x : ℝ} (hA : 0 < A) (hXx : X*V^2 ≤ x)
    (hv : 1+Real.log ⌊V⌋₊ ≤ R) : ‖prefixSum (fun n => (sieveNu V n : ℂ)*χ n) A x‖ ≤ K*X^(-α)*R^3*x := by
  let S := Ioc 0 ⌊V⌋₊
  have inV {n : ℕ} (hn : n ∈ S) := (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le hV)
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ceil_pos.mpr hA).ne'
  simp at ha
  have hx0 := (mul_nonneg hX.le (sq_nonneg V)).trans hXx
  rw [prefixSum, ha, Icc_add_one_left_eq_Ioc, sum_sieveNu_mul _ _ (fun n hn => by aesop)]
  calc _ ≤ ∑ d ∈ S, ∑ e ∈ S, (K*X^(-α)*x) * (d.lcm e : ℝ)⁻¹ := by
        refine norm_sum_le_of_le _ fun d hd => norm_sum_le_of_le _ fun e he => ?_
        have hl := Nat.lcm_pos (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1
        have hsmall : (d.lcm e : ℝ) ≤ V^2 := calc
          _ ≤ (d:ℝ)*e := by exact_mod_cast Nat.lcm_le_mul (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1
          _ ≤ _ := by rw [sq]; bound
        have hlen : X ≤ x/(d.lcm e : ℝ) := (le_div_iff₀ (by exact_mod_cast hl)).mpr <| (by gcongr : X*_ ≤ X*V^2).trans hXx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        grw [weight_bound hV hd, weight_bound hV he, h.multiples hl, Nat.cast_le.mpr (Nat.sub_le _ _), Nat.cast_div_le, Nat.floor_le hx0]
        rw [show θ = -α+1 by norm_num, Real.rpow_add (hX.trans_le hlen), Real.rpow_one]
        grw [Real.rpow_le_rpow_of_nonpos hX hlen (by norm_num : -α ≤ 0)]
        exact le_of_eq (by ring)
       _ ≤ _ := by simp_rw [← mul_sum]; grw [lcm_harmonic, hv]; linarith

/-- One small power simultaneously dominates the logarithms of all cell parameters. -/
lemma log_cap (c : ℝ) {r : ℝ} (hr : 0 < r) : ∀ᶠ q : ℕ in atTop,
    2 ≤ q ∧ 4 + (|c|+1)*Real.log q ≤ (q : ℝ)^r := by
  have h := isLittleO_log_rpow_atTop hr
  have cap := (((Real.isLittleO_const_log_atTop (c := (4:ℝ))).trans h).add
    (h.const_mul_left (|c|+1))).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, cap.bound zero_lt_one] with q hq hcap
  refine ⟨hq, (le_abs_self _).trans ?_⟩
  simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) r)] using hcap

theorem sieve_offdiag (hBur : BurgessPrimitive) {ε' t u ε : ℝ} (hε' : 0 < ε')
    (ht : 1/3 + 2*ε' < t) (htu : t ≤ u) (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop,
    ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ s : ℂ, 1 ≤ s.re → ‖s‖ ≤ 2 + Real.log q →
      ‖∑ n ∈ cell q t u, sieveTerm ((q:ℝ)^((t-1/3)/2 - ε')) ψ s n‖ ≤ ε*Real.log q := by
  obtain ⟨C, hC, bur⟩ := burgess_uniform hBur (show 0 < ε'/3 by positivity)
  filter_upwards [log_cap u (show 0 < ε'/18 by positivity),
    log_level_atTop.eventually_ge_atTop (3*C/ε)]
    with q ⟨hq,hcap⟩ hbudget ψ hψ s hs hsn
  have hq1 : (1 : ℝ) ≤ q := by bound
  have hq0 : (0 : ℝ) < q := by positivity
  have hℓ := Real.log_nonneg hq1
  let K := C * (q : ℝ)^(1/9 + ε'/3)
  have hK : 0 ≤ K := by positivity
  set δ := (t-1/3)/2 - ε'
  set A := (q : ℝ)^t
  set B := (q : ℝ)^u
  set V := (q : ℝ)^δ
  have hV : 1 ≤ V := Real.one_le_rpow hq1 (by bound)
  have hA : 1 ≤ A := Real.one_le_rpow hq1 (by linarith)
  have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le hq1 htu
  let X := (q : ℝ) ^ (1/3 + 2*ε')
  let R := (q : ℝ)^(ε'/18)
  have hb : 1+Real.log B ≤ R := by
    rw [Real.log_rpow hq0]; linarith [mul_le_mul_of_nonneg_right (le_abs_self u) hℓ]
  have hv : 1+Real.log ⌊V⌋₊ ≤ R := by
    apply le_trans _ hb; gcongr
    · exact_mod_cast Nat.floor_pos.mpr hV
    · exact (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hq1 (by dsimp [δ]; linarith))
  have base : X * V^2 = A := by
    rw [← Real.rpow_natCast _ 2]; simp_rw [V, X, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
    congr 1; dsimp [δ]; ring
  have hp x (hx : x ∈ Set.Icc A B) : ‖prefixSum (fun n => (sieveNu V n : ℂ)*ψ n) A x‖ ≤ K*X^(-α)*R^3*x :=
    sieve_partial hK (bur (by omega) _ hψ) (by positivity) (by positivity) (by positivity) (base.le.trans hx.1) hv
  have H := wt_bound hA hAB (by positivity) hp hs
  refine le_trans (le_trans (le_of_eq ?_) H) ?_
  · dsimp [prefixSum, sieveTerm, cell]; congr 1; apply sum_congr rfl; intros; ring
  have hR : 1 ≤ R := by linarith [Real.log_nonneg (hA.trans hAB)]
  refine le_trans (b := 3*(K*X^(-α)*R^3)*R^3) ?_ ?_
  · rw [mul_comm 3 (K*_ * _), mul_assoc (K*_ * _)]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    grw [sub_le_self _ (sq_nonneg _), show Real.log B ≤ R by linarith, hsn.trans (by nlinarith [abs_nonneg u] : _ ≤ R)]
    all_goals first | exact Real.log_nonneg (hA.trans hAB) | nlinarith [mul_le_mul_of_nonneg_right (one_le_pow₀ hR (n := 2)) (zero_le_one.trans hR)]
  apply le_trans (le_of_eq ?_) (by simpa [mul_comm] using (div_le_iff₀ hε).mp hbudget : 3*C ≤ _)
  rw [show 3*(K*X^(-α)*R^3)*R^3 = 3*K*X^(-α)*R^6 by ring]
  dsimp [K, X, R]
  rw [← Real.rpow_natCast _ 6]
  simp_rw [← Real.rpow_mul hq0.le, mul_assoc, ← Real.rpow_add hq0]
  push_cast
  rw [show 1/9+ε'/3 + ((1/3+2*ε')*(-α) + ε'/18*6) = 0 by ring, Real.rpow_zero]; ring

end GradedNear
