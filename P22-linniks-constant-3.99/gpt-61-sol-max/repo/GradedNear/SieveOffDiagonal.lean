
import GradedNear.SieveBasic
import GradedNear.CharacterSums
import GradedNear.Tactics

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
bounded by `O(V^{2/3})` (`lcm_sum_le`). With `ε = ε'/3` the total is
`≪ (1 + log q)^3 q^{-ε'/3} ≪ q^{-ε'/6}`, so `κ = ε'/6` and `q₀ = 2`.
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace GradedNear

/-! ### The Selberg weights -/

/-! ### Character sums over intervals and over multiples -/

/-! ### Summation by parts -/

/-! ### The weight `W(n) = log n · n^{-s}` -/

lemma sum_rpow_neg_two_thirds_le (Y : ℕ) :
    ∑ j ∈ Finset.Ioc 0 Y, (j : ℝ) ^ (-⅔) ≤ 3 * ↑Y ^ ⅓ := by

  have ha : AntitoneOn (fun x : ℝ => x ^ (-⅔)) (Ioc 0 (0 + ↑Y)) := by
    intro x hx y hy hxy
    grind [Real.rpow_le_rpow_of_nonpos]
  have h := ha.sum_le_integral_of_integrableOn ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  )
  rw [integral_rpow (Or.inl (by norm_num))] at h
  norm_num at h
  rw [show Finset.Ioc 0 Y = Finset.Ico 1 (Y + 1) by grind,
      Finset.sum_Ico_eq_sum_range]
  grind

/-! ### Opening the square -/

/-! ### Assembly -/

set_option maxHeartbeats 2000000 in
theorem sieve_offdiag (hBur : BurgessBound) {ε' tmax : ℝ} (hε' : 0 < ε') :
    ∃ C κ : ℝ, 0 < κ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, ⅓ + 2 * ε' < t → t ≤ t' → t' ≤ tmax → 0 ≤ β → β ≤ 1 →
        |τ| ≤ Real.log q →
        ‖∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu (↑q ^ ((t - ⅓) / 2 - ε')) n : ℂ) * ψ n * ↑(Real.log n) *
              ↑n ^ (-((1 + β : ℝ) + ↑τ * I))‖ ≤ C * ↑q ^ (-κ) := by
  obtain ⟨CB, hCB⟩ := hBur (ε' / 3) (by positivity)
  let Z := ∑' g : ℕ, (g : ℝ) ^ (-(4 * ⅓))
  let CL := 9 * Z
  have hCL : 0 ≤ CL := by positivity
  have hLcm (K : ℕ) :
      ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K,
        (Nat.lcm d e : ℝ) ^ (-⅔) ≤ CL * ↑K ^ ⅔ := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    dsimp only [CL]
    rw [mul_right_comm (9 : ℝ)]
    let F : ℕ → ℕ → ℝ := fun g d => if g ∣ d then ↑d ^ (-⅔) else 0

    let X : ℕ → ℕ → ℕ → ℝ := fun g d e => ↑g ^ ⅔ * (F g d * F g e)
    have hX0 : ∀ g d e, 0 ≤ X g d e := by intros; positivity
    have h1 : ∀ d ∈ Finset.Ioc 0 K, ∀ e ∈ Finset.Ioc 0 K,
        ↑ (Nat.lcm d e) ^ (-⅔) ≤ ∑ g ∈ Finset.Ioc 0 K, X g d e := by
      intro d hd e he
      rw [Finset.mem_Ioc] at hd he
      have hgS : Nat.gcd d e ∈ Finset.Ioc 0 K := by
        grind [Nat.gcd_pos_of_pos_left, Nat.gcd_le_left]
      have hval : ↑ (Nat.lcm d e) ^ (-⅔) = X (Nat.gcd d e) d e := by
        simp only [X, F, Nat.gcd_dvd_left d e, Nat.gcd_dvd_right d e, ite_true]
        have hg : (0 : ℝ) < Nat.gcd d e := by simp_all
        have hl : (0 : ℝ) < Nat.lcm d e := by simp_all
        rw [← Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg e),
          ← Nat.cast_mul, ← Nat.gcd_mul_lcm, Nat.cast_mul,
          Real.mul_rpow hg.le hl.le, ← mul_assoc, ← Real.rpow_add hg]
        norm_num
      grind [Finset.single_le_sum]
    calc ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ((Nat.lcm d e : ℕ) : ℝ) ^ (-⅔)
        ≤ ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K, X g d e :=
           by bound
      _ = ∑ g ∈ Finset.Ioc 0 K, ↑g ^ ⅔ *
            ((∑ d ∈ Finset.Ioc 0 K, F g d) * ∑ e ∈ Finset.Ioc 0 K, F g e) := by
        rw [Finset.sum_comm_cycle]
        dsimp only [X]
        sum_ring
      _ ≤ ∑ g ∈ Finset.Ioc 0 K, 9 * ↑K ^ ⅔ * ↑g ^ (-(4 * ⅓)) := by
          gcongr 1 with g hg
          have hg1' := (Finset.mem_Ioc.1 hg).1
          have hg1 : (1 : ℝ) ≤ g := by bound
          have hg0 : (0 : ℝ) < g := by linarith
          have hU : ∑ d ∈ Finset.Ioc 0 K, F g d ≤ 3 * ↑K ^ ⅓ * (g : ℝ)⁻¹ := by
            dsimp only [F]
            rw [sum_Ioc_ite_dvd (f := fun d => (d : ℝ) ^ (-⅔)) hg1', Nat.zero_div]
            simp_rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
            rw [← Finset.mul_sum]
            grw [sum_rpow_neg_two_thirds_le, Nat.cast_div_le]
            rw [Real.div_rpow (Nat.cast_nonneg _) hg0.le]
            apply le_of_eq
            rpow_ring
          grw [hU, hU]
          apply le_of_eq
          rpow_ring

      _ = 9 * ↑K ^ ⅔ *
          ∑ g ∈ Finset.Ioc 0 K, ↑g ^ (-(4 * ⅓)) := by rw [Finset.mul_sum]
      _ ≤ 9 * ↑K ^ ⅔ * Z := by
        gcongr
        exact (Real.summable_nat_rpow.mpr (by norm_num : -(4 * ⅓) < -1)).sum_le_tsum
          _ fun _ _ => by positivity
  clear_value CL
  let C₀ := max CB 0


  let c₁ := max 1 tmax
  have hc₁1 := le_max_left 1 tmax

  let M := 1 + 18 / ε'

  refine ⟨C₀ * (7 * c₁ ^ 2 * CL * M ^ 3), ε' / 6, by positivity, 2, ?_⟩
  intro q hq ψ hψ t t' β τ ht htt' ht'max hβ0 hβ1 hτ
  set qR := (q : ℝ)

  have hq2 : (2 : ℝ) ≤ q := by simp_all
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have ht0 : 0 < t := by linarith
  -- Burgess's bound for intervals of any length
  set Kq := C₀ * qR ^ (⅑ + ε' / 3)
  have hKq0 : 0 ≤ Kq := by positivity

  set s : ℂ := ((1 + β : ℝ) : ℂ) + (τ : ℂ) * I
  have hs : 1 ≤ s.re := by simp [s]; linarith

  let wt (n : ℕ) : ℂ := ↑(Real.log n) * ↑n ^ (-s)

  have norm_wt_le {n : ℕ} (hn : 0 < n) :
      ‖wt n‖ ≤ Real.log n / n := by
    unfold wt
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]

    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
    gcongr

    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by aesop) (by simpa using hs)

  have norm_wt_sub_le {n : ℕ} (hn : 1 ≤ n) :
      ‖wt n - wt (n + 1)‖ ≤ (1 + ‖s‖ * Real.log (n + 1)) / ↑n ^ 2 := by
    let F (x : ℝ) : ℂ := ↑(Real.log x) * cexp (↑(Real.log x) * -s)
    let K := 1 + ‖s‖ * Real.log (n + 1)
    have hn0 : (0 : ℝ) < n := by positivity
    have hlogn : 0 ≤ Real.log (n + 1) :=  by bound


    dsimp only [wt]
    simp (disch := norm_cast <;> omega) only [Complex.cpow_def_of_ne_zero, ← Complex.natCast_log]
    simpa [F, K, norm_sub_rev] using  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := F) (f' := fun x => cexp (↑(Real.log x) * -s) * (1 - ↑(Real.log x) * s) / x)
      (s := Icc ↑n (n + 1)) (C := K / n ^ 2) (x := n) (y := n + 1)
       fun x hx => by
        have h := (Real.hasDerivAt_log (hn0.trans_le hx.1).ne').ofReal_comp
        convert (h.mul (h.mul_const (-s)).cexp).hasDerivWithinAt using 1 <;> push_cast <;> field_simp <;> ring
      (by
        intro x hx
        have hx0 := hn0.trans_le hx.1
        have hx1 : 1 ≤ x := le_trans (by bound) hx.1
        have hl0 := Real.log_nonneg hx1
        have hl := Real.log_le_log hx0 hx.2
        simp only [norm_div, norm_mul, Complex.norm_exp]
        simp [abs_of_pos hx0]
        have he : Real.exp (-(Real.log x * s.re)) ≤ x⁻¹ := by
          calc _ ≤ Real.exp (-Real.log x) := by bound
            _ = x⁻¹ := by grind [Real.exp_neg, Real.exp_log]
        grw [he, norm_sub_le]
        simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0]
        rw [mul_comm (Real.log x)]
        grw [hl]
        change x⁻¹ * K / x ≤ K / n ^ 2
        calc _ = K / x ^ 2 := by field_simp
          _ ≤ K / n ^ 2 := by gcongr; exact hx.1
      ) (convex_Icc _ _) (by simp) (by simp)

  have hsn : ‖s‖ ≤ 2 * (1 + Real.log q) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [s]
    grind
  set δ := (t - ⅓) / 2 - ε'
  have hδ0 : 0 < δ := by bound
  set V : ℝ := qR ^ δ
  have abs_grahamWeight_le_one (d : ℕ) : |grahamWeight V d| ≤ 1 := by
    unfold grahamWeight
    split_ifs with h
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hd1 : (1:ℝ) ≤ d := by aesop

        have hVpos : 0 < V := by linarith
        have hlogV := Real.log_nonneg (le_trans hd1 h)
        have h1 : 0 ≤ Real.log (V / d) :=
          Real.log_nonneg (by field_simp; nlinarith)
        have h2 :=
          Real.log_le_log (by positivity) (div_le_self hVpos.le hd1)
        have hmu : |(μ d : ℝ)| ≤ 1 := by
          have := ArithmeticFunction.abs_moebius_le_one (n := d)
          exact_mod_cast this
        rw [abs_div, abs_mul, abs_of_nonneg h1, abs_of_nonneg hlogV]
        apply div_le_one_of_le₀ _ hlogV
        nlinarith
    simp_all

  set A : ℝ := qR ^ t
  set B : ℝ := qR ^ t'
  have hV1 : 1 ≤ V := Real.one_le_rpow hq1 hδ0.le

  have hexp : qR ^ (⅑ + ε' / 3) * A ^ (-⅓) * V ^ ⅔ =
      qR ^ (-(ε' / 3)) := by
    dsimp [A, V, δ]
    rpow_ring
  have hA1 : 1 ≤ A := Real.one_le_rpow hq1 ht0.le
  have hB1 : 1 ≤ B := Real.one_le_rpow hq1 (by linarith)

  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hN₀ := Nat.ceil_pos.2 hA0
  have hN₁ := Nat.ceil_pos.2 hB0
  -- rewrite the sum over `Ioc`, and open the square
  have sieveNu_eq {n : ℕ} (hn : n ≠ 0) :
      sieveNu V n = ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
         if Nat.lcm d e ∣ n then grahamWeight V d * grahamWeight V e else 0 := by
    unfold sieveNu
    have hsum : ∑ d ∈ n.divisors, grahamWeight V d =
        ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, if d ∣ n then grahamWeight V d else 0 := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · grind
      · intro d hd hnot
        exact ite_eq_right (not_le.2 (Nat.lt_of_floor_lt (by grind [Nat.pos_of_mem_divisors])))
    rw [hsum, sq, Finset.sum_mul_sum]
    congr! 2
    split_ifs <;> simp_all [Nat.lcm_dvd_iff]

  have hIco : Finset.Ico ⌈A⌉₊ ⌈B⌉₊ = Finset.Ioc (⌈A⌉₊ - 1) (⌈B⌉₊ - 1) := by grind
  conv_lhs => simp only [mul_assoc]
  rw [hIco]
  conv_lhs =>
    arg 1
    simp (disch := grind) only [sieveNu_eq, Complex.ofReal_sum, apply_ite,
      Complex.ofReal_zero, Finset.sum_mul]
    simp only [ite_mul, zero_mul, ← mul_ite_zero]
    rw [← Finset.sum_comm_cycle]
    simp only [← Finset.mul_sum]
    simp only [mul_ite_zero]
  set a := ⌈A⌉₊ - 1 with ha
  set b := ⌈B⌉₊ - 1
  have ha1 : (a : ℝ) + 1 = (⌈A⌉₊ : ℝ) := by
    grind [Nat.cast_sub]
  have hb1 : (b : ℝ) + 1 = (⌈B⌉₊ : ℝ) := by
    grind [Nat.cast_sub]
  -- each `(d, e)` term
  -- bounds on the logarithmic factors
  have hL0 : 0 ≤ Real.log (↑b + 1) :=
    by bound
  have hLle : Real.log (↑b + 1) ≤ c₁ * (1 + Real.log q) := by
    rw [hb1]
    have h1 : ↑ ⌈B⌉₊ ≤ 2 * B := by
      grind [Nat.ceil_lt_add_one]
    have h2 :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hB0.ne',  Real.log_rpow hq0 t' ] at h2
    have hlog2 : Real.log 2 ≤ 1 := by
      grind [Real.log_le_sub_one_of_pos]
    have h3 : t' * Real.log q ≤ c₁ * Real.log q :=
      by bound
    linarith

  have hA13 : (↑a + 1) ^ (-⅓) ≤ A ^ (-⅓) := by
    grind [Real.rpow_le_rpow_of_nonpos, Nat.le_ceil]
  have hPq : (1 + Real.log q) ^ 3 ≤ M ^ 3 * qR ^ (ε' / 6) := by
    have hlog := Real.log_le_rpow_div hq0.le (show 0 < ε' / 18 by positivity)
    have hpow := Real.one_le_rpow hq1 (show 0 ≤ ε' / 18 by positivity)
    rw [show ε' / 6 = ε' / 18 * (3 : ℕ) by norm_num; ring,
      Real.rpow_mul_natCast hq0.le, ← mul_pow]
    gcongr

    linear_combination hpow + hlog
  generalize hLdef : Real.log (↑b + 1) = L at hL0 hLle
  generalize hPdef : 1 + Real.log q = P at hLle hsn hPq
  have hP1 : 1 ≤ P := by grind [Real.log_natCast_nonneg]
  have hΛ0 : 0 ≤ L + (1 + ‖s‖ * L) * (1 + L) :=
    by positivity
  have hΛ : L + (1 + ‖s‖ * L) * (1 + L) ≤ 7 * c₁ ^ 2 * P ^ 3 := by
    have hcP : 1 ≤ c₁ * P := by nlinarith
    have h0 : 1 ≤ c₁ * P * P := by nlinarith
    have h1 := mul_le_mul hsn hLle hL0 (by linarith)
    nlinarith

  refine (norm_sum_le_of_le _ fun d hd =>
    norm_sum_le_of_le _ fun e he => show _ ≤
      Kq * ((Nat.lcm d e : ℕ) : ℝ) ^ (-⅔) *
        ((a : ℝ) + 1) ^ (-⅓) * (L + (1 + ‖s‖ * L) * (1 + L)) from by
      rw [Finset.mem_Ioc] at hd he
      have hl := Nat.lcm_pos hd.1 he.1
      generalize hlcm : Nat.lcm d e = l at hl ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      grw [abs_grahamWeight_le_one d, abs_grahamWeight_le_one e]
      simp only [one_mul]
      let f : ℕ → ℂ := fun n => if l ∣ n then ψ n else 0
      let P (x : ℕ) := ∑ k ∈ Finset.Ioc a x, f k
      have hlpos : (0 : ℝ) < l := by simp_all
      have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      set E := Kq * (l : ℝ) ^ (-⅔) * ((a : ℝ) + 1) ^ (-⅓)
      have hE0 : 0 ≤ E := by positivity
      change ‖∑ n ∈ Finset.Ioc a b, if l ∣ n then ψ n * wt n else 0‖ ≤ _
      have sum_Ioc_by_parts (b : ℕ) :
          ∑ n ∈ Finset.Ioc a b, f n * wt n =
            (∑ k ∈ Finset.Ioc a b, f k) * wt (b + 1) +
              ∑ n ∈ Finset.Ioc a b, (∑ k ∈ Finset.Ioc a n, f k) * (wt n - wt (n + 1)) := by
        induction b with
        | zero => simp
        | succ b ih =>
          by_cases hab : a ≤ b
          · grind [Finset.sum_Ioc_succ_top]
          simp [Finset.Ioc_eq_empty (by omega : ¬a < b + 1)]
      simp_rw [← ite_zero_mul]
      rw [sum_Ioc_by_parts]
      have hkey (x : ℕ) : a < x →
          ‖P x‖ ≤ E * x := by
        intro hx
        have hcx : (a : ℝ) + 1 ≤ x := by exact_mod_cast hx
        calc ‖P x‖
            ≤ Kq * (↑x / l) ^ ⅔ := by
              dsimp only [P, f]
              rw [sum_Ioc_ite_dvd (f := fun k => ψ k) hl]
              simp only [Nat.cast_mul, map_mul]
              rw [← Finset.mul_sum, norm_mul]

              obtain ⟨H, hH⟩ := Nat.exists_eq_add_of_le (Nat.div_le_div_right hx.le)
              rw [hH]
              have hHx := by
                calc ↑H ≤ ((x / l : ℕ) : ℝ) := by simp_all
                  _ ≤ ↑x / l := Nat.cast_div_le
              grw [DirichletCharacter.norm_le_one ψ _,  burgess_any_length (by omega) ψ hψ hKq0 (by
                intro N H hH1 hHq
                exact (hCB q ψ hψ N H hH1 hHq).trans (by bound))
               ]
              simp only [one_mul]
              gcongr
          _ ≤ Kq * (↑l ^ (-⅔) * (↑a + 1) ^ (-⅓) * x) := by
              gcongr
              have hx := lt_of_lt_of_le ha1 hcx
              rw [Real.div_rpow hx.le hlpos.le, div_eq_mul_inv, ← Real.rpow_neg hlpos.le]
              have h1 : ↑x ^ ⅔ = ↑x * (x : ℝ) ^ (-⅓) := by
                rw [show ⅔ = 1 + -⅓ by norm_num, Real.rpow_add hx, Real.rpow_one]
              rw [h1]
              have h2 : ↑x ^ (-⅓) ≤ ((a : ℝ) + 1) ^ (-⅓) :=
                Real.rpow_le_rpow_of_nonpos ha1 hcx (by norm_num)

              field_simp; nlinarith
          _ = E * x := by bound
      rcases le_or_gt b a with hab | hab
      · rw [Finset.Ioc_eq_empty (by omega)]
        simp only [Finset.sum_empty, zero_mul, zero_add, norm_zero]
        positivity
      have hb0 : (0 : ℝ) < b := by exact_mod_cast (Nat.zero_le a).trans_lt hab
      -- the boundary term
      have hT1 : ‖ P b * wt (b + 1)‖ ≤
          E * L := by
        rw [norm_mul]
        grw [hkey b hab, norm_wt_le (Nat.succ_pos b)]
        push_cast
        rw [hLdef]
        field_simp
        nlinarith [mul_nonneg hE0 hL0]
      -- the interior terms
      have hT2 : ∀ n ∈ Finset.Ioc a b,
          ‖ P n *
            (wt n - wt (n + 1))‖ ≤ E * (1 + ‖s‖ * L) * (1 / ↑n) := by
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn1 : 1 ≤ n := by omega

        rw [norm_mul]
        have hlog : Real.log ((n : ℝ) + 1) ≤ L := by
          rw [← hLdef]
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.add_le_add_right hn.2 1
        grw [hkey n hn.1, norm_wt_sub_le hn1]
        grw [hlog]
        field_simp
        rfl
      have hharm : ∑ n ∈ Finset.Ioc a b, 1 / (n : ℝ) ≤ 1 + L := by
        calc _ ≤ ∑ n ∈ Finset.Icc 1 b, 1 / (n : ℝ) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · grind
                bound
          _ ≤ 1 + Real.log b := by
              simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log b
          _ ≤ 1 + L := by bound
      grw [norm_add_le, norm_sum_le_of_le _ hT2, hT1]
      rw [← Finset.mul_sum]
      grw [hharm]
      ring_nf
      rfl
     ).trans ?_
  calc
    _ = Kq * (↑a + 1) ^ (-⅓) * (L + (1 + ‖s‖ * L) * (1 + L)) *
        ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
          ↑ (Nat.lcm d e) ^ (-⅔) := by sum_ring
    _ ≤ Kq * A ^ (-⅓) * (7 * c₁ ^ 2 * P ^ 3) *
        (CL * V ^ ⅔) := by
      grw [hLcm, hA13, hΛ,  Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num) ]
    _ = 7 * c₁ ^ 2 * CL * P ^ 3 * (C₀ * qR ^ (-(ε' / 3))) := by grind
    _ ≤ 7 * c₁ ^ 2 * CL * (M ^ 3 * qR ^ (ε' / 6)) * (C₀ * qR ^ (-(ε' / 3))) := by
        gcongr
    _ = C₀ * (7 * c₁ ^ 2 * CL * M ^ 3) * qR ^ (-(ε' / 6)) := by rpow_ring

end GradedNear
