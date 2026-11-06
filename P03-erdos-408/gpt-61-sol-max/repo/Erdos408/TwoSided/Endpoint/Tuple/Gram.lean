module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.OneSided.Major.Sparse

public import Erdos408.OneSided.Analysis.Divisor
public import Erdos408.TwoSided.Setup

/-!
# The sparse Gram bound

E8 of `blueprint/two_sided_correlation.md` §6.5 (PD (6.37)). Choose a maximizer
`τ_j ∈ [j, j + 1]` of `|R⁻¹ ∑ c_u u^{it}|²` for each `j ∈ 𝒥`. By the `TT*` bound it suffices
to bound the absolute row sums of the Gram matrix of `u ↦ u^{iτ_j}` on `(⌊R⌋, ⌊2R⌋]`, as in
`OneSided.sum_norm_unmarkedPoly_sq_le` (`Erdos408/OneSided/Major/Sparse.lean`). Its entries
are at most `R + 1`, which is used for `|j - j'| ≤ 1`. Otherwise `1 ≤ |Δ| ≤ 4T₀ + 2 ≤ x³`, and
by `IntegerKernelBound` at `k = 1`, `a = 0`, `H = lo = R`, `hi = 2R` they are at most
`|κ'| R (2 |j - j'|⁻¹ + exp(-L^{0.95}))`. The row sums are at most `9 (1 + |κ'|) R L / 2`, and
`∑ |c_u|² ≤ 2 R L^{2C_U}`.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset

/-- The duality (`TT*`) bound: if each row of the Gram matrix
`G_{ii'} = ∑_n e_i(n) \overline{e_{i'}(n)}` has absolute sum at most `R`, then
`∑_i |∑_n c_n e_i(n)|² ≤ R ∑_n |c_n|²`. -/
alias sum_norm_sq_le_of_gram_rowSum := _root_.SharedProofs.sum_norm_sq_le_of_gram_rowSum

/-- `∑_{m' ∈ S} 1/|m - m'| ≤ 2 (1 + log N)` for `S` and `m` in an integer interval of
length `N`, the term `m' = m` being `0`. -/
alias sum_inv_abs_intCast_sub_le := _root_.SharedProofs.sum_inv_abs_intCast_sub_le

/-- `n^{ia} \overline{n^{ib}} = n^{i(a - b)}` for `n ≠ 0`. -/
alias natCast_cpow_mul_I_mul_conj_cpow := _root_.SharedProofs.natCast_cpow_mul_I_mul_conj_cpow

/-- `|n^{it}| = 1` for `n ≥ 1`. -/
alias norm_natCast_cpow_ofReal_mul_I := _root_.SharedProofs.norm_natCast_cpow_ofReal_mul_I

/-- `|(⌊R⌋, ⌊2R⌋]| ≤ R + 1` for `R ≥ 0`. -/
theorem card_Ioc_floor_le  {R}  (hR : 0 ≤ R) : (#(Ioc ⌊R⌋₊ ⌊2 * R⌋₊) : ℝ) ≤ R + 1 := by
  rw [Nat.card_Ioc]
  rcases le_or_gt ⌊R⌋₊ ⌊2 * R⌋₊ with h | h
  · rw [Nat.cast_sub h]
    linarith [Nat.floor_le (show 0 ≤ 2 * R by linarith), Nat.lt_floor_add_one R]
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    linarith

/-- **Lemma E8 (sparse Gram bound from AP2).** For `C_m ≥ 0` and `C_U`, eventually, under
`IntegerKernelBound x C_m κ'`: for `R ∈ [exp(L/T²²), x]`, coefficients `|c_u| ≤ L^{C_U}` and a
set `𝒥` of integers with `#𝒥 e^{-L^{0.95}} ≤ 1` and `|j| ≤ 2T₀`, there are bounds `s_j` of
`sup_{[j, j+1]} |R|²` with `∑_{j ∈ 𝒥} s_j ≤ 9(1 + |κ'|) L^{2C_U + 4}`. -/
theorem eventually_sum_sup_normSq_le (Cm CU : ℝ) (hCm : 0 ≤ Cm) :
    ∀ᶠ x : ℝ in atTop, ∀ κ' : ℝ, IntegerKernelBound x Cm κ' →
      ∀ (R : ℝ) (c : ℕ → ℂ) (𝒥 : Finset ℤ),
        Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ R → R ≤ x →
        (∀ u, ‖c u‖ ≤ Real.log x ^ CU) →
        (𝒥.card : ℝ) * Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1 →
        (∀ j ∈ 𝒥, |(j : ℝ)| ≤ 2 * (x * Real.log x ^ (Cm + 2))) →
        ∃ s : ℤ → ℝ,
          (∀ j ∈ 𝒥, ∀ t ∈ Set.Icc (j : ℝ) (j + 1),
            ‖(R : ℂ)⁻¹ * ∑ u ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
                c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ s j) ∧
          ∑ j ∈ 𝒥, s j ≤ 9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4) := by
  filter_upwards [eventually_log_rpow_le_self (Cm + 3),
    Real.tendsto_log_atTop.eventually_ge_atTop 10, eventually_ge_atTop (5 : ℝ)]
    with x hxL hL hx5
  intro κ' hK R c 𝒥 hR₁ hR₂ hc h𝒥 h𝒥T
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR₁
  have hR1 : 1 ≤ R := le_trans (Real.one_le_exp (by
    positivity)) hR₁
  set T₀ := x * L ^ (Cm + 2) with hT₀
  -- `L^{C_m + 2} ≤ x / 9`
  have hT₀x : 9 * L ^ (Cm + 2) ≤ x := by
    have h : L ^ (Cm + 3) = L ^ (Cm + 2) * L := by
      rw [show Cm + 3 = (Cm + 2) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    have : 0 ≤ L ^ (Cm + 2) := by positivity
    nlinarith
  have hT₀0 : 0 ≤ T₀ := by positivity
  set S := Ioc ⌊R⌋₊ ⌊2 * R⌋₊ with hS
  have hSpos : ∀ u ∈ S, 0 < u := fun u hu => by
    rw [mem_Ioc] at hu
    omega
  set f : ℝ → ℝ := fun t => ‖(R : ℂ)⁻¹ * ∑ u ∈ S, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
  have hf : Continuous f := by
    refine ((continuous_const.mul (continuous_finsetSum _ fun u hu =>
      continuous_const.mul ?_)).norm).pow 2
    simp_rw [OneSided.natCast_cpow_mul_I (hSpos u hu).ne']
    fun_prop
  -- the maximizers `τ_j ∈ [j, j + 1]`
  have hmax : ∀ j : ℤ, ∃ τ ∈ Set.Icc (j : ℝ) (j + 1), ∀ t ∈ Set.Icc (j : ℝ) (j + 1),
      f t ≤ f τ := fun j =>
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (by linarith)) hf.continuousOn
  choose τ hτ hτmax using hmax
  refine ⟨fun j => f (τ j), fun j _ t ht => hτmax j t ht, ?_⟩
  -- the integer window
  set M := ⌊2 * T₀⌋ with hM
  have h𝒥M : 𝒥 ⊆ Icc (-M) M := by
    intro j hj
    have h := abs_le.1 (h𝒥T j hj)
    rw [mem_Icc]
    constructor
    · have : -j ≤ M := Int.le_floor.2 (by push_cast; linarith)
      omega
    · exact Int.le_floor.2 h.2
  set e : ℤ → ℕ → ℂ := fun j u => (u : ℂ) ^ ((τ j : ℂ) * Complex.I)
  set Rw := 3 * (R + 1) + |κ'| * R * (4 * (1 + Real.log (M - -M + 1).toNat) + 1) with hRw
  have hRw0 : 0 ≤ Rw := by positivity
  -- a Gram entry
  have hentry : ∀ j ∈ 𝒥, ∀ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖ ≤
      (if |j - j'| ≤ 1 then R + 1 else 0) +
        |κ'| * R * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) := by
    intro j hj j' hj'
    have hG : ∑ u ∈ S, e j u * starRingEnd ℂ (e j' u) =
        ∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I) :=
      sum_congr rfl fun u hu => natCast_cpow_mul_I_mul_conj_cpow (hSpos u hu).ne' _ _
    rw [hG]
    have hsecond : 0 ≤ |κ'| * R *
        (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) := by positivity
    obtain ⟨hτj₁, hτj₂⟩ := hτ j
    obtain ⟨hτj'₁, hτj'₂⟩ := hτ j'
    have hjj' : |((j - j' : ℤ) : ℝ)| ≤ |τ j - τ j'| + 1 := by
      push_cast
      rw [abs_le]
      constructor <;> cases abs_cases (τ j - τ j') <;> linarith
    by_cases h₁ : |j - j'| ≤ 1
    · rw [ite_eq_left h₁]
      refine le_add_of_le_of_nonneg ((norm_sum_le _ _).trans ?_) hsecond
      calc ∑ u ∈ S, ‖(u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖ = #S := by
            rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
            exact sum_congr rfl fun u hu => norm_natCast_cpow_ofReal_mul_I (hSpos u hu) _
        _ ≤ R + 1 := card_Ioc_floor_le hR0.le
    · rw [ite_eq_right h₁, zero_add]
      have h₂ : (2 : ℝ) ≤ |((j - j' : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast (show (2 : ℤ) ≤ |j - j'| by omega)
      have h : 1 ≤ |τ j - τ j'| := by linarith
      have hΔ : |τ j - τ j'| ≤ x ^ 3 := by
        have h₃ := h𝒥T j hj
        have h₄ := h𝒥T j' hj'
        have h₅ : |τ j - τ j'| ≤ 4 * T₀ + 2 := by
          rw [abs_le] at h₃ h₄ ⊢
          constructor <;> linarith
        have h₆ : 4 * T₀ + 2 ≤ x ^ 3 := by
          have : 4 * T₀ ≤ x * x := by
            rw [hT₀]
            nlinarith
          nlinarith
        linarith
      have hk1 : ((1 : ℕ) : ℝ) ≤ L ^ Cm := by
        rw [Nat.cast_one]
        exact Real.one_le_rpow (by linarith) hCm
      have hK' := hK R R (2 * R) hR₁ hR₂ le_rfl le_rfl 1 0 le_rfl hk1 (τ j - τ j') h hΔ
      have hfil : S.filter (· ≡ 0 [MOD 1]) = S :=
        filter_true_of_mem fun u _ => Nat.modEq_one
      rw [hfil] at hK'
      have hinv : (1 + |τ j - τ j'|)⁻¹ ≤ 2 * |((j - j' : ℤ) : ℝ)|⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by linarith)]
        calc (1 + |τ j - τ j'|)⁻¹ * |((j - j' : ℤ) : ℝ)|
            ≤ (1 + |τ j - τ j'|)⁻¹ * (2 * (1 + |τ j - τ j'|)) := by
              gcongr
              linarith
          _ = 2 := by field_simp
      calc ‖∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖
          = R * (R⁻¹ * ‖∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖) := by
            field_simp
        _ ≤ R * (κ' * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hK' hR0.le
        _ ≤ R * (|κ'| * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hR0.le
            calc κ' * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))
                ≤ |κ'| * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) :=
                  mul_le_mul_of_nonneg_right (le_abs_self κ') (by positivity)
              _ ≤ _ := by gcongr
        _ = _ := by ring
  -- the Gram rows are at most `Rw`
  have hrow : ∀ j ∈ 𝒥, ∑ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖ ≤ Rw := by
    intro j hj
    have hnear : ∑ j' ∈ 𝒥, (if |j - j'| ≤ 1 then R + 1 else 0) ≤ 3 * (R + 1) := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      have hsub : {j' ∈ 𝒥 | |j - j'| ≤ 1} ⊆ Icc (j - 1) (j + 1) := fun j' hj' => by
        rw [mem_filter] at hj'
        rw [mem_Icc]
        constructor <;> cases abs_cases (j - j') <;> omega
      have hcard : (#{j' ∈ 𝒥 | |j - j'| ≤ 1} : ℝ) ≤ 3 := by
        have h := card_le_card hsub
        rw [Int.card_Icc, show j + 1 + 1 - (j - 1) = 3 by ring] at h
        exact_mod_cast h
      nlinarith
    have hfar := sum_inv_abs_intCast_sub_le h𝒥M (h𝒥M hj)
    calc ∑ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖
        ≤ ∑ j' ∈ 𝒥, ((if |j - j'| ≤ 1 then R + 1 else 0) +
            |κ'| * R * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) :=
          sum_le_sum fun j' hj' => hentry j hj j' hj'
      _ = ∑ j' ∈ 𝒥, (if |j - j'| ≤ 1 then R + 1 else 0) + |κ'| * R *
            (2 * ∑ j' ∈ 𝒥, |((j - j' : ℤ) : ℝ)|⁻¹ + #𝒥 * Real.exp (-L ^ (0.95 : ℝ))) := by
          rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ Rw := by
          have h := mul_le_mul_of_nonneg_left (show 2 * ∑ j' ∈ 𝒥, |((j - j' : ℤ) : ℝ)|⁻¹ +
            #𝒥 * Real.exp (-L ^ (0.95 : ℝ)) ≤
              4 * (1 + Real.log (M - -M + 1).toNat) + 1 by linarith)
            (by positivity : 0 ≤ |κ'| * R)
          rw [hRw]
          linarith
  -- `log(2M + 1) ≤ 2L`
  have hlogM : Real.log (M - -M + 1).toNat ≤ 2 * L := by
    have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by positivity)
    have hcast : (((M - -M + 1).toNat : ℕ) : ℝ) = 2 * M + 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have hMle : (M : ℝ) ≤ 2 * T₀ := Int.floor_le _
    rw [hcast]
    have hpos : (0 : ℝ) < 2 * M + 1 := by
      positivity
    rw [show 2 * L = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring]
    refine Real.log_le_log hpos ?_
    have : 4 * T₀ ≤ x * x / 2 := by
      rw [hT₀]
      nlinarith
    nlinarith
  -- `Rw ≤ 9 (1 + |κ'|) R L`
  have hRwle : Rw ≤ 9 * (1 + |κ'|) * R * L := by
    rw [hRw]
    have hk0 := abs_nonneg κ'
    have h₁ : 4 * (1 + Real.log (M - -M + 1).toNat) + 1 ≤ 9 * L := by
      nlinarith
    have h₂ : |κ'| * R * (4 * (1 + Real.log (M - -M + 1).toNat) + 1) ≤
        |κ'| * R * (9 * L) := mul_le_mul_of_nonneg_left h₁ (by positivity)
    nlinarith [mul_nonneg hk0 hR0.le]
  -- the coefficients have `∑ |c_u|² ≤ 2 R L^{2C_U}`
  have hcoef : ∑ u ∈ S, ‖c u‖ ^ 2 ≤ 2 * R * L ^ (2 * CU) := by
    have hcu : ∀ u, ‖c u‖ ^ 2 ≤ L ^ (2 * CU) := by
      intro u
      calc ‖c u‖ ^ 2 ≤ (L ^ CU) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc u) 2
        _ = L ^ (2 * CU) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
            ring_nf
    calc ∑ u ∈ S, ‖c u‖ ^ 2 ≤ ∑ _u ∈ S, L ^ (2 * CU) := sum_le_sum fun u _ => hcu u
      _ = #S * L ^ (2 * CU) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (R + 1) * L ^ (2 * CU) := by
          gcongr
          exact card_Ioc_floor_le hR0.le
      _ ≤ 2 * R * L ^ (2 * CU) := by
          gcongr
          linarith
  have hgram := sum_norm_sq_le_of_gram_rowSum 𝒥 S e c hRw0 hrow
  have hL4 : L ^ (2 * CU + 4) = L ^ (2 * CU) * L ^ (4 : ℕ) := by
    rw [Real.rpow_add hL0, ← Real.rpow_natCast]
    norm_num
  calc ∑ j ∈ 𝒥, f (τ j) = R⁻¹ ^ 2 * ∑ j ∈ 𝒥, ‖∑ u ∈ S, c u * e j u‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [f, e]
        rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    _ ≤ R⁻¹ ^ 2 * (9 * (1 + |κ'|) * R * L * (2 * R * L ^ (2 * CU))) := by
        gcongr
        exact hgram.trans (mul_le_mul hRwle hcoef (by positivity) (by positivity))
    _ = 9 * (1 + |κ'|) * L ^ (2 * CU) * (2 * L) := by
        field_simp
    _ ≤ 9 * (1 + |κ'|) * L ^ (2 * CU + 4) := by
        rw [hL4]
        have : 2 * L ≤ L ^ 4 := by
          have h₁ : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith
        have : 0 ≤ 9 * (1 + |κ'|) * L ^ (2 * CU) := by positivity
        nlinarith

end Erdos408.TwoSided.TupleHigh
