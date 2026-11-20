module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import PrimeNumberTheoremAnd.PerronFormula

/-! The Cesàro-weighted Perron formula for an absolutely convergent Dirichlet
series with an arbitrary vertical shift. Both the integer and the von Mangoldt
kernels use the same interchange of sum and integral on the line `re s = 2`. -/

@[expose] public section

namespace Erdos408.SmoothedPerron

open Complex MeasureTheory Set LSeries

variable (a : ℕ → ℂ) (u : ℝ) {Y : ℝ}

private theorem shifted_term (hY : 0 < Y) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term a (s - u * I) n * Perron.f Y s =
      a n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Perron.f_mul_eq_f hY (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  rw [ofReal_natCast, cpow_neg] at h
  rw [term_of_ne_zero hn, ← h, cpow_sub _ _ hn0]
  field_simp

/-- The line integral of the Perron kernel at `y > 1` is `2π (1 - 1/y)`. -/
private theorem integral_perron_f_of_one_lt {y : ℝ} (hy : 1 < y) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 2 * Real.pi * (1 - 1 / y) := by
  have h := Perron.formulaGtOne (σ := 2) hy (by norm_num)
  rw [VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul] at h
  change 1 / (2 * Real.pi * I) * (I * ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I)) = _ at h
  generalize ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = J at h ⊢
  rw [← h]
  field_simp

/-- The line integral of the Perron kernel at `0 < y < 1` vanishes. -/
private theorem integral_perron_f_of_lt_one {y : ℝ} (hy0 : 0 < y) (hy : y < 1) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 0 := by
  have h := Perron.formulaLtOne (σ := 2) hy0 hy (by norm_num)
  rw [VerticalIntegral, smul_eq_mul] at h
  simpa using h

/-- Expand a shifted Dirichlet series on the integration line and evaluate
its Perron integral term by term. -/
theorem formula (hY : 0 < Y) (hYN : ∀ m : ℕ, (m : ℝ) ≠ Y)
    (hsum₂ : LSeriesSummable a 2) (F : ℂ → ℂ)
    (hF : ∀ t : ℝ, F ((2 : ℝ) + t * I) =
      LSeries a ((2 : ℝ) + t * I - u * I) * Perron.f Y ((2 : ℝ) + t * I)) :
    VerticalIntegral F 2 = 2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      a m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y) := by
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term a ((2 : ℝ) + t * I - u * I) n * Perron.f Y ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, F ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [hF, LSeries, ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = a n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ shifted_term a u hY hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hYn := div_pos hY (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hYn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term a 2 n‖ * ∫ t : ℝ, ‖Perron.f Y ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    exact (summable_norm_iff.mpr hsum₂).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊Y⌋₊ then
      2 * Real.pi * (a n * (n : ℂ) ^ ((u : ℂ) * I) * (1 - n / Y)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hnY  :=
        lt_of_le_of_ne ((Nat.le_floor_iff hY.le).mp (Finset.mem_Icc.mp hmem).2) (hYN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hnY)]
      push_cast
      rw [one_div_div]
      ring
    · have hYn : Y < n := (Nat.floor_lt hY.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hY hn0) ((div_lt_one hn0).mpr hYn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊Y⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- The unnormalized Cesàro sum, i.e. the piecewise linear interpolation of the
antiderivative of the sharp partial sum. -/
noncomputable def ramp (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n)

theorem ramp_eq_mul {x : ℝ} (hx : 0 < x) : ramp a x =
    x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (1 - n / (x : ℂ)) := by
  rw [ramp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by have := ofReal_ne_zero.mpr hx.ne'; field_simp

/-- A secant of the Cesàro sum approximates **any** sharp sum at an intermediate
integer. Only the `h` new terms contribute and the discrepancy of each weight is ≤ `h`.
This gives both forward and backward differencing, with the same error. -/
theorem ramp_error {x : ℝ} (hx : 0 ≤ x) (h m : ℕ) (hl : ⌊x⌋₊ ≤ m) (hr : m ≤ ⌊x⌋₊ + h)
    {B : ℝ} (hb : ∀ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + h), ‖a n‖ ≤ B) :
    ‖ramp a (x + h) - ramp a x - h * ∑ n ∈ Finset.Icc 1 m, a n‖ ≤ h ^ 2 * B := by
  let l := ⌊x⌋₊
  let s := Finset.Ioc l (l + h)
  have hI (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by ext; simp; omega
  have hcut : s.filter (· ≤ m) = Finset.Ioc l m := by ext; simp [s]; omega
  have hm : ∑ n ∈ s, a n * (if n ≤ m then (h : ℂ) else 0) = h * ∑ n ∈ Finset.Ioc l m, a n := by
    simp only [mul_ite, mul_zero, ← Finset.sum_filter, hcut, ← Finset.sum_mul]
    ring
  have hprefix : ∑ n ∈ Finset.Ioc 0 l, a n * (((x + h : ℝ) : ℂ) - n) =
      (∑ n ∈ Finset.Ioc 0 l, a n * ((x : ℂ) - n)) + h * ∑ n ∈ Finset.Ioc 0 l, a n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by push_cast; ring
  have hid : ramp a (x + h) - ramp a x - h * ∑ n ∈ Finset.Icc 1 m, a n =
      ∑ n ∈ s, a n * (((x + h - n - if n ≤ m then (h : ℝ) else 0 : ℝ) : ℝ) : ℂ) := by
    simp only [ramp, Nat.floor_add_natCast hx, hI]
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le l) (Nat.le_add_right l h),
      ← Finset.sum_Ioc_consecutive a (Nat.zero_le l) hl, mul_add, hprefix, ← hm]
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, apply_ite Complex.ofReal, ofReal_natCast, ofReal_zero, s, l]
    ring
  rw [hid]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => B * h) fun n hn => ?_).trans_eq ?_)
  · have ⟨hn₀, hn₁⟩ := Finset.mem_Ioc.mp hn
    have htop : (l : ℝ) ≤ x := Nat.floor_le hx
    have hlo : x < n := (Nat.floor_lt hx).mp hn₀
    have hhi : (n : ℝ) ≤ l + h := by exact_mod_cast hn₁
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    refine mul_le_mul (hb n hn) (abs_le.mpr ?_) (abs_nonneg _) ((norm_nonneg _).trans (hb n hn))
    split_ifs <;> constructor <;> linarith
  · simp [s, pow_two, mul_left_comm, mul_comm]

theorem floor_add_half (n : ℕ) : ⌊(n : ℝ) + 1 / 2⌋₊ = n := by
  rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith

theorem natCast_ne_add_half (n m : ℕ) : (m : ℝ) ≠ n + 1 / 2 := by
  intro he
  have hm : m = n := by simpa only [Nat.floor_natCast, floor_add_half] using congrArg (Nat.floor (α := ℝ)) he
  subst hm
  linarith

end Erdos408.SmoothedPerron
