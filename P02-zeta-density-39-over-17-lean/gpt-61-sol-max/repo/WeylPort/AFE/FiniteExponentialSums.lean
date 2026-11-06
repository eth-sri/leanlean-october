module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.AlternatingHarmonic
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual finite exponential sums of Lemma 2 -/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology

/-- The source's negative Fourier mode. -/
noncomputable def expMode (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ))

/-- The exact positive-index finite sum S₀. -/
noncomputable def finiteS0 (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, expMode x n

/-- The exact twisted harmonic sum S₁. -/
noncomputable def finiteS1 (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, expMode x n / (n : ℂ)

/-- Reindexing preserves the first positive integer and the right endpoint. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

section
variable (x : ℝ) (n : ℕ)
include x n

/-- Every actual Fourier mode has unit norm. -/
theorem norm_expMode  : ‖expMode x n‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

/-- The Fourier modes are the actual powers of their first mode. -/
theorem expMode_eq_pow  : expMode x n = expMode x 1 ^ n := by
  unfold expMode
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The exact trigonometric size of a mode minus one. -/
theorem norm_expMode_sub_one  :
    ‖expMode x n - 1‖ = 2 * |Real.sin (Real.pi * x * n)| := by
  unfold expMode
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,
    show (-2 * Real.pi * (n : ℝ) * x) / 2 = -(Real.pi * x * n) by ring,
    Real.sin_neg]
  simp [norm_mul, Real.norm_eq_abs]
end


section
variable {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
include x hx

/-- The denominator is nonzero whenever the source sine denominator is nonzero. -/
theorem expMode_one_ne_one  :
    expMode x 1 ≠ 1 := by
  intro h
  have he := norm_expMode_sub_one x 1
  rw [h, sub_self, norm_zero] at he
  norm_num at he
  exact hx he

/-- The exact sine quotient for every integer cutoff, including the empty sum. -/
theorem norm_finite_mode_sum  (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, expMode x n‖ =
      |Real.sin (Real.pi * x * N)| / |Real.sin (Real.pi * x)| := by
  rw [sum_Icc_one_eq_sum_range]
  have hs : (∑ n ∈ Finset.range N, expMode x (n + 1)) =
      ∑ n ∈ Finset.range N, expMode x 1 ^ (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    exact expMode_eq_pow x (n + 1)
  rw [hs]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq (expMode_one_ne_one hx), norm_mul,
    norm_expMode, mul_one, norm_div, ← expMode_eq_pow, norm_expMode_sub_one,
    norm_expMode_sub_one]
  simp only [Nat.cast_one, mul_one]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- Lemma 2's exact geometric expression at a real cutoff. -/
theorem norm_finiteS0  (y : ℝ) :
    ‖finiteS0 x y‖ = |Real.sin (Real.pi * x * ⌊y⌋₊)| / |Real.sin (Real.pi * x)| :=
  norm_finite_mode_sum hx _

/-- The uniform geometric bound used by the summation-by-parts step. -/
theorem norm_finiteS0_le  (y : ℝ) :
    ‖finiteS0 x y‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  rw [norm_finiteS0 hx]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
end


/-- Below the first positive integer, both source sums are empty. -/
theorem finite_sums_eq_zero {x y : ℝ} (hy : y < 1) : finiteS0 x y = 0 ∧ finiteS1 x y = 0 := by
  simp [finiteS0, finiteS1, Nat.floor_eq_zero.mpr hy]

/-- The paper's noninteger hypothesis discharges the sine denominator. -/
theorem sin_pi_mul_ne_zero_of_noninteger {x : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    Real.sin (Real.pi * x) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have he : (n : ℝ) = x := by nlinarith [Real.pi_pos]
  exact hx n he.symm

/-- The actual mode at an integer frequency is one. -/
theorem expMode_integer (k : ℤ) (n : ℕ) : expMode (k : ℝ) n = 1 := by
  rw [expMode_eq_pow]
  have h : expMode (k : ℝ) 1 = 1 := by
    unfold expMode
    rw [show Complex.I * ((-2 * Real.pi * (1 : ℕ) * (k : ℝ) : ℝ) : ℂ) =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  rw [h, one_pow]

/-- At half-integers the actual modes have precisely the source's alternating signs. -/
theorem expMode_half_integer (k : ℤ) (n : ℕ) :
    expMode ((k : ℝ) + 1 / 2) n = (-1 : ℂ) ^ n := by
  rw [expMode_eq_pow]
  have h : expMode ((k : ℝ) + 1 / 2) 1 = -1 := by
    unfold expMode
    rw [show Complex.I * ((-2 * Real.pi * (1 : ℕ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + -(Real.pi * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [h]

/-- Integer frequencies return the actual harmonic number. -/
theorem finiteS1_integer (k : ℤ) (y : ℝ) : finiteS1 (k : ℝ) y = (harmonic ⌊y⌋₊ : ℂ) := by
  rw [finiteS1, sum_Icc_one_eq_sum_range]
  simp only [expMode_integer, one_div, Nat.cast_add, Nat.cast_one]
  exact Complex.sum_inv_natCast_add_one _

private theorem antitone_reciprocal_succ : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro n m hnm
  apply one_div_le_one_div_of_le (by positivity)
  exact add_le_add_left (Nat.cast_le.mpr hnm) 1

private theorem sum_range_even_pairs (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), f n) = ∑ n ∈ Finset.range N, (f (2 * n) + f (2 * n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The ordered alternating harmonic prefixes converge; no unordered reciprocal sum is used. -/
theorem tendsto_alternating_harmonic_prefix :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 (Real.log 2)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  obtain ⟨l, hl⟩ := antitone_reciprocal_succ.tendsto_alternating_series_of_tendsto_zero hlim
  have hp := hasSum_paired_reciprocal (by norm_num : (0 : ℝ) < 1)
  rw [paired_reciprocal_source_eq (by norm_num : (0 : ℝ) < 1)] at hp
  norm_num at hp
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range (2 * N), (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) =
        ∑ n ∈ Finset.range N, (1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 1 + 1)) := by
    rw [sum_range_even_pairs]
    apply Finset.sum_congr rfl
    intro n _
    norm_num [pow_add]
    ring
  have htwo : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by dsimp; omega) Filter.tendsto_id
  have heven := hl.comp htwo
  simp only [Function.comp_def, hfinite] at heven
  simp only [one_div] at heven
  have he : l = Real.log 2 := tendsto_nhds_unique heven hp.tendsto_sum_nat
  rwa [he] at hl

/-- The alternating harmonic remainder is bounded by its first omitted reciprocal.
The parity argument specializes Mathlib's `alternating_series_error_bound` in
`Analysis/SpecificLimits/Normed.lean` (Apache-2.0), using an ordered limit instead
of unordered summability. Authors: Anatole Dedecker, Sébastien Gouëzel,
Yury Kudryashov, Dylan MacKenzie, Patrick Massot. -/
theorem alternating_harmonic_prefix_error (N : ℕ) :
    |(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) - Real.log 2| ≤
      1 / ((N : ℝ) + 1) := by
  have hlow := Antitone.alternating_series_le_tendsto
    tendsto_alternating_harmonic_prefix antitone_reciprocal_succ
  have hupp := Antitone.tendsto_le_alternating_series
    tendsto_alternating_harmonic_prefix antitone_reciprocal_succ
  obtain he | ho := Nat.even_or_odd N
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    have hl := hlow k
    have hu := hupp k
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at hu
    rw [abs_sub_le_iff]
    have hp : 0 ≤ 1 / ((↑(2 * k) : ℝ) + 1) := by positivity
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    have hl := hlow (k + 1)
    have hu := hupp k
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ] at hl
    norm_num [pow_add] at hl
    rw [abs_sub_le_iff]
    have hp : 0 ≤ 1 / ((↑(2 * k + 1) : ℝ) + 1) := by positivity
    simp only [one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hu hp ⊢
    constructor <;> linarith

/-- Exact conversion of the half-integer harmonic sum to a real alternating prefix. -/
theorem finiteS1_half_integer (k : ℤ) (y : ℝ) :
    finiteS1 ((k : ℝ) + 1 / 2) y =
      -((∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [finiteS1, sum_Icc_one_eq_sum_range]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [expMode_half_integer, pow_succ]
  ring

/-- The norm retains the absolute value of the actual alternating prefix. -/
theorem norm_finiteS1_half_integer (k : ℤ) (y : ℝ) :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ =
      |∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))| := by
  rw [finiteS1_half_integer, norm_neg, Complex.norm_real, Real.norm_eq_abs]

section
variable (k : ℤ) {y : ℝ} (hy : 1 ≤ y)
include k y hy

/-- The half-integer refinement in Lemma 2, with its full two-sided O-star interpretation. -/
theorem finiteS1_half_integer_error  :
    |‖finiteS1 ((k : ℝ) + 1 / 2) y‖ - Real.log 2| ≤ 1 / y := by
  rw [norm_finiteS1_half_integer]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnorm :
      |(|∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))|) - Real.log 2| ≤
        |(∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) - Real.log 2| := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog] using
      abs_norm_sub_norm_le
        (∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) (Real.log 2)
  refine (hnorm.trans (alternating_harmonic_prefix_error _)).trans ?_
  exact one_div_le_one_div_of_le (by linarith) (Nat.lt_floor_add_one y).le

/-- The corresponding half-integer upper bound used in the Poisson error. -/
theorem norm_finiteS1_half_integer_le  :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 + 1 / y := by
  have h := (abs_le.mp (finiteS1_half_integer_error k hy)).2
  linarith
end



