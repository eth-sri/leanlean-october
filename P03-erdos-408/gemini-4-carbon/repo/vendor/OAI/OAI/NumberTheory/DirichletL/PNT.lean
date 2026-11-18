module

public import OAI.NumberTheory.DirichletL.Nonvanishing
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PrimeNumberTheoremAnd.PerronFormula

@[expose] public section

namespace Erdos408

theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

end Erdos408

namespace Erdos408

open Complex Metric DirichletCharacter MeasureTheory Filter Asymptotics

open scoped LSeries.notation Topology

/-! ### Partial summation -/

/-- **Partial summation.** If `f` is bounded by one and its partial sums are `a t + O(B)`,
then `L(f, s) = a s / (s - 1) + s I(s)` on `1 < re s`, where `I` is holomorphic on
`0 < re s` and bounded by `B / re s` there. Adapted from `Erdos770.norm_LFunction_le`. -/
lemma exists_LSeries_eq_add {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (a : ℂ) {B : ℝ}
    (hB : ∀ t : ℝ, 1 ≤ t → ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) - a * t‖ ≤ B) :
    ∃ I : ℂ → ℂ, DifferentiableOn ℂ I {s | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → ‖I s‖ ≤ B / s.re) ∧
      ∀ s : ℂ, 1 < s.re → LSeries f s = a * s / (s - 1) + s * I s := by
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl)
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k
  let A : ℝ → ℂ := fun t ↦ S t - a * t
  -- the remainder cut off below one, as a Mellin transform input
  let g : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator fun _ ↦ (1 : ℂ)
  let F : ℝ → ℂ := fun t ↦ g t * S t - g t * (a * t)
  have hF (t : ℝ) : ‖F t‖ ≤ B := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa [F, g, ht, S] using hB t (Set.mem_Ioi.mp ht).le
    · simpa [F, g, ht] using hB₀
  let I : ℂ → ℂ := fun z ↦ ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))
  have hImellin : I = fun z ↦ mellin F (-z) := by
    funext z
    have hint : (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1) • F t) =
        (Set.Ioi (1 : ℝ)).indicator (fun t ↦ A t * (t : ℂ) ^ (-(z + 1))) := by
      funext t
      rw [show -z - 1 = -(z + 1) by ring]
      by_cases ht : t ∈ Set.Ioi (1 : ℝ)
      · simp [F, g, A, ht, mul_comm, mul_sub]
      · simp [F, g, ht]
    rw [mellin, hint, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr zero_le_one]
  refine ⟨I, ?_, ?_, ?_⟩
  · -- `I` is a Mellin transform, holomorphic on the right half-plane
    intro z hz
    have hmellin : DifferentiableAt ℂ (mellin F) (-z) := by
      refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -z.re - 1) ?_ ?_
        (by simpa using (show 0 < z.re from hz)) ?_ (by simp)
      · have hg : LocallyIntegrableOn g (Set.Ici 0) :=
          ((locallyIntegrable_const 1).indicator measurableSet_Ioi).locallyIntegrableOn _
        have h₁ := (locallyIntegrableOn_mul_sum_Icc (m := 1) f le_rfl hg).mono_set
          Set.Ioi_subset_Ici_self
        have h₂ : LocallyIntegrableOn (fun t : ℝ ↦ g t * (a * t)) (Set.Ioi 0) := by
          have : (fun t : ℝ ↦ g t * (a * t)) =
              (Set.Ioi (1 : ℝ)).indicator fun t : ℝ ↦ a * t := by
            funext t
            by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [g, ht]
          rw [this]
          exact ((Continuous.locallyIntegrable (by fun_prop)).indicator
            measurableSet_Ioi).locallyIntegrableOn _
        exact h₁.sub h₂
      · exact IsBigO.of_bound B (Eventually.of_forall fun t ↦ by simpa using hF t)
      · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht
        simp [F, g, not_lt.mpr (Set.mem_Iio.mp ht).le]
    rw [hImellin]
    exact (hmellin.comp z differentiableAt_id.neg).differentiableWithinAt
  · -- bound the integral
    intro s hs
    have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-s.re - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    calc ‖I s‖
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
        refine norm_integral_le_of_norm_le (hrpow.const_mul _) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
        have ht₀ : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        gcongr
        exact hB t (Set.mem_Ioi.mp ht).le
      _ = B / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
          show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
        field_simp
  · -- the integral representation to the right of one
    intro s hs
    have hs₁ : s - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)
      have h₁ : ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ n := by
        calc ∑ k ∈ Finset.Icc 1 n, ‖f k‖
          _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hf k
          _ = n := by simp
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), Real.rpow_one,
        Real.norm_natCast, one_mul]
      exact h₁
    rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
    -- split off the main term `a t`
    have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ A t * (t : ℂ) ^ (-(s + 1)))
        (volume.restrict (Set.Ioi 1)) := by
      have hS : Measurable S :=
        (measurable_from_nat (f := fun n ↦ ∑ k ∈ Finset.Icc 1 n, f k)).comp
          Nat.measurable_floor
      refine ((hS.sub (by fun_prop)).aestronglyMeasurable).mul ?_
      exact (measurable_ofReal.pow_const _).aestronglyMeasurable
    have hA : IntegrableOn (fun t : ℝ ↦ A t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
      have hrpow : IntegrableOn (fun t : ℝ ↦ B * t ^ (-s.re - 1)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
      refine hrpow.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
      have ht₀ : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      gcongr
      exact hB t (Set.mem_Ioi.mp ht).le
    have hpow : IntegrableOn (fun t : ℝ ↦ a * (t : ℂ) ^ (-s)) (Set.Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one).const_mul _
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-(s + 1)) =
        ∫ t in Set.Ioi (1 : ℝ), (A t * (t : ℂ) ^ (-(s + 1)) + a * (t : ℂ) ^ (-s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      have hcpow : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-(s + 1)) * t := by
        rw [show -s = -(s + 1) + 1 by ring, cpow_add _ _ ht₀, cpow_one]
      simp only [A, hcpow]
      ring
    have hmain : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
      have hs₂ : -s + 1 ≠ 0 := by
        rw [show -s + 1 = -(s - 1) by ring]
        exact neg_ne_zero.mpr hs₁
      rw [integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one, ofReal_one, one_cpow,
        show s - 1 = -(-s + 1) by ring]
      field_simp
    rw [hsplit, integral_add hA hpow, integral_const_mul, hmain]
    field_simp
    ring

/-- The partial sums of a nontrivial Dirichlet character are bounded by its modulus.
Copied from `Erdos770.norm_sum_Icc_le`. -/
lemma norm_sum_Icc_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ N := by
  let f : ℕ → ℂ := fun k ↦ χ k
  -- a full period of values sums to zero
  have h₀ : ∑ k ∈ Finset.range N, f k = 0 := by
    rw [← χ.sum_eq_zero_of_ne_one hχ]
    exact Finset.sum_nbij' (fun k ↦ (k : ZMod N)) ZMod.val (by simp)
      (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x))
      (fun k hk ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hk))
      (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)
  -- so does a shifted full period
  have hperiod : ∑ k ∈ Finset.range N, f (k + 1) = 0 := by
    have h₁ := Finset.sum_range_succ f N
    have h₂ := Finset.sum_range_succ' f N
    have hN : f N = f 0 := by simp [f]
    linear_combination h₁ - h₂ + h₀ + hN
  -- rewrite the partial sums over `range`
  have hIcc (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  -- bound by strong induction, peeling off full periods
  have hbound (n : ℕ) : ‖∑ k ∈ Finset.range n, f (k + 1)‖ ≤ N := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases lt_or_ge n N with hn | hn
      · calc ‖∑ k ∈ Finset.range n, f (k + 1)‖
          _ ≤ ∑ k ∈ Finset.range n, ‖f (k + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
          _ = n := by simp
          _ ≤ N := by exact_mod_cast hn.le
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        have hshift (k : ℕ) : f (N + k + 1) = f (k + 1) := by
          change χ ((N + k + 1 : ℕ) : ZMod N) = χ ((k + 1 : ℕ) : ZMod N)
          push_cast
          rw [ZMod.natCast_self, zero_add]
        rw [Finset.sum_range_add, hperiod, zero_add]
        simp_rw [hshift]
        exact ih m (by have := NeZero.pos N; omega)
  exact (hIcc n).symm ▸ hbound n

/-- A nontrivial Dirichlet L-function grows at most linearly in `‖s‖` to the right of zero.
Adapted from `Erdos770.norm_LFunction_le`. -/
theorem norm_LFunction_le_of_ne_one {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) : ‖LFunction χ s‖ ≤ k * ‖s‖ / s.re := by
  obtain ⟨I, hI, hIb, hL⟩ := exists_LSeries_eq_add (f := fun n ↦ χ n)
    (fun n ↦ χ.norm_le_one n) 0 (B := k) (fun t _ ↦ by simpa using norm_sum_Icc_le hχ ⌊t⌋₊)
  -- both sides are analytic on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hEq : Set.EqOn (LFunction χ) (fun z ↦ z * I z) U := by
    have hLan := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
    refine hLan.eqOn_of_preconnected_of_eventuallyEq
      ((differentiableOn_id.mul hI).analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [LFunction_eq_LSeries χ hz, hL z hz]
    simp
  calc ‖LFunction χ s‖
    _ = ‖s‖ * ‖I s‖ := by rw [hEq hs, norm_mul]
    _ ≤ ‖s‖ * (k / s.re) := by gcongr; exact hIb s hs
    _ = k * ‖s‖ / s.re := by ring

/-- The Riemann zeta function is `s / (s - 1) + O(‖s‖ / re s)` to the right of zero. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hfloor (t : ℝ) (ht : 1 ≤ t) :
      ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) - 1 * t‖ ≤ 1 := by
    have h₁ := Nat.floor_le (zero_le_one.trans ht)
    have h₂ := Nat.lt_floor_add_one t
    simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
      nsmul_eq_mul, mul_one, one_mul]
    rw [show (⌊t⌋₊ : ℂ) - t = ((⌊t⌋₊ - t : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨I, hI, hIb, hL⟩ := exists_LSeries_eq_add (f := 1) (fun n ↦ by simp) 1 hfloor
  -- `(s - 1) ζ(s)` is entire, and equals `s + (s - 1) s I(s)` on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hEq : Set.EqOn (LFunctionTrivChar₁ 1) (fun z ↦ z + (z - 1) * z * I z) U := by
    have hZan := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd hU
    refine hZan.eqOn_of_preconnected_of_eventuallyEq
      ((differentiableOn_id.add (((differentiableOn_id.sub_const 1).mul
        differentiableOn_id).mul hI)).analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz₁ : z - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [LFunctionTrivChar₁, Function.update_of_ne (sub_ne_zero.mp hz₁), LFunctionTrivChar,
      LFunction_modOne_eq, ← LSeries_one_eq_riemannZeta hz, hL z hz]
    field_simp
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  have hζ : riemannZeta s = s / (s - 1) + s * I s := by
    have h := hEq hs
    rw [LFunctionTrivChar₁, Function.update_of_ne hs₁, LFunctionTrivChar,
      LFunction_modOne_eq] at h
    field_simp
    linear_combination h
  calc ‖riemannZeta s‖
    _ ≤ ‖s / (s - 1)‖ + ‖s * I s‖ := by rw [hζ]; exact norm_add_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
      rw [norm_div, norm_mul]
      gcongr
      exact hIb s hs
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by ring

/-- The L-function of the trivial character mod `k` is at most `k` times the bound
`norm_riemannZeta_le` for zeta. -/
theorem norm_LFunction_one_le {k : ℕ} [NeZero k] {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖LFunction (1 : DirichletCharacter ℂ k) s‖ ≤ k * (‖s‖ / ‖s - 1‖ + ‖s‖ / s.re) := by
  rw [← LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta hs₁, norm_mul]
  gcongr
  · -- each Euler factor is at most `2 ≤ p`, and `∏ p ∣ k`
    rw [norm_prod]
    calc ∏ p ∈ k.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
      _ ≤ ∏ p ∈ k.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ ?_)
        have hp := Nat.prime_of_mem_primeFactors hp
        calc ‖1 - (p : ℂ) ^ (-s)‖
          _ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
            rw [norm_one, norm_natCast_cpow_of_pos hp.pos]
            gcongr
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le)
              (by simp; linarith)
          _ ≤ p := by exact_mod_cast hp.two_le
      _ ≤ k := by
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd (NeZero.pos k) (Nat.prod_primeFactors_dvd k)
  · exact norm_riemannZeta_le hs hs₁

/-- `‖s‖ / re s ≤ 1 + 2 |im s|` on `re s ≥ 1/2`. -/
private lemma norm_div_re_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖s‖ / s.re ≤ 1 + 2 * |s.im| := by
  have hσ : 0 < s.re := by linarith
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hσ] at h
  rw [div_le_iff₀ hσ]
  nlinarith [abs_nonneg s.im]

/-- Polynomial growth of Dirichlet L-functions on `re s ≥ 1/2`, away from `s = 1`, with an
explicit constant. -/
theorem norm_LFunction_le_two_mul {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs₁ : 1 ≤ ‖s - 1‖) :
    ‖LFunction χ s‖ ≤ 2 * k * (|s.im| + 3) := by
  have hσ : 0 < s.re := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht := norm_div_re_le hs
  have hti := abs_nonneg s.im
  rcases eq_or_ne χ 1 with rfl | hχ
  · have hs₁' : s ≠ 1 := by
      rintro rfl
      norm_num at hs₁
    -- `‖s‖ / ‖s - 1‖ ≤ 1 + 1 / ‖s - 1‖ ≤ 2`
    have hpole : ‖s‖ / ‖s - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := norm_le_norm_sub_add s 1
      rw [norm_one] at this
      linarith
    calc ‖LFunction 1 s‖
      _ ≤ k * (‖s‖ / ‖s - 1‖ + ‖s‖ / s.re) := norm_LFunction_one_le hσ hs₁'
      _ ≤ k * (2 + (1 + 2 * |s.im|)) := by gcongr
      _ ≤ 2 * k * (|s.im| + 3) := by nlinarith
  · calc ‖LFunction χ s‖
      _ ≤ k * ‖s‖ / s.re := norm_LFunction_le_of_ne_one hχ hσ
      _ = k * (‖s‖ / s.re) := by ring
      _ ≤ k * (1 + 2 * |s.im|) := by gcongr
      _ ≤ 2 * k * (|s.im| + 3) := by nlinarith

/-! ### Bounds to the right of one -/

/-- The zeta series `∑ (n + 1) ^ (-σ)` is bounded by `σ / (σ - 1)`. Copied from the proof of
`Erdos770.le_norm_LFunction`. -/
private lemma tsum_one_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ σ / (σ - 1) := by
  have hσ₀ : 0 < σ := by linarith
  have hσ₁ : 0 < σ - 1 := by linarith
  have h₀ : 0 ≤ ZetaAsymptotics.termTSum σ :=
    tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) σ
  rw [ZetaAsymptotics.termTSum_of_lt hσ] at h₀
  rw [le_div_iff₀ hσ₁]
  have h₁ := mul_le_mul_of_nonneg_left (sub_nonneg.mp h₀) (mul_nonneg hσ₀.le hσ₁.le)
  field_simp at h₁
  linarith

/-- A Dirichlet L-function is bounded above by `re s / (re s - 1)` to the right of one. -/
theorem norm_LFunction_le_of_one_lt_re {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {s : ℂ} (hs : 1 < s.re) : ‖LFunction χ s‖ ≤ s.re / (s.re - 1) := by
  have hsum : LSeriesSummable (fun n ↦ χ n) s := LSeriesSummable_of_one_lt_re χ hs
  have hζsum : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s.re := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  -- each term is bounded by the corresponding zeta term
  have hterm (n : ℕ) : ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ s.re := by
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte]
    push_cast
    gcongr
    exact χ.norm_le_one _
  have hshift : Summable fun n : ℕ ↦ ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr hsum.norm
  rw [LFunction_eq_LSeries χ hs, LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  calc ‖∑' n : ℕ, LSeries.term (fun n ↦ χ n) s (n + 1)‖
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ := norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := hshift.tsum_le_tsum hterm hζsum
    _ ≤ s.re / (s.re - 1) := tsum_one_div_rpow_le hs

open scoped ArithmeticFunction.Moebius in
/-- A Dirichlet L-function is bounded below by `(re s - 1) / re s` to the right of one.
Copied from `Erdos770.le_norm_LFunction`. -/
theorem le_norm_LFunction {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {s : ℂ}
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  -- the L-series of `μ χ` inverts `L(s, χ)`
  have hmul : LFunction χ s * LSeries (↗χ * ↗μ) s = 1 := by
    rw [LFunction_eq_LSeries χ hs]
    exact LSeries.mul_mu_eq_one χ hs
  have hsum : LSeriesSummable (↗χ * ↗μ) s :=
    LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hζsum : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s.re := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  -- each term of the `μ χ` series is bounded by the corresponding zeta term
  have hterm (n : ℕ) :
      ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ s.re := by
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte, Pi.mul_apply, norm_mul]
    push_cast
    gcongr
    calc ‖χ (n + 1)‖ * ‖(μ (n + 1) : ℂ)‖
      _ ≤ 1 * 1 := by
        gcongr
        · exact χ.norm_le_one _
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = 1 := one_mul 1
  have hM : ‖LSeries (↗χ * ↗μ) s‖ ≤ s.re / (s.re - 1) := by
    have hshift : Summable fun n : ℕ ↦ ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
      (summable_nat_add_iff 1).mpr hsum.norm
    rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    calc ‖∑' n : ℕ, LSeries.term (↗χ * ↗μ) s (n + 1)‖
      _ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
        norm_tsum_le_tsum_norm hshift
      _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := hshift.tsum_le_tsum hterm hζsum
      _ ≤ s.re / (s.re - 1) := tsum_one_div_rpow_le hs
  -- invert the bound
  have hnorm : ‖LFunction χ s‖ * ‖LSeries (↗χ * ↗μ) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hMpos : 0 < ‖LSeries (↗χ * ↗μ) s‖ := by
    refine norm_pos_iff.mpr fun h ↦ ?_
    simp [h] at hmul
  rw [eq_comm, ← div_eq_iff hMpos.ne'] at hnorm
  rw [← hnorm, ← one_div_div]
  exact one_div_le_one_div_of_le hMpos hM

/-! ### Borel–Carathéodory and three circles -/

/-- A holomorphic function on an open set whose exponential is holomorphic is holomorphic.
Copied from `Erdos770.differentiableOn_of_exp_eq`. -/
lemma differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U) {G g : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U) (hg : ContinuousOn g U)
    (he : Set.EqOn (Complex.exp ∘ g) G U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hGc : DifferentiableAt ℂ G z := (hG z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z) (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (G z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (G w)) =ᶠ[nhds z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hGc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- A holomorphic function on a ball with no zeros and value `1` at the center has a
holomorphic logarithm vanishing at the center. Copied from `Erdos770.exists_holomorphic_log`. -/
lemma exists_holomorphic_log {G : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball c R)) (h0 : ∀ z ∈ ball c R, G z ≠ 0) (hc : G c = 1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧
      Set.EqOn (Complex.exp ∘ h) G (ball c R) ∧ h c = 0 := by
  have : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball
    hG.continuousOn (by rintro ⟨z, hz, heq⟩; exact h0 z hz heq)
  refine ⟨fun z ↦ h z - h c, (differentiableOn_of_exp_eq isOpen_ball hG hh he).sub_const _,
    fun z hz ↦ ?_, sub_self _⟩
  have hec : Complex.exp (h c) = 1 := (he (mem_ball_self hR)).trans hc
  simp only [Function.comp_apply, Complex.exp_sub, hec, div_one]
  exact he hz

/-- **Borel–Carathéodory** followed by a **Cauchy estimate**: if `h` is holomorphic on
`ball c r₂` with `h c = 0` and `re h ≤ B` there, then `‖h'‖ = O(B)` on `closedBall c r₁`.
Copied from `Erdos770.norm_deriv_le_of_re_le`. -/
lemma norm_deriv_le_of_re_le {h : ℂ → ℂ} {c z : ℂ} {r₁ r₂ B : ℝ} (h₁ : 0 ≤ r₁)
    (h₁₂ : r₁ < r₂) (hB : 0 ≤ B) (hh : DifferentiableOn ℂ h (ball c r₂)) (hc : h c = 0)
    (hre : ∀ w ∈ ball c r₂, (h w).re ≤ B) (hz : z ∈ closedBall c r₁) :
    ‖deriv h z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * B := by
  set r₃ := (r₁ + r₂) / 2 with hr₃
  have h₁₃ : r₁ < r₃ := by linarith
  have h₃₂ : r₃ < r₂ := by linarith
  have hC : 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 = 2 * r₃ / (r₂ - r₃) / (r₃ - r₁) := by
    have : r₂ - r₁ ≠ 0 := by linarith
    rw [show r₂ - r₃ = (r₂ - r₁) / 2 by linarith, show r₃ - r₁ = (r₂ - r₁) / 2 by linarith, hr₃]
    field_simp
    ring
  rw [hC]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set C := 2 * r₃ / (r₂ - r₃) / (r₃ - r₁)
  have hCpos : 0 < C := by
    have : 0 < r₃ := by linarith
    have : 0 < r₂ - r₃ := by linarith
    have : 0 < r₃ - r₁ := by linarith
    positivity
  -- Borel–Carathéodory on `closedBall c r₃`, recentred at the origin
  have hbc : ∀ w ∈ closedBall c r₃, ‖h w‖ ≤ 2 * (B + ε / C) * r₃ / (r₂ - r₃) := by
    intro w hw
    have hw' : ‖w - c‖ ≤ r₃ := by simpa [dist_eq_norm] using hw
    have hh' : DifferentiableOn ℂ (fun v ↦ h (c + v)) (ball 0 r₂) := by
      refine hh.comp (by fun_prop) fun v hv ↦ ?_
      simpa [mem_ball, dist_eq_norm] using hv
    have hb := Complex.borelCaratheodory (M := B + ε / C) (by positivity) hh'
      (fun v hv ↦ (hre _ (by simpa [mem_ball, dist_eq_norm] using hv)).trans
        (le_add_of_nonneg_right (by positivity)))
      (by linarith) (show w - c ∈ ball 0 r₂ by simpa using hw'.trans_lt h₃₂)
    simp only [add_sub_cancel, add_zero, hc, norm_zero, zero_mul, zero_div] at hb
    refine hb.trans ?_
    have : 0 < r₂ - ‖w - c‖ := by linarith
    have : 0 ≤ r₃ := by linarith
    gcongr
  -- Cauchy estimate on `sphere z (r₃ - r₁)`
  have hzc : ‖z - c‖ ≤ r₁ := by simpa [dist_eq_norm] using hz
  have hsub : closedBall z (r₃ - r₁) ⊆ closedBall c r₃ := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ r₃ := by linarith
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith)
    (hh.diffContOnCl_ball (hsub.trans (closedBall_subset_ball h₃₂)))
    (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
  refine hd.trans (le_of_eq ?_)
  rw [show 2 * (B + ε / C) * r₃ / (r₂ - r₃) / (r₃ - r₁) = C * (B + ε / C) by simp only [C]; ring,
    mul_add, mul_div_cancel₀ _ hCpos.ne']

/-- **Borel–Carathéodory**, recentred at `c`: if `h` is holomorphic on `ball c R` with
`h c = 0` and `re h ≤ B` there, then `‖h‖ ≤ 2 B r / (R - r)` on `closedBall c r`. -/
lemma norm_le_of_re_le {h : ℂ → ℂ} {c z : ℂ} {r R B : ℝ} (hrR : r < R) (hB : 0 < B)
    (hh : DifferentiableOn ℂ h (ball c R)) (hc : h c = 0)
    (hre : ∀ w ∈ ball c R, (h w).re ≤ B) (hz : z ∈ closedBall c r) :
    ‖h z‖ ≤ 2 * B * r / (R - r) := by
  have hz' : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
  have hh' : DifferentiableOn ℂ (fun v ↦ h (c + v)) (ball 0 R) := by
    refine hh.comp (by fun_prop) fun v hv ↦ ?_
    simpa [mem_ball, dist_eq_norm] using hv
  have hb := Complex.borelCaratheodory_zero (M := B) hB hh'
    (fun v hv ↦ hre _ (by simpa [mem_ball, dist_eq_norm] using hv))
    (by linarith [norm_nonneg (z - c)]) (show z - c ∈ ball 0 R by simpa using hz'.trans_lt hrR)
    (by simpa using hc)
  simp only [add_sub_cancel] at hb
  refine hb.trans ?_
  have : 0 < R - ‖z - c‖ := by linarith
  have : 0 < R - r := by linarith
  have : 0 ≤ r := (norm_nonneg _).trans hz'
  gcongr

/-- **Borel–Carathéodory** for logarithmic derivatives: if `F` is holomorphic and zero-free
on `ball c r₂` with `‖F‖ ≤ M ‖F c‖` there, then `‖F' / F‖ = O(log M)` on `closedBall c r₁`. -/
theorem norm_logDeriv_le_of_norm_le {F : ℂ → ℂ} {c z : ℂ} {r₁ r₂ M : ℝ} (h₁ : 0 ≤ r₁)
    (h₁₂ : r₁ < r₂) (hM : 1 ≤ M) (hF : DifferentiableOn ℂ F (ball c r₂))
    (h0 : ∀ w ∈ ball c r₂, F w ≠ 0) (hFM : ∀ w ∈ ball c r₂, ‖F w‖ ≤ M * ‖F c‖)
    (hz : z ∈ closedBall c r₁) :
    ‖deriv F z / F z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * Real.log M := by
  have h₂ : 0 < r₂ := h₁.trans_lt h₁₂
  have hc0 : F c ≠ 0 := h0 c (mem_ball_self h₂)
  -- a holomorphic logarithm `h` of `F / F c`, with `re h ≤ log M`
  obtain ⟨h, hh, hexp, hc⟩ := exists_holomorphic_log h₂ (G := fun w ↦ F w / F c)
    (hF.div_const _) (fun w hw ↦ div_ne_zero (h0 w hw) hc0) (div_self hc0)
  have hre : ∀ w ∈ ball c r₂, (h w).re ≤ Real.log M := by
    intro w hw
    have hFw : 0 < ‖F w‖ := norm_pos_iff.mpr (h0 w hw)
    have hFc : 0 < ‖F c‖ := norm_pos_iff.mpr hc0
    calc (h w).re = Real.log ‖Complex.exp (h w)‖ := by rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log (‖F w‖ / ‖F c‖) := by
        rw [← norm_div]; exact congrArg _ (congrArg _ (hexp hw))
      _ ≤ Real.log M := Real.log_le_log (div_pos hFw hFc) ((div_le_iff₀ hFc).mpr (hFM w hw))
  -- the logarithmic derivative of `F` is `h'`
  have hzb : z ∈ ball c r₂ := closedBall_subset_ball h₁₂ hz
  have hlogh : deriv F z / F z = deriv h z := by
    have hev : (fun w ↦ F w / F c) =ᶠ[nhds z] Complex.exp ∘ h := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw using (hexp hw).symm
    have hFF : logDeriv (fun w ↦ F w / F c) z = logDeriv F z := by
      simp_rw [div_eq_mul_inv]
      exact logDeriv_mul_const z _ (inv_ne_zero hc0)
    rw [← logDeriv_apply, ← hFF, (logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_comp Complex.differentiableAt_exp (hh.differentiableAt (isOpen_ball.mem_nhds hzb)),
      Complex.logDeriv_exp, Pi.one_apply, one_mul]
  rw [hlogh]
  exact norm_deriv_le_of_re_le h₁ h₁₂ (Real.log_nonneg hM) hh hc hre hz

/-- **Hadamard's three circles theorem**, from the three lines theorem through
`w ↦ c + exp w`: if `h` is holomorphic on `closedBall c r₃`, with `‖h‖ ≤ a` on
`sphere c r₁` and `‖h‖ ≤ b` on `closedBall c r₃`, then `‖h z‖ ≤ a ^ (1 - θ) * b ^ θ` for
`r₁ ≤ ‖z - c‖ ≤ r₃`, where `θ = log (‖z - c‖ / r₁) / log (r₃ / r₁)`. -/
theorem norm_le_of_three_circles {h : ℂ → ℂ} {c z : ℂ} {r₁ r₃ a b : ℝ} (h₁ : 0 < r₁)
    (h₁₃ : r₁ < r₃) (hh : DifferentiableOn ℂ h (closedBall c r₃))
    (ha : ∀ w ∈ sphere c r₁, ‖h w‖ ≤ a) (hb : ∀ w ∈ closedBall c r₃, ‖h w‖ ≤ b)
    (hz₁ : r₁ ≤ ‖z - c‖) (hz₃ : ‖z - c‖ ≤ r₃) :
    ‖h z‖ ≤ a ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      b ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hlu : Real.log r₁ < Real.log r₃ := Real.log_lt_log h₁ h₁₃
  let g : ℂ → ℂ := fun w ↦ h (c + Complex.exp w)
  have hmem (w : ℂ) (hw : w.re ≤ Real.log r₃) : c + Complex.exp w ∈ closedBall c r₃ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hw
      _ = r₃ := Real.exp_log (h₁.trans h₁₃)
  have hz0 : z - c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₁
    linarith
  -- `g` is holomorphic on the half-plane `re w ≤ log r₃`
  have hg : DifferentiableOn ℂ g {w | w.re ≤ Real.log r₃} :=
    hh.comp (by fun_prop) fun w hw ↦ hmem w hw
  have hcl : closure (Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) ⊆
      {w | w.re ≤ Real.log r₃} :=
    closure_minimal (fun w hw ↦ hw.2.le) (isClosed_le continuous_re continuous_const)
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' (f := g)
    (z := Complex.log (z - c)) (a := a) (b := b) hlu ?_ ((hg.mono hcl).diffContOnCl) ?_ ?_ ?_
  · rw [Complex.log_re] at key
    calc ‖h z‖ = ‖g (Complex.log (z - c))‖ := by
          simp only [g]
          rw [Complex.exp_log hz0, add_sub_cancel]
      _ ≤ _ := key
  · rw [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Complex.log_re]
    exact ⟨Real.log_le_log h₁ hz₁, Real.log_le_log (h₁.trans_le hz₁) hz₃⟩
  · refine ⟨b, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmem w hw.2)
  · intro w hw
    refine ha _ ?_
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    rw [hw, Real.exp_log h₁]
  · intro w hw
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    exact hb _ (hmem w hw.le)

/-! ### The three bounds -/

/-- `1 ≤ log (k (|t| + 3))`. -/
private lemma one_le_log_mul (k : ℕ) [NeZero k] (t : ℝ) : 1 ≤ Real.log (k * (|t| + 3)) := by
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  nlinarith [abs_nonneg t]

/-- The distance from `s` to the center `2 + i im s` is `|re s - 2|`. -/
private lemma norm_sub_center (s : ℂ) : ‖s - (2 + s.im * I)‖ = |s.re - 2| := by
  have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [this, norm_real, Real.norm_eq_abs]

/-- Coordinates of a point of `ball c r`. -/
private lemma mem_ball_aux {c w : ℂ} {r : ℝ} (hw : w ∈ ball c r) :
    c.re - r < w.re ∧ w.re < c.re + r ∧ |w.im - c.im| < r := by
  rw [mem_ball, dist_eq_norm] at hw
  have h₁ := abs_re_le_norm (w - c)
  have h₂ := abs_im_le_norm (w - c)
  simp only [sub_re, sub_im] at h₁ h₂
  refine ⟨?_, ?_, by linarith⟩
  · linarith [neg_abs_le (w.re - c.re)]
  · linarith [le_abs_self (w.re - c.re)]

/-- Polynomial growth of Dirichlet L-functions on `re s ≥ 1/2`, away from
`s = 1`. -/
theorem norm_LFunction_le_poly : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 1 / 2 ≤ s.re → 1 ≤ ‖s - 1‖ →
    ‖DirichletCharacter.LFunction χ s‖ ≤ C * k * (|s.im| + 3) :=
  ⟨2, fun _ _ χ _ hs hs₁ ↦ norm_LFunction_le_two_mul χ hs hs₁⟩

/-- The logarithmic derivative of a Dirichlet L-function is `O(log (k (|t| + 3)))`
on `15/16 ≤ re s ≤ 2`, away from `s = 1`. -/
theorem norm_logDeriv_LFunction_le : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 15 / 16 ≤ s.re → s.re ≤ 2 → 1 ≤ ‖s - 1‖ →
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      C * Real.log (k * (|s.im| + 3)) := by
  refine ⟨11201, fun k _ χ s hσ hσ₂ hs₁ ↦ ?_⟩
  set t := s.im
  set c : ℂ := 2 + t * I with hc
  set M : ℝ := 16 * k * (|t| + 3) ^ 2 with hM
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have ht := abs_nonneg t
  have hℓ := one_le_log_mul k t
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = t := by simp [c]
  -- the disc `ball c (9/8)` lies in `7/8 < re w`, with `‖w‖ ≤ |t| + 17/4` there
  have hball (w : ℂ) (hw : w ∈ ball c (9 / 8)) : 7 / 8 < w.re ∧ ‖w‖ ≤ |t| + 17 / 4 := by
    obtain ⟨h₁, h₂, h₃⟩ := mem_ball_aux hw
    rw [hcre] at h₁ h₂
    rw [hcim] at h₃
    refine ⟨by linarith, ?_⟩
    have h₄ := Complex.norm_le_abs_re_add_abs_im w
    have h₅ : |w.re| ≤ 2 + 9 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h₆ : |w.im| ≤ |t| + 9 / 8 := by
      have := abs_sub_abs_le_abs_sub w.im t
      linarith
    linarith
  have hLc : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have h := le_norm_LFunction χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    linarith
  have hs : s ∈ closedBall c (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_center, abs_of_nonpos (by linarith)]
    linarith
  -- a function `F` holomorphic and zero-free on the disc, with `L'/L = F'/F + O(1)` at `s`
  obtain ⟨F, hF, hF0, hFM, hLF⟩ : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball c (9 / 8)) ∧
      (∀ w ∈ ball c (9 / 8), F w ≠ 0) ∧ (∀ w ∈ ball c (9 / 8), ‖F w‖ ≤ M * ‖F c‖) ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ‖deriv F s / F s‖ + 1 := by
    rcases eq_or_ne χ 1 with rfl | hχ
    · -- the trivial character: remove the pole with `(s - 1) L(s, χ)`
      refine ⟨LFunctionTrivChar₁ k, (differentiable_LFunctionTrivChar₁ k).differentiableOn,
        ?_, ?_, ?_⟩
      · intro w hw
        rcases eq_or_ne w 1 with rfl | hw₁
        · exact LFunctionTrivChar₁_apply_one_ne_zero k
        · rw [LFunctionTrivChar₁, Function.update_of_ne hw₁]
          exact mul_ne_zero (sub_ne_zero.mpr hw₁)
            (LFunction_ne_zero_of_seven_eighths_lt_re 1 (hball w hw).1 (fun h ↦ hw₁ h.2))
      · have hc₁ : c ≠ 1 := by
          intro h
          have := congrArg re h
          rw [hcre] at this
          norm_num at this
        have hFc : 1 / 2 ≤ ‖LFunctionTrivChar₁ k c‖ := by
          rw [LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul]
          have h₁ : 1 ≤ ‖c - 1‖ := by
            have := abs_re_le_norm (c - 1)
            rw [sub_re, hcre] at this
            norm_num at this
            exact this
          calc (1 / 2 : ℝ) = 1 * (1 / 2) := by norm_num
            _ ≤ ‖c - 1‖ * ‖LFunction 1 c‖ := mul_le_mul h₁ hLc (by norm_num) (by positivity)
        intro w hw
        obtain ⟨hw₁, hw₂⟩ := hball w hw
        have hbound : ‖LFunctionTrivChar₁ k w‖ ≤ 8 * k * (|t| + 3) ^ 2 := by
          rcases eq_or_ne w 1 with rfl | hw1
          · simp only [LFunctionTrivChar₁, Function.update_self]
            calc ‖∏ p ∈ k.primeFactors, (1 - (p : ℂ)⁻¹)‖
              _ ≤ ∏ p ∈ k.primeFactors, (1 : ℝ) := by
                rw [norm_prod]
                refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ ?_)
                have hp := (Nat.prime_of_mem_primeFactors hp).one_lt
                have hp' : (1 : ℝ) < p := by exact_mod_cast hp
                rw [show (1 - (p : ℂ)⁻¹) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring,
                  norm_real, Real.norm_eq_abs, abs_le]
                have : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by linarith)
                have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp'
                constructor <;> linarith
              _ ≤ 8 * k * (|t| + 3) ^ 2 := by
                rw [Finset.prod_const_one]
                nlinarith
          · rw [LFunctionTrivChar₁, Function.update_of_ne hw1, norm_mul]
            have hL := norm_LFunction_one_le (k := k) (by linarith : 0 < w.re) hw1
            have hw1' : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
            have hw1'' : ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
            have hwre : 0 < w.re := by linarith
            calc ‖w - 1‖ * ‖LFunction 1 w‖
              _ ≤ ‖w - 1‖ * (k * (‖w‖ / ‖w - 1‖ + ‖w‖ / w.re)) := by gcongr
              _ = k * (‖w‖ + ‖w - 1‖ * ‖w‖ / w.re) := by field_simp
              _ ≤ k * ((|t| + 17 / 4) + (|t| + 21 / 4) * (|t| + 17 / 4) / (7 / 8)) := by
                gcongr
                linarith
              _ ≤ k * (8 * (|t| + 3) ^ 2) := by
                gcongr
                rw [add_div' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
                nlinarith
              _ = 8 * k * (|t| + 3) ^ 2 := by ring
        calc ‖LFunctionTrivChar₁ k w‖
          _ ≤ 8 * k * (|t| + 3) ^ 2 := hbound
          _ = M * (1 / 2) := by rw [hM]; ring
          _ ≤ M * ‖LFunctionTrivChar₁ k c‖ := by gcongr
      · -- `F'/F = L'/L + 1/(s - 1)`
        have hs1 : s ≠ 1 := by
          rintro rfl
          norm_num at hs₁
        have hLs : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
          LFunction_ne_zero_of_seven_eighths_lt_re 1 (by linarith) (fun h ↦ hs1 h.2)
        have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        rw [deriv_LFunctionTrivChar₁_apply_of_ne_one k hs1, LFunctionTrivChar₁,
          Function.update_of_ne hs1]
        have h : ((s - 1) * deriv (LFunctionTrivChar k) s + LFunctionTrivChar k s) /
            ((s - 1) * LFunctionTrivChar k s) =
            deriv (LFunctionTrivChar k) s / LFunctionTrivChar k s + 1 / (s - 1) := by
          field_simp
        rw [h]
        set q := deriv (LFunctionTrivChar k) s / LFunctionTrivChar k s
        calc ‖q‖
          _ = ‖(q + 1 / (s - 1)) - 1 / (s - 1)‖ := by ring_nf
          _ ≤ ‖q + 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
          _ ≤ ‖q + 1 / (s - 1)‖ + 1 := by
            gcongr
            rw [norm_div, norm_one]
            exact div_le_one_of_le₀ hs₁ (norm_nonneg _)
    · -- a nontrivial character: `L` itself
      refine ⟨LFunction χ, (differentiable_LFunction hχ).differentiableOn,
        fun w hw ↦ LFunction_ne_zero_of_seven_eighths_lt_re χ (hball w hw).1 (fun h ↦ hχ h.1),
        fun w hw ↦ ?_, le_add_of_nonneg_right zero_le_one⟩
      obtain ⟨hw₁, hw₂⟩ := hball w hw
      calc ‖LFunction χ w‖
        _ ≤ k * ‖w‖ / w.re := norm_LFunction_le_of_ne_one hχ (by linarith)
        _ ≤ k * (|t| + 17 / 4) / (7 / 8) := by gcongr
        _ ≤ k * (8 * (|t| + 3) ^ 2) := by
          rw [mul_div_assoc]
          gcongr
          rw [div_le_iff₀ (by norm_num)]
          nlinarith
        _ = M * (1 / 2) := by rw [hM]; ring
        _ ≤ M * ‖LFunction χ c‖ := by gcongr
  -- Borel–Carathéodory on `ball c (9/8)`
  have hM₁ : 1 ≤ M := by rw [hM]; nlinarith
  have hBC := norm_logDeriv_le_of_norm_le (by norm_num) (by norm_num) hM₁ hF hF0 hFM hs
  have hlogM : Real.log M ≤ 5 * Real.log (k * (|t| + 3)) := by
    have hx : 3 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    have hx' : |t| + 3 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
    refine Real.log_le_log (by positivity) ?_
    calc M = 16 * (k * (|t| + 3)) * (|t| + 3) := by rw [hM]; ring
      _ ≤ 16 * (k * (|t| + 3)) * (k * (|t| + 3)) := by gcongr
      _ ≤ (k * (|t| + 3)) ^ 3 * (k * (|t| + 3)) * (k * (|t| + 3)) := by
        gcongr
        calc (16 : ℝ) ≤ 3 ^ 3 := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) hx 3
      _ = (k * (|t| + 3)) ^ 5 := by ring
  calc ‖deriv (LFunction χ) s / LFunction χ s‖
    _ ≤ ‖deriv F s / F s‖ + 1 := hLF
    _ ≤ 4 * (17 / 16 + 9 / 8) / (9 / 8 - 17 / 16) ^ 2 * Real.log M + 1 := by gcongr
    _ ≤ 2240 * (5 * Real.log (k * (|t| + 3))) + 1 := by norm_num; linarith
    _ ≤ 11201 * Real.log (k * (|t| + 3)) := by linarith

/-- On `63/64 ≤ re s ≤ 2` and `|im s| ≥ 3`, a Dirichlet L-function is at most
`exp(C √(log (k (|t| + 3))))`. -/
theorem norm_LFunction_le_exp_sqrt : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 63 / 64 ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im| →
    ‖DirichletCharacter.LFunction χ s‖ ≤
      Real.exp (C * Real.sqrt (Real.log (k * (|s.im| + 3)))) := by
  refine ⟨193537, fun k _ χ s hσ hσ₂ ht₃ ↦ ?_⟩
  set t := s.im
  set c : ℂ := 2 + t * I with hc
  set ℓ := Real.log (k * (|t| + 3)) with hℓdef
  set A : ℝ := 193536 with hA
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hℓ : 1 ≤ ℓ := one_le_log_mul k t
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = t := by simp [c]
  -- the disc `ball c (9/8)` lies in `7/8 < re w`, at distance at least one from `1`
  have hball (w : ℂ) (hw : w ∈ ball c (9 / 8)) :
      7 / 8 < w.re ∧ 1 ≤ ‖w - 1‖ ∧ |w.im| ≤ |t| + 9 / 8 := by
    obtain ⟨h₁, -, h₃⟩ := mem_ball_aux hw
    rw [hcre] at h₁
    rw [hcim] at h₃
    have h₄ := abs_sub_abs_le_abs_sub w.im t
    have h₅ := abs_sub_abs_le_abs_sub t w.im
    rw [abs_sub_comm] at h₅
    refine ⟨by linarith, ?_, by linarith⟩
    have := abs_im_le_norm (w - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  have hne (w : ℂ) (hw : w ∈ ball c (9 / 8)) : w ≠ 1 := by
    rintro rfl
    have := (hball 1 hw).2.1
    norm_num at this
  have hLd : DifferentiableOn ℂ (LFunction χ) (ball c (9 / 8)) := fun w hw ↦
    (differentiableAt_LFunction χ w (Or.inl (hne w hw))).differentiableWithinAt
  have hL0 (w : ℂ) (hw : w ∈ ball c (9 / 8)) : LFunction χ w ≠ 0 :=
    LFunction_ne_zero_of_seven_eighths_lt_re χ (hball w hw).1 (fun h ↦ hne w hw h.2)
  have hLc : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have h := le_norm_LFunction χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    linarith
  have hLc₂ : ‖LFunction χ c‖ ≤ 2 := by
    have h := norm_LFunction_le_of_one_lt_re χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    exact h
  have hc0 : LFunction χ c ≠ 0 := hL0 c (mem_ball_self (by norm_num))
  -- a holomorphic logarithm `h` of `L / L c` on `ball c (9/8)`
  obtain ⟨h, hh, hexp, hc⟩ := exists_holomorphic_log (by norm_num : (0 : ℝ) < 9 / 8)
    (G := fun w ↦ LFunction χ w / LFunction χ c) (hLd.div_const _)
    (fun w hw ↦ div_ne_zero (hL0 w hw) hc0) (div_self hc0)
  have hre (w : ℂ) (hw : w ∈ ball c (9 / 8)) :
      (h w).re = Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖) := by
    calc (h w).re = Real.log ‖Complex.exp (h w)‖ := by rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖) := by
        rw [← norm_div]; exact congrArg _ (congrArg _ (hexp hw))
  -- `re h ≤ 768` on `ball c (127/128)`, inside `1 < re w`
  have hre₁ : ∀ w ∈ ball c (127 / 128), (h w).re ≤ 768 := by
    intro w hw
    have hw' : w ∈ ball c (9 / 8) := ball_subset_ball (by norm_num) hw
    obtain ⟨h₁, h₂, -⟩ := mem_ball_aux hw
    rw [hcre] at h₁ h₂
    have hLw := norm_LFunction_le_of_one_lt_re χ (s := w) (by linarith)
    have h₃ : w.re / (w.re - 1) ≤ 384 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hpos : 0 < ‖LFunction χ w‖ / ‖LFunction χ c‖ :=
      div_pos (norm_pos_iff.mpr (hL0 w hw')) (norm_pos_iff.mpr hc0)
    rw [hre w hw']
    calc Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖)
      _ ≤ ‖LFunction χ w‖ / ‖LFunction χ c‖ := Real.log_le_self hpos.le
      _ ≤ 384 / (1 / 2) := by gcongr; linarith
      _ = 768 := by norm_num
  -- `re h ≤ 3 ℓ` on `ball c (9/8)`, by polynomial growth
  have hre₂ : ∀ w ∈ ball c (9 / 8), (h w).re ≤ 3 * ℓ := by
    intro w hw
    obtain ⟨h₁, h₂, h₃⟩ := hball w hw
    have hLw := norm_LFunction_le_two_mul χ (s := w) (by linarith) h₂
    have hpos : 0 < ‖LFunction χ w‖ / ‖LFunction χ c‖ :=
      div_pos (norm_pos_iff.mpr (hL0 w hw)) (norm_pos_iff.mpr hc0)
    have hx : 6 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    rw [hre w hw, hℓdef, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
    refine Real.log_le_log hpos ?_
    calc ‖LFunction χ w‖ / ‖LFunction χ c‖
      _ ≤ 2 * k * (|t| + 9 / 8 + 3) / (1 / 2) := by
        refine div_le_div₀ (by positivity) (hLw.trans ?_) (by norm_num) hLc
        gcongr
      _ ≤ 8 * (k * (|t| + 3)) := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      _ ≤ (k * (|t| + 3)) ^ 2 * (k * (|t| + 3)) := by gcongr; nlinarith
      _ = (k * (|t| + 3)) ^ 3 := by ring
  -- Borel–Carathéodory: `‖h‖ ≤ A` on `closedBall c (63/64)`, `‖h‖ ≤ A ℓ` on `closedBall c (17/16)`
  have hA₁ : ∀ w ∈ closedBall c (63 / 64), ‖h w‖ ≤ A := by
    intro w hw
    have := norm_le_of_re_le (r := 63 / 64) (R := 127 / 128) (B := 768) (by norm_num)
      (by norm_num) (hh.mono (ball_subset_ball (by norm_num))) hc hre₁ hw
    rw [hA]
    norm_num at this
    linarith
  have hA₃ : ∀ w ∈ closedBall c (17 / 16), ‖h w‖ ≤ A * ℓ := by
    intro w hw
    have := norm_le_of_re_le (r := 17 / 16) (R := 9 / 8) (B := 3 * ℓ) (by norm_num)
      (by linarith) hh hc hre₂ hw
    rw [hA]
    norm_num at this
    linarith
  -- Hadamard's three circles: `‖h s‖ ≤ A √ℓ`
  have hsqrt : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.mpr hℓ
  have hhs : ‖h s‖ ≤ A * Real.sqrt ℓ := by
    have hsc : ‖s - c‖ = 2 - s.re := by
      rw [norm_sub_center, abs_of_nonpos (by linarith)]
      ring
    by_cases hρ : ‖s - c‖ ≤ 63 / 64
    · have := hA₁ s (by rw [mem_closedBall, dist_eq_norm]; exact hρ)
      nlinarith
    · push Not at hρ
      have key := norm_le_of_three_circles (by norm_num) (by norm_num)
        (hh.mono (closedBall_subset_ball (by norm_num)))
        (fun w hw ↦ hA₁ w (sphere_subset_closedBall hw)) hA₃ hρ.le (by linarith)
      set θ := (Real.log ‖s - c‖ - Real.log (63 / 64)) /
        (Real.log (17 / 16) - Real.log (63 / 64)) with hθ
      have hθ₂ : θ ≤ 1 / 2 := by
        have hlog : Real.log (63 / 64) < Real.log (17 / 16) := Real.log_lt_log (by norm_num)
          (by norm_num)
        have hρ₂ : Real.log ‖s - c‖ ≤ Real.log (65 / 64) :=
          Real.log_le_log (by linarith) (by linarith)
        have h₂ : 2 * Real.log (65 / 64) ≤ Real.log (17 / 16) + Real.log (63 / 64) := by
          rw [← Real.log_mul (by norm_num) (by norm_num),
            show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
          exact Real.log_le_log (by norm_num) (by norm_num)
        rw [hθ, div_le_iff₀ (by linarith)]
        linarith
      calc ‖h s‖
        _ ≤ A ^ (1 - θ) * (A * ℓ) ^ θ := key
        _ = A * ℓ ^ θ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
            ← Real.rpow_add (by positivity)]
          simp
        _ ≤ A * ℓ ^ (1 / 2 : ℝ) := by
          gcongr
        _ = A * Real.sqrt ℓ := by rw [Real.sqrt_eq_rpow]
  -- conclude from `L s = L c exp (h s)`
  have hsb : s ∈ ball c (9 / 8) := by
    rw [mem_ball, dist_eq_norm, norm_sub_center, abs_of_nonpos (by linarith)]
    linarith
  have hLs : LFunction χ s = LFunction χ c * Complex.exp (h s) := by
    have := hexp hsb
    simp only [Function.comp_apply] at this
    rw [this]
    field_simp
  calc ‖LFunction χ s‖
    _ = ‖LFunction χ c‖ * Real.exp (h s).re := by rw [hLs, norm_mul, Complex.norm_exp]
    _ ≤ 2 * Real.exp (A * Real.sqrt ℓ) := by
      gcongr
      exact (re_le_norm _).trans hhs
    _ ≤ Real.exp 1 * Real.exp (A * Real.sqrt ℓ) := by
      gcongr
      linarith [Real.add_one_le_exp 1]
    _ = Real.exp (1 + A * Real.sqrt ℓ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (193537 * Real.sqrt ℓ) := by
      gcongr
      rw [hA]
      linarith

end Erdos408

namespace Erdos408

open Filter Classical

namespace PNT

/-! ### The smoothed Perron formula -/

section Perron

open Complex ArithmeticFunction DirichletCharacter

/-- The integrand `-(L'/L)(s, χ) x^s / (s (s + 1))` of the smoothed explicit
formula. -/
noncomputable def perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / (s * (s + 1)))

open MeasureTheory Set LSeries
open scoped LSeries.notation

/-- On `re s > 1`, `-(L'/L)(s, χ)` is the L-series of `χ Λ`. -/
theorem neg_logDeriv_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s) = LSeries (↗χ * ↗Λ) s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    LSeries_twist_vonMangoldt_eq χ hs, neg_div]

/-- On `re s = 2`, the terms of the L-series of `χ Λ` are dominated by those of `Λ`
at `2`. -/
theorem norm_term_twist_vonMangoldt_le {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.re = 2) (n : ℕ) : ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ 2 n‖ := by
  rw [norm_term_eq, norm_term_eq, hs, show (2 : ℂ).re = 2 by simp]
  split_ifs
  · rfl
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  gcongr
  simpa [norm_mul] using mul_le_of_le_one_left (abs_nonneg (Λ n)) hχ

/-- The terms `Λ(n) / n²` are absolutely summable. -/
theorem summable_norm_term_vonMangoldt : Summable fun n ↦ ‖term ↗Λ 2 n‖ :=
  summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))

/-- On `re s = 2`, `‖(L'/L)(s, χ)‖ ≤ ∑ Λ(n) / n²`. -/
theorem norm_neg_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s.re = 2) :
    ‖-(deriv (LFunction χ) s / LFunction χ s)‖ ≤ ∑' n, ‖term ↗Λ 2 n‖ := by
  have hle := norm_term_twist_vonMangoldt_le χ hs
  have hsum : Summable fun n ↦ ‖term (↗χ * ↗Λ) s n‖ :=
    summable_norm_term_vonMangoldt.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [neg_logDeriv_LFunction_eq χ (by rw [hs]; norm_num), LSeries]
  exact (norm_tsum_le_tsum_norm hsum).trans
    (Summable.tsum_le_tsum hle hsum summable_norm_term_vonMangoldt)

/-- On `re s = 2`, `‖x^s / (s (s + 1))‖ ≤ x² / t²` with `t = im s`. -/
theorem norm_perron_f_le {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    ‖Perron.f x ((2 : ℝ) + t * I)‖ ≤ x ^ 2 / t ^ 2 := by
  set s : ℂ := (2 : ℝ) + t * I
  have hs : ‖s‖ * ‖s + 1‖ = ‖s * (s + 1)‖ := (norm_mul _ _).symm
  have h1 : |t| ≤ ‖s‖ := by simpa [s] using abs_im_le_norm s
  have h2 : |t| ≤ ‖s + 1‖ := by simpa [s] using abs_im_le_norm (s + 1)
  have h3 : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [← hs, ← sq_abs]
    nlinarith [abs_nonneg t]
  rw [Perron.f, norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [s, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    add_zero, Real.rpow_two]
  gcongr

/-- On `re s = 2`, the Perron integrand is dominated by `x^s / (s (s + 1))`. -/
theorem norm_perronIntegrand_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x t : ℝ) :
    ‖perronIntegrand χ x ((2 : ℝ) + t * I)‖ ≤
      (∑' n, ‖term ↗Λ 2 n‖) * ‖Perron.f x ((2 : ℝ) + t * I)‖ := by
  rw [perronIntegrand, norm_mul]
  gcongr
  exact norm_neg_logDeriv_LFunction_le χ (by simp)

/-- The Perron integrand is integrable on the line `re s = 2`. -/
theorem integrable_perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 0 < x) : Integrable fun t : ℝ ↦ perronIntegrand χ x ((2 : ℝ) + t * I) := by
  have hf : Integrable fun t : ℝ ↦ Perron.f x ((2 : ℝ) + t * I) :=
    Perron.isIntegrable hx (by norm_num) (by norm_num)
  have hline : Continuous fun t : ℝ ↦ ((2 : ℝ) : ℂ) + t * I := by fun_prop
  have hL : Continuous fun t : ℝ ↦ LFunction χ ((2 : ℝ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    refine ((differentiableAt_LFunction χ _ (Or.inl fun h ↦ ?_)).continuousAt).comp
      hline.continuousAt
    simpa using congrArg re h
  have hmeas : AEStronglyMeasurable fun t : ℝ ↦ perronIntegrand χ x ((2 : ℝ) + t * I) :=
    ((((measurable_deriv (LFunction χ)).comp hline.measurable).div
      hL.measurable).neg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  exact (hf.norm.const_mul _).mono' hmeas
    (Filter.Eventually.of_forall fun t ↦ norm_perronIntegrand_le χ x t)

/-- Each term of the L-series times `x^s / (s (s + 1))` is a Perron kernel at `x / n`. -/
theorem term_mul_perron_f_eq (f : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term f s n * Perron.f x s = f n * Perron.f (x / n) s := by
  have h := Perron.f_mul_eq_f hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  rw [ofReal_natCast, cpow_neg] at h
  rw [term_of_ne_zero hn, ← h]
  ring

/-- The line integral of the Perron kernel at `y > 1` is `2π (1 - 1/y)`. -/
theorem integral_perron_f_of_one_lt {y : ℝ} (hy : 1 < y) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 2 * Real.pi * (1 - 1 / y) := by
  have h := Perron.formulaGtOne (σ := 2) hy (by norm_num)
  rw [VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul] at h
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  change 1 / (2 * Real.pi * I) * (I * ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I)) = _ at h
  generalize ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = J at h ⊢
  rw [← h]
  field_simp

/-- The line integral of the Perron kernel at `0 < y < 1` vanishes. -/
theorem integral_perron_f_of_lt_one {y : ℝ} (hy0 : 0 < y) (hy : y < 1) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 0 := by
  have h := Perron.formulaLtOne (σ := 2) hy0 hy (by norm_num)
  rw [VerticalIntegral, smul_eq_mul] at h
  simpa using h

/-- A function bounded by `B / t²` on `(T, ∞)` has integral there of norm at most `B / T`. -/
theorem norm_setIntegral_Ioi_le {g : ℝ → ℂ} {B T : ℝ} (hT : 0 < T)
    (hg : IntegrableOn g (Ioi T)) (hgB : ∀ t, T < t → ‖g t‖ ≤ B / t ^ 2) :
    ‖∫ t in Ioi T, g t‖ ≤ B / T := by
  have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hle : ∀ t ∈ Ioi T, ‖g t‖ ≤ B * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv]
    exact hgB t ht
  calc ‖∫ t in Ioi T, g t‖
      ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, B * t ^ (-2 : ℝ) :=
        setIntegral_mono_on hg.norm (hrpow.const_mul B) measurableSet_Ioi hle
    _ = B / T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
        norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- The smoothed Perron formula: the vertical integral of `perronIntegrand` on
`re s = 2` is `2πi` times the weighted sum. -/
theorem verticalIntegral_perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 1 < x) (hxN : ∀ m : ℕ, (m : ℝ) ≠ x) :
    VerticalIntegral (perronIntegrand χ x) 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) := by
  have hx0 : 0 < x := by linarith
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term (↗χ * ↗Λ) ((2 : ℝ) + t * I) n * Perron.f x ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, perronIntegrand χ x ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [perronIntegrand, neg_logDeriv_LFunction_eq χ (by simp), LSeries, ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = (↗χ * ↗Λ) n * Perron.f (x / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ term_mul_perron_f_eq _ hx0 hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hxn : 0 < x / n := div_pos hx0 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hxn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term (↗χ * ↗Λ) 2 n‖ * ∫ t : ℝ, ‖Perron.f x ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    have hχΛ : LSeriesSummable (↗χ * ↗Λ) 2 :=
      LSeriesSummable_twist_vonMangoldt χ (by norm_num)
    exact (summable_norm_iff.mpr hχΛ).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊x⌋₊ then
      2 * Real.pi * ((Λ n : ℂ) * χ n * (1 - n / x)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hnx : (n : ℝ) < x :=
        lt_of_le_of_ne ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hmem).2) (hxN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hnx)]
      push_cast
      rw [one_div_div]
      simp only [Pi.mul_apply]
      ring
    · have hxn : x < n := (Nat.floor_lt hx0.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hx0 hn0) ((div_lt_one hn0).mpr hxn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- Truncating the vertical integral at height `T` costs `O(x² / T)`. -/
theorem exists_norm_verticalIntegral_sub_le :
    ∃ C : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x T : ℝ}, 1 ≤ x → 1 ≤ T →
      ‖VerticalIntegral (perronIntegrand χ x) 2 -
          VIntegral (perronIntegrand χ x) 2 (-T) T‖ ≤ C * x ^ 2 / T := by
  refine ⟨2 * ∑' n, ‖term ↗Λ 2 n‖, fun χ x T hx hT ↦ ?_⟩
  set A := ∑' n, ‖term ↗Λ 2 n‖
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set F : ℝ → ℂ := fun t ↦ perronIntegrand χ x ((2 : ℝ) + t * I)
  have hF_int : Integrable F := integrable_perronIntegrand χ hx0
  have hA : 0 ≤ A := tsum_nonneg fun _ ↦ norm_nonneg _
  -- Pointwise, `‖F t‖ ≤ A x² / t²`.
  have hF_le : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ A * x ^ 2 / t ^ 2 := by
    intro t ht
    rw [mul_div_assoc]
    exact (norm_perronIntegrand_le χ x t).trans
      (mul_le_mul_of_nonneg_left (norm_perron_f_le hx0 ht) hA)
  -- Bound the two tails.
  have hupper : ‖∫ t in Ici T, F t‖ ≤ A * x ^ 2 / T := by
    rw [integral_Ici_eq_integral_Ioi]
    exact norm_setIntegral_Ioi_le hT0 hF_int.integrableOn
      fun t ht ↦ hF_le t (hT0.trans ht).ne'
  have hlower : ‖∫ t in Iic (-T), F t‖ ≤ A * x ^ 2 / T := by
    rw [← integral_comp_neg_Ioi]
    refine norm_setIntegral_Ioi_le hT0 hF_int.comp_neg.integrableOn fun t ht ↦ ?_
    rw [← neg_sq t]
    exact hF_le (-t) (neg_ne_zero.mpr (hT0.trans ht).ne')
  rw [verticalIntegral_split_three (-T) T hF_int, add_right_comm, add_sub_cancel_right]
  calc ‖I • (∫ t in Iic (-T), F t) + I • ∫ t in Ici T, F t‖
      ≤ ‖∫ t in Iic (-T), F t‖ + ‖∫ t in Ici T, F t‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        simp
    _ ≤ A * x ^ 2 / T + A * x ^ 2 / T := add_le_add hlower hupper
    _ = 2 * A * x ^ 2 / T := by ring

end Perron

/-! ### Bounds on the kernel and on the edges -/

section Edges

open Complex

/-- To the right of `1/16`, `‖s (s + 1)‖` is at least `(1 + |im s|)² / 64`. -/
lemma one_add_abs_im_sq_le_norm_mul {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    (1 + |s.im|) ^ 2 ≤ 64 * ‖s * (s + 1)‖ := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₂ : s.re ≤ ‖s‖ := re_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  have h₄ : (s + 1).re ≤ ‖s + 1‖ := re_le_norm _
  simp only [add_im, one_im, add_zero, add_re, one_re] at h₃ h₄
  have h₅ : 1 + |s.im| ≤ 32 * ‖s‖ := by linarith
  have h₆ : 1 + |s.im| ≤ 2 * ‖s + 1‖ := by linarith
  calc (1 + |s.im|) ^ 2 ≤ (32 * ‖s‖) * (2 * ‖s + 1‖) := by
        rw [sq]; exact mul_le_mul h₅ h₆ (by positivity) (by positivity)
    _ = 64 * ‖s * (s + 1)‖ := by rw [norm_mul]; ring

/-- To the right of `1/16`, `‖x^s / (s (s + 1))‖ ≤ 64 x^{re s} / (1 + |im s|)²`. -/
lemma norm_cpow_div_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ 64 * x ^ s.re / (1 + |s.im|) ^ 2 := by
  have h := one_add_abs_im_sq_le_norm_mul hs
  have hpos : 0 < ‖s * (s + 1)‖ := by
    have : 0 < (1 + |s.im|) ^ 2 := by positivity
    linarith
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx, div_le_div_iff₀ hpos (by positivity)]
  have := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le s.re)
  linarith

/-- Off the real axis, `‖x^s / (s (s + 1))‖ ≤ x^{re s} / (im s)²`. -/
lemma norm_cpow_div_le_of_im_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ x ^ s.re / s.im ^ 2 := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  simp only [add_im, one_im, add_zero] at h₃
  have h : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) (norm_nonneg _)
  have hpos : 0 < s.im ^ 2 := by positivity
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hpos h

/-- `1 + log (|t| + 3) ≤ 5 (1 + |t|)^{1/2}`. -/
lemma one_add_log_le_rpow (t : ℝ) :
    1 + Real.log (|t| + 3) ≤ 5 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h₁ : Real.log (|t| + 3) ≤ Real.log 3 + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have h₂ : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h₃ : Real.log (1 + |t|) ≤ (1 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h₄ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  linarith

/-- A horizontal segment integral is at most the length times a pointwise bound. -/
lemma norm_hIntegral_le {F : ℂ → ℂ} {a b y C : ℝ} (hab : a ≤ b)
    (hF : ∀ σ ∈ Set.Icc a b, ‖F (σ + y * I)‖ ≤ C) : ‖HIntegral F a b y‖ ≤ C * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (f := fun σ : ℝ ↦ F (σ + y * I)) fun σ hσ ↦ by
      rw [Set.uIoc_of_le hab] at hσ
      exact hF σ (Set.Ioc_subset_Icc_self hσ)
  rwa [abs_of_nonneg (by linarith)] at h

/-- A vertical segment integral is at most `c ∫ (1 + |t|)^{-3/2} dt` when the integrand is
dominated by `c (1 + |t|)^{-3/2}`. -/
lemma norm_vIntegral_le {F : ℂ → ℂ} {σ T c : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ c * (1 + |t|) ^ (-(3 / 2) : ℝ)) :
    ‖VIntegral F σ (-T) T‖ ≤ c * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have hint : MeasureTheory.Integrable fun t : ℝ ↦ c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := MeasureTheory.volume) (r := 3 / 2)
      (by simp; norm_num)
    simpa [Real.norm_eq_abs] using h.const_mul c
  have hc : 0 ≤ c := by simpa using (norm_nonneg _).trans (hF 0)
  rw [VIntegral, norm_smul, norm_I, one_mul, ← MeasureTheory.integral_const_mul]
  calc ‖∫ t in -T..T, F (σ + t * I)‖
      ≤ ∫ t in -T..T, c * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Filter.Eventually.of_forall fun t _ ↦ hF t) hint.intervalIntegrable
    _ ≤ ∫ t, c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun t ↦ by positivity)

end Edges

/-! ### Logarithmic derivatives near `s = 1` -/

section NearOne

open Complex DirichletCharacter Metric

open scoped LSeries.notation

/-- **Borel–Carathéodory near `s = 1`.** If `g` is entire and zero-free on `re s > 7/8`,
at most `M` on `29/32 < re s < 4`, `|im s| < 3`, and at least `1/2` on `re s = 2`,
`|im s| ≤ 1`, then `‖g'/g‖ ≤ 8832 log (2M)` on `15/16 ≤ re s ≤ 2`, `|im s| ≤ 1`. -/
lemma norm_logDeriv_le_of_near_one {g : ℂ → ℂ} {M : ℝ} (hg : Differentiable ℂ g)
    (hg₀ : ∀ w : ℂ, 7 / 8 < w.re → g w ≠ 0)
    (hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 → ‖g w‖ ≤ M)
    (hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖g (2 + t * I)‖) {z : ℂ} (hz₁ : 15 / 16 ≤ z.re)
    (hz₂ : z.re ≤ 2) (hz : |z.im| ≤ 1) :
    ‖deriv g z / g z‖ ≤ 8832 * Real.log (2 * M) := by
  set c : ℂ := 2 + z.im * I
  -- the ball `ball c (35/32)` lies where `g` is bounded and zero-free
  have hball : ∀ w ∈ ball c (35 / 32), 29 / 32 < w.re ∧ w.re < 4 ∧ |w.im| < 3 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h₁ := (abs_re_le_norm (w - c)).trans_lt hw
    have h₂ := (abs_im_le_norm (w - c)).trans_lt hw
    simp only [c, sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_im, add_im,
      mul_im] at h₁ h₂
    norm_num at h₁ h₂
    obtain ⟨h₁, h₁'⟩ := abs_lt.mp h₁
    obtain ⟨h₂, h₂'⟩ := abs_lt.mp h₂
    obtain ⟨h₃, h₃'⟩ := abs_le.mp hz
    exact ⟨by linarith, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have hcb : c ∈ ball c (35 / 32) := mem_ball_self (by norm_num)
  have hgc : 1 / 2 ≤ ‖g c‖ := hm z.im hz
  have hgc₀ : g c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hMc : ‖g c‖ ≤ M := by
    obtain ⟨h₁, h₂, h₃⟩ := hball c hcb
    exact hM c h₁ h₂ h₃
  -- a holomorphic logarithm of `g / g c` on the ball
  obtain ⟨h, hh, he, hh₀⟩ := exists_holomorphic_log (c := c) (R := 35 / 32) (by norm_num)
    (hg.differentiableOn.div_const (g c))
    (fun w hw ↦ div_ne_zero (hg₀ w (by linarith [(hball w hw).1])) hgc₀) (div_self hgc₀)
  set B := Real.log M - Real.log ‖g c‖ with hB
  have hB₀ : 0 ≤ B := sub_nonneg.mpr (Real.log_le_log (by linarith) hMc)
  have hre : ∀ w ∈ ball c (35 / 32), (h w).re ≤ B := by
    intro w hw
    obtain ⟨h₁, h₂, h₃⟩ := hball w hw
    have hgw : g w ≠ 0 := hg₀ w (by linarith)
    have hew : Complex.exp (h w) = g w / g c := he hw
    have hlog : (h w).re = Real.log ‖g w‖ - Real.log ‖g c‖ := by
      rw [← Real.log_exp (h w).re, ← Complex.norm_exp, hew, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hgw) (norm_ne_zero_iff.mpr hgc₀)]
    rw [hlog, hB]
    gcongr
    exact hM w h₁ h₂ h₃
  -- `z` lies in `closedBall c (17/16)`
  have hzc : z ∈ closedBall c (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm]
    have hzc' : z - c = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [hzc', norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hzb : z ∈ ball c (35 / 32) := closedBall_subset_ball (by norm_num) hzc
  -- the derivative of the logarithm is `g' / g`
  have hderiv : deriv h z = deriv g z / g z := by
    have hhz : DifferentiableAt ℂ h z := hh.differentiableAt (isOpen_ball.mem_nhds hzb)
    have hev : (fun w ↦ Complex.exp (h w)) =ᶠ[nhds z] fun w ↦ g w / g c :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb) fun w hw ↦ he hw
    have h₁ := hev.deriv_eq
    have hez : Complex.exp (h z) = g z / g c := he hzb
    rw [deriv_cexp hhz, deriv_div_const, hez] at h₁
    have hgz : g z ≠ 0 := hg₀ z (by linarith)
    field_simp at h₁ ⊢
    linear_combination h₁
  rw [← hderiv]
  refine (norm_deriv_le_of_re_le (by norm_num) (by norm_num) hB₀ hh hh₀ hre hzc).trans ?_
  have hM₀ : 0 < M := by linarith
  have hlog2 : B ≤ Real.log (2 * M) := by
    rw [Real.log_mul (by norm_num) hM₀.ne', hB]
    have : Real.log (1 / 2) ≤ Real.log ‖g c‖ := Real.log_le_log (by norm_num) hgc
    rw [one_div, Real.log_inv] at this
    linarith
  norm_num
  linarith

/-- The entire function `(s - 1) ζ(s)`, with its value `1` at `s = 1`. -/
noncomputable def zetaReg : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

/-- `(s - 1) ζ(s)` is entire. -/
lemma differentiable_zetaReg : Differentiable ℂ zetaReg := by
  have hne : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ zetaReg w := by
    intro w hw
    have hev : zetaReg =ᶠ[nhds w] fun s ↦ (s - 1) * riemannZeta s := by
      filter_upwards [eventually_ne_nhds hw] with v hv
      simp [zetaReg, Function.update_of_ne hv]
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq hev
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact hne s hs
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with w hw using hne w hw
  · simpa only [zetaReg, continuousAt_update_same] using riemannZeta_residue_one

/-- The entire function `(s - 1) L(s, χ₀)` for the principal character `χ₀` mod `k`. -/
noncomputable def trivReg (k : ℕ) : ℂ → ℂ :=
  fun s ↦ (∏ p ∈ k.primeFactors, (1 - (p : ℂ) ^ (-s))) * zetaReg s

/-- Away from `s = 1`, `trivReg k s = (s - 1) L(s, χ₀)`. -/
lemma trivReg_eq {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1) :
    trivReg k s = (s - 1) * LFunction (1 : DirichletCharacter ℂ k) s := by
  have h := LFunctionTrivChar_eq_mul_riemannZeta (N := k) hs
  simp only [LFunctionTrivChar] at h
  rw [trivReg, zetaReg, Function.update_of_ne hs, h]
  ring

/-- `(s - 1) L(s, χ₀)` is entire. -/
lemma differentiable_trivReg (k : ℕ) : Differentiable ℂ (trivReg k) := by
  intro s
  refine DifferentiableAt.mul (DifferentiableAt.fun_finsetProd fun p hp ↦ ?_)
    (differentiable_zetaReg s)
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hp₀)
    |>.const_sub 1

/-- On `re s ≥ 0`, the Euler factors at the primes dividing `k` have product at most `k`. -/
lemma norm_prod_one_sub_le {k : ℕ} [NeZero k] {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ k.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ k := by
  rw [norm_prod]
  calc ∏ p ∈ k.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
      ≤ ∏ p ∈ k.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p hp ↦ ?_
        have hp := Nat.prime_of_mem_primeFactors hp
        have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_natCast_cpow_of_pos hp.pos]
        have : (p : ℝ) ^ (-s).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using hs)
        linarith
    _ ≤ k := by
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd (NeZero.pos k) (Nat.prod_primeFactors_dvd k)

/-- `(s - 1) L(s, χ₀)` has no zeros on `re s > 7/8`. -/
lemma trivReg_ne_zero {k : ℕ} [NeZero k] {s : ℂ} (hs : 7 / 8 < s.re) : trivReg k s ≠ 0 := by
  rcases ne_or_eq s 1 with h | rfl
  · rw [trivReg_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h)
      (LFunction_ne_zero_of_seven_eighths_lt_re 1 hs fun h' ↦ h h'.2)
  · rw [trivReg, zetaReg, Function.update_self, mul_one]
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    have hp := Nat.prime_of_mem_primeFactors hp
    rw [cpow_neg_one, sub_ne_zero]
    intro h
    have : (1 : ℂ) = p := by simpa using congrArg (·⁻¹) h
    exact hp.one_lt.ne (by exact_mod_cast this)

/-- Away from `s = 1`, `L'/L(s, χ₀) = g'/g(s) - 1/(s - 1)` for `g = trivReg k`. -/
lemma logDeriv_LFunction_one_eq {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1)
    (hL : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0) :
    deriv (LFunction (1 : DirichletCharacter ℂ k)) s / LFunction (1 : DirichletCharacter ℂ k) s =
      deriv (trivReg k) s / trivReg k s - 1 / (s - 1) := by
  have hev : trivReg k =ᶠ[nhds s] fun w ↦ (w - 1) * LFunction (1 : DirichletCharacter ℂ k) w := by
    filter_upwards [eventually_ne_nhds hs] with w hw using trivReg_eq hw
  have hd : HasDerivAt (fun w ↦ (w - 1) * LFunction (1 : DirichletCharacter ℂ k) w)
      (1 * LFunction (1 : DirichletCharacter ℂ k) s +
        (s - 1) * deriv (LFunction (1 : DirichletCharacter ℂ k)) s) s :=
    ((hasDerivAt_id s).sub_const 1).mul
      (differentiableAt_LFunction 1 s (Or.inl hs)).hasDerivAt
  rw [hev.deriv_eq, hd.deriv, trivReg_eq hs]
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- `log (k (|t| + 3)) ≤ 6 k (1 + |t|)^{1/2}`. -/
lemma log_mul_le_mul_rpow {k : ℝ} (hk : 1 ≤ k) (t : ℝ) :
    Real.log (k * (|t| + 3)) ≤ 6 * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have h₁ := one_add_log_le_rpow t
  have h₂ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h₃ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  rw [Real.log_mul (by linarith) (by linarith [abs_nonneg t])]
  nlinarith

/-- On the line `re s = 15/16`, `‖L'/L(s, χ)‖ ≤ A k (1 + |t|)^{1/2}`. -/
theorem exists_norm_logDeriv_le_left : ∃ A : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (t : ℝ),
    ‖deriv (LFunction χ) (15 / 16 + t * I) / LFunction χ (15 / 16 + t * I)‖ ≤
      A * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := norm_logDeriv_LFunction_le
  obtain ⟨C₂, hC₂⟩ := norm_LFunction_le_poly
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_zetaReg.continuous.continuousOn
  set A₁ := 8832 * 2 * (36 * |C₂| + |M₀| + 1) + 16
  refine ⟨6 * |C₁| + 8832 * 16 + A₁, fun k _ χ t ↦ ?_⟩
  set s : ℂ := 15 / 16 + t * I
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hr : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  have hre : s.re = 15 / 16 := by simp [s]
  have him : s.im = t := by simp [s]
  have hA₁ : 0 ≤ A₁ := by positivity
  by_cases hfar : 1 ≤ ‖s - 1‖
  · -- away from `s = 1`, use the logarithmic bound
    have h := hC₁ k χ s (by rw [hre]) (by rw [hre]; norm_num) hfar
    rw [him] at h
    have hlog := log_mul_le_mul_rpow hk t
    have hlog₀ : 0 ≤ Real.log (k * (|t| + 3)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t])
    calc _ ≤ C₁ * Real.log (k * (|t| + 3)) := h
      _ ≤ |C₁| * (6 * k * (1 + |t|) ^ (1 / 2 : ℝ)) :=
          mul_le_mul (le_abs_self _) hlog hlog₀ (abs_nonneg _)
      _ ≤ (6 * |C₁| + 8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
          have : 0 ≤ (8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by positivity
          nlinarith
  -- near `s = 1`, use Borel–Carathéodory
  have ht : |t| ≤ 1 := by
    have := abs_im_le_norm (s - 1)
    rw [sub_im, him, one_im, sub_zero] at this
    linarith
  have hs₁ : s ≠ 1 := fun h ↦ by rw [h, one_re] at hre; norm_num at hre
  have hz₁ : 15 / 16 ≤ s.re := hre.ge
  have hz₂ : s.re ≤ 2 := by rw [hre]; norm_num
  have hz : |s.im| ≤ 1 := by rwa [him]
  suffices hnear : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ (8832 * 16 + A₁) * k by
    calc _ ≤ (8832 * 16 + A₁) * k := hnear
      _ ≤ (6 * |C₁| + 8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
          have : 0 ≤ (8832 * 16 + A₁) * k := by positivity
          have : 0 ≤ 6 * |C₁| * k := by positivity
          nlinarith
  by_cases hχ : χ = 1
  · subst hχ
    -- `g = (s - 1) L(s, χ₀)`
    have hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 →
        ‖trivReg k w‖ ≤ (36 * |C₂| + |M₀| + 1) * k := by
      intro w h₁ h₂ h₃
      by_cases hw : ‖w - 1‖ ≤ 1
      · rw [trivReg, norm_mul]
        have hP := norm_prod_one_sub_le (k := k) (s := w) (by linarith)
        have hZ := (hM₀ w (by rwa [mem_closedBall, dist_eq_norm])).trans (le_abs_self M₀)
        calc _ ≤ (k : ℝ) * |M₀| := mul_le_mul hP hZ (norm_nonneg _) (by positivity)
          _ ≤ (36 * |C₂| + |M₀| + 1) * k := by nlinarith [abs_nonneg C₂]
      · have hw₁ : w ≠ 1 := fun h ↦ hw (by simp [h])
        rw [trivReg_eq hw₁, norm_mul]
        have hL := hC₂ k 1 w (by linarith) (by linarith)
        have hn : ‖w - 1‖ ≤ 6 := by
          refine (norm_le_abs_re_add_abs_im _).trans ?_
          rw [sub_re, one_re, sub_im, one_im, sub_zero]
          have := abs_lt.mpr (⟨by linarith, by linarith⟩ : -3 < w.re - 1 ∧ w.re - 1 < 3)
          linarith
        have hL' : ‖LFunction (1 : DirichletCharacter ℂ k) w‖ ≤ |C₂| * k * 6 := by
          refine hL.trans ?_
          have : C₂ * k ≤ |C₂| * k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          have : 0 ≤ |C₂| * k := by positivity
          nlinarith [abs_nonneg w.im]
        calc _ ≤ 6 * (|C₂| * k * 6) := mul_le_mul hn hL' (norm_nonneg _) (by norm_num)
          _ ≤ (36 * |C₂| + |M₀| + 1) * k := by nlinarith [abs_nonneg M₀, abs_nonneg C₂]
    have hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖trivReg k (2 + t * I)‖ := by
      intro t _
      have hne : (2 + t * I : ℂ) ≠ 1 := fun h ↦ by simpa using congrArg re h
      rw [trivReg_eq hne, norm_mul]
      have h₁ : 1 ≤ ‖(2 + t * I : ℂ) - 1‖ := by
        have := re_le_norm ((2 + t * I : ℂ) - 1)
        simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, one_re] at this
        norm_num at this
        linarith
      have h₂ := le_norm_LFunction (1 : DirichletCharacter ℂ k) (s := 2 + t * I) (by simp)
      have hre₂ : (2 + t * I : ℂ).re = 2 := by simp
      rw [hre₂] at h₂
      norm_num at h₂
      nlinarith
    have hB := norm_logDeriv_le_of_near_one (differentiable_trivReg k)
      (fun w hw ↦ trivReg_ne_zero hw) hM hm hz₁ hz₂ hz
    have hL₀ : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
      LFunction_ne_zero_of_seven_eighths_lt_re 1 (by rw [hre]; norm_num) fun h ↦ hs₁ h.2
    rw [logDeriv_LFunction_one_eq hs₁ hL₀]
    have hinv : ‖1 / (s - 1)‖ ≤ 16 := by
      have h₁ : 1 / 16 ≤ ‖s - 1‖ := by
        have := abs_re_le_norm (s - 1)
        rw [sub_re, hre, one_re] at this
        norm_num at this
        linarith
      rw [norm_div, norm_one]
      exact (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hlog : Real.log (2 * ((36 * |C₂| + |M₀| + 1) * k)) ≤ 2 * ((36 * |C₂| + |M₀| + 1) * k) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc _ ≤ ‖deriv (trivReg k) s / trivReg k s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
      _ ≤ 8832 * (2 * ((36 * |C₂| + |M₀| + 1) * k)) + 16 := by linarith
      _ ≤ (8832 * 16 + A₁) * k := by
          have : (16 : ℝ) ≤ 16 * k := by linarith
          simp only [A₁]
          nlinarith
  · -- `g = L(s, χ)` is entire
    have hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 →
        ‖LFunction χ w‖ ≤ 8 * k := by
      intro w h₁ h₂ h₃
      refine (norm_LFunction_le_of_ne_one hχ (by linarith)).trans ?_
      rw [div_le_iff₀ (by linarith)]
      have hn : ‖w‖ ≤ 7 := by
        refine (norm_le_abs_re_add_abs_im _).trans ?_
        rw [abs_of_pos (by linarith)]
        linarith
      nlinarith
    have hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖LFunction χ (2 + t * I)‖ := by
      intro t _
      have h₂ := le_norm_LFunction χ (s := 2 + t * I) (by simp)
      have hre₂ : (2 + t * I : ℂ).re = 2 := by simp
      rw [hre₂] at h₂
      norm_num at h₂
      linarith
    have hB := norm_logDeriv_le_of_near_one (differentiable_LFunction hχ)
      (fun w hw ↦ LFunction_ne_zero_of_seven_eighths_lt_re χ hw fun h ↦ hχ h.1) hM hm hz₁ hz₂ hz
    have hlog : Real.log (2 * (8 * k)) ≤ 2 * (8 * k) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc _ ≤ 8832 * Real.log (2 * (8 * k)) := hB
      _ ≤ 8832 * (2 * (8 * k)) := by linarith
      _ ≤ (8832 * 16 + A₁) * k := by nlinarith

end NearOne

/-! ### The smoothed sum -/

section Smoothed

open Complex ArithmeticFunction DirichletCharacter

/-- The rectangle integral recovers the right edge from the other three. -/
lemma vIntegral_eq_rectangleIntegral (F : ℂ → ℂ) (U : ℝ) :
    VIntegral F 2 (-U) U = RectangleIntegral F (15 / 16 - U * I) (2 + U * I) -
      HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U := by
  simp only [RectangleIntegral, sub_re, add_re, sub_im, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  norm_num
  abel

/-- The kernel `x^s / (s (s + 1))` is holomorphic on `re s > 0`. -/
lemma differentiableOn_kernel {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs₁ : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    simp at this hs
    linarith
  have h₁ : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have h₂ : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s + 1)) s := by fun_prop
  exact (h₁.div h₂ (mul_ne_zero hs₀ hs₁)).differentiableWithinAt

/-- The rectangle `[15/16, 2] × [-U, U]` lies in the zero-free half-plane `re s > 7/8`. -/
lemma rectangle_subset_re_gt (U : ℝ) :
    Rectangle (15 / 16 - U * I) (2 + U * I) ⊆ {s : ℂ | 7 / 8 < s.re} := by
  intro s hs
  rw [Rectangle, mem_reProdIm] at hs
  have h := hs.1
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h
  norm_num [Set.uIcc_of_le] at h
  exact lt_of_lt_of_le (by norm_num) h.1

/-- Across the rectangle `[15/16, 2] × [-U, U]`, the Perron integrand picks up only the
residue `x / 2` of the principal character at `s = 1`. -/
theorem rectangleIntegral_perronIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {x : ℝ} (hx : 0 < x) {U : ℝ} (hU : 0 < U) :
    RectangleIntegral (perronIntegrand χ x) (15 / 16 - U * I) (2 + U * I) =
      if χ = 1 then 2 * Real.pi * I * (x / 2) else 0 := by
  set K : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  have hKd := differentiableOn_kernel hx
  have hKΩ : ∀ s : ℂ, 7 / 8 < s.re → DifferentiableAt ℂ K s := fun s hs ↦
    hKd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < s.re by linarith))
  split_ifs with hχ
  · subst hχ
    set g := trivReg k
    have hg := differentiable_trivReg k
    set H : ℂ → ℂ := fun s ↦ -(deriv g s / g s) * K s + dslope K 1 s
    have hre : (15 / 16 - U * I : ℂ).re ≤ (2 + U * I : ℂ).re := by simp; norm_num
    have him : (15 / 16 - U * I : ℂ).im ≤ (2 + U * I : ℂ).im := by simp; linarith
    have hnhds : Rectangle (15 / 16 - U * I) (2 + U * I) ∈ nhds (1 : ℂ) := by
      rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him]
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, add_im,
        mul_im, one_re, one_im]
      norm_num
      exact hU
    have hH : HolomorphicOn H (Rectangle (15 / 16 - U * I) (2 + U * I)) := by
      intro s hs
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hdg : DifferentiableAt ℂ (deriv g) s := ((hg.analyticAt s).deriv).differentiableAt
      have hslope : DifferentiableAt ℂ (dslope K 1) s := by
        have h₁ : {s : ℂ | 0 < s.re} ∈ nhds (1 : ℂ) :=
          (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
        exact ((differentiableOn_dslope h₁).mpr hKd).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds
            (show (0 : ℝ) < s.re by linarith))
      exact (((hdg.div (hg s) (trivReg_ne_zero hs')).neg.mul (hKΩ s hs')).add
        hslope).differentiableWithinAt
    have hpart : Set.EqOn (perronIntegrand (1 : DirichletCharacter ℂ k) x - fun s ↦ K 1 / (s - 1)) H
        (Rectangle (15 / 16 - U * I) (2 + U * I) \ {1}) := by
      intro s ⟨hs, hs₁⟩
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hs₁' : s ≠ 1 := hs₁
      have hL : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
        LFunction_ne_zero_of_seven_eighths_lt_re 1 hs' fun h ↦ hs₁' h.2
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁'
      simp only [Pi.sub_apply, perronIntegrand, H, logDeriv_LFunction_one_eq hs₁' hL,
        dslope_of_ne _ hs₁', slope_def_field]
      change -(deriv g s / g s - 1 / (s - 1)) * K s - K 1 / (s - 1) = _
      field_simp
      ring
    have h := ResidueTheoremOnRectangleWithSimplePole hre him hnhds hH hpart
    rw [RectangleIntegral', smul_eq_mul] at h
    have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hK1 : K 1 = x / 2 := by simp [K]; ring
    rw [← hK1, ← h]
    field_simp
  · have hF : HolomorphicOn (perronIntegrand χ x) {s : ℂ | 7 / 8 < s.re} := by
      intro s hs
      have hs' : 7 / 8 < s.re := hs
      have hLd := differentiable_LFunction hχ
      have hdL : DifferentiableAt ℂ (deriv (LFunction χ)) s :=
        ((hLd.analyticAt s).deriv).differentiableAt
      have hL : LFunction χ s ≠ 0 :=
        LFunction_ne_zero_of_seven_eighths_lt_re χ hs' fun h ↦ hχ h.1
      exact ((hdL.div (hLd s) hL).neg.mul (hKΩ s hs')).differentiableWithinAt
    exact hF.vanishesOnRectangle (rectangle_subset_re_gt U)

/-- The smoothed twisted prime sum:
`∑_{m ≤ x} Λ(m) χ(m) (1 - m / x) = [χ = 1] x / 2 + O(k x^{15/16})`. -/
theorem exists_norm_smoothed_sub_le : ∃ B : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (x : ℝ), 2 ≤ x → (∀ m : ℕ, (m : ℝ) ≠ x) →
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) -
          (if χ = 1 then (x : ℂ) / 2 else 0)‖ ≤ B * k * x ^ (15 / 16 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_verticalIntegral_sub_le
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_LFunction_le
  obtain ⟨A, hA⟩ := exists_norm_logDeriv_le_left
  set I₀ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  have hI₀ : 0 ≤ I₀ := MeasureTheory.integral_nonneg fun t ↦ by positivity
  refine ⟨|C₁| + 12 * |C₂| + 64 * |A| * I₀, ?_⟩
  intro k _ χ x hx hxN
  set U := x ^ 2 with hUdef
  set L := LFunction χ
  set F := perronIntegrand χ x
  set Kx : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  set S := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)
  set P : ℂ := if χ = 1 then (x : ℂ) / 2 else 0
  have hx₀ : 0 < x := by linarith
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hU : 4 ≤ U := by nlinarith
  have hnormF : ∀ s, ‖F s‖ = ‖deriv L s / L s‖ * ‖Kx s‖ := fun s ↦ by
    simp only [F, perronIntegrand, norm_mul, norm_neg, L, Kx]
  -- the rectangle picks up the residue
  have hR : RectangleIntegral F (15 / 16 - U * I) (2 + U * I) = 2 * Real.pi * I * P := by
    rw [rectangleIntegral_perronIntegrand χ hx₀ (by linarith)]
    split_ifs <;> simp [P, *]
  -- the horizontal edges at height `±U`
  have hH : ∀ τ ∈ ({U, -U} : Set ℝ), ‖HIntegral F (15 / 16) 2 τ‖ ≤ 6 * |C₂| * k := by
    intro τ hτ
    have hτ₂ : |τ| = U := by
      rcases hτ with rfl | rfl
      · exact abs_of_pos (by linarith)
      · rw [abs_neg]; exact abs_of_pos (by linarith)
    have hlog : Real.log (k * (U + 3)) ≤ 3 * k * U := by
      rw [Real.log_mul (by linarith) (by linarith)]
      have h₁ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have h₂ : Real.log (U + 3) ≤ U + 2 :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      nlinarith
    have hpt : ∀ σ ∈ Set.Icc (15 / 16 : ℝ) 2, ‖F (σ + τ * I)‖ ≤ 3 * |C₂| * k := by
      intro σ hσ
      have hre : (σ + τ * I : ℂ).re = σ := by simp
      have him : (σ + τ * I : ℂ).im = τ := by simp
      have hfar : 1 ≤ ‖(σ + τ * I : ℂ) - 1‖ := by
        have := abs_im_le_norm ((σ + τ * I : ℂ) - 1)
        rw [sub_im, him, one_im, sub_zero, hτ₂] at this
        linarith
      have h₁ := hC₂ k χ (σ + τ * I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) hfar
      rw [him, hτ₂] at h₁
      have h₂ : ‖Kx (σ + τ * I)‖ ≤ 1 / U := by
        have h := norm_cpow_div_le_of_im_ne_zero hx₀ (s := σ + τ * I)
          (by rw [him]; intro h; rw [h, abs_zero] at hτ₂; linarith)
        rw [hre, him] at h
        have hxσ : x ^ σ ≤ x ^ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2
          rwa [Real.rpow_two] at this
        refine h.trans ?_
        rw [← sq_abs τ, hτ₂, hUdef, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hlog₀ : 0 ≤ Real.log (k * (U + 3)) := Real.log_nonneg (by nlinarith)
      rw [hnormF]
      calc ‖deriv L (σ + τ * I) / L (σ + τ * I)‖ * ‖Kx (σ + τ * I)‖
          ≤ (|C₂| * (3 * k * U)) * (1 / U) := by
            refine mul_le_mul (h₁.trans ?_) h₂ (norm_nonneg _) (by positivity)
            exact mul_le_mul (le_abs_self _) hlog hlog₀ (abs_nonneg _)
        _ = 3 * |C₂| * k := by field_simp
    refine (norm_hIntegral_le (by norm_num) hpt).trans ?_
    have : 0 ≤ |C₂| * k := by positivity
    nlinarith
  -- the left edge `re s = 15/16`
  have hV : ‖VIntegral F (15 / 16) (-U) U‖ ≤ 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by
    refine norm_vIntegral_le (by linarith) fun t ↦ ?_
    have hs : (((15 / 16 : ℝ) : ℂ) + t * I) = 15 / 16 + t * I := by push_cast; ring
    have h₁ := (hA k χ t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) (by positivity))
    have hre : (15 / 16 + t * I : ℂ).re = 15 / 16 := by simp
    have him : (15 / 16 + t * I : ℂ).im = t := by simp
    have h₂ := norm_cpow_div_le hx₀ (s := 15 / 16 + t * I) (by rw [hre]; norm_num)
    rw [hre, him] at h₂
    have hu : 0 < 1 + |t| := by positivity
    have h₃ : (1 + |t|) ^ (-(3 / 2) : ℝ) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
      rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub hu,
        Real.rpow_natCast]
    rw [hs, hnormF, h₃]
    calc ‖deriv L (15 / 16 + t * I) / L (15 / 16 + t * I)‖ * ‖Kx (15 / 16 + t * I)‖
        ≤ (|A| * k * (1 + |t|) ^ (1 / 2 : ℝ)) * (64 * x ^ (15 / 16 : ℝ) / (1 + |t|) ^ 2) :=
          mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = 64 * |A| * k * x ^ (15 / 16 : ℝ) * ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2) := by
          ring
  -- truncating the vertical integral at height `U`
  have hC : ‖VerticalIntegral F 2 - VIntegral F 2 (-U) U‖ ≤ |C₁| := by
    refine (hC₁ χ (by linarith) (by linarith)).trans ?_
    rw [← hUdef, mul_div_assoc, div_self (by positivity), mul_one]
    exact le_abs_self _
  -- assembling the pieces
  have hS : VerticalIntegral F 2 = 2 * Real.pi * I * S :=
    verticalIntegral_perronIntegrand χ (by linarith) hxN
  have hsplit : 2 * Real.pi * I * (S - P) = (VerticalIntegral F 2 - VIntegral F 2 (-U) U) +
      (-HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U) := by
    rw [vIntegral_eq_rectangleIntegral, hR, hS]
    ring
  have hnorm : ‖2 * Real.pi * I * (S - P)‖ = 2 * Real.pi * ‖S - P‖ := by
    simp [abs_of_pos Real.pi_pos]
  have hle : ‖2 * Real.pi * I * (S - P)‖ ≤
      |C₁| + (6 * |C₂| * k + 6 * |C₂| * k + 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add hC ?_)
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ?_ (hH U (by simp)))) hV)
    rw [norm_neg]
    exact hH (-U) (by simp)
  have hxr : 1 ≤ x ^ (15 / 16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h₄ : ‖S - P‖ ≤ 2 * Real.pi * ‖S - P‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.two_le_pi])
  have h₅ : |C₁| ≤ |C₁| * k * x ^ (15 / 16 : ℝ) := by
    have : 1 ≤ k * x ^ (15 / 16 : ℝ) := one_le_mul_of_one_le_of_one_le hk hxr
    nlinarith [abs_nonneg C₁]
  have h₆ : 12 * |C₂| * k ≤ 12 * |C₂| * k * x ^ (15 / 16 : ℝ) := by
    have : 0 ≤ 12 * |C₂| * k := by positivity
    nlinarith
  have h₇ : (|C₁| + 12 * |C₂| + 64 * |A| * I₀) * k * x ^ (15 / 16 : ℝ) =
      |C₁| * k * x ^ (15 / 16 : ℝ) + 12 * |C₂| * k * x ^ (15 / 16 : ℝ) +
        64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by ring
  rw [h₇]
  linarith

end Smoothed

/-! ### Removing the smoothing -/

section Unsmoothing

open Complex

/-- Differencing the weighted sums `W(z) = ∑_{n ≤ z} a(n) (z - n)` over a step `h` recovers
`h ∑_{n ≤ x} a(n)` up to `h² log (x + h)`, when `‖a(n)‖ ≤ log n`. -/
lemma norm_sum_sub_sum_sub_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Real.log n) {x : ℝ}
    (hx : 0 ≤ x) (h : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) -
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) -
          h * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ h ^ 2 * Real.log (x + h) := by
  have hI : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n ↦ by ext; simp; omega
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hxm : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  rw [Nat.floor_add_natCast hx, hI, hI]
  generalize ⌊x⌋₊ = m at hmx hxm ⊢
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) (Nat.le_add_right m h)]
  -- the sums over `n ≤ x` cancel
  have hcancel : ∑ n ∈ Finset.Ioc 0 m, a n * (((x + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Ioc 0 m, a n * ((x : ℂ) - n) - h * ∑ n ∈ Finset.Ioc 0 m, a n = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    push_cast
    ring
  rw [show ∀ A B C D : ℂ, A + B - C - D = (A - C - D) + B by intros; ring, hcancel, zero_add]
  -- each new term is at most `h log (x + h)`
  have hterm : ∀ n ∈ Finset.Ioc m (m + h),
      ‖a n * (((x + h : ℝ) : ℂ) - n)‖ ≤ h * Real.log (x + h) := by
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ioc.mp hn
    have hn₁' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hn₁
    have hn₂' : (n : ℝ) ≤ m + h := by exact_mod_cast hn₂
    have hn₀ : (0 : ℝ) < n := by linarith
    rw [norm_mul, mul_comm]
    have h₁ : ‖((x + h : ℝ) : ℂ) - n‖ ≤ h := by
      rw [show ((x + h : ℝ) : ℂ) - n = ((x + h - n : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have h₂ : ‖a n‖ ≤ Real.log (x + h) :=
      (ha n).trans (Real.log_le_log hn₀ (by linarith))
    exact mul_le_mul h₁ h₂ (norm_nonneg _) (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
  exact le_of_eq (by ring)

end Unsmoothing

end PNT

open Complex PNT

/-- The prime number theorem in progressions with a power saving (AC0):
`∑_{n ≤ y} Λ(n) χ(n) = [χ = 1] y + O(k^C y^{1-c})`. -/
theorem sum_vonMangoldt_mul_char_sub_le : ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
        (if χ = 1 then (y : ℂ) else 0)‖ ≤ C * (k : ℝ) ^ C * y ^ (1 - c) := by
  obtain ⟨B, hB⟩ := exists_norm_smoothed_sub_le
  set C₀ := 32 * |B| + 520
  refine ⟨1 / 64, by norm_num, C₀, fun k _ χ y hy ↦ ?_⟩
  set a : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
  have ha : ∀ n, ‖a n‖ ≤ Real.log n := fun n ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ n)).trans ArithmeticFunction.vonMangoldt_le_log
  set I₁ : ℂ := if χ = 1 then 1 else 0
  have hI₁ : ‖I₁‖ ≤ 1 := by simp only [I₁]; split_ifs <;> simp
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hy₀ : 0 < y := by linarith
  -- powers of `r = y^{1/64}`
  set r := y ^ (1 / 64 : ℝ) with hr
  have hr₀ : 0 < r := Real.rpow_pos_of_pos hy₀ _
  have hr₁ : 1 ≤ r := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : ∀ n : ℕ, y ^ ((n : ℝ) / 64) = r ^ n := fun n ↦ by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
    congr 1
    ring
  have hy64 : y = r ^ 64 := by rw [← hpow 64]; norm_num
  have hy60 : y ^ (15 / 16 : ℝ) = r ^ 60 := by rw [← hpow 60]; norm_num
  have hy62 : y ^ (31 / 32 : ℝ) = r ^ 62 := by rw [← hpow 62]; norm_num
  have hy63 : y ^ (1 - 1 / 64 : ℝ) = r ^ 63 := by rw [← hpow 63]; norm_num
  have hr62 : r ^ 62 ≤ r ^ 63 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr63 : r ^ 63 ≤ r ^ 64 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr1 : 1 ≤ r ^ 62 := one_le_pow₀ hr₁
  -- the evaluation points `x = ⌊y⌋ + 1/2` and `x + h`, with `h = ⌈y^{31/32}⌉`
  set m := ⌊y⌋₊
  set x : ℝ := m + 1 / 2
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy₀.le
  have hym : y < m + 1 := Nat.lt_floor_add_one y
  have hx : 2 ≤ x := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast Nat.le_floor (by exact_mod_cast hy)
    simp only [x]
    linarith
  have hxfloor : ⌊x⌋₊ = m := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> simp only [x] <;> linarith
  set h := ⌈y ^ (31 / 32 : ℝ)⌉₊
  have hh₁ : r ^ 62 ≤ h := hy62 ▸ Nat.le_ceil _
  have hh₂ : (h : ℝ) ≤ 2 * r ^ 62 := by
    have h₁ : (h : ℝ) < y ^ (31 / 32 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ y ^ (31 / 32 : ℝ) by positivity)
    rw [hy62] at h₁
    linarith
  have hh₀ : (0 : ℝ) < h := by linarith
  have hhalf : ∀ n : ℕ, ∀ j : ℕ, (n : ℝ) ≠ j + 1 / 2 := by
    intro n j hn
    have : ((2 * n : ℕ) : ℝ) = ((2 * j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective this
    omega
  have hxN : ∀ n : ℕ, (n : ℝ) ≠ x := fun n ↦ hhalf n m
  have hxhN : ∀ n : ℕ, (n : ℝ) ≠ x + h := fun n hn ↦ hhalf n (m + h) (by rw [hn]; push_cast; ring)
  have hxh : x + h ≤ 4 * r ^ 64 := by
    simp only [x]
    nlinarith
  -- the weighted sums `W(z) = ∑_{n ≤ z} a(n) (z - n)` are `I₁ z²/2 + O(k z^{31/16})`
  have hW : ∀ z : ℝ, 2 ≤ z → (∀ n : ℕ, (n : ℝ) ≠ z) → z ≤ 4 * r ^ 64 →
      ‖∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2)‖ ≤
        16 * |B| * k * r ^ 124 := by
    intro z hz hzN hz₄
    have hz₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
    have h₁ := hB k χ z hz hzN
    have heq : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2) =
        (z : ℂ) * (∑ m ∈ Finset.Icc 1 ⌊z⌋₊,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ m * (1 - m / z) -
            (if χ = 1 then (z : ℂ) / 2 else 0)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun n _ ↦ ?_
        simp only [a]
        field_simp
      · simp only [I₁]
        split_ifs <;> ring
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hz15 : z ^ (15 / 16 : ℝ) ≤ 4 * r ^ 60 := by
      calc z ^ (15 / 16 : ℝ) ≤ (4 * y) ^ (15 / 16 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hz₄) (by norm_num)
        _ = 4 ^ (15 / 16 : ℝ) * r ^ 60 := by
            rw [Real.mul_rpow (by norm_num) hy₀.le, hy60]
        _ ≤ 4 * r ^ 60 := by
            gcongr
            calc (4 : ℝ) ^ (15 / 16 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    have h₂ : ‖_‖ ≤ |B| * k * (4 * r ^ 60) :=
      h₁.trans (by gcongr; exact le_abs_self B)
    calc z * ‖_‖ ≤ (4 * r ^ 64) * (|B| * k * (4 * r ^ 60)) :=
          mul_le_mul hz₄ h₂ (norm_nonneg _) (by positivity)
      _ = 16 * |B| * k * r ^ 124 := by ring
  have hWx := hW x hx hxN (by linarith)
  have hWxh := hW (x + h) (by linarith) hxhN hxh
  -- the differencing error
  have hR := norm_sum_sub_sum_sub_le ha (by linarith : (0 : ℝ) ≤ x) h
  have hlog : Real.log (x + h) ≤ 256 * r := by
    have h₁ := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x + h) (by norm_num : (0 : ℝ) < 1 / 64)
    have h₂ : (x + h) ^ (1 / 64 : ℝ) ≤ 4 * r := by
      calc (x + h) ^ (1 / 64 : ℝ) ≤ (4 * y) ^ (1 / 64 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hxh) (by norm_num)
        _ = 4 ^ (1 / 64 : ℝ) * r := by rw [Real.mul_rpow (by norm_num) hy₀.le]
        _ ≤ 4 * r := by
            gcongr
            calc (4 : ℝ) ^ (1 / 64 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    calc Real.log (x + h) ≤ (x + h) ^ (1 / 64 : ℝ) / (1 / 64) := h₁
      _ ≤ 4 * r / (1 / 64) := by gcongr
      _ = 256 * r := by ring
  -- the identity behind the differencing
  set S := ∑ n ∈ Finset.Icc 1 m, a n
  set Wx := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n)
  set Wxh := ∑ n ∈ Finset.Icc 1 ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)
  have hid : (h : ℂ) * (S - I₁ * y) = (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S) +
        I₁ * (h * ((x : ℂ) - y + h / 2)) := by
    push_cast
    ring
  have hxy : ‖(x : ℂ) - y + h / 2‖ ≤ 1 / 2 + h / 2 := by
    rw [show (x : ℂ) - y + h / 2 = ((x - y + h / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_le]
    simp only [x]
    constructor <;> linarith
  have hmain : (h : ℝ) * ‖S - I₁ * y‖ ≤ 32 * |B| * k * r ^ 124 +
      h ^ 2 * (256 * r) + h * (1 / 2 + h / 2) := by
    have h₁ : ‖(h : ℂ) * (S - I₁ * y)‖ = h * ‖S - I₁ * y‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h₁, hid]
    have h₂ : ‖I₁ * (h * ((x : ℂ) - y + h / 2))‖ ≤ h * (1 / 2 + h / 2) := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc ‖I₁‖ * (h * ‖(x : ℂ) - y + h / 2‖) ≤ 1 * (h * (1 / 2 + h / 2)) := by
            gcongr
        _ = h * (1 / 2 + h / 2) := one_mul _
    have h₃ : ‖Wxh - Wx - h * S‖ ≤ h ^ 2 * (256 * r) := by
      rw [hxfloor] at hR
      refine hR.trans ?_
      gcongr
    have h₄ := norm_add_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S)) (I₁ * (h * ((x : ℂ) - y + h / 2)))
    have h₅ := norm_sub_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2))) (Wxh - Wx - h * S)
    have h₆ := norm_sub_le (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) (Wx - I₁ * ((x : ℂ) ^ 2 / 2))
    linarith
  -- dividing by `h ≥ r^62`
  have hfinal : ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := by
    refine le_of_mul_le_mul_left (hmain.trans ?_) hh₀
    have hB₀ : 0 ≤ |B| * k := by positivity
    have e₁ : 32 * |B| * k * r ^ 124 ≤ h * (32 * |B| * k * r ^ 63) := by
      have : r ^ 124 ≤ r ^ 62 * r ^ 63 := by
        rw [← pow_add]; exact pow_le_pow_right₀ hr₁ (by norm_num)
      calc 32 * |B| * k * r ^ 124 ≤ 32 * |B| * k * (r ^ 62 * r ^ 63) := by gcongr
        _ ≤ 32 * |B| * k * (h * r ^ 63) := by gcongr
        _ = h * (32 * |B| * k * r ^ 63) := by ring
    have e₂ : (h : ℝ) ^ 2 * (256 * r) ≤ h * (512 * r ^ 63) := by
      have : (h : ℝ) * r ≤ 2 * r ^ 63 := by
        calc (h : ℝ) * r ≤ 2 * r ^ 62 * r := by gcongr
          _ = 2 * r ^ 63 := by ring
      nlinarith
    have e₃ : (h : ℝ) * (1 / 2 + h / 2) ≤ h * (2 * r ^ 63) := by
      gcongr
      linarith
    have e₄ : 32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63 ≤ C₀ * k * r ^ 63 := by
      have h₁ : (514 : ℝ) * r ^ 63 ≤ 520 * k * r ^ 63 := by
        have : 0 ≤ r ^ 63 := by positivity
        nlinarith
      have h₂ : C₀ * k * r ^ 63 = 32 * |B| * k * r ^ 63 + 520 * k * r ^ 63 := by
        simp only [C₀]; ring
      linarith
    calc 32 * |B| * k * r ^ 124 + (h : ℝ) ^ 2 * (256 * r) + h * (1 / 2 + h / 2)
        ≤ h * (32 * |B| * k * r ^ 63) + h * (512 * r ^ 63) + h * (2 * r ^ 63) := by
          linarith
      _ = h * (32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63) := by ring
      _ ≤ h * (C₀ * k * r ^ 63) := mul_le_mul_of_nonneg_left e₄ hh₀.le
  -- conclude
  have hS : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
      (if χ = 1 then (y : ℂ) else 0) = S - I₁ * y := by
    simp only [S, I₁, a, m]
    split_ifs <;> ring
  have hC₀ : 1 ≤ C₀ := by simp only [C₀]; linarith [abs_nonneg B]
  have hkC : (k : ℝ) ≤ (k : ℝ) ^ C₀ := by
    calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (k : ℝ) ^ C₀ := Real.rpow_le_rpow_of_exponent_le hk hC₀
  rw [hS, hy63]
  calc ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := hfinal
    _ ≤ C₀ * (k : ℝ) ^ C₀ * r ^ 63 := by gcongr

end Erdos408
