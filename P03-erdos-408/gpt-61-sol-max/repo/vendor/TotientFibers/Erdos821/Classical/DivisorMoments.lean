module
public import Mathlib.Tactic

public import OAI.NumberTheory.PrimeGaps.OrthantIntegrals
public import Erdos821.Blueprint.Classical

@[expose] public section

open scoped BigOperators

namespace Erdos821.Classical

/-- The divisor count is submultiplicative. -/
theorem divisors_card_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  let S := a.primeFactors ∪ b.primeFactors
  have hS : (a * b).primeFactors = S := by
    simp [S, Nat.primeFactors_mul ha hb]
  rw [Nat.card_divisors (mul_ne_zero ha hb), Nat.card_divisors ha,
    Nat.card_divisors hb, hS]
  have hA : ∏ p ∈ S, (a.factorization p + 1) =
      ∏ p ∈ a.primeFactors, (a.factorization p + 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_union_left)
    aesop
  have hB : ∏ p ∈ S, (b.factorization p + 1) =
      ∏ p ∈ b.primeFactors, (b.factorization p + 1) := by
    symm
    apply Finset.prod_subset (Finset.subset_union_right)
    aesop
  have hprod : ∀ p ∈ S,
      a.factorization p + b.factorization p + 1 ≤
        (a.factorization p + 1) * (b.factorization p + 1) := by
    grind
  calc
    _ = ∏ p ∈ S, (a.factorization p + b.factorization p + 1) := by
      simp_all
    _ ≤ ∏ p ∈ S, ((a.factorization p + 1) * (b.factorization p + 1)) := by
      apply Finset.prod_le_prod
      intro p hp
      exact hprod p hp
    _ = _ := by rw [Finset.prod_mul_distrib, hA, hB]

/-- The generalized divisor function of order `2^k` majorizes the `k`-th
power of the ordinary divisor count. -/
theorem divisorMultiplicity_pow_lower  k n  (hn : 0 < n) :
    n.divisors.card ^ k ≤ OAI.LargePrimeGaps.divisorMultiplicity (2 ^ k) n := by
  induction k generalizing n with
  | zero =>
      simp [OAI.LargePrimeGaps.divisorMultiplicity, hn.ne']
  | succ k ih =>
      let q := 2 ^ k
      have hpow : 2 ^ (k + 1) = q + q := by
        dsimp [q]
        rw [pow_succ, Nat.mul_two]
      rw [hpow]
      have hrep (m : ℕ) :
          OAI.LargePrimeGaps.divisorMultiplicity (q + q) m =
            ∑ d ∈ m.divisors,
              OAI.LargePrimeGaps.divisorMultiplicity q d *
                OAI.LargePrimeGaps.divisorMultiplicity q (m / d) := by
        rw [OAI.LargePrimeGaps.divisorMultiplicity, pow_add,
          ArithmeticFunction.mul_apply]
        rw [Nat.sum_divisorsAntidiagonal
          (fun a b => (ArithmeticFunction.zeta ^ q) a * (ArithmeticFunction.zeta ^ q) b)]
        rfl
      calc
        n.divisors.card ^ (k + 1) = n.divisors.card ^ k * n.divisors.card := by
          rw [pow_succ]
        _ = ∑ d ∈ n.divisors, n.divisors.card ^ k := by simp [mul_comm]
        _ ≤ ∑ d ∈ n.divisors,
            OAI.LargePrimeGaps.divisorMultiplicity q d *
              OAI.LargePrimeGaps.divisorMultiplicity q (n / d) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
          have hqp : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdp
          have hfac : d * (n / d) = n := Nat.mul_div_cancel' hdvd
          have hcount : n.divisors.card ≤ d.divisors.card * (n / d).divisors.card := by
            grind [divisors_card_mul_le]
          calc
            n.divisors.card ^ k ≤
                (d.divisors.card * (n / d).divisors.card) ^ k :=
              Nat.pow_le_pow_left hcount k
            _ = d.divisors.card ^ k * (n / d).divisors.card ^ k := by rw [Nat.mul_pow]
            _ ≤ OAI.LargePrimeGaps.divisorMultiplicity q d *
                OAI.LargePrimeGaps.divisorMultiplicity q (n / d) :=
              Nat.mul_le_mul (ih d hdp) (ih (n / d) hqp)
        _ = OAI.LargePrimeGaps.divisorMultiplicity (q + q) n := (hrep n).symm

/-- The fixed divisor moments have logarithmic reciprocal and counting bounds. -/
def DivisorMoments  :=
  ∀ k : ℕ, ∃ C K : ℝ, 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / n) ≤
      K * Real.log (2 * Y) ^ C ∧
    (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k) ≤
      K * Y * Real.log (2 * Y) ^ C

theorem divisorMoments : DivisorMoments := by
  intro k
  let D : ℕ := 2 ^ k
  let c : ℝ := 1 + (Real.log 2)⁻¹
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(D : ℝ), c ^ D, by positivity, ?_⟩
  intro Y hY
  let N : ℕ := ⌊Y⌋₊
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (le_trans (by norm_num) hY)).2 (by exact_mod_cast hY)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (le_trans (by norm_num) hY)
  have hN2Y : (N : ℝ) ≤ 2 * Y := by nlinarith [hNY, hY]
  have hlogY : Real.log (N : ℝ) ≤ Real.log (2 * Y) :=
    Real.log_le_log hNpos (by nlinarith [hN2Y])
  have hlog2Y : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) (by nlinarith [hY])
  have hlogpos : 0 < Real.log (2 * Y) :=
    Real.log_pos (by nlinarith [hY])
  have hharm : (harmonic N : ℝ) ≤ c * Real.log (2 * Y) := by
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log (2 * Y) := by simpa [add_comm] using add_le_add_left hlogY 1
      _ ≤ c * Real.log (2 * Y) := by
        have hprod : 1 ≤ (Real.log 2)⁻¹ * Real.log (2 * Y) := by
          calc
            1 = (Real.log 2)⁻¹ * Real.log 2 := by field_simp [hlog2.ne']
            _ ≤ (Real.log 2)⁻¹ * Real.log (2 * Y) :=
              mul_le_mul_of_nonneg_left hlog2Y (inv_nonneg.mpr hlog2.le)
        dsimp [c]
        nlinarith [hprod]
  have hrec :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤
        (harmonic N : ℝ) ^ D := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N,
          (OAI.LargePrimeGaps.divisorMultiplicity D n : ℝ) / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnp : 0 < n := by
          have hn' := Finset.mem_Icc.mp hn
          omega
        have hmaj : (n.divisors.card : ℝ) ^ k ≤
            (OAI.LargePrimeGaps.divisorMultiplicity D n : ℝ) := by
          exact_mod_cast divisorMultiplicity_pow_lower k n hnp
        exact div_le_div_of_nonneg_right hmaj (by positivity)
      _ ≤ (harmonic N : ℝ) ^ D :=
        OAI.LargePrimeGaps.sum_divisorMultiplicity_reciprocal_le D N
  have hrecBound :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤
        c ^ D * Real.log (2 * Y) ^ (D : ℝ) := by
    calc
      _ ≤ (harmonic N : ℝ) ^ D := hrec
      _ ≤ (c * Real.log (2 * Y)) ^ D := by
        have hHnonneg : (0 : ℝ) ≤ (harmonic N : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          positivity
        exact pow_le_pow_left₀ hHnonneg hharm D
      _ = c ^ D * Real.log (2 * Y) ^ D := by rw [mul_pow]
      _ = c ^ D * Real.log (2 * Y) ^ (D : ℝ) := by simp [Real.rpow_natCast]
  have hunweighted :
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k) ≤
        Y * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, Y * ((n.divisors.card : ℝ) ^ k / n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Icc.mp hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hnI.2).trans hNY
        have hfactor :
            (n.divisors.card : ℝ) ^ k =
              ((n.divisors.card : ℝ) ^ k / n) * (n : ℝ) := by
          field_simp [hnpos.ne']
        calc
          (n.divisors.card : ℝ) ^ k =
              ((n.divisors.card : ℝ) ^ k / n) * (n : ℝ) := hfactor
          _ ≤ ((n.divisors.card : ℝ) ^ k / n) * Y :=
            mul_le_mul_of_nonneg_left hnY
              (div_nonneg (by positivity) hnpos.le)
          _ = Y * ((n.divisors.card : ℝ) ^ k / n) := by ring
      _ = Y * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) := by
        rw [Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · simpa only [N] using hrecBound
  · calc
      _ ≤ Y * (c ^ D * Real.log (2 * Y) ^ (D : ℝ)) := hunweighted.trans (mul_le_mul_of_nonneg_left hrecBound (by positivity))
      _ = c ^ D * Y * Real.log (2 * Y) ^ (D : ℝ) := by ring

end Erdos821.Classical

namespace Erdos821.DivisorHarmonic

open Erdos821.Classical

end Erdos821.DivisorHarmonic

theorem Erdos821.Blueprint.DivisorMoments_proof :
    Erdos821.Blueprint.DivisorMoments := Erdos821.Classical.divisorMoments
