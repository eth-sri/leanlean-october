module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.Extraction.Allocation.Strip
import Erdos408.Analytic.ProxyTwist

public import Erdos408.Extraction.TypeII.Euler
public import Erdos408.Extraction.TypeII.PrimeSums

/-!
# The damped weight is completely multiplicative

`n = n̄ · n_P`, where `n̄` strips the candidate primes and `n_P` is the
candidate part, and `log n = log n̄ + ∑_{p ∈ P} v_p(n) log p`. The damped weight
`g_j(n) = [n̄ Y-rough] j^{-Ω_P(n)}` is the completely multiplicative function
with prime values `1/j` on candidate primes, `0` on the other primes `≤ Y`,
and `1` above `Y`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-! ### Stripping a set of primes -/

section Strip

variable (P : Finset ℕ)

/-- The part of `n` made of the primes of `P`. -/
noncomputable def partPrimes (n : ℕ)  :=
  ∏ p ∈ n.primeFactors with p ∈ P, p ^ n.factorization p

section
variable (n : ℕ)


theorem stripPrimes_eq_prod   :
    stripPrimes P n = (n.factorization.filter (· ∉ P)).prod (· ^ ·) := by
  rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
  rfl

alias factorization_stripPrimes := _root_.Erdos408.factorization_stripPrimes

theorem primeFactors_stripPrimes   :
    (stripPrimes P n).primeFactors = n.primeFactors.filter (· ∉ P) := by
  rw [← Nat.support_factorization, factorization_stripPrimes, Finsupp.support_filter,
    Nat.support_factorization]

alias stripPrimes_ne_zero := _root_.Erdos408.stripPrimes_ne_zero

theorem partPrimes_ne_zero   : partPrimes P n ≠ 0 := by
  unfold partPrimes
  exact prod_ne_zero_iff.2 fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).ne_zero

/-- `n = n̄ · n_P`. -/
theorem stripPrimes_mul_partPrimes  {n}  (hn : n ≠ 0) :
    stripPrimes P n * partPrimes P n = n := by
  have h := Finsupp.prod_filter_mul_prod_filter_not (f := n.factorization) (p := (· ∉ P))
    (g := (· ^ ·))
  have hpart : (n.factorization.filter fun a => ¬a ∉ P).prod (· ^ ·) = partPrimes P n := by
    rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
    unfold partPrimes
    simp only [not_not]
  simp_all [stripPrimes_eq_prod]

theorem stripPrimes_dvd   : stripPrimes P n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  exact Dvd.intro _ (stripPrimes_mul_partPrimes P hn)

theorem stripPrimes_le  {n}  (hn : n ≠ 0) : stripPrimes P n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (stripPrimes_dvd P n)

theorem partPrimes_eq_prod   :
    partPrimes P n = (n.factorization.filter (· ∈ P)).prod (· ^ ·) := by
  rw [Finsupp.prod_filter_index, Finsupp.support_filter, Nat.support_factorization]
  rfl

theorem factorization_partPrimes   :
    (partPrimes P n).factorization = n.factorization.filter (· ∈ P) := by
  rw [partPrimes_eq_prod]
  refine Nat.prod_pow_factorization_eq_self fun p hp => ?_
  simp_all

theorem primeFactors_partPrimes   :
    (partPrimes P n).primeFactors = n.primeFactors.filter (· ∈ P) := by
  rw [← Nat.support_factorization, factorization_partPrimes, Finsupp.support_filter,
    Nat.support_factorization]

end

section
variable {n : ℕ} (hn : n ≠ 0)


include hn in
theorem partPrimes_le     : partPrimes P n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Dvd.intro_left _ (stripPrimes_mul_partPrimes P hn))

include hn in
/-- `log n = log n̄ + ∑_{p ∈ P} v_p(n) log p`. -/
theorem log_eq_log_stripPrimes_add     :
    Real.log n = Real.log (stripPrimes P n) +
      ∑ p ∈ n.primeFactors with p ∈ P, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← stripPrimes_mul_partPrimes P hn]
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast stripPrimes_ne_zero P n)
    (by exact_mod_cast partPrimes_ne_zero P n)]
  congr 1
  unfold partPrimes
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    aesop)]
  simp_all

end

end Strip

/-! ### The damped weight -/

/-- The prime values of the damped weight: `1/j` on candidate primes, `0` on the other
primes up to `Y`, and `1` above `Y`. -/
noncomputable def proxyLoc (x : ℝ) (j : ℕ) (p : ℕ)  :=
  if p ∈ candidatePrimes x then (j : ℝ)⁻¹ else if (p : ℝ) ≤ proxyCutoff x then 0 else 1

section
variable (x : ℝ)


/-- `g_j = cmul (proxyLoc x j)` on positive integers. -/
theorem dampedWeight_eq_cmul    j   {n}  (hn : n ≠ 0) :
    dampedWeight x j n = cmul (proxyLoc x j) n := by
  rw [cmul_apply hn, Finsupp.prod, Nat.support_factorization,
    ← prod_filter_mul_prod_filter_not n.primeFactors (· ∈ candidatePrimes x)]
  have h1 : ∏ p ∈ n.primeFactors with p ∈ candidatePrimes x,
      proxyLoc x j p ^ n.factorization p = ((j : ℝ)⁻¹) ^ candidateOmega x n := by
    rw [candidateOmega, ← prod_pow_eq_pow_sum]
    exact prod_congr rfl fun p hp => by simp [proxyLoc, (mem_filter.1 hp).2]
  rw [h1, dampedWeight, candidateStrip, primeFactors_stripPrimes]
  split_ifs with h
  · rw [prod_eq_one fun p hp => ?_, mul_one]
    obtain ⟨hpn, hpP⟩ := mem_filter.1 hp
    have := h p (mem_filter.2 ⟨hpn, hpP⟩)
    simp [proxyLoc, hpP, not_le.2 this]
  · push Not at h
    obtain ⟨p, hp, hpY⟩ := h
    rw [prod_eq_zero hp, mul_zero]
    obtain ⟨hpn, hpP⟩ := mem_filter.1 hp
    have hv : n.factorization p ≠ 0 :=
      (Nat.prime_of_mem_primeFactors hpn).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hpn) |>.ne'
    simp [proxyLoc, hpP, hpY, hv]

theorem dampedWeight_nonneg    j n  : 0 ≤ dampedWeight x j n := by
  unfold dampedWeight
  split_ifs
  · positivity
  · exact le_rfl

theorem dampedWeight_le_one    {j}  (hj : 1 ≤ j)  n  : dampedWeight x j n ≤ 1 := by
  unfold dampedWeight
  bound

end

/-! ### Candidate primes -/

section
variable {x γ : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ)


include hL in
/-- Candidate primes are primes in `[exp(L^{0.28}), exp(L^{0.45})]`. -/
theorem mem_candidatePrimes     {p : ℕ} (hp : p ∈ candidatePrimes x) :
    p.Prime ∧ Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by solve_by_elim [_root_.SharedProofs.permuted_mem_candidatePrimes]

/-! ### Pointwise bounds for the proxies -/

include hL hj in
/-- The density `D_j` is at least `∏_{p ≤ Y} (1 - 1/p) > 0`. -/
theorem prod_le_dampedDensity         :
    0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ∧
      ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ≤ dampedDensity x j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) :=
    prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
  refine ⟨hpos, ?_⟩
  unfold dampedDensity
  refine le_mul_of_one_le_right hpos.le (one_le_prod₀ fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
  have ht : (j : ℝ)⁻¹ / p ≤ 1 / 2 := by
    bound
  have ht0 : 0 ≤ (j : ℝ)⁻¹ / p := by positivity
  rw [one_le_inv₀ (by linarith)]
  linarith

include hL hj in
theorem dampedDensity_pos         :
    0 < dampedDensity x j :=
  lt_of_lt_of_le (prod_le_dampedDensity hL hj).1 (prod_le_dampedDensity hL hj).2

include hx hL hγ hj in
/-- `a_j^0(n) ≤ [x^γ < n] g_j(n) / (D_j γ L)`. -/
theorem unstrippedProxy_le          
        :
    0 ≤ unstrippedProxy x γ j n ∧ unstrippedProxy x γ j n ≤
      (if x ^ γ < n then dampedWeight x j n else 0) /
        (dampedDensity x j * (γ * Real.log x)) := by
  have hD := dampedDensity_pos hL hj
  have hg := dampedWeight_nonneg x j n
  unfold unstrippedProxy
  split_ifs with h
  · have hn : γ * Real.log x < Real.log n := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_lt_log (by positivity) h
    have hγL : 0 < γ * Real.log x := by positivity
    refine ⟨div_nonneg hg (mul_nonneg hD.le (hγL.trans hn).le), ?_⟩
    bound
  · simp

include hx hL hγ hj in
/-- `a_j(n) ≤ [x^γ < n] g_j(n) / (D_j γ L)`, since `n̄ ≤ n`. -/
theorem strippedProxy_le          
        :
    0 ≤ strippedProxy x γ j n ∧ strippedProxy x γ j n ≤
      (if x ^ γ < n then dampedWeight x j n else 0) /
        (dampedDensity x j * (γ * Real.log x)) := by
  have hD := dampedDensity_pos hL hj
  have hg := dampedWeight_nonneg x j n
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx.le hγ.le
  unfold strippedProxy
  split_ifs with h h'
  · have hn : γ * Real.log x < Real.log (candidateStrip x n) := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_lt_log (by positivity) h
    have hγL : 0 < γ * Real.log x := by positivity
    refine ⟨div_nonneg hg (mul_nonneg hD.le (hγL.trans hn).le), ?_⟩
    bound
  · exfalso
    apply h'
    rcases eq_or_ne n 0 with rfl | hn
    · simp [candidateStrip, stripPrimes] at h
      linarith
    exact lt_of_lt_of_le h (by exact_mod_cast stripPrimes_le _ hn)
  · exact ⟨le_rfl, div_nonneg hg (mul_nonneg hD.le (by positivity))⟩
  · simp

end

end Erdos408.TypeII
