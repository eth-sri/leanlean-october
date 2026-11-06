module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.IdealEuler
public import PrimeNumberTheoremAnd.Wiener

@[expose] public section

namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

def primeBase (I : Ideal O)  := if h : IsPrimePow I then h.choose else 1

theorem primeBase_spec  {I}  (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  grind [primeBase]

theorem primeBase_pow  {P}  (hP : Prime P)  {k}  (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

def value (I : Ideal O)  :=
  if IsPrimePow I then Real.log (Ideal.absNorm (primeBase I)) else 0

@[simp] theorem value_zero : value (0 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_zero, ite_false]

@[simp] theorem value_one : value (1 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_one, ite_false]

theorem value_pow  {P}  (hP : Prime P)  {k}  (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, ite_eq_left (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg  I  : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, ite_eq_left hI]
    positivity
  · simp only [value, hI, ite_false, le_refl]

section
variable {P : Ideal O} (hP : Prime P) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {I J : Ideal O} (hI : IsPrimePow I)

include hI in
theorem isPrimePow_absNorm     :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow  
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := ite_eq_right (fun h => hI (isPrimePow_absNorm h))

include hP hp in
theorem prime_mem_primesOver_of_dvd_norm    
        (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

include hp hk hI in
theorem primeBase_mem_primesOver      
        (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

include hI in
theorem primeBase_injective_on_norm    
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (SmoothMobiusCorrection.prime_norm_two_le ⟨_, hP⟩)
    grind
  simp_all

end

def normFiber (n : ℕ)  :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_normFiber  n   I  : I ∈ normFiber n ↔ Ideal.absNorm I = n :=
  Set.Finite.mem_toFinset _

def coeff (w : Ideal O → ℝ) (n : ℕ)  := ∑ I ∈ normFiber n, w I * value I

section
variable (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ)

include hw in
theorem coeff_nonneg       :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted   (hw : ∀ I, w I ≤ 1)  n  :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers   :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

end

theorem coeff_eq_zero_of_not_primePow  {n}  (hn : ¬IsPrimePow n)
     w  : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  simp_all [value_eq_zero_of_norm_not_primePow]

def primesOver (p : ℕ) [Fact p.Prime]  :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).toFinset

section
variable (p : ℕ) (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I) (hw1 : ∀ I, w I ≤ 1)

@[simp] theorem mem_primesOver   [Fact p.Prime]  P  :
    P ∈ primesOver p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver O :=
  Set.Finite.mem_toFinset _

theorem primesOver_card   [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le   [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [ShortDraftHeckeBridge.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [ShortDraftHeckeBridge.ramified_count]
  grind

theorem coeff_prime_pow_le   [hp : Fact p.Prime]  {k}  (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    grind [primeBase_injective_on_norm]
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      gcongr <;> first | assumption | positivity | linarith
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt   (hw : ∀ I, w I ≤ 1)  n  :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    grind [coeff_le_unweighted, coeff_prime_pow_le]
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

include hw0 hw1 in
theorem coeff_chebyshev    
      :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

include hw0 hw1 in
theorem coeff_summable_nterm    
       {σ}  (hσ : 1 < σ) :
    Summable (nterm (fun n => (coeff w n : ℂ)) σ) := by
  have hs : Summable (nterm (fun n => (vonMangoldt n : ℂ)) σ) := by
    simpa only [← nterm_eq_norm_term] using
      (@ArithmeticFunction.LSeriesSummable_vonMangoldt (σ : ℂ) (by simpa using hσ)).norm
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro n
    exact ite_nonneg (by positivity) (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  · intro n
    by_cases hn : n = 0
    · simp only [nterm, hn, ite_true, mul_zero, le_refl]
    · simp only [nterm, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (coeff_le_two_vonMangoldt w hw1 n)
        (Real.rpow_nonneg (by positivity) _)

include hw0 hw1 in
theorem coeff_LSeriesSummable    
       {s}  (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff w n : ℂ)) s := by
  apply Summable.of_norm
  simpa only [norm_term_eq_nterm_re] using coeff_summable_nterm w hw0 hw1 hs

end

def classCoeff (C : Set (Ideal O)) (n : ℕ)  :=
  coeff (fun I => if I ∈ C then 1 else 0) n

section
variable (C : Set (Ideal O)) (n : ℕ)

theorem classCoeff_nonneg     : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt     :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev   :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

theorem classCoeff_summable_nterm    {σ}  (hσ : 1 < σ) :
    Summable (nterm (fun n => (classCoeff C n : ℂ)) σ) :=
  (by aesop (add safe [coeff_summable_nterm]))

end

end

end SevenEighths.IdealMangoldt

end OAI
