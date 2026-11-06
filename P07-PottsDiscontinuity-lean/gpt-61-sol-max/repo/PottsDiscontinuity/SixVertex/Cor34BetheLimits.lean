module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Conventions
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34BetheBase
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34Cyclotomic
public import PottsDiscontinuity.SixVertex.InfinityValue

/-!
# Corollary 3.4: specialize the Bethe eigenvalue limit at the discrete base

This module identifies the generic continuous-family eigenvalue limits with the centered
cyclotomic products in (3.5), then evaluates them for the full range `r ≥ 0`.
-/

@[expose] public section

open Finset Complex Filter Topology
open PottsDiscontinuity.PerronFrobenius


namespace PottsDiscontinuity.SixVertex

/-- The centered base momenta have total momentum zero, so their phases multiply to one. -/
theorem cor34_base_z_product_eq_one {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N) :
     ∏ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j)  = 1 := by
  rw [BetheAnsatz.prod_z_eq_exp_sum]
  
  
  rw [ Bethe.sum_eq_zero_of_mem_R_n_sym (Bethe.discreteBaseSolution_mem_S_n hN hn).2.2 ]
  simp

private theorem cor34_discreteIndex_ne_zero_of_even {n : ℕ} (hn : Even n) (j : Fin n) :
    Bethe.discreteBetheIndex n j ≠ 0 := by
  intro h
  have hnat : 2 * (j.val + 1) = n + 1 := by
    have hreal : 2 * ( j.val  + 1) = (n : ℝ) + 1 := by
      grind [Bethe.discreteBetheIndex]
    exact_mod_cast hreal
  rcases hn with ⟨k, hk⟩
  omega

section

variable {N n : ℕ}
include N n

private theorem cor34_base_momentum_ne_zero_of_even 
    (hn : Even n) (hbound : 2 * n ≤ N) (j : Fin n) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hnpos  := Nat.zero_lt_of_lt j.isLt
  
  
  
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (cor34_discreteIndex_ne_zero_of_even hn j)) (by
                                                     exact_mod_cast  Nat.ne_of_gt (Nat.sub_pos_of_lt (by omega)) )

/-- No even-parity base momentum is a zero root. -/
theorem cor34_base_z_ne_one_of_even  (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hn : Even n) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := BetheAnsatz.z_ne_one ((Bethe.discreteBaseSolution_mem_S_n hN hbound).left j)
                                                              (cor34_base_momentum_ne_zero_of_even hn hbound j)

/-- The normalized even Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedRegularEigenvalue_base_limit 
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hn : Even n) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((2 : ℂ) / ∏ j : Fin n,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  have hlim := cor34_normalizedRegularEigenvalue_tendsto hp
     fun j => by simp_all [cor34_base_z_ne_one_of_even] 
  have hprod := cor34_base_z_product_eq_one hN hbound
  
  have hform :
       ∏ j : Fin n,
          BetheAnsatz.z (Bethe.discreteBaseSolution N n j) /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j))  +
        ∏ j : Fin n,
           -1  /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
         2  / ∏ j : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    simp_all <;> grind
  rw [hp0] at hlim
  rw [hform] at hlim
  exact hlim

private theorem cor34_even_base_denominator_at_r_zero 
    (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * n) :
    ∏ j : Fin n,
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 2 := by
  
  have hnN : n < N := by omega
  let η  := cor34_halfRoot n
  let ζ  := η ^ 2
  let α  := η ^ (n + 1)
  
  
  have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * n )) := by
    grind [cor34_halfRoot]
  have hηroot : IsPrimitiveRoot η (2 * n) := by
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * n) (by omega) using 1
    
    norm_num
  have hζroot : IsPrimitiveRoot ζ n := by
    
    exact hηroot.pow (by omega) (by omega)
  have hηnroot : IsPrimitiveRoot (η ^ n) 2 :=
    hηroot.pow (by omega) (by omega)
  have hηn  := hηnroot.eq_neg_one_of_two_right
  
  
  have hp := X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) (by omega) (by
                                                                         dsimp [α]
                                                                         calc
                                                                           (η ^ (n + 1)) ^ n = (η ^ n) ^ (n + 1) := by
                                                                             rw [← pow_mul, Nat.mul_comm, pow_mul]
                                                                           _ = (-1 : ℂ) ^ (n + 1) := by rw [hηn]
                                                                           _ = -1 := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 (by
                                                                                                                                         simp_all))
  have heval := congrArg (Polynomial.eval  1 ) hp
  
  have hηne : η ≠ 0 := by
    simp_all 
  have hperiod : η ^ (2 * (n : ℤ)) = 1 := by
    convert hηroot.zpow_eq_one using 1; norm_cast
  have hphase (j : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n j) = η ^ (n + 1 + 2 * j.val) := by
    have hNm : N - n = n := by omega
    calc
      BetheAnsatz.z (Bethe.discreteBaseSolution N n j) =
          η ^ (2 *  j.val  + 1 - (n : ℤ)) := by
        simpa [hNm] using cor34_base_z_eq_halfRoot_zpow hnN j
      _ = η ^ (2 *  j.val  + 1 - (n : ℤ)) * η ^ (2 * (n : ℤ)) := by
        rw [hperiod, mul_one]
      _ = η ^ ( 2 *  j.val  + 1 -  n   + 2 * (n : ℤ)) :=
        (zpow_add₀ hηne _ _).symm
      _ = η ^ ((n + 1 + 2 * j.val : ℕ) : ℤ) := by congr 1; omega
      _ = η ^ (n + 1 + 2 * j.val) := by rw [zpow_natCast]
  
  let f  := fun i => if hi : i < n then
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
  calc
    ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        ∏ j : Fin n, f j := by
          aesop
    _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
    _ = ∏ i ∈ Finset.range n, (1 - ζ ^ i * α) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hin  := Finset.mem_range.mp hi
          simp only [f, dite_eq_left hin]
          simpa using congrArg (fun z : ℂ => 1 - z) (hphase ⟨i, hin⟩ |>.trans ( fun (j : Fin n) => by
                                                                                  
                                                                                  
                                                                                  ring  ⟨i, hin⟩))
    _ = 2 :=  by
                norm_num [Polynomial.eval_prod] at heval ⊢
                exact heval.symm 

end

private theorem cor34_odd_base_momentum_ne_zero {N n q : ℕ} (hnq : n + 1 = 2 * q)
    (hbound : 2 * n ≤ N) (j : Fin n)
    (hcenter : j ≠ ⟨q - 1, by omega⟩) :
    Bethe.discreteBaseSolution N n j ≠ 0 := div_ne_zero
                                        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by
                                                                                                    intro h
                                                                                                    have hval : j.val + 1 = q := by
                                                                                                      have hreal : 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 := by
                                                                                                        grind [Bethe.discreteBetheIndex]
                                                                                                      have hnat : 2 * (j.val + 1) = n + 1 := by exact_mod_cast hreal
                                                                                                      omega
                                                                                                    all_goals grind)) (by
                                                                                                            exact_mod_cast  Nat.ne_of_gt (Nat.sub_pos_of_lt (by omega)) )

/-- All nonzero-root factors in the odd limiting eigenvalue are regular. -/
theorem cor34_odd_base_z_ne_one {N n q : ℕ} (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) (j : Fin n)
    (hj : j ∈ Finset.univ.erase ⟨q - 1, by omega⟩) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  
  apply BetheAnsatz.z_ne_one ((Bethe.discreteBaseSolution_mem_S_n hN hbound).1 j)
  exact cor34_odd_base_momentum_ne_zero hnq hbound j (by
    simp_all)

/-- The normalized odd Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedZeroEigenvalue_base_limit {N n q : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hlim := cor34_normalizedZeroEigenvalue_tendsto (N := N) hp l
     fun j hj => by simpa [hp0] using cor34_odd_base_z_ne_one hN hbound hnq j hj 
  have hsign : (-1 : ℂ) ^ (n - 1) = 1 := by
    have hnEven : Even (n - 1) := by
      refine ⟨q - 1, ?_⟩
      omega
    simp_all
  have hform :
      ( N  -  n ) *
        ∏ j ∈ Finset.univ.erase l,
           -1  / (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ( N  -  n ) /
        ∏ j ∈ Finset.univ.erase l,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    aesop
  rw [hp0] at hlim
  rw [hform] at hlim
  simpa [l] using hlim

private theorem cor34_halfRoot_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (cor34_halfRoot m) (2 * m) := by
  
  
  rw [(by
         grind [cor34_halfRoot] : cor34_halfRoot m = Complex.exp (2 * Real.pi * Complex.I / (2 * m )))]
  convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
  
  norm_num

section

variable {N n r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * (n + r))
include hp hp0 hNpos hbound hnpos hn hN

/-- For even `n` and positive `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
private theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive  (hr : 0 < r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  
  have hm : N - n = n + 2 * r := by omega
  let m  := n + 2 * r
  let η  := cor34_halfRoot m
  let k  := 2 * m + 1 - n
  
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_halfRoot_primitive (by omega)
  
  have hperiod : η ^ (2 * (m : ℤ)) = 1 := by
    convert hηroot.zpow_eq_one using 1; norm_cast
  have heta : cor34_halfRoot (N - n) = η := by
    simp [η, m, hm]
  have hfactor (i : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n i) = η ^ (k + 2 * i.val) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, heta]
    have hexp :  (k + 2 * i.val : ℕ)  =  2 * m  +
        (2 *  i.val  + 1 - (n : ℤ)) := by
      
      omega
    calc
      η ^ (2 *  i.val  + 1 - (n : ℤ)) =
          η ^ ( 2 * m  + (2 *  i.val  + 1 - (n : ℤ))) := by
            rw [zpow_add₀ (by
                             
                             exact Complex.exp_ne_zero _), hperiod, one_mul]
      _ = η ^ ((k + 2 * i.val : ℕ) : ℤ) := by rw [← hexp]
      _ = η ^ (k + 2 * i.val) := by rw [zpow_natCast]
  have hden :
       ∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))  =
        ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
    let f  := fun i => if hi : i < n then
      1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
    calc
      ∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
          ∏ i : Fin n, f i := by
            grind
      _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
      _ = ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
            apply Finset.prod_congr rfl
            grind
  have hcyclo := cor34_cyclotomic_even_evaluation n r hn hr
  have hvalue :
       2  / ∏ i : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
         2 ^ r  * ∏ j ∈ Finset.range r,
          ( 1 + Real.cos
            (Real.pi *  (2 * j + 1 )  / ( n  + 2 * r))  : ℂ) := by
    grind [cor34_halfRoot]
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using  cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn 

/-- For even `n` and nonnegative `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot  (hr : 0 ≤ r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · simp_all [cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive]
  · have hrzero : r = 0 := by omega
    subst r
    
    
    have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
    have hvalue :  2  /
        ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [ cor34_even_base_denominator_at_r_zero hnpos hn (by simpa using hN) ]
      norm_num
    
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using  by
                   rw [hvalue] at hbase
                   exact hbase 

end

section

variable {N n q r : ℕ} (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r))
include hbound hnq hN

/-- The base phase at an odd centered index is the shifted power used in the odd
cyclotomic evaluation of `SixVertex/Cor34Cyclotomic.lean`, away from the zero root. -/
private theorem cor34_odd_base_phase_shift 
    (i : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      (cor34_halfRoot (n + 2 * r) ^ 2) ^
        ( n + 2 * r + 1 - q  + i.val) := by
  let m  := n + 2 * r
  let η  := cor34_halfRoot m
  let ζ  := η ^ 2
  let s  := m + 1 - q
  have hm : N - n = m := by  omega
  
  
  have hζroot : IsPrimitiveRoot ζ m := by
    
    exact (cor34_halfRoot_primitive (by omega)).pow (by omega) (by omega)
  
  have hζperiod : ζ ^ (m : ℤ) = 1 := by
    convert hζroot.zpow_eq_one using 1
  
  have hshift :  (s + i.val : ℕ)  =
       m  + (i.val : ℤ) + 1 - q := by
    
    omega
  have hpow : ζ ^ (s + i.val) = η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
    rw [← zpow_natCast, hshift]
    calc
      ζ ^ ( m  + (i.val : ℤ) + 1 - q) =
          ζ ^ ( m  + ((i.val : ℤ) + 1 - q)) := by  ring
      _ = ζ ^ ((i.val : ℤ) + 1 - q) := by
        rw [zpow_add₀ (by
                         dsimp [ζ, η, cor34_halfRoot]
                         simp_all), hζperiod, one_mul]
      _ = η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
        
        exact (zpow_mul η 2 ( i.val  + 1 - q)).symm
  rw [(by
         rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, hm]
         grind : BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      η ^ (2 * ((i.val : ℤ) + 1 - q))), ← hpow]

/-- The odd cyclotomic denominator is exactly the cyclotomic product of
`SixVertex/Cor34Cyclotomic.lean`, with the zero-root factor replaced by one. -/
private theorem cor34_odd_base_denominator_eq_cyclotomic  :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n,
         if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)  := by
  let l : Fin n := ⟨q - 1, by omega⟩
  let gFin  := fun i => if i = l then 1 else
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)
  
  let f  := fun i => if hi : i < n then gFin ⟨i, hi⟩ else 1
  have hrange : ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) =
      ∏ i : Fin n, gFin i := by
    
    have heq : ∀ i ∈ Finset.range n,
        f i =  if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)  := by
      grind [cor34_odd_base_phase_shift]
    calc
      _ = ∏ i ∈ Finset.range n, f i := Finset.prod_congr rfl  fun i hi => (heq i hi).symm 
      _ = ∏ i : Fin n, f i := (Fin.prod_univ_eq_prod_range f n).symm
      _ = ∏ i : Fin n, gFin i := by
        grind
  
  rw [← (by
           calc
             ∏ i : Fin n, gFin i = ∏ i ∈ Finset.univ, gFin i := by simp
             _ = (∏ i ∈ Finset.univ.erase l, gFin i) * gFin l := by
               symm
               exact Finset.prod_erase_mul Finset.univ gFin (Finset.mem_univ l)
             _ = ∏ i ∈ Finset.univ.erase l,
                   (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
               simp only [gFin, ↓reduceIte, mul_one]
               apply Finset.prod_congr rfl
               simp_all : ∏ i : Fin n, gFin i =
      ∏ i ∈ Finset.univ.erase l,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))), hrange]

end

/-- At half filling, the odd centered denominator is the product over all nontrivial
powers of a primitive `n`th root, hence equals `n`. -/
private theorem cor34_odd_base_denominator_at_r_zero {N n q : ℕ}
    (hnpos : 0 < n) (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q)
    (hN : N = 2 * n) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = (n : ℂ) := by
  let ζ  := cor34_halfRoot n ^ 2
  let s  := n + 1 - q
  let g  := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  let u  := fun i => 1 - ζ ^ (s + i)
  have hζroot : IsPrimitiveRoot ζ n := cor34_halfRoot_primitive (by omega) |>.pow (by omega) (by omega)
  have hden := cor34_odd_base_denominator_eq_cyclotomic
    hbound hnq (r := 0) (by simpa using hN)
  
  have hpre :  ∏ i ∈ Finset.range q, g i  =
      ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q =  q - 1  + 1 by omega, Finset.prod_range_add]
    have hprefix :  ∏ i ∈ Finset.range (q - 1), g i  =
        ∏ i ∈ Finset.range (q - 1), u i := by
      apply Finset.prod_congr rfl
      grind
    rw [hprefix]
    simp [g]
  
  
  have hcanonical :
       ∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1))  =
        (∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show n - 1 =  n - q  + (q - 1) by omega, Finset.prod_range_add]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    grind
  have hζroot' : IsPrimitiveRoot ζ (n - 1 + 1) := by
    grind
  have hprod := hζroot'.prod_one_sub_pow_eq_order
  
  calc
    _ = ∏ i ∈ Finset.range n, g i :=  by
                                        grind 
    _ = (∏ i ∈ Finset.range (q - 1), u i) *
          ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) :=  by
                                                              calc
                                                                ∏ i ∈ Finset.range n, g i =
                                                                    (∏ i ∈ Finset.range q, g i) *
                                                                      ∏ i ∈ Finset.range (n - q), g (q + i) := by
                                                                  have hadd := Finset.prod_range_add g q (n - q)
                                                                  grind
                                                                _ = _ := by rw [hpre, (by
                                                                                         apply Finset.prod_congr rfl
                                                                                         intro i hi
                                                                                         have hskip : q + i ≠ q - 1 := by
                                                                                           
                                                                                           omega
                                                                                         have hexp : s + (q + i) = n + (i + 1) := by
                                                                                           
                                                                                           omega
                                                                                         have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
                                                                                           rw [hexp, pow_add, hζroot.pow_eq_one, one_mul]
                                                                                         simp [g, hskip, hpow] :  ∏ i ∈ Finset.range (n - q), g (q + i)  =
      ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)))] 
    _ = (∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := mul_comm _ _
    _ = ∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1)) := hcanonical.symm
    _ =  n  :=  by
                      simp_all 

section

variable {N n q r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r))
include hp hp0 hNpos hbound hnpos hnq hN

/-- For odd `n` and positive `r`, the normalized zero-root Bethe eigenvalue tends to the
cyclotomic cosine product, hence to the Perron root of the limiting transfer block. -/
private theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive  (hr : 0 < r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  
  have hden := cor34_odd_base_denominator_eq_cyclotomic hbound hnq hN
  have hcyclo := cor34_cyclotomic_odd_evaluation n r q hnq hr
  have hvalue :
      ( N  -  n ) /
        ∏ j ∈ Finset.univ.erase  ⟨q - 1, by omega⟩ ,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
         2 ^ r  * ∏ j ∈ Finset.range r,
          ( 1 + Real.cos
            (Real.pi *  (2 * j + 1 )  / ( n  + 2 * r))  ) := by
    have hcast :  N  - (n : ℂ) =  n + 2 * r  := by
      rw [hN]
      push_cast
      ring
    rw [hden, hcast]
    simpa [cor34_halfRoot] using hcyclo
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using  cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq 

/-- For odd `n` and nonnegative `r`, the normalized zero-root Bethe eigenvalue tends to the
cosine product, hence to the Perron root of the limiting transfer block. -/
theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot  (hr : 0 ≤ r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · exact cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive
      hp hp0 hNpos hbound hnpos hnq hN hrpos
  · have hrzero : r = 0 := by omega
    subst r
    have hN' : N = 2 * n := by simpa using hN
    have hden := cor34_odd_base_denominator_at_r_zero hnpos hbound hnq hN'
    have hbase := cor34_normalizedZeroEigenvalue_base_limit
      hp hp0 hNpos hbound hnq
    have hvalue :
        ( N  -  n ) /
          ∏ j ∈ Finset.univ.erase  ⟨q - 1, by omega⟩ ,
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [hden, hN']
      push_cast
      field_simp [by exact_mod_cast  Nat.ne_of_gt hnpos ]
      norm_num
    have hlim : Tendsto
        (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
           ⟨q - 1, by omega⟩ )
        (𝓝 0) (𝓝  1 ) := by
      rw [hvalue] at hbase
      exact hbase
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using hlim

end

end PottsDiscontinuity.SixVertex
