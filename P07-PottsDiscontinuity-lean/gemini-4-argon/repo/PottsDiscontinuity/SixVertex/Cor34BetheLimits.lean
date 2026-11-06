module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Conventions
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34BetheBase
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34Cyclotomic
public import PottsDiscontinuity.SixVertex.InfinityValue

@[expose] public section

open Finset Complex Filter Topology
open PottsDiscontinuity.PerronFrobenius
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

theorem cor34_base_z_product_eq_one {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N) :
    (∏ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
  rw [BetheAnsatz.prod_z_eq_exp_sum,
    Bethe.sum_eq_zero_of_mem_R_n_sym (Bethe.discreteBaseSolution_mem_S_n hN hn).2.2]
  simp

private theorem cor34_base_momentum_ne_zero_of_even {N n : ℕ}
    (hn : Even n) (hbound : 2 * n ≤ N) (j : Fin n) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N - n ≠ 0 by omega)
  have hidx : Bethe.discreteBetheIndex n j ≠ 0 := fun h => by
    have hreal : ((2 * (j.val + 1) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
      push_cast; dsimp [Bethe.discreteBetheIndex] at h; linarith
    have hnat : 2 * (j.val + 1) = n + 1 := Nat.cast_injective hreal
    rcases hn with ⟨k, hk⟩; omega
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hidx) hden

theorem cor34_base_z_ne_one_of_even {N n : ℕ} (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hn : Even n) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 :=
  BetheAnsatz.z_ne_one ((Bethe.discreteBaseSolution_mem_S_n hN hbound).1 j)
    (cor34_base_momentum_ne_zero_of_even hn hbound j)

theorem cor34_normalizedRegularEigenvalue_base_limit {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hn : Even n) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((2 : ℂ) / ∏ j : Fin n,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  have hlim := cor34_normalizedRegularEigenvalue_tendsto hp
    (fun j => by simpa [hp0] using cor34_base_z_ne_one_of_even hN hbound hn j)
  have hsign : (-1 : ℂ) ^ n = 1 := hn.neg_one_pow
  rw [hp0, Finset.prod_div_distrib, Finset.prod_div_distrib] at hlim
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsign,
    cor34_base_z_product_eq_one hN hbound] at hlim
  convert hlim using 2
  ring

private theorem cor34_halfRoot_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (cor34_halfRoot m) (2 * m) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [show cor34_halfRoot m = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) by
    dsimp [cor34_halfRoot]; congr 1; field_simp [hmR]]
  convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
  congr 1; norm_num

private theorem prod_fin_one_sub_base_z_eq_range {N n : ℕ} (g : ℕ → ℂ)
    (hg : ∀ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j) = g j.val) :
    (∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j))) =
      ∏ i ∈ Finset.range n, (1 - g i) := by
  let f : ℕ → ℂ := fun i => if hi : i < n then
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
  calc ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j))
    _ = ∏ j : Fin n, f j := Finset.prod_congr rfl fun j _ => by simp [f]
    _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
    _ = ∏ i ∈ Finset.range n, (1 - g i) := Finset.prod_congr rfl fun i hi => by
      have hin : i < n := Finset.mem_range.mp hi
      simp [f, hin, hg ⟨i, hin⟩]

private theorem cor34_even_base_denominator_at_r_zero {N n : ℕ}
    (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * n) :
    ∏ j : Fin n,
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 2 := by
  let η : ℂ := cor34_halfRoot n
  let ζ : ℂ := η ^ 2
  let α : ℂ := η ^ (n + 1)
  have hηroot : IsPrimitiveRoot η (2 * n) := cor34_halfRoot_primitive hnpos.ne'
  have hζroot : IsPrimitiveRoot ζ n := hηroot.pow (by omega) (by omega)
  have hηn : η ^ n = -1 := (hηroot.pow (by omega) (by omega) : IsPrimitiveRoot (η ^ n) 2).eq_neg_one_of_two_right
  have hnplusOdd : Odd (n + 1) := by obtain ⟨k, hk⟩ := hn; exact ⟨k, by omega⟩
  have hαpow : α ^ n = -1 := by
    dsimp [α]; rw [← pow_mul, Nat.mul_comm, pow_mul, hηn]
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hnplusOdd
  have heval := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) hnpos hαpow)
  have hprod : (∏ i ∈ Finset.range n, (1 - ζ ^ i * α)) = 2 := by
    norm_num [Polynomial.eval_prod] at heval ⊢; exact heval.symm
  have hηne : η ≠ 0 := Complex.exp_ne_zero _
  have hperiod : η ^ (2 * (n : ℤ)) = 1 := by convert hηroot.zpow_eq_one using 1; norm_cast
  rw [prod_fin_one_sub_base_z_eq_range (fun i => ζ ^ i * α) fun j => ?_, hprod]
  have hNm : N - n = n := by omega
  calc BetheAnsatz.z (Bethe.discreteBaseSolution N n j)
    _ = η ^ (2 * (j.val : ℤ) + 1 - (n : ℤ)) := by
      simpa [η, hNm] using cor34_base_z_eq_halfRoot_zpow (show n < N by omega) j
    _ = η ^ ((2 * (j.val : ℤ) + 1 - (n : ℤ)) + 2 * (n : ℤ)) := by
      rw [zpow_add₀ hηne, hperiod, mul_one]
    _ = η ^ ((n + 1 + 2 * j.val : ℕ) : ℤ) := by congr 1; omega
    _ = ζ ^ j.val * α := by rw [zpow_natCast]; dsimp [ζ, α]; rw [pow_add, pow_mul]; ring

theorem cor34_odd_base_z_ne_one {N n q : ℕ} (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) (j : Fin n)
    (hj : j ∈ Finset.univ.erase ⟨q - 1, by omega⟩) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  apply BetheAnsatz.z_ne_one ((Bethe.discreteBaseSolution_mem_S_n hN hbound).1 j)
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N - n ≠ 0 by omega)
  have hidx : Bethe.discreteBetheIndex n j ≠ 0 := fun h => by
    have hreal : ((2 * (j.val + 1) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
      push_cast; dsimp [Bethe.discreteBetheIndex] at h; linarith
    have hnat : 2 * (j.val + 1) = n + 1 := Nat.cast_injective hreal
    exact (Finset.mem_erase.mp hj).1 (Fin.ext (show j.val = q - 1 by omega))
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hidx) hden

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
    (fun j hj => by simpa [hp0] using cor34_odd_base_z_ne_one hN hbound hnq j hj)
  have hnEven : Even (n - 1) := ⟨q - 1, by omega⟩
  have hsign : (-1 : ℂ) ^ (n - 1) = 1 := hnEven.neg_one_pow
  rw [hp0, Finset.prod_div_distrib] at hlim
  simp only [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ,
    Fintype.card_fin, Finset.mem_univ, hsign, one_div] at hlim
  convert hlim using 2
  ring

private theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 < r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
  let m : ℕ := n + 2 * r
  let η : ℂ := cor34_halfRoot m
  let k : ℕ := 2 * m + 1 - n
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_halfRoot_primitive (by omega)
  have hηne : η ≠ 0 := Complex.exp_ne_zero _
  have hperiod : η ^ (2 * (m : ℤ)) = 1 := by convert hηroot.zpow_eq_one using 1; norm_cast
  have hden := prod_fin_one_sub_base_z_eq_range (N := N) (n := n) (fun i => η ^ (k + 2 * i)) fun i => by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, show N - n = m by omega]
    calc η ^ (2 * (i.val : ℤ) + 1 - (n : ℤ))
      _ = η ^ ((2 * m : ℤ) + (2 * (i.val : ℤ) + 1 - (n : ℤ))) := by
        rw [zpow_add₀ hηne, hperiod, one_mul]
      _ = η ^ ((k + 2 * i.val : ℕ) : ℤ) := by congr 1; dsimp [k, m]; omega
      _ = η ^ (k + 2 * i.val) := zpow_natCast _ _
  have hcyclo := cor34_cyclotomic_even_evaluation n r hn hr
  have hvalue :
      (2 : ℂ) / ∏ i : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    rw [hden]; simpa [m, η, k, cor34_halfRoot] using hcyclo
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using hbase

theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · exact cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive
      hp hp0 hNpos hbound hnpos hn hN hrpos
  · obtain rfl : r = 0 := by omega
    have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
    rw [cor34_even_base_denominator_at_r_zero hnpos hn (by simpa using hN)] at hbase
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using hbase

private theorem cor34_odd_base_denominator_eq_cyclotomic {N n q r : ℕ}
    (_hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
  let m : ℕ := n + 2 * r
  let η : ℂ := cor34_halfRoot m
  let ζ : ℂ := η ^ 2
  let s : ℕ := m + 1 - q
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_halfRoot_primitive (by omega)
  have hζroot : IsPrimitiveRoot ζ m := hηroot.pow (by omega) (by omega)
  have hζne : ζ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hζperiod : ζ ^ (m : ℤ) = 1 := by convert hζroot.zpow_eq_one using 1
  have hphase (i : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n i) = ζ ^ (s + i.val) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, show N - n = m by omega,
      show 2 * (i.val : ℤ) + 1 - (n : ℤ) = 2 * ((i.val : ℤ) + 1 - q) by omega,
      ← zpow_natCast, show ((s + i.val : ℕ) : ℤ) = (m : ℤ) + ((i.val : ℤ) + 1 - q) by dsimp [s]; omega,
      zpow_add₀ hζne, hζperiod, one_mul]
    exact zpow_mul η 2 ((i.val : ℤ) + 1 - q)
  let l : Fin n := ⟨q - 1, by omega⟩
  let gFin : Fin n → ℂ := fun i => if i = l then 1 else
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)
  have hgFin : ∏ i : Fin n, gFin i =
      ∏ i ∈ Finset.univ.erase l, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
    rw [← Finset.prod_erase_mul Finset.univ gFin (Finset.mem_univ l)]
    simp only [gFin, ↓reduceIte, mul_one]
    exact Finset.prod_congr rfl fun i hi => ite_eq_right (Finset.mem_erase.mp hi).1
  let f : ℕ → ℂ := fun i => if hi : i < n then gFin ⟨i, hi⟩ else 1
  rw [← hgFin]
  calc ∏ i : Fin n, gFin i
    _ = ∏ i : Fin n, f i := Finset.prod_congr rfl fun i _ => by simp [f]
    _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
    _ = ∏ i ∈ Finset.range n, (if i = q - 1 then 1 else 1 - ζ ^ (s + i)) :=
      Finset.prod_congr rfl fun i hi => by
        have hin : i < n := Finset.mem_range.mp hi
        have hiff : (⟨i, hin⟩ : Fin n) = l ↔ i = q - 1 := Fin.ext_iff
        simp only [f, hin, ↓reduceDIte, gFin, hiff, hphase ⟨i, hin⟩]

private theorem cor34_odd_base_denominator_at_r_zero {N n q : ℕ}
    (_hnpos : 0 < n) (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q)
    (hN : N = 2 * n) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = (n : ℂ) := by
  let ζ : ℂ := cor34_halfRoot n ^ 2
  let s : ℕ := n + 1 - q
  let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  let u : ℕ → ℂ := fun i => 1 - ζ ^ (s + i)
  have hζroot : IsPrimitiveRoot ζ n :=
    (cor34_halfRoot_primitive (by omega)).pow (by omega) (by omega)
  have hden : ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = ∏ i ∈ Finset.range n, g i := by
    simpa [g, ζ, s] using cor34_odd_base_denominator_eq_cyclotomic hbound hnq (r := 0) (by simpa using hN)
  have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_succ]
    simp only [g, ↓reduceIte, mul_one]
    exact Finset.prod_congr rfl fun i hi => ite_eq_right (by have := Finset.mem_range.mp hi; omega)
  have hpost : (∏ i ∈ Finset.range (n - q), g (q + i)) =
      ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) :=
    Finset.prod_congr rfl fun i hi => by
      have hlt := Finset.mem_range.mp hi
      have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
        rw [show s + (q + i) = n + (i + 1) by dsimp [s]; omega, pow_add, hζroot.pow_eq_one, one_mul]
      simp [g, show q + i ≠ q - 1 by omega, hpow]
  have hζroot' : IsPrimitiveRoot ζ (n - 1 + 1) := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hprod := hζroot'.prod_one_sub_pow_eq_order
  norm_cast at hprod
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hprod
  have hsplit : (∏ i ∈ Finset.range n, g i) =
      (∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1))) * ∏ i ∈ Finset.range (q - 1), u i := by
    rw [← hpre, ← hpost, mul_comm, ← Finset.prod_range_add, show q + (n - q) = n by omega]
  rw [hden, hsplit]
  rw [show n - 1 = (n - q) + (q - 1) by omega, Finset.prod_range_add,
    ← show (∏ i ∈ Finset.range (q - 1), u i) =
      ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (n - q + i + 1)) from
    Finset.prod_congr rfl fun i _ => by dsimp [u, s]; congr 2; omega] at hprod
  exact_mod_cast hprod

private theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 < r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq
  have hden := cor34_odd_base_denominator_eq_cyclotomic hbound hnq hN
  have hcyclo := cor34_cyclotomic_odd_evaluation n r q hnq hr
  have hvalue :
      ((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    rw [hden, show (N : ℂ) - (n : ℂ) = (n + 2 * r : ℕ) by rw [hN]; push_cast; ring]
    simpa [cor34_halfRoot] using hcyclo
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using hbase

theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · exact cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive
      hp hp0 hNpos hbound hnpos hnq hN hrpos
  · obtain rfl : r = 0 := by omega
    have hN' : N = 2 * n := by simpa using hN
    have hbase := cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq
    have hval : ((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [cor34_odd_base_denominator_at_r_zero hnpos hbound hnq hN', hN']
      push_cast; field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hnpos.ne']; ring
    rw [hval] at hbase
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using hbase

end PottsDiscontinuity.SixVertex
