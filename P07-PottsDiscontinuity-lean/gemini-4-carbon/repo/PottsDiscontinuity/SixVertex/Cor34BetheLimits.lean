module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Conventions
public import PottsDiscontinuity.BetheAnsatz.Scattering
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
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

private theorem cor34_halfRoot_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (cor34_halfRoot m) (2 * m) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [show cor34_halfRoot m = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) by
    dsimp [cor34_halfRoot]; congr 1; field_simp [hmR]]
  convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1; congr 1; norm_num

private theorem cor34_normalizedRegularEigenvalue_base_limit {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hn : Even n) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((2 : ℂ) / ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  have hmem := Bethe.discreteBaseSolution_mem_S_n hN hbound
  have hne1 (j : Fin n) : BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
    refine BetheAnsatz.z_ne_one (hmem.1 j) ?_
    have hpos : 0 < N - n := by have := j.isLt; omega
    unfold Bethe.discreteBaseSolution
    refine div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) fun h => ?_) (by exact_mod_cast hpos.ne')
    have hnat : 2 * (j.val + 1) = n + 1 := by exact_mod_cast (show 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 by dsimp [Bethe.discreteBetheIndex] at h; linarith)
    obtain ⟨k, hk⟩ := hn; omega
  have hlim := cor34_normalizedRegularEigenvalue_tendsto hp fun j => by simpa [hp0] using hne1 j
  have hprod : (∏ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
    rw [BetheAnsatz.prod_z_eq_exp_sum, Bethe.sum_eq_zero_of_mem_R_n_sym hmem.2.2]; simp
  obtain ⟨k, hk⟩ := hn
  have hsign : (-1 : ℂ) ^ n = 1 := by rw [hk, pow_add, ← mul_pow]; norm_num
  rw [hp0] at hlim
  convert hlim using 2
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsign, hprod]; ring

/-- For even `n` and nonnegative `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
  let m := n + 2 * r
  let η := cor34_halfRoot m
  let k := 2 * m + 1 - n
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_halfRoot_primitive (by dsimp [m]; omega)
  have hηne : η ≠ 0 := Complex.exp_ne_zero _
  have hperiod : η ^ (2 * (m : ℤ)) = 1 := by convert hηroot.zpow_eq_one using 1; norm_cast
  have hden : (∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))) =
      ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
    let f (i : ℕ) : ℂ := if hi : i < n then 1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
    rw [show (∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))) = ∏ i : Fin n, f i from
      Finset.prod_congr rfl fun i _ => by simp [f], Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [f, dite_eq_left hi']
    congr 1
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) ⟨i, hi'⟩, show N - n = m by dsimp [m]; omega]
    change η ^ (2 * (i : ℤ) + 1 - (n : ℤ)) = η ^ (k + 2 * i)
    rw [← zpow_natCast, show ((k + 2 * i : ℕ) : ℤ) = 2 * (m : ℤ) + (2 * (i : ℤ) + 1 - (n : ℤ)) by dsimp [k, m]; omega,
      zpow_add₀ hηne, hperiod, one_mul]
  rw [pfRoot_infinityBlock_value hnpos hN]
  by_cases hrpos : 0 < r
  · have hcyclo := cor34_cyclotomic_even_evaluation n r hn hrpos
    have hval : (2 : ℂ) / ∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r, ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
      rw [hden]; simpa [m, η, k, cor34_halfRoot] using hcyclo
    simpa [hval] using hbase
  · obtain rfl : r = 0 := by omega
    have hm_eq : m = n := by dsimp [m]
    let ζ := η ^ 2; let α := η ^ (n + 1)
    have hζroot : IsPrimitiveRoot ζ n := by rw [← hm_eq]; exact hηroot.pow (by omega) (by omega)
    have hηn : η ^ n = -1 := by
      have hr2 : IsPrimitiveRoot (η ^ m) 2 := hηroot.pow (by omega) (by omega)
      simpa [hm_eq] using hr2.eq_neg_one_of_two_right
    obtain ⟨nh, hnh⟩ := hn
    have hαpow : α ^ n = -1 := by
      dsimp [α]; rw [← pow_mul, Nat.mul_comm, pow_mul, hηn]
      exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 ⟨nh, by omega⟩
    have heval := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) (by omega) hαpow)
    have hprod2 : (∏ x ∈ Finset.range n, (1 - ζ ^ x * α)) = 2 := by
      norm_num [Polynomial.eval_prod] at heval ⊢; exact heval.symm
    have hden2 : (∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))) = 2 := by
      rw [← hprod2]; refine Finset.prod_congr rfl fun i _ => ?_
      dsimp [ζ, α, k, m]; rw [show 2 * n + 1 - n + 2 * i = (n + 1) + 2 * i by omega, pow_add, pow_mul]; ring
    rw [hden, hden2, div_self two_ne_zero] at hbase
    simpa using hbase

private theorem cor34_normalizedZeroEigenvalue_base_limit {N n q : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) :
    Tendsto (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) ⟨q - 1, by omega⟩) (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) / ∏ j ∈ Finset.univ.erase ⟨q - 1, by omega⟩,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hmem := Bethe.discreteBaseSolution_mem_S_n hN hbound
  have hne1 (j : Fin n) (hj : j ∈ Finset.univ.erase l) : BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
    refine BetheAnsatz.z_ne_one (hmem.1 j) ?_
    have hpos : 0 < N - n := by omega
    unfold Bethe.discreteBaseSolution
    refine div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) fun h => ?_) (by exact_mod_cast hpos.ne')
    have hnat : 2 * (j.val + 1) = n + 1 := by exact_mod_cast (show 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 by dsimp [Bethe.discreteBetheIndex] at h; linarith)
    exact (Finset.mem_erase.mp hj).1 (Fin.ext (show j.val = q - 1 by omega))
  have hlim := cor34_normalizedZeroEigenvalue_tendsto (N := N) hp l fun j hj => by simpa [hp0] using hne1 j hj
  have hsign : (-1 : ℂ) ^ (n - 1) = 1 := by rw [show n - 1 = (q - 1) + (q - 1) by omega, pow_add, ← mul_pow]; norm_num
  rw [hp0] at hlim
  convert hlim using 2
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin, hsign]; ring

private theorem cor34_odd_base_denominator_eq_cyclotomic {N n q r : ℕ}
    (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else 1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
  let m := n + 2 * r; let η := cor34_halfRoot m; let ζ := η ^ 2; let l : Fin n := ⟨q - 1, by omega⟩
  have hηroot := cor34_halfRoot_primitive (m := m) (by dsimp [m]; omega)
  have hζroot : IsPrimitiveRoot ζ m := hηroot.pow (by dsimp [m]; omega) (by omega)
  have hζne : ζ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hζper : ζ ^ (m : ℤ) = 1 := by convert hζroot.zpow_eq_one using 1
  have hphase (i : Fin n) : BetheAnsatz.z (Bethe.discreteBaseSolution N n i) = ζ ^ (m + 1 - q + i.val) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, show N - n = m by dsimp [m]; omega,
      show 2 * (i.val : ℤ) + 1 - (n : ℤ) = 2 * ((i.val : ℤ) + 1 - q) by omega]
    change η ^ (2 * ((i.val : ℤ) + 1 - q)) = ζ ^ (m + 1 - q + i.val)
    rw [← zpow_natCast, show ((m + 1 - q + i.val : ℕ) : ℤ) = (m : ℤ) + ((i.val : ℤ) + 1 - q) by dsimp [m]; omega,
      zpow_add₀ hζne, hζper, one_mul, show ζ = η ^ (2 : ℤ) from rfl, ← zpow_mul]
  let gFin (i : Fin n) : ℂ := if i = l then 1 else 1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)
  have hgFin : ∏ i : Fin n, gFin i = ∏ j ∈ Finset.univ.erase l, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    rw [← Finset.prod_erase_mul _ gFin (Finset.mem_univ l)]
    simp only [gFin, ↓reduceIte, mul_one]
    exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_erase.mp hi).1]
  let f (i : ℕ) : ℂ := if hi : i < n then gFin ⟨i, hi⟩ else 1
  rw [← hgFin, show (∏ i : Fin n, gFin i) = ∏ i : Fin n, f i from Finset.prod_congr rfl fun i _ => by simp [f],
    Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  by_cases hc : i = q - 1
  · have hfi : (⟨i, hi'⟩ : Fin n) = l := Fin.ext hc
    rw [ite_eq_left hc]; simp [f, gFin, hi', hfi]
  · have hfi : (⟨i, hi'⟩ : Fin n) ≠ l := fun h => hc (congrArg Fin.val h)
    rw [ite_eq_right hc]; simp [f, gFin, hi', hfi, hphase ⟨i, hi'⟩, ζ, η, m]

/-- For odd `n` and nonnegative `r`, the normalized zero-root Bethe eigenvalue tends to the
cosine product, hence to the Perron root of the limiting transfer block. -/
theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq
  have hden := cor34_odd_base_denominator_eq_cyclotomic hbound hnq hN
  rw [pfRoot_infinityBlock_value hnpos hN]
  by_cases hrpos : 0 < r
  · have hval : ((N : ℂ) - (n : ℂ)) / ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r, ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
      rw [hden, show (N : ℂ) - (n : ℂ) = (n + 2 * r : ℕ) by rw [hN]; push_cast; ring]
      simpa [cor34_halfRoot] using cor34_cyclotomic_odd_evaluation n r q hnq hrpos
    simpa [hval] using hbase
  · obtain rfl : r = 0 := by omega
    let ζ := cor34_halfRoot n ^ 2
    have hζroot : IsPrimitiveRoot ζ n := (cor34_halfRoot_primitive (by omega)).pow (by omega) (by omega)
    let g (i : ℕ) : ℂ := if i = q - 1 then 1 else 1 - ζ ^ (n + 1 - q + i)
    have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (n + 1 - q + i)) := by
      conv_lhs => rw [show q = (q - 1) + 1 by omega, Finset.prod_range_add]
      have hp1 : (∏ i ∈ Finset.range (q - 1), g i) = ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (n + 1 - q + i)) :=
        Finset.prod_congr rfl fun i hi => by
          have hne : i ≠ q - 1 := by have := Finset.mem_range.mp hi; omega
          simp [g, hne]
      rw [hp1]; simp [g]
    have hpost : (∏ i ∈ Finset.range (n - q), g (q + i)) = ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) :=
      Finset.prod_congr rfl fun i hi => by
        have hne : q + i ≠ q - 1 := by omega
        have hpow : ζ ^ (n + 1 - q + (q + i)) = ζ ^ (i + 1) := by
          rw [show n + 1 - q + (q + i) = n + (i + 1) by omega, pow_add, hζroot.pow_eq_one, one_mul]
        simp [g, hne, hpow]
    have hsplit : (∏ i ∈ Finset.range n, g i) = ∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1)) := by
      have hadd := Finset.prod_range_add g q (n - q)
      rw [show q + (n - q) = n by omega] at hadd
      rw [hadd, hpre, hpost, mul_comm]
      have hcan := Finset.prod_range_add (fun i => 1 - ζ ^ (i + 1)) (n - q) (q - 1)
      rw [show n - q + (q - 1) = n - 1 by omega] at hcan
      rw [hcan]; exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun i _ => by congr 2; omega)
    have hζroot' : IsPrimitiveRoot ζ (n - 1 + 1) := by rwa [Nat.sub_add_cancel (by omega)]
    have hord : (∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1))) = (n : ℂ) := by
      have hp := hζroot'.prod_one_sub_pow_eq_order; norm_cast at hp; rwa [Nat.sub_add_cancel (by omega)] at hp
    have hden_n : ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = (n : ℂ) := by
      simpa [g, ζ] using hden.trans (hsplit.trans hord)
    have hval : ((N : ℂ) - (n : ℂ)) / ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [hden_n, show N = 2 * n by omega]; push_cast
      field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hnpos.ne']; norm_num
    rw [hval] at hbase; simpa using hbase

end PottsDiscontinuity.SixVertex
