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

public section

open Finset Complex Filter Topology
open PottsDiscontinuity.PerronFrobenius
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The centered base momenta have total momentum zero, so their phases multiply to one. -/
theorem cor34_base_z_product_eq_one {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N) :
    (∏ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
  rw [BetheAnsatz.prod_z_eq_exp_sum]
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hn
  have hsum := Bethe.sum_eq_zero_of_mem_R_n_sym hp.2.2
  simp_all

theorem cor34_discreteIndex_ne_zero_of_even {n : ℕ} (hn : Even n) (j : Fin n) :
    Bethe.discreteBetheIndex n j ≠ 0 := by
  intro h
  have hnat : 2 * (j.val + 1) = n + 1 := by
    have hreal : 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 := by
      grind [Bethe.discreteBetheIndex]
    exact_mod_cast hreal
  grind

section
variable {N n : ℕ}
theorem cor34_base_momentum_ne_zero_of_even (hn : Even n) (hbound : 2 * n ≤ N) (j : Fin n) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hnpos := Nat.zero_lt_of_lt j.isLt
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (by omega)))
  simp_all [Bethe.discreteBaseSolution, cor34_discreteIndex_ne_zero_of_even]

/-- No even-parity base momentum is a zero root. -/
theorem cor34_base_z_ne_one_of_even (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hn : Even n) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hbound
  exact BetheAnsatz.z_ne_one (hp.1 j)
    (cor34_base_momentum_ne_zero_of_even hn hbound j)

/-- The normalized even Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedRegularEigenvalue_base_limit {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hn : Even n) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((2 : ℂ) / ∏ j : Fin n,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  have hlim := cor34_normalizedRegularEigenvalue_tendsto hp
    (fun j => by simp_all [cor34_base_z_ne_one_of_even])
  have hprod := cor34_base_z_product_eq_one hN hbound
  have hsign : (-1 : ℂ) ^ n = 1 := by
    simp_all
  have hform :
      (∏ j : Fin n,
          BetheAnsatz.z (Bethe.discreteBaseSolution N n j) /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j))) +
        ∏ j : Fin n,
          (-1 : ℂ) /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 : ℂ) / ∏ j : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    simp
    grind
  rw [hp0] at hlim
  grind

end

section
variable {N n q : ℕ}
theorem cor34_odd_base_momentum_ne_zero (hnq : n + 1 = 2 * q)
    (hbound : 2 * n ≤ N) (j : Fin n)
    (hcenter : j ≠ ⟨q - 1, by omega⟩) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hindex : Bethe.discreteBetheIndex n j ≠ 0 := by
    intro h
    have hval : j.val + 1 = q := by
      have hreal : 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 := by
        grind [Bethe.discreteBetheIndex]
      have hnat : 2 * (j.val + 1) = n + 1 := by exact_mod_cast hreal
      omega
    grind
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (by omega)))
  simp_all [Bethe.discreteBaseSolution]

/-- All nonzero-root factors in the odd limiting eigenvalue are regular. -/
theorem cor34_odd_base_z_ne_one (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) (j : Fin n)
    (hj : j ∈ Finset.univ.erase ⟨q - 1, by omega⟩) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hbound
  apply BetheAnsatz.z_ne_one (hp.1 j)
  simp_all [cor34_odd_base_momentum_ne_zero]

/-- The normalized odd Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedZeroEigenvalue_base_limit {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
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
  have hsign : (-1 : ℂ) ^ (n - 1) = 1 := by
    have hnEven : Even (n - 1) := by
      grind
    simp_all
  simp_all
  grind
end

section
variable {N n r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * (n + r))
include hp hp0 hNpos hbound hnpos hn hN
/-- For even `n` and positive `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  let m := n + 2 * r
  let η := cor34_halfRoot m
  let k := 2 * m + 1 - n
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_exp_primitive (by omega)
  have hηne : η ≠ 0 := by
    dsimp [η, cor34_halfRoot]
    simp
  have hperiod : η ^ (2 * (m : ℤ)) = 1 := by
    convert hηroot.zpow_eq_one using 1; norm_cast
  have heta : cor34_halfRoot (N - n) = η := by
    grind
  have hfactor (i : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n i) = η ^ (k + 2 * i.val) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, heta]
    calc
      η ^ (2 * (i.val : ℤ) + 1 - (n : ℤ)) =
          η ^ ((2 * m : ℤ) + (2 * (i.val : ℤ) + 1 - (n : ℤ))) := by
            rw [zpow_add₀ hηne, hperiod, one_mul]
      _ = η ^ ((k + 2 * i.val : ℕ) : ℤ) := by grind
      _ = η ^ (k + 2 * i.val) := by rfl
  have hden :
      (∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))) =
        ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
    let f := fun i => if hi : i < n then
      1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
    calc
      ∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
          ∏ i : Fin n, f i := by
            grind
      _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
      _ = ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
            apply Finset.prod_congr rfl
            grind
  have hcyclo := cor34_cyclotomic_even_evaluation n r hn (by omega)
  have hvalue :
      (2 : ℂ) / ∏ i : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    grind [cor34_halfRoot]
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using (cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn)
end

section
variable {N n q r : ℕ} (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r))
include hbound hnq hN
/-- The base phase at an odd centered index is the shifted power used in the odd
cyclotomic evaluation of `SixVertex/Cor34Cyclotomic.lean`, away from the zero root. -/
theorem cor34_odd_base_phase_shift (i : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      (cor34_halfRoot (n + 2 * r) ^ 2) ^
        ((n + 2 * r + 1 - q) + i.val) := by
  let m := n + 2 * r
  let η := cor34_halfRoot m
  let ζ := η ^ 2
  let s := m + 1 - q
  have hm : N - n = m := by omega
  have hηroot : IsPrimitiveRoot η (2 * m) :=
    cor34_exp_primitive (by omega)
  have hζroot : IsPrimitiveRoot ζ m :=
    hηroot.pow (by omega) (by omega)
  have hζne : ζ ≠ 0 := by
    dsimp [ζ, η, cor34_halfRoot]
    simp
  have hζperiod : ζ ^ (m : ℤ) = 1 := by
    convert hζroot.zpow_eq_one using 1
  have hbase : BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, hm]
    grind
  have hshift : ((s + i.val : ℕ) : ℤ) =
      (m : ℤ) + (i.val : ℤ) + 1 - q := by
    omega
  have hpow : ζ ^ (s + i.val) = η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
    rw [← zpow_natCast, hshift]
    calc
      ζ ^ ((m : ℤ) + (i.val : ℤ) + 1 - q) =
          ζ ^ ((m : ℤ) + ((i.val : ℤ) + 1 - q)) := by ring
      _ = ζ ^ ((i.val : ℤ) + 1 - q) := by
        rw [zpow_add₀ hζne, hζperiod, one_mul]
      _ = η ^ (2 * ((i.val : ℤ) + 1 - q)) :=
        (zpow_mul η 2 ((i.val : ℤ) + 1 - q)).symm
  grind

/-- The odd cyclotomic denominator is exactly the cyclotomic product of
`SixVertex/Cor34Cyclotomic.lean`, with the zero-root factor replaced by one. -/
theorem cor34_odd_base_denominator_eq_cyclotomic  :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  let gFin := fun i => if i = l then 1 else
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)
  have hgFin : ∏ i : Fin n, gFin i =
      ∏ i ∈ Finset.univ.erase l,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
    calc
      ∏ i : Fin n, gFin i = ∏ i ∈ Finset.univ, gFin i := by simp
      _ = (∏ i ∈ Finset.univ.erase l, gFin i) * gFin l := by
        symm
        exact Finset.prod_erase_mul Finset.univ gFin (Finset.mem_univ l)
      _ = ∏ i ∈ Finset.univ.erase l,
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
        simp only [gFin, ↓reduceIte, mul_one]
        apply Finset.prod_congr rfl
        simp_all
  let f := fun i => if hi : i < n then gFin ⟨i, hi⟩ else 1
  have hrange : ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) =
      ∏ i : Fin n, gFin i := by
    have hfrange := Fin.prod_univ_eq_prod_range f n
    have heq : ∀ i ∈ Finset.range n,
        f i = (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
      intro i hi
      by_cases hc : i = q - 1
      · grind
      · have hphase := cor34_odd_base_phase_shift hbound hnq hN ⟨i, (Finset.mem_range.mp hi)⟩
        grind
    calc
      _ = ∏ i ∈ Finset.range n, f i := Finset.prod_congr rfl (fun i hi => (heq i hi).symm)
      _ = ∏ i : Fin n, f i := hfrange.symm
      _ = ∏ i : Fin n, gFin i := by
        grind
  grind
end

section
variable {N n q r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r))
include n q p hp hp0 hNpos hbound hnpos hnq hN
/-- For odd `n` and positive `r`, the normalized zero-root Bethe eigenvalue tends to the
cyclotomic cosine product, hence to the Perron root of the limiting transfer block. -/
theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  have hden := cor34_odd_base_denominator_eq_cyclotomic hbound hnq hN
  have hcyclo := cor34_cyclotomic_odd_evaluation n r q hnq
  have hvalue :
      ((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    have hcast : (N : ℂ) - (n : ℂ) = (n + 2 * r : ℕ) := by
      rw [hN]
      grind
    grind [cor34_halfRoot]
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using (cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq)
end

end PottsDiscontinuity.SixVertex
