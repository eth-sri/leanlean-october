module

public import Mathlib

/-!
# Corollary 3.4: cyclotomic determinant calculation

The Vandermonde factor occurring in the cyclotomic calculation is nonzero whenever the
primitive root has order strictly greater than the number of rows.
-/

@[expose] public section

namespace PottsDiscontinuity.SixVertex

private theorem cor34_cyclotomic_complement_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range (2 * r),
      (1 - Complex.exp
        (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ) : ℝ) : ℂ) * Complex.I))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) : ℂ) := by
  let θ (j : ℕ) : ℝ := Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)
  let f (j : ℕ) : ℂ := 1 - Complex.exp ((θ j : ℂ) * Complex.I)
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpair (j : ℕ) (hj : j ∈ Finset.range r) : f j * f (r + (r - 1 - j)) = (2 - 2 * Real.cos (θ j) : ℂ) := by
    have hjr := Finset.mem_range.mp hj
    have hang : θ (r + (r - 1 - j)) = -θ j + 2 * Real.pi := by
      dsimp [θ]; rw [show n + 1 + 2 * (r + (r - 1 - j)) = 2 * (n + 2 * r) - (n + 1 + 2 * j) by omega,
        Nat.cast_sub (by omega)]; push_cast; field_simp; ring
    have hexp : Complex.exp ((θ (r + (r - 1 - j)) : ℂ) * Complex.I) = Complex.exp (-(θ j : ℂ) * Complex.I) := by
      rw [hang]; convert Complex.exp_mul_I_periodic (-θ j) using 1; push_cast; ring
    dsimp [f]; rw [hexp, Complex.exp_ofReal_mul_I, show -(θ j : ℂ) * Complex.I = ((-θ j : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    have htrig : (Real.cos (θ j) : ℂ) ^ 2 + (Real.sin (θ j) : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq (θ j)
    rw [Complex.ofReal_neg]; ring_nf; rw [Complex.I_sq]; linear_combination htrig
  rw [show 2 * r = r + r by omega, Finset.prod_range_add, ← Finset.prod_range_reflect (fun j => f (r + j)) r,
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl hpair]
  have hreal : (∏ j ∈ Finset.range r, (2 - 2 * Real.cos (θ j))) =
      2 ^ r * ∏ j ∈ Finset.range r, (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
    have h2r : (2 : ℝ) ^ r = ∏ _j ∈ Finset.range r, (2 : ℝ) := by simp
    rw [← Finset.prod_range_reflect, h2r, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjr := Finset.mem_range.mp hj
    have harg : θ (r - 1 - j) = Real.pi - Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ) := by
      dsimp [θ]; rw [show n + 1 + 2 * (r - 1 - j) = n + 2 * r - (2 * j + 1) by omega, Nat.cast_sub (by omega)]
      push_cast; field_simp
    rw [harg, Real.cos_pi_sub]; ring
  exact_mod_cast hreal

private theorem cor34_eta_prim_and_pow {m : ℕ} (hm : m ≠ 0) :
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    IsPrimitiveRoot η (2 * m) ∧ ∀ e : ℕ, η ^ e = Complex.exp (((Real.pi * (e : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_, fun e => ?_⟩
  · rw [show Complex.exp (Real.pi * Complex.I / (m : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) by
      congr 1; field_simp [hmR]]
    convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1; congr 1; norm_num
  · rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp [hmR]

/-- Even-parity cyclotomic evaluation. The shifted powers `η ^ (k + 2i)` encode the
half-integer exponents in the source, with the shift by `2m` fixing a nonnegative exponent. -/
theorem cor34_cyclotomic_even_evaluation (n r : ℕ) (hn : Even n) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let k := 2 * m + 1 - n
    (2 : ℂ) / (∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m := n + 2 * r; let η := Complex.exp (Real.pi * Complex.I / (m : ℂ)); let k := 2 * m + 1 - n
  let f (i : ℕ) : ℂ := 1 - η ^ (k + 2 * i)
  obtain ⟨hηroot, hηpow⟩ := cor34_eta_prim_and_pow (m := m) (by dsimp [m]; omega)
  have hζroot : IsPrimitiveRoot (η ^ 2) m := hηroot.pow (by dsimp [m]; omega) (by omega)
  have hηm : η ^ m = -1 := (hηroot.pow (by dsimp [m]; omega) (by omega) : IsPrimitiveRoot (η ^ m) 2).eq_neg_one_of_two_right
  have hkodd : Odd k := Nat.Odd.sub_even (by dsimp [m]; omega) ⟨m, by omega⟩ hn
  have hαpow : (η ^ k) ^ m = -1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hηm]
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hkodd
  have heval := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod hζroot (α := η ^ k) (a := -1) (by dsimp [m]; omega) hαpow)
  have htot : (∏ i ∈ Finset.range m, f i) = 2 := by
    have hr2 : (∏ i ∈ Finset.range m, (1 - (η ^ 2) ^ i * η ^ k)) = 2 := by norm_num [Polynomial.eval_prod] at heval ⊢; exact heval.symm
    rw [← hr2]; exact Finset.prod_congr rfl fun i _ => by dsimp [f]; rw [← pow_mul, ← pow_add, Nat.add_comm]
  have hDne : (∏ i ∈ Finset.range n, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr <| Ne.symm fun hEq =>
    Nat.not_even_iff_odd.mpr (hkodd.add_even ⟨i, by omega⟩)
      (even_iff_two_dvd.mpr (dvd_trans ⟨m, by omega⟩ ((hηroot.pow_eq_one_iff_dvd _).mp hEq)))
  have hDC : (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) = 2 :=
    (Finset.prod_range_add f n (2 * r)).symm.trans htot
  change (2 : ℂ) / ∏ i ∈ Finset.range n, f i = _
  conv_lhs => arg 1; rw [← hDC]
  rw [mul_div_cancel_left₀ _ hDne]
  have hmcast : ((m : ℕ) : ℝ) = (n : ℝ) + 2 * (r : ℝ) := by dsimp [m]; push_cast; ring
  have hcp := cor34_cyclotomic_complement_product n r (by omega)
  rw [← hmcast] at hcp
  refine (Finset.prod_congr rfl fun j _ => ?_).trans hcp
  dsimp [f]; rw [show k + 2 * (n + j) = 2 * m + (n + 1 + 2 * j) by dsimp [k, m]; omega,
    pow_add, hηroot.pow_eq_one, one_mul, hηpow]

/-- Odd-parity cyclotomic evaluation. The skipped index `q - 1` is the factor with exponent
zero; all other prefix factors are the shifted form of the source's `ζ^(j-q)` factors. -/
theorem cor34_cyclotomic_odd_evaluation (n r q : ℕ) (hnq : n + 1 = 2 * q) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let ζ := η ^ 2
    let s := m + 1 - q
    let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
    (m : ℂ) / (∏ i ∈ Finset.range n, g i) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m := n + 2 * r; let η := Complex.exp (Real.pi * Complex.I / (m : ℂ)); let ζ := η ^ 2; let s := m + 1 - q
  let g (i : ℕ) : ℂ := if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  obtain ⟨hηroot, hηpow⟩ := cor34_eta_prim_and_pow (m := m) (by dsimp [m]; omega)
  have hζroot : IsPrimitiveRoot ζ m := hηroot.pow (by dsimp [m]; omega) (by omega)
  have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (s + i)) := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_add]
    have hp1 : (∏ i ∈ Finset.range (q - 1), g i) = ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (s + i)) :=
      Finset.prod_congr rfl fun i hi => by
        have hne : i ≠ q - 1 := by have := Finset.mem_range.mp hi; omega
        simp [g, hne]
    rw [hp1]; simp [g]
  have hpost : (∏ i ∈ Finset.range (m - q), g (q + i)) = ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) :=
    Finset.prod_congr rfl fun i _ => by
      have hne : q + i ≠ q - 1 := by omega
      have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
        rw [show s + (q + i) = m + (i + 1) by dsimp [s, m]; omega, pow_add, hζroot.pow_eq_one, one_mul]
      simp [g, hne, hpow]
  have htot : (∏ i ∈ Finset.range m, g i) = (m : ℂ) := by
    have hadd := Finset.prod_range_add g q (m - q)
    rw [show q + (m - q) = m by dsimp [m]; omega] at hadd
    have hcan := Finset.prod_range_add (fun i => 1 - ζ ^ (i + 1)) (m - q) (q - 1)
    rw [show m - q + (q - 1) = m - 1 by dsimp [m]; omega] at hcan
    have hζ' : IsPrimitiveRoot ζ (m - 1 + 1) := by rwa [Nat.sub_add_cancel (by dsimp [m]; omega)]
    have hord := hζ'.prod_one_sub_pow_eq_order; norm_cast at hord; rw [Nat.sub_add_cancel (by dsimp [m]; omega)] at hord
    rw [hadd, hpre, hpost, mul_comm, ← hord, hcan]
    exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun i _ => by dsimp [s]; congr 2; omega)
  have hDne : (∏ i ∈ Finset.range n, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => by
    have hin := Finset.mem_range.mp hi
    by_cases hsk : i = q - 1
    · simp [g, hsk]
    · simp only [g, hsk, ↓reduceIte]; refine sub_ne_zero.mpr (Ne.symm fun hEq => ?_)
      by_cases hlo : i < q - 1
      · exact hζroot.pow_ne_one_of_pos_of_lt (by dsimp [s, m]; omega) (by dsimp [s, m]; omega) hEq
      · rw [show s + i = m + (i - q + 1) by dsimp [s, m]; omega, pow_add, hζroot.pow_eq_one, one_mul] at hEq
        exact hζroot.pow_ne_one_of_pos_of_lt (by omega) (by dsimp [m]; omega) hEq
  have hDC : (∏ i ∈ Finset.range n, g i) * ∏ j ∈ Finset.range (2 * r), g (n + j) = (m : ℂ) :=
    (Finset.prod_range_add g n (2 * r)).symm.trans htot
  change (m : ℂ) / ∏ i ∈ Finset.range n, g i = _
  conv_lhs => arg 1; rw [← hDC]
  rw [mul_div_cancel_left₀ _ hDne]
  have hmcast : ((m : ℕ) : ℝ) = (n : ℝ) + 2 * (r : ℝ) := by dsimp [m]; push_cast; ring
  have hcp := cor34_cyclotomic_complement_product n r (by omega)
  rw [← hmcast] at hcp
  refine (Finset.prod_congr rfl fun j _ => ?_).trans hcp
  have hsk : n + j ≠ q - 1 := by omega
  have hpow : ζ ^ (s + (n + j)) = Complex.exp (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
    dsimp [ζ]; rw [show s + (n + j) = m + (q + j) by dsimp [s, m]; omega, pow_add, hζroot.pow_eq_one, one_mul,
      ← pow_mul, hηpow, show 2 * (q + j) = n + 1 + 2 * j by omega]
  simp only [g, hsk, ↓reduceIte, hpow]

end PottsDiscontinuity.SixVertex
