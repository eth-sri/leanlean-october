module

public import Mathlib

/-!
# Corollary 3.4: cyclotomic determinant calculation

The Vandermonde factor occurring in the cyclotomic calculation is nonzero whenever the
primitive root has order strictly greater than the number of rows.
-/

public section

namespace PottsDiscontinuity.SixVertex

theorem cor34_exp_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (Complex.exp (Real.pi * Complex.I / (m : ℂ))) (2 * m) := by
  convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 2
  push_cast; field_simp

theorem cor34_exp_pow (m e : ℕ) : Complex.exp (Real.pi * Complex.I / (m : ℂ)) ^ e =
    Complex.exp (((Real.pi * (e : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  push_cast
  ring

/-- Pairing the complementary conjugate roots in the even cyclotomic calculation gives the
real product displayed in Corollary 3.4. -/
theorem cor34_cyclotomic_even_real_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range r,
      (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))) =
    2 ^ r * ∏ j ∈ Finset.range r,
      (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  calc
    (∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))) =
      ∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos
          (Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
      rw [← Finset.prod_range_reflect]
    _ = ∏ j ∈ Finset.range r,
        (2 * (1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ)))) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      have hnum : n + 1 + 2 * (r - 1 - j) = n + 2 * r - (2 * j + 1) := by omega
      have harg :
          Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ) =
            Real.pi - Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ) := by
        rw [hnum, Nat.cast_sub (by omega)]
        grind
      rw [harg, Real.cos_pi_sub]
      ring
    _ = 2 ^ r * ∏ j ∈ Finset.range r,
        (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- A conjugate pair of unit-circle factors is the corresponding real cosine factor. -/
theorem cor34_one_sub_exp_pair (θ : ℝ) :
    (1 - Complex.exp ((θ : ℂ) * Complex.I)) *
      (1 - Complex.exp (-(θ : ℂ) * Complex.I)) =
        (2 - 2 * Real.cos θ : ℂ) := by
  have hneg : Complex.exp (-(θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    simpa [sub_eq_add_neg] using (Complex.exp_ofReal_mul_I (-θ))
  rw [Complex.exp_ofReal_mul_I θ, hneg]
  have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    simp
  ring_nf
  rw [Complex.I_sq]
  grind

section
variable (n r : ℕ)
/-- The complementary `2r` shifted roots in either parity case pair into the real product
appearing in Corollary 3.4. -/
theorem cor34_cyclotomic_complement_product (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range (2 * r),
      (1 - Complex.exp
        (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ) : ℝ) : ℂ) * Complex.I))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) : ℂ) := by
  let θ := fun j => Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)
  let f := fun j => 1 - Complex.exp ((θ j : ℂ) * Complex.I)
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  have hrev :=
    (Finset.prod_range_reflect (fun j => f (r + j)) r).symm
  have hpair : ∀ j ∈ Finset.range r,
      f j * f (r + (r - 1 - j)) = (2 - 2 * Real.cos (θ j) : ℂ) := by
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have hnum : n + 1 + 2 * (r + (r - 1 - j)) =
        2 * (n + 2 * r) - (n + 1 + 2 * j) := by omega
    have hangle : θ (r + (r - 1 - j)) = 2 * Real.pi - θ j := by
      dsimp [θ]
      rw [hnum, Nat.cast_sub (by omega)]
      grind
    have hexp : Complex.exp ((θ (r + (r - 1 - j)) : ℂ) * Complex.I) =
        Complex.exp (-(θ j : ℂ) * Complex.I) := by
      rw [hangle, show 2 * Real.pi - θ j = -θ j + 2 * Real.pi by ring]
      convert Complex.exp_mul_I_periodic (-θ j) using 1
      simp
    grind [cor34_one_sub_exp_pair]
  calc
    ∏ j ∈ Finset.range (2 * r), f j =
        (∏ j ∈ Finset.range r, f j) * ∏ j ∈ Finset.range r, f (r + j) := by
      rw [show 2 * r = r + r by omega, Finset.prod_range_add]
    _ = (∏ j ∈ Finset.range r, f j) *
        ∏ j ∈ Finset.range r, f (r + (r - 1 - j)) := by simp_all
    _ = ∏ j ∈ Finset.range r, (f j * f (r + (r - 1 - j))) := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range r, (2 - 2 * Real.cos (θ j) : ℂ) :=
      Finset.prod_congr rfl hpair
    _ = (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) : ℂ) := by
      dsimp [θ]
      exact_mod_cast (cor34_cyclotomic_even_real_product n r hm)

/-- Even-parity cyclotomic evaluation. The shifted powers `η ^ (k + 2i)` encode the
half-integer exponents in the source, with the shift by `2m` fixing a nonnegative exponent. -/
theorem cor34_cyclotomic_even_evaluation (hn : Even n) (hr : 0 < n + 2 * r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let k := 2 * m + 1 - n
    (2 : ℂ) / (∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  let m := n + 2 * r
  let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let k := 2 * m + 1 - n
  let ζ := η ^ 2
  let α := η ^ k
  let f := fun i => 1 - η ^ (k + 2 * i)
  have hηroot : IsPrimitiveRoot η (2 * m) := cor34_exp_primitive (by omega)
  have hζroot : IsPrimitiveRoot ζ m :=
    hηroot.pow (by omega) (by omega)
  have hηmroot : IsPrimitiveRoot (η ^ m) 2 :=
    hηroot.pow (by omega) (by omega)
  have hηm := hηmroot.eq_neg_one_of_two_right
  have hkodd : Odd k := by
    grind
  have hαpow : α ^ m = -1 := by
    calc
      (η ^ k) ^ m = (η ^ m) ^ k := by
        ring
      _ = (-1 : ℂ) ^ k := by simp_all
      _ = -1 := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hkodd
  have hηpow := cor34_exp_pow m
  have htotal : (∏ i ∈ Finset.range m, f i) = 2 := by
    have heval := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod hζroot (α := α) (by omega) hαpow)
    have hrootprod :
        (∏ i ∈ Finset.range m, (1 - ζ ^ i * α)) = 2 := by
      norm_num [Polynomial.eval_prod] at heval ⊢
      grind
    calc
      ∏ i ∈ Finset.range m, f i =
          ∏ i ∈ Finset.range m, (1 - ζ ^ i * α) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = 2 := hrootprod
  have hsplit :
      (∏ i ∈ Finset.range m, f i) =
        (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) := by
    rw [Finset.prod_range_add]
  have hcomp :
      (∏ j ∈ Finset.range (2 * r), f (n + j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    calc
      ∏ j ∈ Finset.range (2 * r), f (n + j) =
          ∏ j ∈ Finset.range (2 * r),
            (1 - Complex.exp
              (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have he : k + 2 * (n + j) = 2 * m + (n + 1 + 2 * j) := by
          omega
        dsimp [f]
        rw [he, pow_add, hηroot.pow_eq_one, one_mul, hηpow]
      _ = _ := by
        simpa [m] using cor34_cyclotomic_complement_product n r (by omega)
  grind
end

/-- Odd-parity cyclotomic evaluation. The skipped index `q - 1` is the factor with exponent
zero; all other prefix factors are the shifted form of the source's `ζ^(j-q)` factors. -/
theorem cor34_cyclotomic_odd_evaluation (n r q : ℕ) (hnq : n + 1 = 2 * q) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let ζ := η ^ 2
    let s := m + 1 - q
    let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
    (m : ℂ) / (∏ i ∈ Finset.range n, g i) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m : ℕ := n + 2 * r
  let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let ζ : ℂ := η ^ 2
  let s : ℕ := m + 1 - q
  let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  have hm : m ≠ 0 := by omega
  have hηroot := cor34_exp_primitive hm
  have hζroot : IsPrimitiveRoot ζ m :=
    hηroot.pow (by omega) (by omega)
  have hηpow := cor34_exp_pow m
  have hqle : q ≤ m := by omega
  let u : ℕ → ℂ := fun i => 1 - ζ ^ (s + i)
  have hprefix : (∏ i ∈ Finset.range (q - 1), g i) =
      ∏ i ∈ Finset.range (q - 1), u i := by
    apply Finset.prod_congr rfl
    grind
  have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_add, hprefix]
    simp [g]
  have hpost : (∏ i ∈ Finset.range (m - q), g (q + i)) =
      ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hexp : s + (q + i) = m + (i + 1) := by omega
    have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
      rw [hexp, pow_add, hζroot.pow_eq_one, one_mul]
    grind
  have hsplit :
      (∏ i ∈ Finset.range m, g i) =
        (∏ i ∈ Finset.range (q - 1), u i) *
          ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := by
    calc
      ∏ i ∈ Finset.range m, g i =
          (∏ i ∈ Finset.range q, g i) * ∏ i ∈ Finset.range (m - q), g (q + i) := by
        have hadd := Finset.prod_range_add g q (m - q)
        simp_all
      _ = _ := by simp_all
  have hcanonical :
      (∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1))) =
        (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show m - 1 = (m - q) + (q - 1) by omega, Finset.prod_range_add]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    grind
  have htotal : (∏ i ∈ Finset.range m, g i) = (m : ℂ) := by
    have hζroot' : IsPrimitiveRoot ζ (m - 1 + 1) := by
      grind
    have hprod := hζroot'.prod_one_sub_pow_eq_order
    have hprod' :
        (∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1))) = (m : ℂ) := by
      norm_cast at hprod
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hprod
      omega
    grind
  have hcomp :
      (∏ j ∈ Finset.range (2 * r), g (n + j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    calc
      ∏ j ∈ Finset.range (2 * r), g (n + j) =
          ∏ j ∈ Finset.range (2 * r),
            (1 - Complex.exp
              (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hexp : s + (n + j) = m + (q + j) := by omega
        have hpow : ζ ^ (s + (n + j)) =
            Complex.exp (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
          rw [hexp, pow_add, hζroot.pow_eq_one, one_mul, ← pow_mul, hηpow]
          have hnum : 2 * (q + j) = n + 1 + 2 * j := by omega
          rw [hnum]
        grind
      _ = _ := by
        simpa [m] using cor34_cyclotomic_complement_product n r (by omega)
  have hDC :
      (∏ i ∈ Finset.range n, g i) * ∏ j ∈ Finset.range (2 * r), g (n + j) = (m : ℂ) := by
    calc
      _ = ∏ i ∈ Finset.range m, g i := by
        symm
        simpa using (Finset.prod_range_add g n (2 * r))
      _ = (m : ℂ) := htotal
  rw [div_eq_iff (left_ne_zero_of_mul (hDC.trans_ne (by exact_mod_cast hm))), ← hcomp]
  exact hDC.symm.trans (mul_comm _ _)

end PottsDiscontinuity.SixVertex
