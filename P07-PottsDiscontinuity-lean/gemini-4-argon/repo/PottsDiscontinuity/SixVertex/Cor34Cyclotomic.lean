module

public import Mathlib

@[expose] public section

namespace PottsDiscontinuity.SixVertex

theorem cor34_cyclotomic_even_real_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range r,
      (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))) =
    2 ^ r * ∏ j ∈ Finset.range r,
      (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  calc (∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ))))
    _ = ∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
      rw [← Finset.prod_range_reflect]
    _ = ∏ j ∈ Finset.range r,
        (2 * (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ)))) :=
      Finset.prod_congr rfl fun j hj => by
        have hjr : j < r := Finset.mem_range.mp hj
        have harg : Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ) =
            Real.pi - Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ) := by
          rw [show n + 1 + 2 * (r - 1 - j) = n + 2 * r - (2 * j + 1) by omega,
            Nat.cast_sub (by omega)]
          push_cast; field_simp
        rw [harg, Real.cos_pi_sub]; ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem cor34_one_sub_exp_pair (θ : ℝ) :
    (1 - Complex.exp ((θ : ℂ) * Complex.I)) *
      (1 - Complex.exp (-(θ : ℂ) * Complex.I)) =
        (2 - 2 * Real.cos θ : ℂ) := by
  have hneg : Complex.exp (-(θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    simpa [sub_eq_add_neg] using Complex.exp_ofReal_mul_I (-θ)
  rw [Complex.exp_ofReal_mul_I θ, hneg]
  have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  linear_combination htrig

theorem cor34_cyclotomic_complement_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range (2 * r),
      (1 - Complex.exp
        (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / ((n + 2 * r : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n + 2 * r : ℕ) : ℝ))) : ℂ) := by
  let θ : ℕ → ℝ := fun j => Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / ((n + 2 * r : ℕ) : ℝ)
  let f : ℕ → ℂ := fun j => 1 - Complex.exp ((θ j : ℂ) * Complex.I)
  have hmR : ((n + 2 * r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpair : ∀ j ∈ Finset.range r,
      f j * f (r + (r - 1 - j)) = (2 - 2 * Real.cos (θ j) : ℂ) := fun j hj => by
    have hjr : j < r := Finset.mem_range.mp hj
    have hangle : θ (r + (r - 1 - j)) = -θ j + 2 * Real.pi := by
      dsimp [θ]
      rw [show n + 1 + 2 * (r + (r - 1 - j)) = 2 * (n + 2 * r) - (n + 1 + 2 * j) by omega,
        Nat.cast_sub (by omega)]
      push_cast at hmR ⊢; field_simp; ring
    have hexp : Complex.exp ((θ (r + (r - 1 - j)) : ℂ) * Complex.I) =
        Complex.exp (-(θ j : ℂ) * Complex.I) := by
      rw [hangle]; convert Complex.exp_mul_I_periodic (-θ j) using 1; push_cast; ring
    dsimp [f]; rw [hexp]; exact cor34_one_sub_exp_pair (θ j)
  calc ∏ j ∈ Finset.range (2 * r), f j
    _ = (∏ j ∈ Finset.range r, f j) * ∏ j ∈ Finset.range r, f (r + (r - 1 - j)) := by
      rw [show 2 * r = r + r by omega, Finset.prod_range_add,
        ← Finset.prod_range_reflect (fun j => f (r + j)) r]
    _ = ∏ j ∈ Finset.range r, (2 - 2 * Real.cos (θ j) : ℂ) := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl hpair
    _ = _ := by dsimp [θ]; push_cast; exact_mod_cast cor34_cyclotomic_even_real_product n r hm

private theorem cor34_eta_root_and_pow {m : ℕ} (hm : m ≠ 0) :
    let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    IsPrimitiveRoot η (2 * m) ∧ IsPrimitiveRoot (η ^ 2) m ∧
      ∀ e : ℕ, η ^ e = Complex.exp (((Real.pi * (e : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
  intro η
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    rw [show η = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) by
      dsimp [η]; congr 1; field_simp [hmR]]
    convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
    congr 1; norm_num
  refine ⟨hηroot, hηroot.pow (by omega) (by omega), fun e => ?_⟩
  dsimp [η]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp [hmR]

theorem cor34_cyclotomic_even_evaluation (n r : ℕ) (hn : Even n) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let k := 2 * m + 1 - n
    (2 : ℂ) / (∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m : ℕ := n + 2 * r
  let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let k : ℕ := 2 * m + 1 - n
  let f : ℕ → ℂ := fun i => 1 - η ^ (k + 2 * i)
  have hm : m ≠ 0 := by dsimp [m]; omega
  obtain ⟨hηroot, hζroot, hηpow⟩ := cor34_eta_root_and_pow hm
  have hηm : η ^ m = -1 :=
    (hηroot.pow (by omega) (by omega) : IsPrimitiveRoot (η ^ m) 2).eq_neg_one_of_two_right
  have hkodd : Odd k := Nat.Odd.sub_even (by dsimp [m]; omega) ⟨m, by omega⟩ hn
  have hαpow : (η ^ k) ^ m = -1 := by
    rw [← pow_mul, Nat.mul_comm k m, pow_mul, hηm]
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hkodd
  have heval := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod hζroot (α := η ^ k) (a := -1) (by omega) hαpow)
  have hrootprod : (∏ i ∈ Finset.range m, (1 - (η ^ 2) ^ i * η ^ k)) = 2 := by
    norm_num [Polynomial.eval_prod] at heval ⊢; exact heval.symm
  have htotal : (∏ i ∈ Finset.range m, f i) = 2 := by
    rw [← hrootprod]
    exact Finset.prod_congr rfl fun i _ => by dsimp [f]; rw [← pow_mul, ← pow_add, Nat.add_comm]
  have hcomp : (∏ j ∈ Finset.range (2 * r), f (n + j)) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    refine (Finset.prod_congr rfl fun j _ => ?_).trans
      (cor34_cyclotomic_complement_product n r hm)
    dsimp [f]
    rw [show k + 2 * (n + j) = 2 * m + (n + 1 + 2 * j) by dsimp [k, m]; omega,
      pow_add, hηroot.pow_eq_one, one_mul, hηpow]
  have hDne : (∏ i ∈ Finset.range n, f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr <| Ne.symm fun hEq => by
      have hev : Even (k + 2 * i) := even_iff_two_dvd.mpr
        (dvd_trans (⟨m, by omega⟩ : 2 ∣ 2 * m) ((hηroot.pow_eq_one_iff_dvd _).mp hEq))
      obtain ⟨a, ha⟩ := hkodd.add_even (⟨i, by omega⟩ : Even (2 * i))
      obtain ⟨b, hb⟩ := hev
      omega
  change (2 : ℂ) / (∏ i ∈ Finset.range n, f i) = _
  rw [← hcomp, div_eq_iff hDne, mul_comm, ← Finset.prod_range_add]
  exact htotal.symm

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
  let m : ℕ := n + 2 * r
  let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let ζ : ℂ := η ^ 2
  let s : ℕ := m + 1 - q
  let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  let u : ℕ → ℂ := fun i => 1 - ζ ^ (s + i)
  have hm : m ≠ 0 := by dsimp [m]; omega
  obtain ⟨hηroot, hζroot, hηpow⟩ := cor34_eta_root_and_pow hm
  have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_succ]
    simp only [g, ↓reduceIte, mul_one]
    exact Finset.prod_congr rfl fun i hi => ite_eq_right (by have := Finset.mem_range.mp hi; omega)
  have hpost : (∏ i ∈ Finset.range (m - q), g (q + i)) =
      ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) :=
    Finset.prod_congr rfl fun i _ => by
      have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
        rw [show s + (q + i) = m + (i + 1) by dsimp [s]; omega, pow_add, hζroot.pow_eq_one, one_mul]
      simp [g, show q + i ≠ q - 1 by omega, hpow]
  have htotal : (∏ i ∈ Finset.range m, g i) = (m : ℂ) := by
    have hζroot' : IsPrimitiveRoot ζ (m - 1 + 1) := by
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hprod := hζroot'.prod_one_sub_pow_eq_order
    norm_cast at hprod
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hprod
    have hsplit : (∏ i ∈ Finset.range m, g i) =
        (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) * ∏ i ∈ Finset.range (q - 1), u i := by
      rw [← hpre, ← hpost, mul_comm, ← Finset.prod_range_add, show q + (m - q) = m by omega]
    rw [hsplit]
    rw [show m - 1 = (m - q) + (q - 1) by omega, Finset.prod_range_add,
      ← show (∏ i ∈ Finset.range (q - 1), u i) =
        ∏ i ∈ Finset.range (q - 1), (1 - ζ ^ (m - q + i + 1)) from
      Finset.prod_congr rfl fun i _ => by dsimp [u, s]; congr 2; omega] at hprod
    exact_mod_cast hprod
  have hDne : (∏ i ∈ Finset.range n, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => by
      have hin : i < n := Finset.mem_range.mp hi
      by_cases hskip : i = q - 1
      · simp [g, hskip]
      · simp only [g, hskip, ↓reduceIte]
        refine sub_ne_zero.mpr (Ne.symm fun hEq => ?_)
        by_cases hilow : i < q - 1
        · exact hζroot.pow_ne_one_of_pos_of_lt (by omega) (by dsimp [s]; omega) hEq
        · rw [show s + i = m + (i - q + 1) by dsimp [s]; omega,
            pow_add, hζroot.pow_eq_one, one_mul] at hEq
          exact hζroot.pow_ne_one_of_pos_of_lt (by omega) (by dsimp [m]; omega) hEq
  have hcomp : (∏ j ∈ Finset.range (2 * r), g (n + j)) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    refine (Finset.prod_congr rfl fun j _ => ?_).trans
      (cor34_cyclotomic_complement_product n r hm)
    have hpow : ζ ^ (s + (n + j)) =
        Complex.exp (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
      dsimp [ζ]
      rw [show s + (n + j) = m + (q + j) by dsimp [s]; omega,
        pow_add, hζroot.pow_eq_one, one_mul, ← pow_mul, hηpow,
        show 2 * (q + j) = n + 1 + 2 * j by omega]
    simp only [g, show n + j ≠ q - 1 by omega, ↓reduceIte, hpow]
    rfl
  change (m : ℂ) / (∏ i ∈ Finset.range n, g i) = _
  rw [← hcomp, div_eq_iff hDne, mul_comm, ← Finset.prod_range_add]
  exact htotal.symm

end PottsDiscontinuity.SixVertex
