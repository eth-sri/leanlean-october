module

public import Mathlib

/-!
# Corollary 3.4: cyclotomic determinant calculation

The Vandermonde factor occurring in the cyclotomic calculation is nonzero whenever the
primitive root has order strictly greater than the number of rows.
-/

@[expose] public section

namespace PottsDiscontinuity.SixVertex

/-- Pairing the complementary conjugate roots in the even cyclotomic calculation gives the
real product displayed in Corollary 3.4. -/
theorem cor34_cyclotomic_even_real_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
     ∏ j ∈ Finset.range r,
      (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))  =
    2 ^ r * ∏ j ∈ Finset.range r,
      (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  calc
     ∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos (Real.pi *  (n + 1 + 2 * j : ℕ)  / (n + 2 * r )))  =
      ∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos
          (Real.pi *  (n + 1 + 2 * (r - 1 - j) : ℕ)  / (n + 2 * r ))) := by
      rw [← Finset.prod_range_reflect]
    _ = ∏ j ∈ Finset.range r,
         2 * (1 + Real.cos
          (Real.pi *  (2 * j + 1 : ℕ)  / (n + 2 * r )))  := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjr  := Finset.mem_range.mp hj
      have hnum : n + 1 + 2 * (r - 1 - j) = n + 2 * r - (2 * j + 1) := by omega
      have harg :
          Real.pi *  (n + 1 + 2 * (r - 1 - j) : ℕ)  / (n + 2 * r ) =
            Real.pi - Real.pi *  (2 * j + 1 : ℕ)  / (n + 2 * r ) := by
        rw [hnum]
        
        rw [Nat.cast_sub (by omega)]
        push_cast
        field_simp
      rw [harg, Real.cos_pi_sub]
      ring
    _ = 2 ^ r * ∏ j ∈ Finset.range r,
        (1 + Real.cos (Real.pi *  (2 * j + 1 : ℕ)  / (n + 2 * r ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- A conjugate pair of unit-circle factors is the corresponding real cosine factor. -/
theorem cor34_one_sub_exp_pair (θ : ℝ) :
    (1 - Complex.exp ((θ : ℂ) * Complex.I)) *
      (1 - Complex.exp (-(θ : ℂ) * Complex.I)) =
        (2 - 2 * Real.cos θ : ℂ) := by
  have hneg : Complex.exp (- θ  * Complex.I) =
       Real.cos θ  -  Real.sin θ  * Complex.I := by
    simpa [sub_eq_add_neg] using  Complex.exp_ofReal_mul_I (-θ) 
  rw [Complex.exp_ofReal_mul_I θ, hneg]
  
  have htrig :  Real.cos θ  ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast  by
                      nlinarith [Real.sin_sq_add_cos_sq θ] 
  ring_nf
  rw [Complex.I_sq]
  
  linear_combination htrig

/-- The complementary `2r` shifted roots in either parity case pair into the real product
appearing in Corollary 3.4. -/
theorem cor34_cyclotomic_complement_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
     ∏ j ∈ Finset.range (2 * r),
      (1 - Complex.exp
        (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ) : ℝ) : ℂ) * Complex.I))  =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ( 1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))  : ℂ) := by
  let θ  := fun j => Real.pi *  (n + 1 + 2 * j : ℕ)  / (n + 2 * r )
  let f  := fun j => 1 - Complex.exp ( θ j  * Complex.I)
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  
  
  calc
    ∏ j ∈ Finset.range (2 * r), f j =
        (∏ j ∈ Finset.range r, f j) * ∏ j ∈ Finset.range r, f (r + j) := by
      rw [show 2 * r = r + r by omega, Finset.prod_range_add]
    _ = (∏ j ∈ Finset.range r, f j) *
        ∏ j ∈ Finset.range r, f (r + (r - 1 - j)) := by rw [ (Finset.prod_range_reflect (fun j => f (r + j)) r).symm ]
    _ = ∏ j ∈ Finset.range r,  f j * f (r + (r - 1 - j))  := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range r, (2 - 2 * Real.cos (θ j) : ℂ) :=
      Finset.prod_congr rfl (by
                               intro j hj
                               have hjr  := Finset.mem_range.mp hj
                               have hnum : n + 1 + 2 * (r + (r - 1 - j)) =
                                   2 * (n + 2 * r) - (n + 1 + 2 * j) := by omega
                               
                               have hangle : θ (r + (r - 1 - j)) = 2 * Real.pi - θ j := by
                                 dsimp [θ]
                                 rw [hnum, Nat.cast_sub (by omega)]
                                 push_cast
                                 field_simp
                               have hexp : Complex.exp ((θ (r + (r - 1 - j)) : ℂ) * Complex.I) =
                                   Complex.exp (-(θ j : ℂ) * Complex.I) := by
                                 rw [hangle]
                                 convert Complex.exp_mul_I_periodic (-θ j) using 1
                                 push_cast
                                 ring
                               dsimp [f]
                               rw [hexp]
                               exact_mod_cast cor34_one_sub_exp_pair (θ j))
    _ =  2 ^ r  * ∏ j ∈ Finset.range r,
        ( 1 + Real.cos
          (Real.pi *  (2 * j + 1 : ℕ)  / (n + 2 * r ))  : ℂ) := by
      
      dsimp [θ]
      exact_mod_cast  cor34_cyclotomic_even_real_product n r hm 

/-- Even-parity cyclotomic evaluation. The shifted powers `η ^ (k + 2i)` encode the
half-integer exponents in the source, with the shift by `2m` fixing a nonnegative exponent. -/
theorem cor34_cyclotomic_even_evaluation (n r : ℕ) (hn : Even n) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let k := 2 * m + 1 - n
    (2 : ℂ) /  ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))  =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ( 1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))  : ℂ) := by
  
  let m  := n + 2 * r
  let η  := Complex.exp (Real.pi * Complex.I /  m )
  let k  := 2 * m + 1 - n
  let ζ  := η ^ 2
  let α  := η ^ k
  let f  := fun i => 1 - η ^ (k + 2 * i)
  
  have hmR :  m  ≠ 0 := by simp_all <;> omega
  
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * m )) := by
      grind
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
    
    norm_num
  have hζroot : IsPrimitiveRoot ζ m := by
    
    exact hηroot.pow (by omega) (by omega)
  have hηmroot : IsPrimitiveRoot (η ^ m) 2 := hηroot.pow (by omega) (by omega)
  have hηm  := hηmroot.eq_neg_one_of_two_right
  
  
  have hηpow (e : ℕ) :
      η ^ e = Complex.exp ( (Real.pi *  e  /  m  : ℝ)  * Complex.I) := by
    
    rw [← Complex.exp_nat_mul]
    
    push_cast
    field_simp 
  have htotal :  ∏ i ∈ Finset.range m, f i  = 2 := by
    have hp := X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) (by omega) (by
                                                                           
                                                                           calc
                                                                             (η ^ k) ^ m = (η ^ m) ^ k := by
                                                                               ring
                                                                             _ = (-1 ) ^ k := by rw [hηm]
                                                                             _ = -1 := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 (by
                                                                                                                                           grind))
    have heval := congrArg (Polynomial.eval  1 ) hp
    
    calc
      ∏ i ∈ Finset.range m, f i =
          ∏ i ∈ Finset.range m, (1 - ζ ^ i * α) := by
        apply Finset.prod_congr rfl
        intro i hi
        
        rw [← pow_mul, ← pow_add, Nat.add_comm]
      _ = 2 :=  by
                  norm_num [Polynomial.eval_prod] at heval ⊢
                  exact heval.symm 
  have hsplit :
       ∏ i ∈ Finset.range m, f i  =
        (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) := by
    
    rw [Finset.prod_range_add]
  
  have hDne :  ∏ i ∈ Finset.range n, f i  ≠ 0 := by
    grind
  have hDC :
      (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) = 2 := by
    grind
  calc
     2  /  ∏ i ∈ Finset.range n, f i  =
        ((∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j)) /
           ∏ i ∈ Finset.range n, f i  := by rw [hDC]
    _ = ∏ j ∈ Finset.range (2 * r), f (n + j) := by field_simp 
    _ = _ :=  by
                calc
                  ∏ j ∈ Finset.range (2 * r), f (n + j) =
                      ∏ j ∈ Finset.range (2 * r),
                        (1 - Complex.exp
                          ( (Real.pi *  (n + 1 + 2 * j : ℕ)  /  m  : ℝ)  * Complex.I)) := by
                    apply Finset.prod_congr rfl
                    intro j hj
                    have he : k + 2 * (n + j) = 2 * m + (n + 1 + 2 * j) := by
                      
                      omega
                    dsimp [f]
                    rw [he, pow_add, hηroot.pow_eq_one, one_mul, hηpow]
                  _ = _ := by
                    grind [cor34_cyclotomic_complement_product] 

/-- Odd-parity cyclotomic evaluation. The skipped index `q - 1` is the factor with exponent
zero; all other prefix factors are the shifted form of the source's `ζ^(j-q)` factors. -/
theorem cor34_cyclotomic_odd_evaluation (n r q : ℕ) (hnq : n + 1 = 2 * q) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let ζ := η ^ 2
    let s := m + 1 - q
    let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
    (m : ℂ) /  ∏ i ∈ Finset.range n, g i  =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ( 1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))  : ℂ) := by
  dsimp
  let m  := n + 2 * r
  let η  := Complex.exp (Real.pi * Complex.I /  m )
  let ζ  := η ^ 2
  let s  := m + 1 - q
  let g  := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  have hm : m ≠ 0 := by  omega
  
  
  have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * m )) := by
    grind
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
    
    norm_num
  have hζroot : IsPrimitiveRoot ζ m := by
    
    exact hηroot.pow (by omega) (by omega)
  have hηpow (e : ℕ) :
      η ^ e = Complex.exp ( (Real.pi *  e  /  m  : ℝ)  * Complex.I) := by
    
    rw [← Complex.exp_nat_mul]
    
    push_cast
    field_simp 
  have hqpos : 0 < q := by omega
  have hqle : q ≤ m := by  omega
  let u  := fun i => 1 - ζ ^ (s + i)
  have hprefix :  ∏ i ∈ Finset.range (q - 1), g i  =
      ∏ i ∈ Finset.range (q - 1), u i := by
    apply Finset.prod_congr rfl
    all_goals grind
  have hpre :  ∏ i ∈ Finset.range q, g i  = ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q =  q - 1  + 1 by omega, Finset.prod_range_add]
    rw [hprefix]
    simp [g]
  have hpost :  ∏ i ∈ Finset.range (m - q), g (q + i)  =
      ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hskip : q + i ≠ q - 1 := by omega
    have hexp : s + (q + i) = m + (i + 1) := by  omega
    have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
      rw [hexp, pow_add, hζroot.pow_eq_one, one_mul]
    simp [g, hskip, hpow]
  
  have hcanonical :
       ∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1))  =
        (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show m - 1 =  m - q  + (q - 1) by omega, Finset.prod_range_add]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    all_goals grind
  have htotal :  ∏ i ∈ Finset.range m, g i  =  m  := by
    have hζroot' : IsPrimitiveRoot ζ (m - 1 + 1) := by
      grind
    have hprod := hζroot'.prod_one_sub_pow_eq_order
    
    calc
      ∏ i ∈ Finset.range m, g i =
          (∏ i ∈ Finset.range (q - 1), u i) *
            ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) :=  by
                                                                calc
                                                                  ∏ i ∈ Finset.range m, g i =
                                                                      (∏ i ∈ Finset.range q, g i) * ∏ i ∈ Finset.range (m - q), g (q + i) := by
                                                                    have hadd := Finset.prod_range_add g q (m - q)
                                                                    simp_all
                                                                  _ = _ := by rw [hpre, hpost] 
      _ = (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) *
            ∏ i ∈ Finset.range (q - 1), u i := mul_comm _ _
      _ = ∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1)) := hcanonical.symm
      _ =  m  :=  by
                        norm_cast at hprod
                        rw [Nat.sub_add_cancel (by omega )] at hprod
                        exact hprod 
  have hfactor_ne : ∀ i ∈ Finset.range n, g i ≠ 0 := by
    intro i hi
    have hin  := Finset.mem_range.mp hi
    by_cases hskip : i = q - 1
    · simp [g, hskip]
    · have hpowne : ζ ^ (s + i) ≠ 1 := by
        intro hEq
        by_cases hilow : i < q - 1
        · 
          exact hζroot.pow_ne_one_of_pos_of_lt (by omega) (by  omega) hEq
        · 
          have hred : s + i = m + (i - q + 1) := by  omega
          have hredpow : ζ ^ (s + i) = ζ ^ (i - q + 1) := by
            rw [hred, pow_add, hζroot.pow_eq_one, one_mul]
          
          exact hζroot.pow_ne_one_of_pos_of_lt (by omega) (by  omega) (hredpow.symm.trans hEq)
      simp [g, hskip]
      exact sub_ne_zero.mpr hpowne.symm
  
  
  
  calc
     m  /  ∏ i ∈ Finset.range n, g i  =
        ((∏ i ∈ Finset.range n, g i) * ∏ j ∈ Finset.range (2 * r), g (n + j)) /
           ∏ i ∈ Finset.range n, g i  := by rw [ Trans.trans (Eq.symm (Finset.prod_range_add g n (2 * r))) htotal ]
    _ = ∏ j ∈ Finset.range (2 * r), g (n + j) := by field_simp [ Finset.prod_ne_zero_iff.mpr hfactor_ne ]
    _ = _ :=  by
                calc
                  ∏ j ∈ Finset.range (2 * r), g (n + j) =
                      ∏ j ∈ Finset.range (2 * r),
                        (1 - Complex.exp
                          (  Real.pi *  (n + 1 + 2 * j )  /  m    * Complex.I)) := by
                    apply Finset.prod_congr rfl
                    intro j hj
                    have hskip : n + j ≠ q - 1 := by omega
                    have hexp : s + (n + j) = m + (q + j) := by  omega
                    have hpow : ζ ^ (s + (n + j)) =
                        Complex.exp ( (Real.pi *  (n + 1 + 2 * j : ℕ)  /  m  : ℝ)  * Complex.I) := by
                      
                      rw [hexp, pow_add, hζroot.pow_eq_one, one_mul, ← pow_mul, hηpow]
                      have hnum : 2 * (q + j) = n + 1 + 2 * j := by omega
                      rw [hnum]
                    simp [g, hskip, hpow]
                  _ = _ := by
                    simpa [m] using cor34_cyclotomic_complement_product n r  hm  

end PottsDiscontinuity.SixVertex
