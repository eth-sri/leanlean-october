module

public import Mathlib
public import PottsDiscontinuity.Bethe.KMap

/-!
# Footnote 5: `Θ(k(α), k(β))` and the derivative identities

For `Δ < -1` and `λ > 0` with `cosh λ = -Δ`, the Bethe phase composed with the change of variable
`x = k(α)`, `y = k(β)` is a function of `α - β` only:

  `Θ_Δ(k_λ(α), k_λ(β)) = -k_{2λ}(α - β)`   for all real `α, β`

(`theta_kMap_kMap`; equivalently `exp(-iΘ(k(α),k(β))) = (e^{2λ} - e^{-i(α-β)}) /
(e^{2λ - i(α-β)} - 1)`, the Möbius identity which the source only records in a commented-out
draft).  Differentiating, with `k_{2λ}' = Ξ_{2λ}`, gives the identities of footnote 5,

  `Ξ_{2λ}(α - β) = -d/dα Θ(k(α),k(β)) = d/dβ Θ(k(α),k(β))`,

equivalently `∂₁Θ(k(α),k(β)) = -Ξ_{2λ}(α-β)/k'(α)` and `∂₂Θ(k(α),k(β)) = Ξ_{2λ}(α-β)/k'(β)`
(`k' = Ξ_λ`).  All statements hold for every real `α, β` (in particular on `[-π, π]`).
-/

@[expose] public section

open Complex Filter Topology Set

namespace PottsDiscontinuity.Bethe

/-! ### Algebra -/

theorem key_algebra {K : Type*} [Field K] (E w w' u v : K) (hE : E ≠ 0) (hE2 : E ^ 2 - 1 ≠ 0)
    (hu : u = (E * w - 1) / (E - w)) (hv : v = (E * w' - 1) / (E - w'))
    (h1 : E - w ≠ 0) (h2 : E * w - 1 ≠ 0) (h3 : E - w' ≠ 0) (h4 : E * w' - 1 ≠ 0)
    (h5 : E ^ 2 * w' - w ≠ 0) (h6 : E ^ 2 * w - w' ≠ 0) (hw' : w' ≠ 0) :
    u / v * ((u⁻¹ + v + (E + E⁻¹)) / (u + v⁻¹ + (E + E⁻¹))) =
      (E ^ 2 * (w / w') - 1) / (E ^ 2 - w / w') := by
  have hden : u + v⁻¹ + (E + E⁻¹) =
      (E ^ 2 - 1) * (E ^ 2 * w' - w) / (E * (E - w) * (E * w' - 1)) := by
    rw [hu, hv]
    field_simp
    ring
  have hnum : u⁻¹ + v + (E + E⁻¹) =
      (E ^ 2 - 1) * (E ^ 2 * w - w') / (E * (E - w') * (E * w - 1)) := by
    rw [hu, hv]
    field_simp
    ring
  rw [hden, hnum, hu, hv]
  
  field_simp

theorem ofReal_mul_sub_ne_zero {r : ℝ} (hr : 1 < r) {w w' : ℂ} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) :
    (r : ℂ) * w' - w ≠ 0 := by
  intro h
  
  have h2 : ‖ r  * w'‖ = ‖w‖ := by rw [ sub_eq_zero.mp h ]
  rw [norm_mul, hw', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  linarith

/-- `e^{ik(α)} = (E w - 1)/(E - w)` with `w = e^{iα}`, `E = e^λ`. -/
theorem exp_I_mul_kMap_unit {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Complex.exp (I * (kMap lam α : ℂ)) =
      ((Real.exp lam : ℂ) * Complex.exp (I * α) - 1) /
        ((Real.exp lam : ℂ) - Complex.exp (I * α)) := by
  rw [exp_I_mul_kMap_aux hlam α, Complex.exp_neg]
  
  
  
  field_simp

theorem cosh_eq_neg_iff_lt {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ) : Δ < -1 := by
  have := Real.one_lt_cosh.mpr hlam.ne'
  linarith

/-! ### The Möbius identity for `Θ(k(α), k(β))` -/

section

variable {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ) (α β : ℝ)
include hlam hΔ

/-- `exp(-iΘ(k(α),k(β))) = e^{i k_{2λ}(α-β)} = (e^{2λ} - e^{-i(α-β)}) / (e^{2λ-i(α-β)} - 1)`. -/
theorem exp_neg_I_theta_kMap  :
    Complex.exp (-(I * (theta Δ (kMap lam α) (kMap lam β) : ℂ))) =
      Complex.exp (I * (kMap (2 * lam) (α - β) : ℂ)) := by
  
  have hlam2 : 0 < 2 * lam := by linarith
  have hE :  1  < Real.exp lam := by simpa using hlam
  have hE2 :  1  < Real.exp lam ^ 2 := by nlinarith
  have hw := norm_exp_I_mul' α
  have hw' := norm_exp_I_mul' β
  rw [exp_neg_I_theta (cosh_eq_neg_iff_lt hlam hΔ), thetaRhs, exp_I_mul_kMap_unit hlam2]
  have e1 : Complex.exp (I * (  kMap lam α   -   kMap lam β  )) =
      Complex.exp (I *  kMap lam α ) / Complex.exp (I *  kMap lam β ) := by
    rw [mul_sub, Complex.exp_sub]
  
  
  have hd : 2 *  Δ  = -( Real.exp lam  + (Real.exp lam : ℂ)⁻¹) := by
    have h1 : Δ = -((Real.exp lam + (Real.exp lam)⁻¹) / 2) := by
      have := Real.cosh_eq lam
      rw [Real.exp_neg] at this
      linarith
    rw [h1]
    push_cast
    ring
  
  
  rw [e1,  Complex.exp_neg _ ,  Complex.exp_neg _ , hd, sub_neg_eq_add, sub_neg_eq_add, (by
                                                                                           push_cast
                                                                                           rw [mul_sub, Complex.exp_sub] : Complex.exp (I *  ((α - β : ℝ) ) ) = Complex.exp (I * α) / Complex.exp (I * β)), (by
                                                                                               rw [two_mul, Real.exp_add]; push_cast; ring : (Real.exp (2 * lam) ) = (Real.exp lam : ℂ) ^ 2)]
  set E : ℂ := (Real.exp lam : ℂ) with hEdef
  
  have hE2c : E ^ 2 - 1 ≠ 0 := by
    
    rw [(by
           rw [hEdef]; push_cast; ring : E ^ 2 - 1 = ( (Real.exp lam ^ 2 - 1 : ℝ)  ))]
    exact Complex.ofReal_ne_zero.mpr (by linarith )
  
  
  
  
  
  
  
  have a5 := ofReal_mul_sub_ne_zero hE2 hw hw'
  have a6 := ofReal_mul_sub_ne_zero hE2 hw' hw
  rw [(by rw [hEdef]; push_cast; ring : ( (Real.exp lam ^ 2 : ℝ)  ) = E ^ 2)] at a5 a6
  
  
  have := key_algebra E (Complex.exp (I * α)) (Complex.exp (I * β))
    (Complex.exp (I *  kMap lam α )) (Complex.exp (I *  kMap lam β ))
    (by
       simp_all) hE2c (exp_I_mul_kMap_unit hlam α) (exp_I_mul_kMap_unit hlam β) (ofReal_sub_ne_zero hE hw) (ofReal_mul_sub_one_ne_zero hE hw) (ofReal_sub_ne_zero hE hw') (ofReal_mul_sub_one_ne_zero hE hw') a5 a6 (Complex.exp_ne_zero (I *  β ))
  rw [this]

/-- Footnote 5 (integrated form): `Θ_Δ(k_λ(α), k_λ(β)) = -k_{2λ}(α - β)`, for `Δ < -1`,
`λ > 0`, `cosh λ = -Δ`, and all real `α, β`. -/
theorem theta_kMap_kMap  :
    theta Δ (kMap lam α) (kMap lam β) = -kMap (2 * lam) (α - β) := by
  
  
  have key : (fun p  => theta Δ (kMap lam p.1) (kMap lam p.2)) =
      fun p : ℝ × ℝ => -kMap (2 * lam) (p.1 - p.2) := by
    refine eq_of_exp_eq (X := ℝ × ℝ) ?_ ?_ ?_ (0, 0) ?_
    · exact  (continuous_theta (cosh_eq_neg_iff_lt hlam hΔ)).comp
        (((continuous_kMap hlam).comp continuous_fst).prodMk
          ((continuous_kMap hlam).comp continuous_snd)) 
    · exact ((continuous_kMap (by linarith)).comp (continuous_fst.sub continuous_snd)).neg
    · intro p
      
      have h2 : Complex.exp ( (-kMap (2 * lam) (p.1 - p.2) : ℝ)  * I) =
          (Complex.exp (I *  kMap (2 * lam) (p.1 - p.2) ))⁻¹ := by
        rw [← Complex.exp_neg];  push_cast; ring
      rw [h2, ←  exp_neg_I_theta_kMap hlam hΔ p.1 p.2 , Complex.exp_neg, inv_inv, mul_comm]
    · simp [kMap_zero, theta_self]
  exact congrFun key (α, β)

end

/-! ### The derivative identities of footnote 5 -/

section

variable {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ) (α β : ℝ)
include hlam hΔ α β

/-- `d/dα Θ(k(α), k(β)) = -Ξ_{2λ}(α - β)`. -/
theorem hasDerivAt_theta_kMap_left  :
    HasDerivAt (fun a => theta Δ (kMap lam a) (kMap lam β)) (-Xi (2 * lam) (α - β)) α := by
  
  
  
  rw [ funext fun a => theta_kMap_kMap hlam hΔ a β ]
  exact  ((hasDerivAt_kMap (by linarith) (α - β)).comp_sub_const α β).neg 

/-- `d/dβ Θ(k(α), k(β)) = Ξ_{2λ}(α - β)`. -/
theorem hasDerivAt_theta_kMap_right  :
    HasDerivAt (fun b => theta Δ (kMap lam α) (kMap lam b)) (Xi (2 * lam) (α - β)) β := by
  
  
  have h3 : HasDerivAt (fun b => -kMap (2 * lam) (α - b)) (- -Xi (2 * lam) (α - β) ) β := ((hasDerivAt_kMap (by linarith) (α - β)).comp_const_sub α β).neg
  have e  :=
    funext (theta_kMap_kMap hlam hΔ α)
  simp_all

/-- Chain-rule form: `∂₁Θ(k(α), k(β)) = -Ξ_{2λ}(α - β) / k'(α)` with `k' = Ξ_λ`. -/
theorem deriv_theta_left_kMap  :
    deriv (fun s => theta Δ s (kMap lam β)) (kMap lam α) =
      -Xi (2 * lam) (α - β) / Xi lam α := by
  
  
  
  
  have h4 := (((analyticAt_theta_left (cosh_eq_neg_iff_lt hlam hΔ) (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt).comp α (hasDerivAt_kMap hlam α)).unique (hasDerivAt_theta_kMap_left hlam hΔ α β)
  have hpos := Xi_pos hlam α
  field_simp
  linarith

/-- Chain-rule form: `∂₂Θ(k(α), k(β)) = Ξ_{2λ}(α - β) / k'(β)` with `k' = Ξ_λ`. -/
theorem deriv_theta_right_kMap  :
    deriv  (theta Δ (kMap lam α))  (kMap lam β) =
      Xi (2 * lam) (α - β) / Xi lam β := by
  
  
  
  
  have h4 := (((analyticAt_theta_right (cosh_eq_neg_iff_lt hlam hΔ) (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt).comp β (hasDerivAt_kMap hlam β)).unique (hasDerivAt_theta_kMap_right hlam hΔ α β)
  have hpos := Xi_pos hlam β
  field_simp
  linarith

end

/-! ### Corollaries in terms of `Δ` alone -/

/-- For `Δ < -1`, with `k = k_{λ(Δ)}` and `λ(Δ) = arcosh(-Δ)`:
`Θ_Δ(k(α), k(β)) = -k_{2λ(Δ)}(α - β)`. -/
theorem theta_kMap_lamOf {Δ : ℝ} (hΔ : Δ < -1) (α β : ℝ) :
    theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) = -kMap (2 * lamOf Δ) (α - β) :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.Bethe.theta_kMap_kMap, _root_.PottsDiscontinuity.Bethe.lamOf_pos, _root_.PottsDiscontinuity.Bethe.cosh_lamOf]

end PottsDiscontinuity.Bethe
