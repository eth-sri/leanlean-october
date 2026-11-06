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
  rw [show u + v⁻¹ + (E + E⁻¹) =
        (E ^ 2 - 1) * (E ^ 2 * w' - w) / (E * (E - w) * (E * w' - 1)) by rw [hu, hv]; field_simp; ring,
    show u⁻¹ + v + (E + E⁻¹) =
        (E ^ 2 - 1) * (E ^ 2 * w - w') / (E * (E - w') * (E * w - 1)) by rw [hu, hv]; field_simp; ring,
    hu, hv]
  have h7 : E ^ 2 - w / w' ≠ 0 := fun h => h5 (by field_simp at h; linear_combination h)
  field_simp

theorem ofReal_mul_sub_ne_zero {r : ℝ} (hr : 1 < r) {w w' : ℂ} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) :
    (r : ℂ) * w' - w ≠ 0 := fun h => by
  have h2 := congrArg norm (sub_eq_zero.mp h)
  rw [norm_mul, hw, hw', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  linarith

/-- `e^{ik(α)} = (E w - 1)/(E - w)` with `w = e^{iα}`, `E = e^λ`. -/
theorem exp_I_mul_kMap_unit {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Complex.exp (I * (kMap lam α : ℂ)) =
      ((Real.exp lam : ℂ) * Complex.exp (I * α) - 1) /
        ((Real.exp lam : ℂ) - Complex.exp (I * α)) := by
  rw [exp_I_mul_kMap_aux hlam α, Complex.exp_neg]
  have hne := ofReal_sub_ne_zero (by simpa using hlam : (1 : ℝ) < Real.exp lam) (norm_exp_I_mul' α)
  have hw0 := Complex.exp_ne_zero (I * (α : ℂ))
  field_simp

theorem cosh_eq_neg_iff_lt {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ) : Δ < -1 := by
  linarith [Real.one_lt_cosh.mpr hlam.ne']

/-! ### The Möbius identity for `Θ(k(α), k(β))` -/

/-- `exp(-iΘ(k(α),k(β))) = e^{i k_{2λ}(α-β)} = (e^{2λ} - e^{-i(α-β)}) / (e^{2λ-i(α-β)} - 1)`. -/
theorem exp_neg_I_theta_kMap {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ)
    (α β : ℝ) :
    Complex.exp (-(I * (theta Δ (kMap lam α) (kMap lam β) : ℂ))) =
      Complex.exp (I * (kMap (2 * lam) (α - β) : ℂ)) := by
  have hΔ1 := cosh_eq_neg_iff_lt hlam hΔ
  have hlam2 : 0 < 2 * lam := by linarith
  have hE : (1 : ℝ) < Real.exp lam := by simpa using hlam
  have hE2 : (1 : ℝ) < Real.exp lam ^ 2 := by nlinarith
  have hw := norm_exp_I_mul' α
  have hw' := norm_exp_I_mul' β
  rw [exp_neg_I_theta hΔ1, thetaRhs, exp_I_mul_kMap_unit hlam2,
    show Complex.exp (I * (((kMap lam α : ℝ) : ℂ) - ((kMap lam β : ℝ) : ℂ))) =
      Complex.exp (I * (kMap lam α : ℂ)) / Complex.exp (I * (kMap lam β : ℂ)) by
        rw [mul_sub, Complex.exp_sub],
    Complex.exp_neg, Complex.exp_neg,
    show 2 * (Δ : ℂ) = -((Real.exp lam : ℂ) + (Real.exp lam : ℂ)⁻¹) by
      have := Real.cosh_eq lam; rw [Real.exp_neg] at this
      rw [show Δ = -((Real.exp lam + (Real.exp lam)⁻¹) / 2) by linarith]; push_cast; ring,
    sub_neg_eq_add, sub_neg_eq_add,
    show Complex.exp (I * (((α - β : ℝ) : ℂ))) = Complex.exp (I * α) / Complex.exp (I * β) by
      push_cast; rw [mul_sub, Complex.exp_sub],
    show (Real.exp (2 * lam) : ℂ) = (Real.exp lam : ℂ) ^ 2 by
      rw [two_mul, Real.exp_add]; push_cast; ring]
  set E : ℂ := (Real.exp lam : ℂ) with hEdef
  have hEne : E ≠ 0 := by rw [hEdef]; exact_mod_cast (Real.exp_pos lam).ne'
  have hE2c : E ^ 2 - 1 ≠ 0 := by
    rw [show E ^ 2 - 1 = (((Real.exp lam ^ 2 - 1 : ℝ)) : ℂ) by rw [hEdef]; push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hE2r : (((Real.exp lam ^ 2 : ℝ)) : ℂ) = E ^ 2 := by rw [hEdef]; push_cast; ring
  have a5 := ofReal_mul_sub_ne_zero hE2 hw hw'
  have a6 := ofReal_mul_sub_ne_zero hE2 hw' hw
  rw [hE2r] at a5 a6
  exact key_algebra E (Complex.exp (I * α)) (Complex.exp (I * β))
    (Complex.exp (I * (kMap lam α : ℂ))) (Complex.exp (I * (kMap lam β : ℂ)))
    hEne hE2c (exp_I_mul_kMap_unit hlam α) (exp_I_mul_kMap_unit hlam β)
    (ofReal_sub_ne_zero hE hw) (ofReal_mul_sub_one_ne_zero hE hw)
    (ofReal_sub_ne_zero hE hw') (ofReal_mul_sub_one_ne_zero hE hw')
    a5 a6 (Complex.exp_ne_zero (I * (β : ℂ)))

/-- Footnote 5 (integrated form): `Θ_Δ(k_λ(α), k_λ(β)) = -k_{2λ}(α - β)`, for `Δ < -1`,
`λ > 0`, `cosh λ = -Δ`, and all real `α, β`. -/
theorem theta_kMap_kMap {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ) (α β : ℝ) :
    theta Δ (kMap lam α) (kMap lam β) = -kMap (2 * lam) (α - β) := by
  have hΔ1 := cosh_eq_neg_iff_lt hlam hΔ
  have hlam2 : 0 < 2 * lam := by linarith
  refine congrFun (eq_of_exp_eq (X := ℝ × ℝ)
    ((continuous_theta hΔ1).comp
      (((continuous_kMap hlam).comp continuous_fst).prodMk
        ((continuous_kMap hlam).comp continuous_snd)))
    (((continuous_kMap hlam2).comp (continuous_fst.sub continuous_snd)).neg)
    (fun p => ?_) (0, 0) (by simp [kMap_zero, theta_self])) (α, β)
  dsimp only [Function.comp_def, Pi.neg_apply, Pi.sub_apply]
  rw [show Complex.exp (((-kMap (2 * lam) (p.1 - p.2) : ℝ) : ℂ) * I) =
      (Complex.exp (I * (kMap (2 * lam) (p.1 - p.2) : ℂ)))⁻¹ by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring,
    ← exp_neg_I_theta_kMap hlam hΔ p.1 p.2, Complex.exp_neg, inv_inv, mul_comm]

/-! ### The derivative identities of footnote 5 -/

/-- `d/dα Θ(k(α), k(β)) = -Ξ_{2λ}(α - β)`. -/
theorem hasDerivAt_theta_kMap_left {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ)
    (α β : ℝ) :
    HasDerivAt (fun a => theta Δ (kMap lam a) (kMap lam β)) (-Xi (2 * lam) (α - β)) α := by
  rw [show (fun a => theta Δ (kMap lam a) (kMap lam β)) = fun a => -kMap (2 * lam) (a - β) from
    funext fun a => theta_kMap_kMap hlam hΔ a β]
  exact ((hasDerivAt_kMap (by linarith) (α - β)).comp_sub_const α β).neg

/-- `d/dβ Θ(k(α), k(β)) = Ξ_{2λ}(α - β)`. -/
theorem hasDerivAt_theta_kMap_right {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ)
    (α β : ℝ) :
    HasDerivAt (fun b => theta Δ (kMap lam α) (kMap lam b)) (Xi (2 * lam) (α - β)) β := by
  rw [show (fun b => theta Δ (kMap lam α) (kMap lam b)) = fun b => -kMap (2 * lam) (α - b) from
    funext fun b => theta_kMap_kMap hlam hΔ α b]
  convert ((hasDerivAt_kMap (by linarith : 0 < 2 * lam) (α - β)).comp_const_sub α β).neg using 1
  ring

/-- Chain-rule form: `∂₁Θ(k(α), k(β)) = -Ξ_{2λ}(α - β) / k'(α)` with `k' = Ξ_λ`. -/
theorem deriv_theta_left_kMap {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ)
    (α β : ℝ) :
    deriv (fun s => theta Δ s (kMap lam β)) (kMap lam α) =
      -Xi (2 * lam) (α - β) / Xi lam α := by
  have h4 := (((analyticAt_theta_left (cosh_eq_neg_iff_lt hlam hΔ) (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt).comp
    α (hasDerivAt_kMap hlam α)).unique (hasDerivAt_theta_kMap_left hlam hΔ α β)
  have hpos := Xi_pos hlam α
  field_simp; linarith

/-- Chain-rule form: `∂₂Θ(k(α), k(β)) = Ξ_{2λ}(α - β) / k'(β)` with `k' = Ξ_λ`. -/
theorem deriv_theta_right_kMap {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : Real.cosh lam = -Δ)
    (α β : ℝ) :
    deriv (fun t => theta Δ (kMap lam α) t) (kMap lam β) =
      Xi (2 * lam) (α - β) / Xi lam β := by
  have h4 := (((analyticAt_theta_right (cosh_eq_neg_iff_lt hlam hΔ) (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt).comp
    β (hasDerivAt_kMap hlam β)).unique (hasDerivAt_theta_kMap_right hlam hΔ α β)
  have hpos := Xi_pos hlam β
  field_simp; linarith

/-! ### Corollaries in terms of `Δ` alone -/

/-- For `Δ < -1`, with `k = k_{λ(Δ)}` and `λ(Δ) = arcosh(-Δ)`:
`Θ_Δ(k(α), k(β)) = -k_{2λ(Δ)}(α - β)`. -/
theorem theta_kMap_lamOf {Δ : ℝ} (hΔ : Δ < -1) (α β : ℝ) :
    theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) = -kMap (2 * lamOf Δ) (α - β) :=
  theta_kMap_kMap (lamOf_pos hΔ) (cosh_lamOf hΔ) α β

end PottsDiscontinuity.Bethe
