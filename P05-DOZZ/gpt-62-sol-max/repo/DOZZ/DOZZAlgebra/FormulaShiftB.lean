/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.StripIdentities
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The first DOZZ formula shift on its finite generic locus
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}


/-- The charge shift of the DOZZ expression follows from an affine-power Upsilon
multiplier and one scalar normalization. -/
theorem dozzFormula_shift_of_upsilon_shift {U : ℂ → ℂ} {μ γ : ℝ} {χ k₀ k₁ K : ℂ}
    (hγ : 0 < γ) (hU : IsUpsilon γ U) (hχ : χ ≠ 0)
    (hT : (dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) ≠ 0)
    (hshift : ∀ z, (∀ n : ℕ, χ * z ≠ -(n : ℂ)) →
      U (z + χ) = lFun (χ * z) * ((γ / 2 : ℝ) : ℂ) ^ (k₀ + k₁ * z) * U z)
    (hscalar : ((γ / 2 : ℝ) : ℂ) ^ (k₁ * (Q γ : ℂ)) =
      (K * lFun (-χ ^ 2)) * ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        (2 * χ / (γ : ℂ))) (α₂ α₃ : ℂ) :
    ∀ᶠ x in codiscrete ℂ, dozzFormula γ μ U (x + χ) α₂ α₃ =
      K * shiftCoeffA γ χ x α₂ α₃ * dozzFormula γ μ U (x - χ) α₂ α₃ := by
  let b : ℂ := ((γ / 2 : ℝ) : ℂ)
  let T : ℂ := ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ)
  let d₀ := (α₂ + α₃ - χ - 2 * (Q γ : ℂ)) / 2
  let d₁ := (α₂ + α₃ - χ) / 2
  let d₂ := (-α₂ + α₃ - χ) / 2
  let d₃ := (α₂ - α₃ - χ) / 2
  let v₀ (x : ℂ) := 1 / 2 * x + d₀
  let v₁ (x : ℂ) := -1 / 2 * x + d₁
  let v₂ (x : ℂ) := 1 / 2 * x + d₂
  let v₃ (x : ℂ) := 1 / 2 * x + d₃
  let e (x : ℂ) := k₀ + k₁ * x
  let k (x : ℂ) := lFun (χ * x) * b ^ e x
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr ((show 0 < γ / 2 by positivity).ne')
  have hTc : T ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  have hgen (a d : ℂ) (ha : a ≠ 0) : ∀ᶠ x in codiscrete ℂ,
      U (a * x + d) ≠ 0 ∧ lFun (χ * (a * x + d)) ≠ 0 := by
    filter_upwards [eventually_upsilon_affine_ne_zero hγ hU (d := d) ha,
      eventually_affine_lFun_ne_zero (d := χ * d) (mul_ne_zero hχ ha)] with x hUx hLx
    exact ⟨hUx, by simpa only [mul_add, mul_assoc] using hLx⟩
  filter_upwards [hgen 1 0 one_ne_zero, hgen 1 (-χ) one_ne_zero,
    hgen (1 / 2) d₀ (by norm_num), hgen (-1 / 2) d₁ (by norm_num),
    hgen (1 / 2) d₂ (by norm_num), hgen (1 / 2) d₃ (by norm_num)]
    with x hx hxm h₀ h₁ h₂ h₃
  have hs (z : ℂ) (hz : lFun (χ * z) ≠ 0) : U (z + χ) = k z * U z :=
    hshift z fun n hn => hz (by rw [lFun, hn, Complex.Gamma_neg_nat_eq_zero, zero_div])
  have hnum : U (x + χ) = k x * k (x - χ) * U (x - χ) := by
    rw [hs x (by simpa using hx.2)]
    conv_lhs => rhs; rw [← sub_add_cancel x χ, hs _ (by simpa [sub_eq_add_neg] using hxm.2)]
    ring
  have hk (z : ℂ) (hz : lFun (χ * z) ≠ 0) : k z ≠ 0 :=
    mul_ne_zero hz (Complex.cpow_ne_zero_iff.mpr (Or.inl hb))
  have hne (z : ℂ) (hz : U z ≠ 0 ∧ lFun (χ * z) ≠ 0) : U (z + χ) ≠ 0 := by
    rw [hs z hz.2]
    exact mul_ne_zero (hk z hz.2) hz.1
  have hden₁ : U (v₀ x + χ) * U (v₁ x) * U (v₂ x + χ) * U (v₃ x + χ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hne _ h₀) h₁.1) (hne _ h₂)) (hne _ h₃)
  have hden₂ : U (v₀ x) * U (v₁ x + χ) * U (v₂ x) * U (v₃ x) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h₀.1 (hne _ h₁)) h₂.1) h₃.1
  let p (y : ℂ) := (2 * (Q γ : ℂ) - (y + α₂ + α₃)) / (γ : ℂ)
  have hp : p (x + χ) = p (x - χ) - 2 * χ / (γ : ℂ) := by dsimp [p]; ring
  have hkp (u v w : ℂ) : k u * k v * k w =
      lFun (χ * u) * lFun (χ * v) * lFun (χ * w) * b ^ (e u + e v + e w) := by
    rw [Complex.cpow_add _ _ hb, Complex.cpow_add _ _ hb]
    dsimp [k]
    ring
  have hcoef : shiftCoeffA γ χ x α₂ α₃ =
      lFun (-χ ^ 2) * lFun (χ * x) * lFun (χ * (x - χ)) * lFun (χ * v₁ x) /
        (lFun (χ * v₀ x) * lFun (χ * v₃ x) * lFun (χ * v₂ x)) := by
    unfold shiftCoeffA
    rw [show χ * x - χ ^ 2 = χ * (x - χ) by ring,
      show χ / 2 * (x + α₂ + α₃ - 2 * x - χ) = χ * v₁ x by dsimp [v₁, d₁]; ring,
      show χ / 2 * (x + α₂ + α₃ - χ - 2 * Q γ) = χ * v₀ x by dsimp [v₀, d₀]; ring,
      show χ / 2 * (x + α₂ + α₃ - 2 * α₃ - χ) = χ * v₃ x by dsimp [v₃, d₃]; ring,
      show χ / 2 * (x + α₂ + α₃ - 2 * α₂ - χ) = χ * v₂ x by dsimp [v₂, d₂]; ring]
  have he : e x + e (x - χ) + e (v₁ x) =
      (e (v₀ x) + e (v₂ x) + e (v₃ x)) + k₁ * (Q γ : ℂ) := by
    ring
  have hprod : T ^ p (x + χ) * (k x * k (x - χ) * k (v₁ x)) =
      (K * shiftCoeffA γ χ x α₂ α₃) * T ^ p (x - χ) * (k (v₀ x) * k (v₂ x) * k (v₃ x)) := by
    rw [hp, Complex.cpow_sub _ _ hTc, hkp, hkp, hcoef, he, Complex.cpow_add _ _ hb]
    change b ^ (k₁ * (Q γ : ℂ)) = (K * lFun (-χ ^ 2)) * T ^ (2 * χ / (γ : ℂ)) at hscalar
    rw [hscalar]
    have hpow : T ^ (2 * χ / (γ : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hTc)
    have hn₀ : lFun (χ * v₀ x) ≠ 0 := h₀.2
    have hn₂ : lFun (χ * v₂ x) ≠ 0 := h₂.2
    have hn₃ : lFun (χ * v₃ x) ≠ 0 := h₃.2
    generalize T ^ (2 * χ / (γ : ℂ)) = t at hpow ⊢
    field_simp [hpow, hn₀, hn₂, hn₃]
  have hF (z : ℂ) : dozzFormula γ μ U z α₂ α₃ = T ^ p z * (deriv U 0 * U z * U α₂ * U α₃) /
      (U ((z + α₂ + α₃ - 2 * Q γ) / 2) * U ((z + α₂ + α₃) / 2 - z) *
        U ((z + α₂ + α₃) / 2 - α₂) * U ((z + α₂ + α₃) / 2 - α₃)) := rfl
  rw [hF, hF,
    show (x + χ + α₂ + α₃ - 2 * Q γ) / 2 = v₀ x + χ by dsimp [v₀, d₀]; ring,
    show (x - χ + α₂ + α₃ - 2 * Q γ) / 2 = v₀ x by dsimp [v₀, d₀]; ring,
    show (x + χ + α₂ + α₃) / 2 - (x + χ) = v₁ x by dsimp [v₁, d₁]; ring,
    show (x - χ + α₂ + α₃) / 2 - (x - χ) = v₁ x + χ by dsimp [v₁, d₁]; ring,
    show (x + χ + α₂ + α₃) / 2 - α₂ = v₂ x + χ by dsimp [v₂, d₂]; ring,
    show (x - χ + α₂ + α₃) / 2 - α₂ = v₂ x by dsimp [v₂, d₂]; ring,
    show (x + χ + α₂ + α₃) / 2 - α₃ = v₃ x + χ by dsimp [v₃, d₃]; ring,
    show (x - χ + α₂ + α₃) / 2 - α₃ = v₃ x by dsimp [v₃, d₃]; ring,
    ← mul_div_assoc, div_eq_div_iff hden₁ hden₂, hnum, hs _ h₀.2, hs _ h₁.2, hs _ h₂.2, hs _ h₃.2]
  linear_combination (deriv U 0 * U (x - χ) * U α₂ * U α₃ *
    U (v₀ x) * U (v₁ x) * U (v₂ x) * U (v₃ x)) * hprod

/-- Splitting off the positive real power of `γ/2` in the DOZZ base. -/
theorem dozzFormula_shift_scalar {γ μ r n : ℝ} {C : ℂ} (hγ : 0 < γ)
    (hB : 0 < dozzBase γ μ)
    (h : (dozzBase γ μ : ℂ) ^ (r : ℂ) * C = ((γ / 2 : ℝ) : ℂ) ^ (n : ℂ)) :
    ((γ / 2 : ℝ) : ℂ) ^ ((n + (2 - γ ^ 2 / 2) * r : ℝ) : ℂ) =
      C * ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ (r : ℂ) := by
  have hb : 0 < γ / 2 := by positivity
  have hbp := Real.rpow_pos_of_pos hb (2 - γ ^ 2 / 2)
  rw [← Complex.ofReal_cpow (mul_nonneg hB.le hbp.le), Real.mul_rpow hB.le hbp.le,
    ← Real.rpow_mul hb.le, Complex.ofReal_mul, Complex.ofReal_cpow hB.le, Complex.ofReal_cpow hb.le,
    Complex.ofReal_add, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hb.ne'), ← h]
  ring

/-- The DOZZ formula shift by `γ/2` on its finite generic locus. -/
theorem dozzFormula_shift_b {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + γ / 2) α₂ α₃ =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - γ / 2) α₂ α₃ := by
  let b : ℂ := (γ : ℂ) / 2
  let K : ℂ := -(1 / (Real.pi * μ))
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hb : b ≠ 0 := div_ne_zero hγc (by norm_num)
  have hβ : (0 : ℝ) < γ / 2 := by positivity
  have hB := dozzBase_pos hγ hγ2 hμ
  refine dozzFormula_shift_of_upsilon_shift (χ := b) (k₀ := 1) (k₁ := -(γ : ℂ))
    (K := K) hγ hU hb (mul_ne_zero hB.ne' (Real.rpow_pos_of_pos hβ _).ne') ?_ ?_ α₂ α₃
  · intro z hz
    simpa only [neg_mul, ← sub_eq_add_neg] using IsUpsilon.shift_b hγ hγ2 hU z hz
  have hq : b ^ 2 = ((γ ^ 2 / 4 : ℝ) : ℂ) := by dsimp [b]; push_cast; ring
  have hqr : 0 < γ ^ 2 / 4 := by positivity
  have hq1 : γ ^ 2 / 4 < 1 := by nlinarith
  have hΓp : Complex.Gamma (b ^ 2) ≠ 0 := by
    rw [hq]
    exact Complex.Gamma_ne_zero_of_re_pos (by rwa [Complex.ofReal_re])
  have hΓm : Complex.Gamma (-b ^ 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    rw [hq, neg_inj] at hn
    have hn' : γ ^ 2 / 4 = (n : ℝ) := by exact_mod_cast hn
    cases n <;> simp at hn' <;> linarith
  have hl := lFun_mul_neg (pow_ne_zero 2 hb) hΓp hΓm
  have hB' : (dozzBase γ μ : ℂ) = (Real.pi * μ : ℂ) * lFun (b ^ 2) := by
    simp [dozzBase, hq, ← show (γ : ℂ) ^ 2 / 4 = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, lFun_gammaSq_real]
  have h := dozzFormula_shift_scalar (r := 1) (n := -4) (C := K * lFun (-b ^ 2)) hγ hB (by
    rw [Complex.ofReal_one, cpow_one, hB', show (((-4 : ℝ) : ℂ)) = -(4 : ℂ) by norm_num,
      Complex.cpow_neg, Complex.cpow_ofNat]
    calc
      _ = -(lFun (b ^ 2) * lFun (-b ^ 2)) := by dsimp [K]; field_simp [hμ.ne', Real.pi_ne_zero]
      _ = _ := by rw [hl, ← pow_mul, Complex.ofReal_div, Complex.ofReal_ofNat, ← neg_div, neg_neg, one_div])
  convert h using 2 <;> push_cast <;> dsimp [b, Q] <;> push_cast <;> field_simp <;> ring

end DOZZ.Proofs
