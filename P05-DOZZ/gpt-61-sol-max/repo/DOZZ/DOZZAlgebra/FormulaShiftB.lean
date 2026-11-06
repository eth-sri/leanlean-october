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
import Mathlib.Tactic

/-!
# The first DOZZ formula shift on its finite generic locus
-/

public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

/-- The DOZZ formula shift by `γ/2`, proved directly on a codiscrete finite locus. -/
theorem dozzFormula_shift_b {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + γ / 2) α₂ α₃ =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - γ / 2) α₂ α₃ := by
  let b  := (γ : ℂ) / 2
  let d₀  := (α₂ + α₃ - b - 2 * (Q γ : ℂ)) / 2
  let d₁  := (α₂ + α₃ - b) / 2
  let d₂  := (-α₂ + α₃ - b) / 2
  let d₃  := (α₂ - α₃ - b) / 2
  let v₀  := fun α => (1 / 2 : ℂ) * α + d₀
  let v₁  := fun α => (-1 / 2 : ℂ) * α + d₁
  let v₂  := fun α => (1 / 2 : ℂ) * α + d₂
  let v₃  := fun α => (1 / 2 : ℂ) * α + d₃
  let v₀p  := fun α => (1 / 2 : ℂ) * α + (d₀ + b)
  let v₁p  := fun α => (-1 / 2 : ℂ) * α + (d₁ + b)
  let v₂p  := fun α => (1 / 2 : ℂ) * α + (d₂ + b)
  let v₃p  := fun α => (1 / 2 : ℂ) * α + (d₃ + b)
  let k  := fun z => lFun (b * z) * b ^ (1 - (γ : ℂ) * z)
  let T  := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc  := (T : ℂ)
  let q  := b ^ 2
  have hbR : 0 < γ / 2 := by positivity
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hb : b ≠ 0 := by continuity
  have hbCast : b = ((γ / 2 : ℝ) : ℂ) := by
    dsimp [b]
    push_cast
    ring
  have hTpos : 0 < T := mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos hbR _)
  have hTc : Tc ≠ 0 := Complex.ofReal_ne_zero.mpr hTpos.ne'
  have hqpos : 0 < γ ^ 2 / 4 := by positivity
  have hqone : γ ^ 2 / 4 < 1 := by nlinarith [mul_pos hγ (sub_pos.mpr hγ2)]
  have hqeq : q = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
    dsimp [q, b]
    push_cast
    ring
  have hqne : q ≠ 0 := by
    simp_all
  have hΓq : Complex.Gamma q ≠ 0 := by
    rw [hqeq, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hqpos).ne'
  have hΓ1q : Complex.Gamma (1 - q) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, hqeq, Complex.ofReal_re]
      linarith)
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := by
    intro hzero
    have hrec := Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hqne)
    grind
  have hLprod := lFun_mul_neg hqne hΓq hΓnegq
  have hBpow : ((γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) =
      b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (le_of_lt hbR), ← hbCast]
  have hTcEq : Tc = (dozzBase γ μ : ℂ) *
      b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) := by
    continuity
  have hsum : ((2 - γ ^ 2 / 2 : ℝ) : ℂ) +
      ((γ * Q γ : ℝ) : ℂ) = 4 := by
    have hreal : 2 - γ ^ 2 / 2 + γ * Q γ = 4 := by
      unfold Q
      field_simp [hγ.ne']
      ring
    exact_mod_cast hreal
  have hB : (dozzBase γ μ : ℂ) = (Real.pi * μ : ℂ) * lFun q := by
    have harg : ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    have hLq : lFun q =
        ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
      rw [hqeq, ← harg]
      exact lFun_gammaSq_real γ
    unfold dozzBase
    rw [lFun_gammaSq_real, hLq]
    simp only [Complex.ofReal_re]
    push_cast
    ring_nf
  have hpowmul  :=
    (Complex.cpow_add ((2 - γ ^ 2 / 2 : ℝ) : ℂ)
      ((γ * Q γ : ℝ) : ℂ) hb).symm
  have hqpow : b ^ (4 : ℂ) = q ^ 2 := by
    rw [Complex.cpow_ofNat]
    dsimp [q]
    ring
  have hbaseId : Tc * b ^ ((γ * Q γ : ℝ) : ℂ) *
      (-(lFun (-q)) / (Real.pi * μ)) = 1 := by
    grind

  let pplus  := fun α =>
    (2 * (Q γ : ℂ) - (α + b + α₂ + α₃)) / (γ : ℂ)
  let pminus  := fun α =>
    (2 * (Q γ : ℂ) - (α - b + α₂ + α₃)) / (γ : ℂ)
  have hexp : ∀ α : ℂ, pplus α = pminus α - 1 := by
    grind
  have hpow : ∀ α : ℂ, Tc ^ pplus α = Tc ^ pminus α / Tc := by
    intro α
    rw [hexp α, Complex.cpow_sub _ _ hTc]
    simp
  have hαm : ∀ z : ℂ, z - γ / 2 = z - b := by
    intro z
    rfl

  let poleA := eventually_affine_ne_neg_nat (c := b) (d := 0) hb
  let poleAm := eventually_affine_ne_neg_nat (c := b) (d := -b ^ 2) hb
  let poleV₀ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₀) (div_ne_zero hb (by norm_num))
  let poleV₁ := eventually_affine_ne_neg_nat (c := -b / 2) (d := b * d₁) (div_ne_zero (neg_ne_zero.mpr hb) (by norm_num))
  let poleV₂ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₂) (div_ne_zero hb (by norm_num))
  let poleV₃ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₃) (div_ne_zero hb (by norm_num))
  let nonzeroV₀ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀) (by norm_num)
  let nonzeroV₀p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀ + b) (by norm_num)
  let nonzeroV₁ := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁) (by norm_num)
  let nonzeroV₁p := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁ + b) (by norm_num)
  let nonzeroV₂ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂) (by norm_num)
  let nonzeroV₂p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂ + b) (by norm_num)
  let nonzeroV₃ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃) (by norm_num)
  let nonzeroV₃p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃ + b) (by norm_num)
  let lnonzeroV₀ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₀) (div_ne_zero hb (by norm_num))
  let lnonzeroV₂ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₂) (div_ne_zero hb (by norm_num))
  let lnonzeroV₃ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₃) (div_ne_zero hb (by norm_num))
  filter_upwards [poleA, poleAm, poleV₀, poleV₁, poleV₂, poleV₃,
    nonzeroV₀, nonzeroV₀p, nonzeroV₁, nonzeroV₁p, nonzeroV₂, nonzeroV₂p,
    nonzeroV₃, nonzeroV₃p, lnonzeroV₀, lnonzeroV₂, lnonzeroV₃]
    with α hpa hpam hp₀ hp₁ hp₂ hp₃ hu₀ hu₀p hu₁ hu₁p hu₂ hu₂p hu₃ hu₃p hl₀ hl₂ hl₃
  have hnotA : ∀ n : ℕ, b * α ≠ -(n : ℂ) := by simpa using hpa
  have hnotAm : ∀ n : ℕ, b * (α - b) ≠ -(n : ℂ) := by
    grind
  have hnotV₀ : ∀ n : ℕ, b * v₀ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₀ n
    convert hn using 1
    simp [v₀]
    ring
  have hnotV₁ : ∀ n : ℕ, b * v₁ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₁ n
    convert hn using 1
    simp [v₁]
    ring
  have hnotV₂ : ∀ n : ℕ, b * v₂ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₂ n
    convert hn using 1
    simp [v₂]
    ring
  have hnotV₃ : ∀ n : ℕ, b * v₃ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₃ n
    convert hn using 1
    simp [v₃]
    ring
  have hsA := IsUpsilon.shift_b hγ hγ2 hU α hnotA
  have hsAm := IsUpsilon.shift_b hγ hγ2 hU (α - b) hnotAm
  have hnum : U (α + b) = k α * k (α - b) * U (α - b) := by
    grind
  have hu₀' : U (v₀ α + b) = k (v₀ α) * U (v₀ α) := by
    simpa [k] using IsUpsilon.shift_b hγ hγ2 hU (v₀ α) hnotV₀
  have hu₁' : U (v₁ α + b) = k (v₁ α) * U (v₁ α) := by
    simpa [k] using IsUpsilon.shift_b hγ hγ2 hU (v₁ α) hnotV₁
  have hu₂' : U (v₂ α + b) = k (v₂ α) * U (v₂ α) := by
    simpa [k] using IsUpsilon.shift_b hγ hγ2 hU (v₂ α) hnotV₂
  have hu₃' : U (v₃ α + b) = k (v₃ α) * U (v₃ α) := by
    simpa [k] using IsUpsilon.shift_b hγ hγ2 hU (v₃ α) hnotV₃
  have hv₀p : v₀p α = v₀ α + b := by dsimp [v₀p, v₀]; ring
  have hv₁p : v₁p α = v₁ α + b := by dsimp [v₁p, v₁]; ring
  have hv₂p : v₂p α = v₂ α + b := by dsimp [v₂p, v₂]; ring
  have hv₃p : v₃p α = v₃ α + b := by dsimp [v₃p, v₃]; ring
  have hdenPlus : U (v₀ α + b) * U (v₁ α) * U (v₂ α + b) * U (v₃ α + b) ≠ 0 := by
    grind
  have hdenMinus : U (v₀ α) * U (v₁ α + b) * U (v₂ α) * U (v₃ α) ≠ 0 := by
    grind




  have hargL₀ : b * v₀ α = b / 2 * α + b * d₀ := by dsimp [v₀]; ring
  have hargL₂ : b * v₂ α = b / 2 * α + b * d₂ := by dsimp [v₂]; ring
  have hargL₃ : b * v₃ α = b / 2 * α + b * d₃ := by dsimp [v₃]; ring
  have hL₀ : lFun (b * v₀ α) ≠ 0 := by rw [hargL₀]; exact hl₀
  have hL₂ : lFun (b * v₂ α) ≠ 0 := by rw [hargL₂]; exact hl₂
  have hL₃ : lFun (b * v₃ α) ≠ 0 := by rw [hargL₃]; exact hl₃

  have hWplus0 : ((α + γ / 2 + α₂ + α₃ - 2 * Q γ) / 2) = v₀p α := by
    dsimp [v₀p, d₀, b]
    ring
  have hWminus0 : ((α - γ / 2 + α₂ + α₃ - 2 * Q γ) / 2) = v₀ α := by
    dsimp [v₀, d₀, b]
    ring
  have hUplus1 : ((α + γ / 2 + α₂ + α₃) / 2 - (α + γ / 2)) = v₁ α := by
    dsimp [v₁, d₁, b]
    ring
  have hUminus1 : ((α - γ / 2 + α₂ + α₃) / 2 - (α - γ / 2)) = v₁p α := by
    dsimp [v₁p, d₁, b]
    ring
  have hUplus2 : ((α + γ / 2 + α₂ + α₃) / 2 - α₂) = v₂p α := by
    dsimp [v₂p, d₂, b]
    ring
  have hUminus2 : ((α - γ / 2 + α₂ + α₃) / 2 - α₂) = v₂ α := by
    dsimp [v₂, d₂, b]
    ring
  have hUplus3 : ((α + γ / 2 + α₂ + α₃) / 2 - α₃) = v₃p α := by
    dsimp [v₃p, d₃, b]
    ring
  have hUminus3 : ((α - γ / 2 + α₂ + α₃) / 2 - α₃) = v₃ α := by
    dsimp [v₃, d₃, b]
    ring
  have hCoeffArg₁ : b / 2 * ((α + α₂ + α₃) - 2 * α - b) = b * v₁ α := by
    dsimp [v₁, d₁]
    ring
  have hCoeffArg₀ : b / 2 * ((α + α₂ + α₃) - b - 2 * (Q γ : ℂ)) = b * v₀ α := by
    dsimp [v₀, d₀]
    ring
  have hCoeffArg₂ : b / 2 * ((α + α₂ + α₃) - 2 * α₂ - b) = b * v₂ α := by
    dsimp [v₂, d₂]
    ring
  have hCoeffArg₃ : b / 2 * ((α + α₂ + α₃) - 2 * α₃ - b) = b * v₃ α := by
    dsimp [v₃, d₃]
    ring
  have hcoeff : shiftCoeffA γ (γ / 2) α α₂ α₃ =
      lFun (-q) * lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α) /
        (lFun (b * v₀ α) * lFun (b * v₃ α) * lFun (b * v₂ α)) := by
    unfold shiftCoeffA
    change
      (lFun (-b ^ 2) * lFun (b * α) * lFun (b * α - b ^ 2) *
        lFun (b / 2 * ((α + α₂ + α₃) - 2 * α - b))) /
        (lFun (b / 2 * ((α + α₂ + α₃) - b - 2 * (Q γ : ℂ))) *
          lFun (b / 2 * ((α + α₂ + α₃) - 2 * α₃ - b)) *
          lFun (b / 2 * ((α + α₂ + α₃) - 2 * α₂ - b))) = _
    rw [show -b ^ 2 = -q by dsimp [q]]
    rw [show b * α - b ^ 2 = b * (α - b) by ring]
    grind
  have hscalar : Tc ^ pplus α * k α * k (α - b) * k (v₁ α) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α α₂ α₃ *
        Tc ^ pminus α * k (v₀ α) * k (v₂ α) * k (v₃ α) := by
    have hmul (a x y z : ℂ) : a * k x * k y * k z =
        a * (lFun (b * x) * lFun (b * y) * lFun (b * z)) *
          b ^ ((1 - (γ : ℂ) * x) + (1 - (γ : ℂ) * y) + (1 - (γ : ℂ) * z)) := by
      dsimp [k]
      rw [Complex.cpow_add _ _ hb, Complex.cpow_add _ _ hb]
      ring
    have hExp : (1 - (γ : ℂ) * α) + (1 - (γ : ℂ) * (α - b)) +
        (1 - (γ : ℂ) * v₁ α) =
        ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) +
          (1 - (γ : ℂ) * v₃ α)) - (γ : ℂ) * (Q γ : ℂ) := by
      ring
    rw [hpow α, hcoeff, hmul, hmul, hExp, Complex.cpow_sub _ _ hb]
    have hbaseDiv : (Real.pi * μ : ℂ) /
        b ^ ((γ * Q γ : ℝ) : ℂ) = -(Tc * lFun (-q)) := by

      have hpiμ  :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
          (Complex.ofReal_ne_zero.mpr hμ.ne')
      have hpowne : b ^ ((γ * Q γ : ℝ) : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
      grind
    push_cast at hbaseDiv
    field_simp [hTc, hL₀, hL₂, hL₃, hμ.ne', Real.pi_ne_zero]
    linear_combination (
      (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α)) *
      b ^ ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) +
        (1 - (γ : ℂ) * v₃ α))) * hbaseDiv
  have hpowplus : Tc ^ pplus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α + γ / 2 + α₂ + α₃)) / γ) := by
    ring
  have hpowminus : Tc ^ pminus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α - γ / 2 + α₂ + α₃)) / γ) := by
    ring
  unfold dozzFormula
  rw [← hpowplus, ← hpowminus]
  rw [hWplus0, hWminus0, hUplus1, hUminus1,
    hUplus2, hUminus2, hUplus3, hUminus3]
  rw [hv₀p, hv₁p, hv₂p, hv₃p]
  rw [← mul_div_assoc]
  rw [div_eq_div_iff hdenPlus hdenMinus]
  rw [hαm α, hnum, hu₀', hu₁', hu₂', hu₃']
  linear_combination
    (deriv U 0 * U (α - b) * U α₂ * U α₃ *
      U (v₀ α) * U (v₁ α) * U (v₂ α) * U (v₃ α)) * hscalar

end DOZZ.Proofs

end
