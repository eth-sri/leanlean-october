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

public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

/-- The DOZZ formula shift by `γ/2`, proved directly on a codiscrete finite locus. -/
theorem dozzFormula_shift_binv {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + 2 / γ) α₂ α₃ =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - 2 / γ) α₂ α₃ := by
  let c : ℂ := (2 / γ : ℝ)
  let s : ℂ := (γ / 2 : ℝ)
  let d₀  := (α₂ + α₃ - c - 2 * (Q γ : ℂ)) / 2
  let d₁  := (α₂ + α₃ - c) / 2
  let d₂  := (-α₂ + α₃ - c) / 2
  let d₃  := (α₂ - α₃ - c) / 2
  let v₀  := fun α => (1 / 2 : ℂ) * α + d₀
  let v₁  := fun α => (-1 / 2 : ℂ) * α + d₁
  let v₂  := fun α => (1 / 2 : ℂ) * α + d₂
  let v₃  := fun α => (1 / 2 : ℂ) * α + d₃
  let v₀p  := fun α => (1 / 2 : ℂ) * α + (d₀ + c)
  let v₁p  := fun α => (-1 / 2 : ℂ) * α + (d₁ + c)
  let v₂p  := fun α => (1 / 2 : ℂ) * α + (d₂ + c)
  let v₃p  := fun α => (1 / 2 : ℂ) * α + (d₃ + c)
  let k  := fun z => lFun (c * z) * s ^ (4 / (γ : ℂ) * z - 1)
  let T  := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc  := (T : ℂ)
  let rR  := 4 / γ ^ 2
  let r  := (rR : ℂ)
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hc : c ≠ 0 := by
    continuity
  have hcCast : c = ((2 / γ : ℝ) : ℂ) := rfl
  have hcComplex : c = (2 / (γ : ℂ)) := by
    rw [hcCast]
    norm_cast
  have hsCast : s = ((γ / 2 : ℝ) : ℂ) := rfl
  have hs : s ≠ 0 := by
    simp_all

  have hsR : 0 < γ / 2 := by positivity
  have hTpos : 0 < T := mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos hsR _)
  have hTc  := Complex.ofReal_ne_zero.mpr hTpos.ne'
  have hrpos : 0 < rR := by dsimp [rR]; positivity
  have hrCast : r = ((4 / γ ^ 2 : ℝ) : ℂ) := rfl
  have hrne : ∀ n : ℕ, rR ≠ (n : ℝ) := by
    intro n
    exact hγk n
  have hΓr : Complex.Gamma r ≠ 0 := by
    rw [hrCast, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hrpos).ne'
  have hΓnegr : Complex.Gamma (-r) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hrEq  := neg_inj.mp hn
    change (rR : ℂ) = (n : ℂ) at hrEq
    have : rR = (n : ℝ) := by exact_mod_cast hrEq
    exact (hrne n) this
  have hΓ1r : Complex.Gamma (1 - r) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hreal : 1 - rR = -(n : ℝ) := by
      have hrEq  := hn
      change (1 - (rR : ℂ)) = -(n : ℂ) at hrEq
      exact_mod_cast hrEq
    have : rR = ((n + 1 : ℕ) : ℝ) := by
      grind
    exact (hrne (n + 1)) this
  have hLr : lFun r ≠ 0 := div_ne_zero hΓr hΓ1r
  have hrne0  := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hLprod := lFun_mul_neg hrne0 hΓr hΓnegr
  have hsum : rR * (2 - γ ^ 2 / 2) + 4 = 4 * Q γ / γ := by
    dsimp [rR]
    unfold Q
    field_simp [hγ.ne']
    ring
  have hbase  := dozzBase_pos hγ hγ2 hμ
  have hbaseNe  :=
    Complex.ofReal_ne_zero.mpr hbase.ne'
  have hTpow : Tc ^ r =
      (((dozzBase γ μ) ^ rR * (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [show Tc = (T : ℂ) by rfl, show r = (rR : ℂ) by rfl,
      ← Complex.ofReal_cpow hTpos.le]
    apply congrArg (fun x : ℝ => (x : ℂ))
    dsimp [T]
    rw [Real.mul_rpow hbase.le (Real.rpow_nonneg hsR.le _)]
    rw [← Real.rpow_mul hsR.le]
    congr 1
    ring_nf
  have hbaseId : Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
      s ^ ((4 * Q γ / γ : ℝ) : ℂ) := by
    have hpi  := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hDpowC : ((dozzBase γ μ : ℝ) : ℂ) ^ r ≠ 0 := by
      simp_all
    have hdual : dualMu γ μ =
        ((dozzBase γ μ : ℝ) : ℂ) ^ r / (Real.pi * lFun r) := rfl
    have hgamma4 : (γ / 2) ^ 4 = 1 / rR ^ 2 := by
      grind

    have hcoef : ((dozzBase γ μ : ℝ) : ℂ) ^ r *
        (-(lFun (-r)) / (Real.pi * dualMu γ μ)) = 1 / r ^ 2 := by
      grind
    have hgamma4Real : (γ / 2) ^ (4 : ℝ) = 1 / rR ^ 2 := by
      simp_all
    have hscalarReal : (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) *
        (1 / rR ^ 2) = (γ / 2) ^ (4 * Q γ / γ) := by
      calc
        _ = (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) * (γ / 2) ^ (4 : ℝ) := by rw [← hgamma4Real]
        _ = (γ / 2) ^ (rR * (2 - γ ^ 2 / 2) + 4) := (Real.rpow_add hsR _ _).symm
        _ = (γ / 2) ^ (4 * Q γ / γ) := by rw [hsum]
    rw [hTpow]
    have hDpowCast : ((dozzBase γ μ) ^ rR : ℝ) =
        ((dozzBase γ μ : ℝ) : ℂ) ^ r := by
      rw [show r = (rR : ℂ) by rfl, Complex.ofReal_cpow hbase.le]
    have hcoefCast : 1 / r ^ 2 = ((1 / rR ^ 2 : ℝ) : ℂ) := by
      push_cast <;> ring
    have hpowS : s ^ ((4 * Q γ / γ : ℝ) : ℂ) =
        (((γ / 2) ^ (4 * Q γ / γ) : ℝ) : ℂ) := by
      rw [hsCast, Complex.ofReal_cpow hsR.le]
    calc
      (((dozzBase γ μ) ^ rR * (γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
          (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
          (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
            (((dozzBase γ μ : ℝ) : ℂ) ^ r *
              (-(lFun (-r)) / (Real.pi * dualMu γ μ))) := by
                rw [Complex.ofReal_mul, hDpowCast]
                ring
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) * (1 / r ^ 2) := by
        rw [hcoef]
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
          ((1 / rR ^ 2 : ℝ) : ℂ) := by rw [hcoefCast]
      _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) * (1 / rR ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul]
      _ = (((γ / 2) ^ (4 * Q γ / γ) : ℝ) : ℂ) := by
        exact_mod_cast hscalarReal
      _ = s ^ ((4 * Q γ / γ : ℝ) : ℂ) := hpowS.symm
  have hSexp : ((4 * Q γ / γ : ℝ) : ℂ) =
      (γ : ℂ)⁻¹ * (Q γ : ℂ) * 4 := by
    push_cast
    field_simp [hγ.ne']
  have hScpow : s ^ ((4 * Q γ / γ : ℝ) : ℂ) =
      s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) := by
    congr 1
  let pplus  := fun α =>
    (2 * (Q γ : ℂ) - (α + c + α₂ + α₃)) / (γ : ℂ)
  let pminus  := fun α =>
    (2 * (Q γ : ℂ) - (α - c + α₂ + α₃)) / (γ : ℂ)
  have hexp : ∀ α : ℂ, pplus α = pminus α - r := by
    intro α
    dsimp [pplus, pminus, c, r, rR]
    push_cast <;> ring
  have hpow : ∀ α : ℂ, Tc ^ pplus α = Tc ^ pminus α / Tc ^ r := by
    intro α
    rw [hexp α, Complex.cpow_sub _ _ hTc]
  have hαm : ∀ z : ℂ, z - 2 / γ = z - c := by
    intro z
    rw [hcComplex]

  let poleA := eventually_affine_ne_neg_nat (c := c) (d := 0) hc
  let poleAm := eventually_affine_ne_neg_nat (c := c) (d := -c ^ 2) hc
  let poleV₀ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₀) (div_ne_zero hc (by norm_num))
  let poleV₁ := eventually_affine_ne_neg_nat (c := -c / 2) (d := c * d₁) (div_ne_zero (neg_ne_zero.mpr hc) (by norm_num))
  let poleV₂ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₂) (div_ne_zero hc (by norm_num))
  let poleV₃ := eventually_affine_ne_neg_nat (c := c / 2) (d := c * d₃) (div_ne_zero hc (by norm_num))
  let nonzeroV₀ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀) (by norm_num)
  let nonzeroV₀p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₀ + c) (by norm_num)
  let nonzeroV₁ := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁) (by norm_num)
  let nonzeroV₁p := eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ))
    (d := d₁ + c) (by norm_num)
  let nonzeroV₂ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂) (by norm_num)
  let nonzeroV₂p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₂ + c) (by norm_num)
  let nonzeroV₃ := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃) (by norm_num)
  let nonzeroV₃p := eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ))
    (d := d₃ + c) (by norm_num)
  let lnonzeroV₀ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₀) (div_ne_zero hc (by norm_num))
  let lnonzeroV₂ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₂) (div_ne_zero hc (by norm_num))
  let lnonzeroV₃ := eventually_affine_lFun_ne_zero (c := c / 2) (d := c * d₃) (div_ne_zero hc (by norm_num))
  filter_upwards [poleA, poleAm, poleV₀, poleV₁, poleV₂, poleV₃,
    nonzeroV₀, nonzeroV₀p, nonzeroV₁, nonzeroV₁p, nonzeroV₂, nonzeroV₂p,
    nonzeroV₃, nonzeroV₃p, lnonzeroV₀, lnonzeroV₂, lnonzeroV₃]
    with α hpa hpam hp₀ hp₁ hp₂ hp₃ hu₀ hu₀p hu₁ hu₁p hu₂ hu₂p hu₃ hu₃p hl₀ hl₂ hl₃
  have hnotA : ∀ n : ℕ, c * α ≠ -(n : ℂ) := by simpa using hpa
  have hnotAShift : ∀ n : ℕ, (2 / (γ : ℂ)) * α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotA
  have hnotAm : ∀ n : ℕ, c * (α - c) ≠ -(n : ℂ) := by
    grind
  have hnotAmShift : ∀ n : ℕ, (2 / (γ : ℂ)) * (α - c) ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotAm
  have hnotV₀ : ∀ n : ℕ, c * v₀ α ≠ -(n : ℂ) := by
    grind
  have hnotV₀Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₀ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₀
  have hnotV₁ : ∀ n : ℕ, c * v₁ α ≠ -(n : ℂ) := by
    grind
  have hnotV₁Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₁ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₁
  have hnotV₂ : ∀ n : ℕ, c * v₂ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₂ n
    convert hn using 1
    simp [v₂]
    ring
  have hnotV₂Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₂ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₂
  have hnotV₃ : ∀ n : ℕ, c * v₃ α ≠ -(n : ℂ) := by
    intro n hn
    apply hp₃ n
    convert hn using 1
    simp [v₃]
    ring
  have hnotV₃Shift : ∀ n : ℕ, (2 / (γ : ℂ)) * v₃ α ≠ -(n : ℂ) := by
    simpa [hcComplex] using hnotV₃
  have hsA := IsUpsilon.shift_binv hγ hγ2 hU α hnotAShift
  have hsAm := IsUpsilon.shift_binv hγ hγ2 hU (α - c) hnotAmShift
  have hnum : U (α + c) = k α * k (α - c) * U (α - c) := by
    grind
  have hu₀' : U (v₀ α + c) = k (v₀ α) * U (v₀ α) := by
    simpa [k, hcComplex, hsCast] using IsUpsilon.shift_binv hγ hγ2 hU (v₀ α) hnotV₀Shift
  have hu₁' : U (v₁ α + c) = k (v₁ α) * U (v₁ α) := by
    simpa [k, hcComplex, hsCast] using IsUpsilon.shift_binv hγ hγ2 hU (v₁ α) hnotV₁Shift
  have hu₂' : U (v₂ α + c) = k (v₂ α) * U (v₂ α) := by
    simpa [k, hcComplex, hsCast] using IsUpsilon.shift_binv hγ hγ2 hU (v₂ α) hnotV₂Shift
  have hu₃' : U (v₃ α + c) = k (v₃ α) * U (v₃ α) := by
    simpa [k, hcComplex, hsCast] using IsUpsilon.shift_binv hγ hγ2 hU (v₃ α) hnotV₃Shift
  have hv₀p : v₀p α = v₀ α + c := by dsimp [v₀p, v₀]; ring
  have hv₁p : v₁p α = v₁ α + c := by dsimp [v₁p, v₁]; ring
  have hv₂p : v₂p α = v₂ α + c := by dsimp [v₂p, v₂]; ring
  have hv₃p : v₃p α = v₃ α + c := by dsimp [v₃p, v₃]; ring
  have hdenPlus : U (v₀ α + c) * U (v₁ α) * U (v₂ α + c) * U (v₃ α + c) ≠ 0 := by
    rw [← hv₀p, ← hv₂p, ← hv₃p]
    positivity
  have hdenMinus : U (v₀ α) * U (v₁ α + c) * U (v₂ α) * U (v₃ α) ≠ 0 := by
    rw [← hv₁p]
    positivity

  have hargL₀ : c * v₀ α = c / 2 * α + c * d₀ := by dsimp [v₀]; ring
  have hargL₂ : c * v₂ α = c / 2 * α + c * d₂ := by dsimp [v₂]; ring
  have hargL₃ : c * v₃ α = c / 2 * α + c * d₃ := by dsimp [v₃]; ring
  have hL₀ : lFun (c * v₀ α) ≠ 0 := by rw [hargL₀]; exact hl₀
  have hL₂ : lFun (c * v₂ α) ≠ 0 := by rw [hargL₂]; exact hl₂
  have hL₃ : lFun (c * v₃ α) ≠ 0 := by rw [hargL₃]; exact hl₃

  have hWplus0 : ((α + 2 / γ + α₂ + α₃ - 2 * Q γ) / 2) = v₀p α := by
    dsimp [v₀p, d₀, c]
    push_cast
    ring
  have hWminus0 : ((α - 2 / γ + α₂ + α₃ - 2 * Q γ) / 2) = v₀ α := by
    dsimp [v₀, d₀, c]
    push_cast
    ring
  have hUplus1 : ((α + 2 / γ + α₂ + α₃) / 2 - (α + 2 / γ)) = v₁ α := by
    dsimp [v₁, d₁, c]
    push_cast
    ring
  have hUminus1 : ((α - 2 / γ + α₂ + α₃) / 2 - (α - 2 / γ)) = v₁p α := by
    dsimp [v₁p, d₁, c]
    push_cast
    ring
  have hUplus2 : ((α + 2 / γ + α₂ + α₃) / 2 - α₂) = v₂p α := by
    dsimp [v₂p, d₂, c]
    push_cast
    ring
  have hUminus2 : ((α - 2 / γ + α₂ + α₃) / 2 - α₂) = v₂ α := by
    dsimp [v₂, d₂, c]
    push_cast
    ring
  have hUplus3 : ((α + 2 / γ + α₂ + α₃) / 2 - α₃) = v₃p α := by
    dsimp [v₃p, d₃, c]
    push_cast
    ring
  have hUminus3 : ((α - 2 / γ + α₂ + α₃) / 2 - α₃) = v₃ α := by
    dsimp [v₃, d₃, c]
    push_cast
    ring
  have hCoeffArg₁ : c / 2 * ((α + α₂ + α₃) - 2 * α - c) = c * v₁ α := by
    dsimp [v₁, d₁]
    ring
  have hCoeffArg₀ : c / 2 * ((α + α₂ + α₃) - c - 2 * (Q γ : ℂ)) = c * v₀ α := by
    dsimp [v₀, d₀]
    ring
  have hCoeffArg₂ : c / 2 * ((α + α₂ + α₃) - 2 * α₂ - c) = c * v₂ α := by
    dsimp [v₂, d₂]
    ring
  have hCoeffArg₃ : c / 2 * ((α + α₂ + α₃) - 2 * α₃ - c) = c * v₃ α := by
    dsimp [v₃, d₃]
    ring
  have hcoeff : shiftCoeffA γ (2 / γ) α α₂ α₃ =
      lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α) /
        (lFun (c * v₀ α) * lFun (c * v₃ α) * lFun (c * v₂ α)) := by
    have hcsq : c ^ 2 = r := by
      rw [hcCast, hrCast]
      push_cast <;> ring
    unfold shiftCoeffA
    rw [← hcComplex]
    rw [show -c ^ 2 = -r by rw [hcsq]]
    rw [show c * α - c ^ 2 = c * (α - c) by ring]
    rw [hCoeffArg₁, hCoeffArg₀, hCoeffArg₃, hCoeffArg₂]
  have hscalar : Tc ^ pplus α * k α * k (α - c) * k (v₁ α) =
      -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α α₂ α₃ *
        Tc ^ pminus α * k (v₀ α) * k (v₂ α) * k (v₃ α) := by
    have hmul (a x y z : ℂ) : a * k x * k y * k z =
        a * (lFun (c * x) * lFun (c * y) * lFun (c * z)) *
          s ^ ((4 / (γ : ℂ) * x - 1) + (4 / (γ : ℂ) * y - 1) + (4 / (γ : ℂ) * z - 1)) := by
      dsimp [k]
      rw [Complex.cpow_add _ _ hs, Complex.cpow_add _ _ hs]
      ring
    have hExp : (4 / (γ : ℂ) * α - 1) +
        (4 / (γ : ℂ) * (α - c) - 1) + (4 / (γ : ℂ) * v₁ α - 1) =
        ((4 / (γ : ℂ) * v₀ α - 1) +
          (4 / (γ : ℂ) * v₂ α - 1) + (4 / (γ : ℂ) * v₃ α - 1)) +
          (4 * (Q γ : ℂ) / γ) := by
      ring
    rw [hpow α, hcoeff, hmul, hmul, hExp, Complex.cpow_add _ _ hs]
    have hden : (Real.pi : ℂ) * dualMu γ μ ≠ 0 := by
      rw [dualMu]
      have hpi  := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hbasepow : ((dozzBase γ μ : ℝ) : ℂ) ^ r ≠ 0 := by
        apply Complex.cpow_ne_zero_iff.mpr
        exact Or.inl hbaseNe
      positivity
    have hbaseDiv : s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) * (Real.pi : ℂ) / Tc ^ r =
        -lFun (-r) / dualMu γ μ := by
      have hTcPow : Tc ^ r ≠ 0 := by
        apply Complex.cpow_ne_zero_iff.mpr
        exact Or.inl hTc
      have hh : Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) =
          s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) := by
        rw [← hScpow]
        exact hbaseId
      have hh' := congrArg (fun z : ℂ => z * (Real.pi : ℂ)) hh
      apply (div_eq_iff hTcPow).2
      calc
        s ^ ((γ : ℂ)⁻¹ * (Q γ : ℂ) * 4) * (Real.pi : ℂ) =
            Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) * (Real.pi : ℂ) := hh'.symm
        _ = (-lFun (-r) / dualMu γ μ) * Tc ^ r := by
          field_simp [hden]
    field_simp [hden, hL₀, hL₂, hL₃]
    linear_combination (norm := ring_nf) (Tc ^ pminus α *
      (lFun (c * α) * lFun (c * (α - c)) * lFun (c * v₁ α)) *
      s ^ ((4 / (γ : ℂ) * v₀ α - 1) + (4 / (γ : ℂ) * v₂ α - 1) +
        (4 / (γ : ℂ) * v₃ α - 1))) * hbaseDiv
    simp [hγc] <;> ring
  have hpowplus : Tc ^ pplus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α + 2 / γ + α₂ + α₃)) / γ) := by
    simp [pplus, Tc, T, hcComplex]
  have hpowminus : Tc ^ pminus α =
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^
        ((2 * Q γ - (α - 2 / γ + α₂ + α₃)) / γ) := by
    simp [pminus, Tc, T, hcComplex]
  unfold dozzFormula
  rw [← hpowplus, ← hpowminus]
  rw [hWplus0, hWminus0, hUplus1, hUminus1,
    hUplus2, hUminus2, hUplus3, hUminus3]
  rw [hv₀p, hv₁p, hv₂p, hv₃p]
  rw [← mul_div_assoc]
  rw [div_eq_div_iff hdenPlus hdenMinus]
  rw [show α + 2 / γ = α + c by rw [hcComplex], hαm α,
    hnum, hu₀', hu₁', hu₂', hu₃']
  linear_combination
    (deriv U 0 * U (α - c) * U α₂ * U α₃ *
      U (v₀ α) * U (v₁ α) * U (v₂ α) * U (v₃ α)) * hscalar

end DOZZ.Proofs
