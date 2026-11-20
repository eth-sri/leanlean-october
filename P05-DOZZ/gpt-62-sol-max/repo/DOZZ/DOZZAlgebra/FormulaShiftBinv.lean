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
public import DOZZ.DOZZAlgebra.FormulaShiftB

/-!
# The first DOZZ formula shift on its finite generic locus
-/

@[expose] public section

open Complex Filter Set Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

/-- The DOZZ formula shift by `2/γ` on its finite generic locus. -/
theorem dozzFormula_shift_binv {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + 2 / γ) α₂ α₃ =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - 2 / γ) α₂ α₃ := by
  let c : ℂ := 2 / (γ : ℂ)
  let r : ℝ := 4 / γ ^ 2
  let K : ℂ := -(1 / (Real.pi * dualMu γ μ))
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hc : c ≠ 0 := div_ne_zero (by norm_num) hγc
  have hβ : (0 : ℝ) < γ / 2 := by positivity
  have hB := dozzBase_pos hγ hγ2 hμ
  refine dozzFormula_shift_of_upsilon_shift (χ := c) (k₀ := -1) (k₁ := 4 / (γ : ℂ))
    (K := K) hγ hU hc (mul_ne_zero hB.ne' (Real.rpow_pos_of_pos hβ _).ne') ?_ ?_ α₂ α₃
  · intro z hz
    simp only [← sub_eq_add_neg, add_comm (-1 : ℂ)]
    exact IsUpsilon.shift_binv hγ hγ2 hU z hz
  have hr : c ^ 2 = (r : ℂ) := by dsimp [c, r]; push_cast; ring
  have hrp : 0 < r := by dsimp [r]; positivity
  have hΓm : Complex.Gamma (-(r : ℂ)) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n hn => hγk n ?_
    rw [neg_inj] at hn
    exact_mod_cast hn
  have hlr : lFun (r : ℂ) ≠ 0 := by
    refine div_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by rwa [Complex.ofReal_re]))
      (Complex.Gamma_ne_zero fun n hn => hγk (n + 1) ?_)
    have hn' : 1 - r = -(n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  have hl := lFun_mul_neg (Complex.ofReal_ne_zero.mpr hrp.ne')
    (Complex.Gamma_ne_zero_of_re_pos (by rwa [Complex.ofReal_re])) hΓm
  have h := dozzFormula_shift_scalar (r := r) (n := 4) (C := K * lFun (-c ^ 2)) hγ hB (by
    rw [hr, show ((4 : ℝ) : ℂ) = (4 : ℂ) by norm_num, Complex.cpow_ofNat]
    dsimp [K]
    rw [show dualMu γ μ = (dozzBase γ μ : ℂ) ^ (r : ℂ) / (Real.pi * lFun (r : ℂ)) by rfl]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hBn : (dozzBase γ μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
    have hpow : (dozzBase γ μ : ℂ) ^ (r : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hBn)
    calc
      _ = -(lFun (r : ℂ) * lFun (-(r : ℂ))) := by field_simp [hπ, hlr, hpow]
      _ = _ := by rw [hl, ← neg_div, neg_neg]; dsimp [r]; push_cast; field_simp; ring)
  convert h using 2 <;> push_cast <;> dsimp [c, r, Q] <;> push_cast <;> field_simp <;> ring

end DOZZ.Proofs
