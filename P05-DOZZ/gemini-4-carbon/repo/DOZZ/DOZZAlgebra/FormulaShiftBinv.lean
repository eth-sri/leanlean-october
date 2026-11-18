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

/-- The DOZZ formula shift by `γ/2`, proved directly on a codiscrete finite locus. -/
theorem dozzFormula_shift_binv {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + 2 / γ) α₂ α₃ =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - 2 / γ) α₂ α₃ := by
  let c : ℂ := ((2 / γ : ℝ) : ℂ)
  let s : ℂ := ((γ / 2 : ℝ) : ℂ)
  let rR : ℝ := 4 / γ ^ 2
  let r : ℂ := (rR : ℂ)
  let T : ℝ := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc : ℂ := (T : ℂ)
  let k (z : ℂ) : ℂ := lFun (c * z) * s ^ (4 / (γ : ℂ) * z - 1)
  have hγc := Complex.ofReal_ne_zero.2 hγ.ne'
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hcC : c = 2 / (γ : ℂ) := by dsimp [c]; push_cast; rfl
  have hsR : 0 < γ / 2 := half_pos hγ
  have hs : s ≠ 0 := Complex.ofReal_ne_zero.2 hsR.ne'
  have hbase : 0 < dozzBase γ μ := dozzBase_pos hγ hγ2 hμ
  have hTpos : 0 < T := mul_pos hbase (Real.rpow_pos_of_pos hsR _)
  have hTc : Tc ≠ 0 := Complex.ofReal_ne_zero.2 hTpos.ne'
  have hrpos : 0 < rR := by dsimp [rR]; positivity
  have hrne0 : r ≠ 0 := Complex.ofReal_ne_zero.2 hrpos.ne'
  have hΓr : Complex.Gamma r ≠ 0 := by
    dsimp [r]; rw [Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hrpos).ne'
  have hΓnegr : Complex.Gamma (-r) ≠ 0 := Complex.Gamma_ne_zero fun n hn =>
    hγk n (neg_inj.1 (by dsimp [r, rR] at hn; exact_mod_cast hn))
  have hLr : lFun r ≠ 0 := div_ne_zero hΓr (Complex.Gamma_ne_zero fun n hn =>
    hγk (n + 1) (by push_cast; linarith [show 1 - 4 / γ ^ 2 = -(n : ℝ) by dsimp [r, rR] at hn; exact_mod_cast hn]))
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hDpowC : ((dozzBase γ μ : ℝ) : ℂ) ^ r ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hbase.ne'))
  have hden_pi : (Real.pi : ℂ) * dualMu γ μ ≠ 0 :=
    mul_ne_zero hpi (div_ne_zero hDpowC (mul_ne_zero hpi hLr))
  have hbaseDiv : s ^ (4 * (Q γ : ℂ) / (γ : ℂ)) * (Real.pi : ℂ) / Tc ^ r = -lFun (-r) / dualMu γ μ := by
    have hTcPow : Tc ^ r ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hTc)
    have hTpow : Tc ^ r = ((dozzBase γ μ : ℝ) : ℂ) ^ r * (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [show Tc = (T : ℂ) from rfl, show r = (rR : ℂ) from rfl, ← Complex.ofReal_cpow hTpos.le,
        ← Complex.ofReal_cpow hbase.le, ← Complex.ofReal_mul]
      congr 1; dsimp [T]
      rw [Real.mul_rpow hbase.le (Real.rpow_nonneg hsR.le _), ← Real.rpow_mul hsR.le, mul_comm (2 - _)]
    have hprod : -(r ^ 2 * lFun (-r) * lFun r) = 1 := by
      rw [show -(r ^ 2 * lFun (-r) * lFun r) = r ^ 2 * -(lFun r * lFun (-r)) by ring,
        lFun_mul_neg hrne0 hΓr hΓnegr]
      field_simp [hrne0]
    have hcoef : ((dozzBase γ μ : ℝ) : ℂ) ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) = 1 / r ^ 2 := by
      unfold dualMu
      change ((dozzBase γ μ : ℝ) : ℂ) ^ r * (-lFun (-r) / ((Real.pi : ℂ) * (((dozzBase γ μ : ℝ) : ℂ) ^ r / ((Real.pi : ℂ) * lFun r)))) = 1 / r ^ 2
      field_simp [hpi, hLr, hDpowC]; exact hprod
    have hscal : ((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) * (1 / rR ^ 2) = (γ / 2) ^ (4 * Q γ / γ) := by
      have hg4 : (γ / 2) ^ (4 : ℝ) = 1 / rR ^ 2 := (Real.rpow_natCast _ 4).trans (by dsimp [rR]; field_simp [hγ.ne']; ring)
      rw [← hg4, ← Real.rpow_add hsR]; congr 1; dsimp [rR]; unfold Q; field_simp [hγ.ne']; ring
    have hId : Tc ^ r * (-(lFun (-r)) / (Real.pi * dualMu γ μ)) = s ^ (4 * (Q γ : ℂ) / (γ : ℂ)) := by
      calc Tc ^ r * (-lFun (-r) / (Real.pi * dualMu γ μ))
        _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) *
            (((dozzBase γ μ : ℝ) : ℂ) ^ r * (-lFun (-r) / (Real.pi * dualMu γ μ))) := by rw [hTpow]; ring
        _ = (((γ / 2) ^ (rR * (2 - γ ^ 2 / 2)) : ℝ) : ℂ) * ((1 / rR ^ 2 : ℝ) : ℂ) := by
            rw [hcoef]; congr 1; dsimp [r]; push_cast; rfl
        _ = s ^ (4 * (Q γ : ℂ) / (γ : ℂ)) := by
            rw [← Complex.ofReal_mul, hscal, Complex.ofReal_cpow hsR.le, show s = ((γ / 2 : ℝ) : ℂ) from rfl]
            congr 1; push_cast; rfl
    rw [div_eq_iff hTcPow]
    have hmul := congrArg (· * (Real.pi : ℂ)) hId.symm
    refine hmul.trans ?_
    field_simp [hden_pi]
  let sgn (i : Fin 4) : ℂ := if i = 1 then -1 / 2 else 1 / 2
  let d (i : Fin 4) : ℂ :=
    if i = 0 then (α₂ + α₃ - c - 2 * (Q γ : ℂ)) / 2
    else if i = 1 then (α₂ + α₃ - c) / 2
    else if i = 2 then (-α₂ + α₃ - c) / 2
    else (α₂ - α₃ - c) / 2
  let v (i : Fin 4) (α : ℂ) : ℂ := sgn i * α + d i
  have hsgn_ne (i : Fin 4) : sgn i ≠ 0 := by fin_cases i <;> norm_num [sgn]
  have hcsgn_ne (i : Fin 4) : c * sgn i ≠ 0 := mul_ne_zero hc (hsgn_ne i)
  have hall_v : ∀ᶠ α in codiscrete ℂ, ∀ i : Fin 4,
      (∀ n : ℕ, (c * sgn i) * α + c * d i ≠ -(n : ℂ)) ∧
      U (v i α) ≠ 0 ∧ U (v i α + c) ≠ 0 ∧ lFun ((c * sgn i) * α + c * d i) ≠ 0 := by
    rw [eventually_all]
    intro i
    filter_upwards [eventually_affine_ne_neg_nat (hcsgn_ne i),
      eventually_upsilon_affine_ne_zero hγ hU (c := sgn i) (d := d i) (hsgn_ne i),
      eventually_upsilon_affine_ne_zero hγ hU (c := sgn i) (d := d i + c) (hsgn_ne i),
      eventually_affine_lFun_ne_zero (hcsgn_ne i)] with α hp hu hup hl
    exact ⟨hp, hu, by simpa [v, add_assoc] using hup, hl⟩
  filter_upwards [eventually_affine_ne_neg_nat (c := c) (d := 0) hc,
    eventually_affine_ne_neg_nat (c := c) (d := -c ^ 2) hc, hall_v] with α hpa hpam hv
  have hshiftU {z : ℂ} (hz : ∀ n : ℕ, c * z ≠ -(n : ℂ)) : U (z + c) = k z * U z := by
    simpa [k, hcC, s] using IsUpsilon.shift_binv hγ hγ2 hU z (by simpa [hcC] using hz)
  have hnum : U (α + c) = k α * k (α - c) * U (α - c) := by
    rw [hshiftU (by simpa using hpa), show U α = U (α - c + c) by congr 1; ring,
      hshiftU (fun n hn => hpam n (by linear_combination hn)), ← mul_assoc]
  have huv (i : Fin 4) : U (v i α + c) = k (v i α) * U (v i α) :=
    hshiftU fun n hn => (hv i).1 n (by dsimp [v] at hn; linear_combination hn)
  have hLv (i : Fin 4) : lFun (c * v i α) ≠ 0 := by
    simpa [v, mul_add, mul_assoc] using (hv i).2.2.2
  have hdenPlus : U (v 0 α + c) * U (v 1 α) * U (v 2 α + c) * U (v 3 α + c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hv 0).2.2.1 (hv 1).2.1) (hv 2).2.2.1) (hv 3).2.2.1
  have hdenMinus : U (v 0 α) * U (v 1 α + c) * U (v 2 α) * U (v 3 α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hv 0).2.1 (hv 1).2.2.1) (hv 2).2.1) (hv 3).2.1
  let pplus := (2 * (Q γ : ℂ) - (α + c + α₂ + α₃)) / (γ : ℂ)
  let pminus := (2 * (Q γ : ℂ) - (α - c + α₂ + α₃)) / (γ : ℂ)
  have hpow : Tc ^ pplus = Tc ^ pminus / Tc ^ r := by
    rw [show pplus = pminus - r by dsimp [pplus, pminus, c, r, rR]; push_cast; field_simp [hγc]; ring,
      Complex.cpow_sub _ _ hTc]
  have hv0 : v 0 α = (α + α₂ + α₃ - c - 2 * (Q γ : ℂ)) / 2 := by simp [v, sgn, d]; ring
  have hv1 : v 1 α = (-α + α₂ + α₃ - c) / 2 := by simp [v, sgn, d]; ring
  have hv2 : v 2 α = (α - α₂ + α₃ - c) / 2 := by simp [v, sgn, d]; ring
  have hv3 : v 3 α = (α + α₂ - α₃ - c) / 2 := by simp [v, sgn, d]; ring
  have hcoeff : shiftCoeffA γ c α α₂ α₃ =
      lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v 1 α) /
        (lFun (c * v 0 α) * lFun (c * v 3 α) * lFun (c * v 2 α)) := by
    unfold shiftCoeffA
    rw [show -c ^ 2 = -r by dsimp [c, r, rR]; push_cast; field_simp [hγ.ne']; ring,
      show c * α - c ^ 2 = c * (α - c) by ring,
      show c / 2 * (α + α₂ + α₃ - 2 * α - c) = c * v 1 α by rw [hv1]; ring,
      show c / 2 * (α + α₂ + α₃ - c - 2 * (Q γ : ℂ)) = c * v 0 α by rw [hv0]; ring,
      show c / 2 * (α + α₂ + α₃ - 2 * α₃ - c) = c * v 3 α by rw [hv3]; ring,
      show c / 2 * (α + α₂ + α₃ - 2 * α₂ - c) = c * v 2 α by rw [hv2]; ring]
  have hscalar : Tc ^ pplus * k α * k (α - c) * k (v 1 α) =
      -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ c α α₂ α₃ *
        Tc ^ pminus * k (v 0 α) * k (v 2 α) * k (v 3 α) := by
    have hExp : (4 / (γ : ℂ) * α - 1) + (4 / (γ : ℂ) * (α - c) - 1) + (4 / (γ : ℂ) * v 1 α - 1) =
        ((4 / (γ : ℂ) * v 0 α - 1) + (4 / (γ : ℂ) * v 2 α - 1) + (4 / (γ : ℂ) * v 3 α - 1)) +
          4 * (Q γ : ℂ) / (γ : ℂ) := by
      rw [hv0, hv1, hv2, hv3]; dsimp only [c]; push_cast; unfold Q; field_simp [hγc]; ring
    rw [hpow, hcoeff]; dsimp only [k]
    have hpL : s ^ (4 / (γ : ℂ) * α - 1) * s ^ (4 / (γ : ℂ) * (α - c) - 1) * s ^ (4 / (γ : ℂ) * v 1 α - 1) =
        s ^ ((4 / (γ : ℂ) * v 0 α - 1) + (4 / (γ : ℂ) * v 2 α - 1) + (4 / (γ : ℂ) * v 3 α - 1)) *
          s ^ (4 * (Q γ : ℂ) / (γ : ℂ)) := by
      rw [← Complex.cpow_add _ _ hs, ← Complex.cpow_add _ _ hs, hExp, Complex.cpow_add _ _ hs]
    have hpR : s ^ (4 / (γ : ℂ) * v 0 α - 1) * s ^ (4 / (γ : ℂ) * v 2 α - 1) * s ^ (4 / (γ : ℂ) * v 3 α - 1) =
        s ^ ((4 / (γ : ℂ) * v 0 α - 1) + (4 / (γ : ℂ) * v 2 α - 1) + (4 / (γ : ℂ) * v 3 α - 1)) := by
      rw [← Complex.cpow_add _ _ hs, ← Complex.cpow_add _ _ hs]
    generalize s ^ ((4 / (γ : ℂ) * v 0 α - 1) + (4 / (γ : ℂ) * v 2 α - 1) + (4 / (γ : ℂ) * v 3 α - 1)) = S₀ at hpL hpR
    calc Tc ^ pminus / Tc ^ r * (lFun (c * α) * s ^ (4 / (γ : ℂ) * α - 1)) *
          (lFun (c * (α - c)) * s ^ (4 / (γ : ℂ) * (α - c) - 1)) * (lFun (c * v 1 α) * s ^ (4 / (γ : ℂ) * v 1 α - 1))
      _ = Tc ^ pminus * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v 1 α) *
          (s ^ (4 / (γ : ℂ) * α - 1) * s ^ (4 / (γ : ℂ) * (α - c) - 1) * s ^ (4 / (γ : ℂ) * v 1 α - 1)) / Tc ^ r := by ring
      _ = Tc ^ pminus * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v 1 α) * S₀ *
          (s ^ (4 * (Q γ : ℂ) / (γ : ℂ)) * (Real.pi : ℂ) / Tc ^ r) / (Real.pi : ℂ) := by
          rw [hpL]; field_simp [hpi]
      _ = Tc ^ pminus * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v 1 α) * S₀ *
          (-lFun (-r) / dualMu γ μ) / (Real.pi : ℂ) := by rw [hbaseDiv]
      _ = -(1 / (Real.pi * dualMu γ μ)) *
          (lFun (-r) * lFun (c * α) * lFun (c * (α - c)) * lFun (c * v 1 α) /
            (lFun (c * v 0 α) * lFun (c * v 3 α) * lFun (c * v 2 α))) * Tc ^ pminus *
          (lFun (c * v 0 α) * lFun (c * v 2 α) * lFun (c * v 3 α)) * S₀ := by
          have hLv0 := hLv 0; have hLv2 := hLv 2; have hLv3 := hLv 3
          field_simp [hpi, hden_pi, hLv0, hLv2, hLv3]
      _ = _ := by rw [← hpR]; ring
  unfold dozzFormula
  simp only [show ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) = Tc from rfl, ← hcC]
  rw [show (α + c + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2 = v 0 α + c by rw [hv0]; ring,
    show (α - c + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2 = v 0 α by rw [hv0]; ring,
    show (α + c + α₂ + α₃) / 2 - (α + c) = v 1 α by rw [hv1]; ring,
    show (α - c + α₂ + α₃) / 2 - (α - c) = v 1 α + c by rw [hv1]; ring,
    show (α + c + α₂ + α₃) / 2 - α₂ = v 2 α + c by rw [hv2]; ring,
    show (α - c + α₂ + α₃) / 2 - α₂ = v 2 α by rw [hv2]; ring,
    show (α + c + α₂ + α₃) / 2 - α₃ = v 3 α + c by rw [hv3]; ring,
    show (α - c + α₂ + α₃) / 2 - α₃ = v 3 α by rw [hv3]; ring,
    ← mul_div_assoc, div_eq_div_iff hdenPlus hdenMinus,
    hnum, huv 0, huv 1, huv 2, huv 3]
  linear_combination (deriv U 0 * U (α - c) * U α₂ * U α₃ * U (v 0 α) * U (v 1 α) * U (v 2 α) * U (v 3 α)) * hscalar

end DOZZ.Proofs
