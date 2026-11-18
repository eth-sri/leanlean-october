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
theorem dozzFormula_shift_b {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + γ / 2) α₂ α₃ =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - γ / 2) α₂ α₃ := by
  let b : ℂ := (γ : ℂ) / 2
  let q : ℂ := b ^ 2
  let T : ℝ := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc : ℂ := (T : ℂ)
  let k (z : ℂ) : ℂ := lFun (b * z) * b ^ (1 - (γ : ℂ) * z)
  have hbR : 0 < γ / 2 := half_pos hγ
  have hγc : (γ : ℂ) ≠ 0 := mod_cast hγ.ne'
  have hb : b ≠ 0 := div_ne_zero hγc two_ne_zero
  have hbCast : b = ((γ / 2 : ℝ) : ℂ) := by dsimp [b]; push_cast; rfl
  have hTc : Tc ≠ 0 := Complex.ofReal_ne_zero.2 (mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos hbR _)).ne'
  have hqeq : q = ((γ ^ 2 / 4 : ℝ) : ℂ) := by dsimp [q, b]; push_cast; ring
  have hqne : q ≠ 0 := pow_ne_zero 2 hb
  have hΓq : Complex.Gamma q ≠ 0 := by
    rw [hqeq, Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hΓ1q : Complex.Gamma (1 - q) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.one_re, hqeq, Complex.ofReal_re]; nlinarith)
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := fun h0 =>
    hΓ1q (by rw [show 1 - q = -q + 1 by ring, Complex.Gamma_add_one (-q) (neg_ne_zero.2 hqne), h0, mul_zero])
  have hbaseDiv : (Real.pi * μ : ℂ) / b ^ ((γ * Q γ : ℝ) : ℂ) = -(Tc * lFun (-q)) := by
    have hB : (dozzBase γ μ : ℂ) = (Real.pi * μ : ℂ) * lFun q := by
      have hLq : lFun q = ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
        rw [hqeq, show ((γ ^ 2 / 4 : ℝ) : ℂ) = (γ : ℂ) ^ 2 / 4 by push_cast; ring]
        exact lFun_gammaSq_real γ
      unfold dozzBase; rw [lFun_gammaSq_real, hLq]; simp only [Complex.ofReal_re]; push_cast; ring
    have hTcEq : Tc = (dozzBase γ μ : ℂ) * b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) := by
      dsimp [Tc, T]; rw [Complex.ofReal_mul, Complex.ofReal_cpow hbR.le, ← hbCast]
    have hsum : ((2 - γ ^ 2 / 2 : ℝ) : ℂ) + ((γ * Q γ : ℝ) : ℂ) = 4 :=
      mod_cast (by unfold Q; field_simp [hγ.ne']; ring : 2 - γ ^ 2 / 2 + γ * Q γ = 4)
    have hId : Tc * b ^ ((γ * Q γ : ℝ) : ℂ) * (-lFun (-q)) = (Real.pi * μ : ℂ) := by
      calc Tc * b ^ ((γ * Q γ : ℝ) : ℂ) * (-lFun (-q))
        _ = (Real.pi * μ : ℂ) * lFun q *
            (b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) * b ^ ((γ * Q γ : ℝ) : ℂ)) * (-lFun (-q)) := by
            rw [hTcEq, hB]; ring
        _ = (Real.pi * μ : ℂ) * (-(lFun q * lFun (-q)) * q ^ 2) := by
            rw [← Complex.cpow_add _ _ hb, hsum, Complex.cpow_ofNat]; dsimp [q]; ring
        _ = (Real.pi * μ : ℂ) := by rw [lFun_mul_neg hqne hΓq hΓnegq]; field_simp [hqne]
    rw [div_eq_iff (Complex.cpow_ne_zero_iff.2 (Or.inl hb)), ← hId]; ring
  let sgn (i : Fin 4) : ℂ := if i = 1 then -1 / 2 else 1 / 2
  let d (i : Fin 4) : ℂ :=
    if i = 0 then (α₂ + α₃ - b - 2 * (Q γ : ℂ)) / 2
    else if i = 1 then (α₂ + α₃ - b) / 2
    else if i = 2 then (-α₂ + α₃ - b) / 2
    else (α₂ - α₃ - b) / 2
  let v (i : Fin 4) (α : ℂ) : ℂ := sgn i * α + d i
  have hsgn_ne (i : Fin 4) : sgn i ≠ 0 := by fin_cases i <;> norm_num [sgn]
  have hbsgn_ne (i : Fin 4) : b * sgn i ≠ 0 := mul_ne_zero hb (hsgn_ne i)
  have hall_v : ∀ᶠ α in codiscrete ℂ, ∀ i : Fin 4,
      (∀ n : ℕ, (b * sgn i) * α + b * d i ≠ -(n : ℂ)) ∧
      U (v i α) ≠ 0 ∧ U (v i α + b) ≠ 0 ∧ lFun ((b * sgn i) * α + b * d i) ≠ 0 := by
    rw [eventually_all]; intro i
    filter_upwards [eventually_affine_ne_neg_nat (hbsgn_ne i),
      eventually_upsilon_affine_ne_zero hγ hU (c := sgn i) (d := d i) (hsgn_ne i),
      eventually_upsilon_affine_ne_zero hγ hU (c := sgn i) (d := d i + b) (hsgn_ne i),
      eventually_affine_lFun_ne_zero (hbsgn_ne i)] with α hp hu hup hl
    exact ⟨hp, hu, by simpa [v, add_assoc] using hup, hl⟩
  filter_upwards [eventually_affine_ne_neg_nat (c := b) (d := 0) hb,
    eventually_affine_ne_neg_nat (c := b) (d := -b ^ 2) hb, hall_v] with α hpa hpam hv
  have hshiftU {z : ℂ} (hz : ∀ n : ℕ, b * z ≠ -(n : ℂ)) : U (z + b) = k z * U z := by
    simpa [k, b, hbCast.symm] using IsUpsilon.shift_b hγ hγ2 hU z hz
  have hnum : U (α + b) = k α * k (α - b) * U (α - b) := by
    rw [hshiftU (by simpa using hpa), show U α = U (α - b + b) by congr 1; ring,
      hshiftU (fun n hn => hpam n (by linear_combination hn)), ← mul_assoc]
  have huv (i : Fin 4) : U (v i α + b) = k (v i α) * U (v i α) :=
    hshiftU fun n hn => (hv i).1 n (by dsimp [v] at hn; linear_combination hn)
  have hLv (i : Fin 4) : lFun (b * v i α) ≠ 0 := by simpa [v, mul_add, mul_assoc] using (hv i).2.2.2
  have hdenPlus : U (v 0 α + b) * U (v 1 α) * U (v 2 α + b) * U (v 3 α + b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hv 0).2.2.1 (hv 1).2.1) (hv 2).2.2.1) (hv 3).2.2.1
  have hdenMinus : U (v 0 α) * U (v 1 α + b) * U (v 2 α) * U (v 3 α) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hv 0).2.1 (hv 1).2.2.1) (hv 2).2.1) (hv 3).2.1
  let pplus := (2 * (Q γ : ℂ) - (α + b + α₂ + α₃)) / (γ : ℂ)
  let pminus := (2 * (Q γ : ℂ) - (α - b + α₂ + α₃)) / (γ : ℂ)
  have hpow : Tc ^ pplus = Tc ^ pminus / Tc := by
    rw [show pplus = pminus - 1 by dsimp [pplus, pminus, b]; field_simp [hγc]; ring,
      Complex.cpow_sub _ _ hTc, Complex.cpow_one]
  have hv0 : v 0 α = (α + α₂ + α₃ - b - 2 * (Q γ : ℂ)) / 2 := by simp [v, sgn, d]; ring
  have hv1 : v 1 α = (-α + α₂ + α₃ - b) / 2 := by simp [v, sgn, d]; ring
  have hv2 : v 2 α = (α - α₂ + α₃ - b) / 2 := by simp [v, sgn, d]; ring
  have hv3 : v 3 α = (α + α₂ - α₃ - b) / 2 := by simp [v, sgn, d]; ring
  have hcoeff : shiftCoeffA γ b α α₂ α₃ =
      lFun (-q) * lFun (b * α) * lFun (b * (α - b)) * lFun (b * v 1 α) /
        (lFun (b * v 0 α) * lFun (b * v 3 α) * lFun (b * v 2 α)) := by
    unfold shiftCoeffA
    rw [show -b ^ 2 = -q from rfl, show b * α - b ^ 2 = b * (α - b) by ring,
      show b / 2 * (α + α₂ + α₃ - 2 * α - b) = b * v 1 α by rw [hv1]; ring,
      show b / 2 * (α + α₂ + α₃ - b - 2 * (Q γ : ℂ)) = b * v 0 α by rw [hv0]; ring,
      show b / 2 * (α + α₂ + α₃ - 2 * α₃ - b) = b * v 3 α by rw [hv3]; ring,
      show b / 2 * (α + α₂ + α₃ - 2 * α₂ - b) = b * v 2 α by rw [hv2]; ring]
  have hscalar : Tc ^ pplus * k α * k (α - b) * k (v 1 α) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ b α α₂ α₃ *
        Tc ^ pminus * k (v 0 α) * k (v 2 α) * k (v 3 α) := by
    have hExp : (1 - (γ : ℂ) * α) + (1 - (γ : ℂ) * (α - b)) + (1 - (γ : ℂ) * v 1 α) =
        ((1 - (γ : ℂ) * v 0 α) + (1 - (γ : ℂ) * v 2 α) + (1 - (γ : ℂ) * v 3 α)) -
          ((γ * Q γ : ℝ) : ℂ) := by
      rw [hv0, hv1, hv2, hv3]; dsimp only [b]; push_cast; unfold Q; field_simp [hγc]; ring
    rw [hpow, hcoeff]; dsimp only [k]
    have hpL : b ^ (1 - (γ : ℂ) * α) * b ^ (1 - (γ : ℂ) * (α - b)) * b ^ (1 - (γ : ℂ) * v 1 α) =
        b ^ ((1 - (γ : ℂ) * v 0 α) + (1 - (γ : ℂ) * v 2 α) + (1 - (γ : ℂ) * v 3 α)) /
          b ^ ((γ * Q γ : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hb, ← Complex.cpow_add _ _ hb, hExp, Complex.cpow_sub _ _ hb]
    have hpR : b ^ (1 - (γ : ℂ) * v 0 α) * b ^ (1 - (γ : ℂ) * v 2 α) * b ^ (1 - (γ : ℂ) * v 3 α) =
        b ^ ((1 - (γ : ℂ) * v 0 α) + (1 - (γ : ℂ) * v 2 α) + (1 - (γ : ℂ) * v 3 α)) := by
      rw [← Complex.cpow_add _ _ hb, ← Complex.cpow_add _ _ hb]
    generalize b ^ ((1 - (γ : ℂ) * v 0 α) + (1 - (γ : ℂ) * v 2 α) + (1 - (γ : ℂ) * v 3 α)) = B₀ at hpL hpR
    have hLv0 := hLv 0; have hLv2 := hLv 2; have hLv3 := hLv 3
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hμc := Complex.ofReal_ne_zero.2 hμ.ne'
    calc Tc ^ pminus / Tc * (lFun (b * α) * b ^ (1 - (γ : ℂ) * α)) *
          (lFun (b * (α - b)) * b ^ (1 - (γ : ℂ) * (α - b))) * (lFun (b * v 1 α) * b ^ (1 - (γ : ℂ) * v 1 α))
      _ = Tc ^ pminus / Tc * (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v 1 α) * B₀) *
          ((Real.pi * μ : ℂ) / b ^ ((γ * Q γ : ℝ) : ℂ)) / (Real.pi * μ : ℂ) := by
          rw [show Tc ^ pminus / Tc * (lFun (b * α) * b ^ (1 - (γ : ℂ) * α)) *
                (lFun (b * (α - b)) * b ^ (1 - (γ : ℂ) * (α - b))) *
                (lFun (b * v 1 α) * b ^ (1 - (γ : ℂ) * v 1 α)) =
              Tc ^ pminus / Tc * (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v 1 α)) *
                (b ^ (1 - (γ : ℂ) * α) * b ^ (1 - (γ : ℂ) * (α - b)) * b ^ (1 - (γ : ℂ) * v 1 α)) by ring,
            hpL]
          field_simp [hTc, hpi, hμc]
      _ = Tc ^ pminus / Tc * (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v 1 α) * B₀) *
          (-(Tc * lFun (-q))) / (Real.pi * μ : ℂ) := by rw [hbaseDiv]
      _ = -(1 / (Real.pi * μ)) *
          (lFun (-q) * lFun (b * α) * lFun (b * (α - b)) * lFun (b * v 1 α) /
            (lFun (b * v 0 α) * lFun (b * v 3 α) * lFun (b * v 2 α))) * Tc ^ pminus *
          (lFun (b * v 0 α) * lFun (b * v 2 α) * lFun (b * v 3 α)) * B₀ := by
          field_simp [hTc, hpi, hμc, hLv0, hLv2, hLv3]
      _ = _ := by rw [← hpR]; ring
  unfold dozzFormula
  simp only [show ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) = Tc from rfl,
    show (γ : ℂ) / 2 = b from rfl]
  rw [show (α + b + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2 = v 0 α + b by rw [hv0]; ring,
    show (α - b + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2 = v 0 α by rw [hv0]; ring,
    show (α + b + α₂ + α₃) / 2 - (α + b) = v 1 α by rw [hv1]; ring,
    show (α - b + α₂ + α₃) / 2 - (α - b) = v 1 α + b by rw [hv1]; ring,
    show (α + b + α₂ + α₃) / 2 - α₂ = v 2 α + b by rw [hv2]; ring,
    show (α - b + α₂ + α₃) / 2 - α₂ = v 2 α by rw [hv2]; ring,
    show (α + b + α₂ + α₃) / 2 - α₃ = v 3 α + b by rw [hv3]; ring,
    show (α - b + α₂ + α₃) / 2 - α₃ = v 3 α by rw [hv3]; ring,
    ← mul_div_assoc, div_eq_div_iff hdenPlus hdenMinus,
    hnum, huv 0, huv 1, huv 2, huv 3]
  linear_combination (deriv U 0 * U (α - b) * U α₂ * U α₃ * U (v 0 α) * U (v 1 α) * U (v 2 α) * U (v 3 α)) * hscalar

end DOZZ.Proofs

end
