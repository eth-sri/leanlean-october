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
theorem dozzFormula_shift_b {U} (hγ : 0 < γ) (hγ2 : γ < 2) {μ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) α₂ α₃ :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + γ / 2) α₂ α₃ =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - γ / 2) α₂ α₃ := by
  let b := (γ : ℂ) / 2
  let d₀ := (α₂ + α₃ - b - 2 * (Q γ : ℂ)) / 2
  let d₁ := (α₂ + α₃ - b) / 2
  let d₂ := (-α₂ + α₃ - b) / 2
  let d₃ := (α₂ - α₃ - b) / 2
  let v₀ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₀
  let v₁ : ℂ → ℂ := fun α => (-1 / 2 : ℂ) * α + d₁
  let v₂ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₂
  let v₃ : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + d₃
  let v₀p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₀ + b)
  let v₁p : ℂ → ℂ := fun α => (-1 / 2 : ℂ) * α + (d₁ + b)
  let v₂p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₂ + b)
  let v₃p : ℂ → ℂ := fun α => (1 / 2 : ℂ) * α + (d₃ + b)
  let k : ℂ → ℂ := fun z => lFun (b * z) * b ^ (1 - (γ : ℂ) * z)
  let T := dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2)
  let Tc := (T : ℂ)
  let q : ℂ := b ^ 2
  have hbR : 0 < γ / 2 := by positivity
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hb : b ≠ 0 := by dsimp [b]; exact div_ne_zero hγc (by norm_num)
  have hbCast : b = ((γ / 2 : ℝ) : ℂ) := by
    dsimp [b]
    push_cast
    ring
  have hTc : Tc ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0 < T by dsimp [T]; exact mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos hbR _)).ne'
  have hqpos : 0 < γ ^ 2 / 4 := by positivity
  have : γ ^ 2 / 4 < 1 := by nlinarith [mul_pos hγ (sub_pos.mpr hγ2)]
  have hqeq : q = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
    dsimp [q, b]
    push_cast
    ring
  have hqne : q ≠ 0 := by
    rw [hqeq]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqpos)
  have hΓ1q : Complex.Gamma (1 - q) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, hqeq, Complex.ofReal_re]
      linarith)
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := by
    intro hzero
    have hrec' : Complex.Gamma (1 - q) = (-q) * Complex.Gamma (-q) := by
      calc
        Complex.Gamma (1 - q) = Complex.Gamma (-q + 1) := by congr 1; ring
        _ = (-q) * Complex.Gamma (-q) := (Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hqne))
    rw [hzero, mul_zero] at hrec'
    exact hΓ1q hrec'
  have hB : (dozzBase γ μ : ℂ) = (Real.pi * μ : ℂ) * lFun q := by
    unfold dozzBase
    rw [lFun_gammaSq_real, (show lFun q = ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) by rw [hqeq, ← (show ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring)]; exact lFun_gammaSq_real γ)]
    simp only [Complex.ofReal_re]
    push_cast
    ring_nf
  have hqpow : b ^ (4 : ℂ) = q ^ 2 := by
    rw [Complex.cpow_ofNat]
    dsimp [q]
    ring
  have hbaseId : Tc * b ^ ((γ * Q γ : ℝ) : ℂ) *
      (-(lFun (-q)) / (Real.pi * μ)) = 1 := by
    calc
      _ = (Real.pi * μ : ℂ) * lFun q *
          (b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) * b ^ ((γ * Q γ : ℝ) : ℂ)) *
            (-(lFun (-q)) / (Real.pi * μ)) := by
        rw [(show Tc = (dozzBase γ μ : ℂ) * b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) by dsimp [Tc, T]; rw [Complex.ofReal_mul, (show ((γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) = b ^ ((2 - γ ^ 2 / 2 : ℝ) : ℂ) by rw [Complex.ofReal_cpow (le_of_lt hbR), ← hbCast])]), hB]
        ring_nf
      _ = (Real.pi * μ : ℂ) * lFun q *
          b ^ (((2 - γ ^ 2 / 2 : ℝ) : ℂ) + ((γ * Q γ : ℝ) : ℂ)) *
            (-(lFun (-q)) / (Real.pi * μ)) := by
        rw [((Complex.cpow_add ((2 - γ ^ 2 / 2 : ℝ) : ℂ) ((γ * Q γ : ℝ) : ℂ) hb).symm)]
      _ = (Real.pi * μ : ℂ) * lFun q * b ^ (4 : ℂ) *
            (-(lFun (-q)) / (Real.pi * μ)) := by rw [(show ((2 - γ ^ 2 / 2 : ℝ) : ℂ) + ((γ * Q γ : ℝ) : ℂ) = 4 by exact_mod_cast (by unfold Q; field_simp [hγ.ne']; ring))]
      _ = (Real.pi * μ : ℂ) * lFun q * q ^ 2 *
            (-(lFun (-q)) / (Real.pi * μ)) := by rw [hqpow]
      _ = -(lFun q * lFun (-q)) * q ^ 2 := by
        field_simp [hμ.ne', Real.pi_ne_zero]
      _ = -(-1 / q ^ 2) * q ^ 2 := by rw [(lFun_mul_neg hqne (by rw [hqeq, Complex.Gamma_ofReal]; exact_mod_cast (Real.Gamma_pos_of_pos hqpos).ne') hΓnegq)]
      _ = 1 := by field_simp [hqne]

  let pplus : ℂ → ℂ := fun α =>
    (2 * (Q γ : ℂ) - (α + b + α₂ + α₃)) / (γ : ℂ)
  let pminus : ℂ → ℂ := fun α =>
    (2 * (Q γ : ℂ) - (α - b + α₂ + α₃)) / (γ : ℂ)
  have hexp : ∀ α : ℂ, pplus α = pminus α - 1 := by
    intro α
    dsimp [pplus, pminus, b]
    field_simp [hγc]
    ring_nf
  have hpow : ∀ α : ℂ, Tc ^ pplus α = Tc ^ pminus α / Tc := by
    intro α
    rw [hexp α, Complex.cpow_sub _ _ hTc]
    simp
  let poleV₀ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₀) (by
    exact div_ne_zero hb (by norm_num))
  let poleV₁ := eventually_affine_ne_neg_nat (c := -b / 2) (d := b * d₁) (by
    exact div_ne_zero (neg_ne_zero.mpr hb) (by norm_num))
  let poleV₂ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₂) (by
    exact div_ne_zero hb (by norm_num))
  let poleV₃ := eventually_affine_ne_neg_nat (c := b / 2) (d := b * d₃) (by
    exact div_ne_zero hb (by norm_num))
  let lnonzeroV₀ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₀) (by
    exact div_ne_zero hb (by norm_num))
  let lnonzeroV₂ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₂) (by
    exact div_ne_zero hb (by norm_num))
  let lnonzeroV₃ := eventually_affine_lFun_ne_zero (c := b / 2) (d := b * d₃) (by
    exact div_ne_zero hb (by norm_num))
  filter_upwards [(eventually_affine_ne_neg_nat (c := b) (d := 0) hb), (eventually_affine_ne_neg_nat (c := b) (d := -b ^ 2) hb), poleV₀, poleV₁, poleV₂, poleV₃,
    (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₀) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₀ + b) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ)) (d := d₁) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (-1 / 2 : ℂ)) (d := d₁ + b) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₂) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₂ + b) (by norm_num)),
    (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₃) (by norm_num)), (eventually_upsilon_affine_ne_zero hγ hU (c := (1 / 2 : ℂ)) (d := d₃ + b) (by norm_num)), lnonzeroV₀, lnonzeroV₂, lnonzeroV₃]
    with α hpa hpam hp₀ hp₁ hp₂ hp₃ hu₀ hu₀p hu₁ hu₁p hu₂ hu₂p hu₃ hu₃p hl₀ hl₂ hl₃
  have hnotAm : ∀ n : ℕ, b * (α - b) ≠ -(n : ℂ) := by
    intro n hn
    apply hpam n
    convert hn using 1
    ring
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
  have hnum : U (α + b) = k α * k (α - b) * U (α - b) := by
    have hsA' : U (α + b) = k α * U α := by simpa [k] using (IsUpsilon.shift_b hγ hγ2 hU α (by simpa using hpa))
    rw [(show U α = k (α - b) * U (α - b) by rw [← (show α - b + ((γ / 2 : ℝ) : ℂ) = α by rw [hbCast]; ring)]; simpa [k, hbCast] using (IsUpsilon.shift_b hγ hγ2 hU (α - b) hnotAm))] at hsA'
    simpa [mul_assoc] using hsA'
  have hv₀p : v₀p α = v₀ α + b := by dsimp [v₀p, v₀]; ring
  have hv₁p : v₁p α = v₁ α + b := by dsimp [v₁p, v₁]; ring
  have hv₂p : v₂p α = v₂ α + b := by dsimp [v₂p, v₂]; ring
  have hv₃p : v₃p α = v₃ α + b := by dsimp [v₃p, v₃]; ring
  have hdenPlus : U (v₀ α + b) * U (v₁ α) * U (v₂ α + b) * U (v₃ α + b) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · have h₀ : U (v₀ α + b) ≠ 0 := by rw [← hv₀p]; exact hu₀p
          exact h₀
        · exact hu₁
      · have h₂ : U (v₂ α + b) ≠ 0 := by rw [← hv₂p]; exact hu₂p
        exact h₂
    · have h₃ : U (v₃ α + b) ≠ 0 := by rw [← hv₃p]; exact hu₃p
      exact h₃
  have hdenMinus : U (v₀ α) * U (v₁ α + b) * U (v₂ α) * U (v₃ α) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact hu₀
        · have h₁ : U (v₁ α + b) ≠ 0 := by rw [← hv₁p]; exact hu₁p
          exact h₁
      · exact hu₂
    · exact hu₃
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
    rw [(show b / 2 * ((α + α₂ + α₃) - 2 * α - b) = b * v₁ α by dsimp [v₁, d₁]; ring), (show b / 2 * ((α + α₂ + α₃) - b - 2 * (Q γ : ℂ)) = b * v₀ α by dsimp [v₀, d₀]; ring), (show b / 2 * ((α + α₂ + α₃) - 2 * α₃ - b) = b * v₃ α by dsimp [v₃, d₃]; ring), (show b / 2 * ((α + α₂ + α₃) - 2 * α₂ - b) = b * v₂ α by dsimp [v₂, d₂]; ring)]
  have hscalar : Tc ^ pplus α * k α * k (α - b) * k (v₁ α) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α α₂ α₃ *
        Tc ^ pminus α * k (v₀ α) * k (v₂ α) * k (v₃ α) := by
    have hExp : (1 - (γ : ℂ) * α) + (1 - (γ : ℂ) * (α - b)) +
        (1 - (γ : ℂ) * v₁ α) =
        ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) +
          (1 - (γ : ℂ) * v₃ α)) - (γ : ℂ) * (Q γ : ℂ) := by
      dsimp [v₀, v₁, v₂, v₃,
        d₀, d₁, d₂, d₃, b]
      unfold Q
      field_simp [hγ.ne']
      ring
    rw [hpow α, hcoeff]
    dsimp [k]
    rw [show Tc ^ pminus α / Tc *
          (lFun (b * α) * b ^ (1 - (γ : ℂ) * α)) *
          (lFun (b * (α - b)) * b ^ (1 - (γ : ℂ) * (α - b))) *
          (lFun (b * v₁ α) * b ^ (1 - (γ : ℂ) * v₁ α)) =
          (Tc ^ pminus α / Tc) *
            (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α)) *
              (b ^ (1 - (γ : ℂ) * α) * b ^ (1 - (γ : ℂ) * (α - b)) *
                b ^ (1 - (γ : ℂ) * v₁ α)) by ring]
    rw [show -(1 / (Real.pi * μ)) *
          (lFun (-q) * lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α) /
            (lFun (b * v₀ α) * lFun (b * v₃ α) * lFun (b * v₂ α))) * Tc ^ pminus α *
          (lFun (b * v₀ α) * b ^ (1 - (γ : ℂ) * v₀ α)) *
          (lFun (b * v₂ α) * b ^ (1 - (γ : ℂ) * v₂ α)) *
          (lFun (b * v₃ α) * b ^ (1 - (γ : ℂ) * v₃ α)) =
          -(1 / (Real.pi * μ)) *
            (lFun (-q) * lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α) /
              (lFun (b * v₀ α) * lFun (b * v₃ α) * lFun (b * v₂ α))) * Tc ^ pminus α *
            (lFun (b * v₀ α) * lFun (b * v₂ α) * lFun (b * v₃ α)) *
              (b ^ (1 - (γ : ℂ) * v₀ α) * b ^ (1 - (γ : ℂ) * v₂ α) *
                b ^ (1 - (γ : ℂ) * v₃ α)) by ring]
    rw [(show b ^ (1 - (γ : ℂ) * α) * b ^ (1 - (γ : ℂ) * (α - b)) * b ^ (1 - (γ : ℂ) * v₁ α) = b ^ ((1 - (γ : ℂ) * α) + (1 - (γ : ℂ) * (α - b)) + (1 - (γ : ℂ) * v₁ α)) by rw [← Complex.cpow_add _ _ hb, ← Complex.cpow_add _ _ hb]), (show b ^ (1 - (γ : ℂ) * v₀ α) * b ^ (1 - (γ : ℂ) * v₂ α) * b ^ (1 - (γ : ℂ) * v₃ α) = b ^ ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) + (1 - (γ : ℂ) * v₃ α)) by rw [← Complex.cpow_add _ _ hb, ← Complex.cpow_add _ _ hb]), hExp, Complex.cpow_sub _ _ hb]
    field_simp [hTc, (show lFun (b * v₀ α) ≠ 0 by rw [(show b * v₀ α = b / 2 * α + b * d₀ by dsimp [v₀]; ring)]; exact hl₀), (show lFun (b * v₂ α) ≠ 0 by rw [(show b * v₂ α = b / 2 * α + b * d₂ by dsimp [v₂]; ring)]; exact hl₂), (show lFun (b * v₃ α) ≠ 0 by rw [(show b * v₃ α = b / 2 * α + b * d₃ by dsimp [v₃]; ring)]; exact hl₃), hμ.ne', Real.pi_ne_zero]
    have hbaseDiv : (Real.pi * μ : ℂ) /
        b ^ ((γ * Q γ : ℝ) : ℂ) = -(Tc * lFun (-q)) := by
      have hh := hbaseId
      field_simp [(mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Complex.ofReal_ne_zero.mpr hμ.ne')), (Complex.cpow_ne_zero_iff.mpr (Or.inl hb))] at hh ⊢
      have hh' := congrArg (fun z : ℂ => z * (μ : ℂ)) hh
      field_simp [hμ.ne'] at hh'
      simpa [mul_assoc, mul_comm, mul_left_comm] using hh'.symm
    calc
      _ = (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α) *
          b ^ ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) +
            (1 - (γ : ℂ) * v₃ α))) *
          ((Real.pi * μ : ℂ) / b ^ ((γ * Q γ : ℝ) : ℂ)) := by
        push_cast
        ring
      _ = (lFun (b * α) * lFun (b * (α - b)) * lFun (b * v₁ α) *
          b ^ ((1 - (γ : ℂ) * v₀ α) + (1 - (γ : ℂ) * v₂ α) +
            (1 - (γ : ℂ) * v₃ α))) * (-(Tc * lFun (-q))) := by rw [hbaseDiv]
      _ = _ := by ring
  unfold dozzFormula
  rw [← (show Tc ^ pplus α = ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ ((2 * Q γ - (α + γ / 2 + α₂ + α₃)) / γ) by rw [(show Tc = ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) by simp [Tc, T, Complex.ofReal_mul])]), ← (show Tc ^ pminus α = ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ ((2 * Q γ - (α - γ / 2 + α₂ + α₃)) / γ) by rw [(show Tc = ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) by simp [Tc, T, Complex.ofReal_mul])])]
  rw [(show ((α + γ / 2 + α₂ + α₃ - 2 * Q γ) / 2) = v₀p α by dsimp [v₀p, d₀, b]; ring), (show ((α - γ / 2 + α₂ + α₃ - 2 * Q γ) / 2) = v₀ α by dsimp [v₀, d₀, b]; ring), (show ((α + γ / 2 + α₂ + α₃) / 2 - (α + γ / 2)) = v₁ α by dsimp [v₁, d₁, b]; ring), (show ((α - γ / 2 + α₂ + α₃) / 2 - (α - γ / 2)) = v₁p α by dsimp [v₁p, d₁, b]; ring),
    (show ((α + γ / 2 + α₂ + α₃) / 2 - α₂) = v₂p α by dsimp [v₂p, d₂, b]; ring), (show ((α - γ / 2 + α₂ + α₃) / 2 - α₂) = v₂ α by dsimp [v₂, d₂, b]; ring), (show ((α + γ / 2 + α₂ + α₃) / 2 - α₃) = v₃p α by dsimp [v₃p, d₃, b]; ring), (show ((α - γ / 2 + α₂ + α₃) / 2 - α₃) = v₃ α by dsimp [v₃, d₃, b]; ring)]
  rw [hv₀p, hv₁p, hv₂p, hv₃p, ← mul_div_assoc, div_eq_div_iff hdenPlus hdenMinus]
  rw [(show ∀ z : ℂ, z - γ / 2 = z - b by intro z; rfl) α, hnum, (show U (v₀ α + b) = k (v₀ α) * U (v₀ α) by simpa [k] using (IsUpsilon.shift_b hγ hγ2 hU (v₀ α) hnotV₀)), (show U (v₁ α + b) = k (v₁ α) * U (v₁ α) by simpa [k] using (IsUpsilon.shift_b hγ hγ2 hU (v₁ α) hnotV₁)), (show U (v₂ α + b) = k (v₂ α) * U (v₂ α) by simpa [k] using (IsUpsilon.shift_b hγ hγ2 hU (v₂ α) hnotV₂)), (show U (v₃ α + b) = k (v₃ α) * U (v₃ α) by simpa [k] using (IsUpsilon.shift_b hγ hγ2 hU (v₃ α) hnotV₃))]
  linear_combination
    (deriv U 0 * U (α - b) * U α₂ * U α₃ *
      U (v₀ α) * U (v₁ α) * U (v₂ α) * U (v₃ α)) * hscalar

end DOZZ.Proofs

end
