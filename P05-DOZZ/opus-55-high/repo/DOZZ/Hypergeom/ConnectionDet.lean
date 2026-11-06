/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! The determinant of the corrected Gauss connection matrix. -/

@[expose] public section

open Complex

namespace DOZZ.Proofs

private lemma invGamma_reflection_pair (z : ℂ) :
    (Complex.Gamma z)⁻¹ * (Complex.Gamma (1 - z))⁻¹ =
      Complex.sin (Real.pi * z) / (Real.pi : ℂ) := by
  by_cases hz : z ∈ Complex.integerComplement
  · have hsin : Complex.sin (Real.pi * z) ≠ 0 := sin_pi_mul_ne_zero hz
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hΓz : Complex.Gamma z ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      apply (Complex.mem_integerComplement_iff.mp hz)
      exact ⟨-(m : ℤ), by exact_mod_cast hm.symm⟩
    have hΓ1z : Complex.Gamma (1 - z) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      apply (Complex.mem_integerComplement_iff.mp hz)
      refine ⟨(m : ℤ) + 1, ?_⟩
      have hz' : z = (1 : ℂ) + (m : ℂ) := by grind
      calc
        ((m : ℤ) + 1 : ℤ) = (1 : ℂ) + (m : ℂ) := by push_cast; ring
        _ = z := hz'.symm
    calc
      (Complex.Gamma z)⁻¹ * (Complex.Gamma _)⁻¹ =
          (Complex.Gamma _)⁻¹ * (Complex.Gamma z)⁻¹ := by rw [mul_comm]
      _ = (Complex.Gamma z * Complex.Gamma _)⁻¹ := by ring
      _ = ((Real.pi : ℂ) / Complex.sin _)⁻¹ := by
        rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = Complex.sin _ / (Real.pi : ℂ) := by
        simp
  · have hzint : ∃ n : ℤ, (n : ℂ) = z := by
      by_contra hn
      tauto
    obtain ⟨n, hn⟩ := hzint
    have hsin : Complex.sin (Real.pi * z) = 0 := by
      rw [← hn, mul_comm]
      exact Complex.sin_int_mul_pi n
    have hcases : (∃ m : ℕ, n = -(m : ℤ)) ∨
        (∃ m : ℕ, 1 - n = -(m : ℤ)) := by
      by_cases hn0 : n ≤ 0
      · left
        refine ⟨(-n).toNat, ?_⟩
        simp_all
      · right
        have hn1 : 1 ≤ n := by omega
        refine ⟨(n - 1).toNat, ?_⟩
        simp_all
    rcases hcases with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hz' : z = -(m : ℂ) := by
        simp_all
      grind
    · have h1z : (1 : ℂ) - z = -(m : ℂ) := by
        rw [← hn]
        exact_mod_cast hm
      grind
section
variable (a b c : ℂ)

private lemma gauss_connection_sine_identity :
    Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) -
        Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) =
      Complex.sin (Real.pi * c) * Complex.sin (Real.pi * (c - a - b)) := by
  set x := Real.pi * c
  set y := Real.pi * a
  set z := Real.pi * b
  have hca : Real.pi * (c - a) = x - y := by ring
  have hcb : Real.pi * (c - b) = x - z := by ring
  have hδ : Real.pi * (c - a - b) = x - (y + z) := by ring
  rw [hca, hcb, hδ, Complex.sin_sub, Complex.sin_sub, Complex.sin_sub,
    Complex.sin_add, Complex.cos_add]
  linear_combination (Complex.sin_sq_add_cos_sq x) * Complex.sin y * Complex.sin z

/-- Determinant `det M = (c-1)/δ` of the connection matrix of `gauss_connection_minus/plus`,
corrected as in erratum K1 (see docs/ERRATA-AND-DEVIATIONS.md). Reciprocal Gamma is entire. -/
theorem gauss_connection_det (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    (Complex.Gamma c * Complex.Gamma (c - a - b) *
        (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
      (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
        (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) -
      (Complex.Gamma c * Complex.Gamma (a + b - c) *
        (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) *
      (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
        (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) =
    (c - 1) / (c - a - b) := by
  let δ := c - a - b
  have hcInt : c ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    tauto
  have hδInt : δ ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    tauto
  have hsC := sin_pi_mul_ne_zero hcInt
  have hsδ := sin_pi_mul_ne_zero hδInt
  have hδ0 : δ ≠ 0 := by
    aesop
  have hc1 : c ≠ 1 := by aesop
  have hΓc : Complex.Gamma c * Complex.Gamma (2 - c) =
      (1 - c) * (Real.pi / Complex.sin (Real.pi * c)) := by
    calc
      Complex.Gamma c * Complex.Gamma (2 - c) =
          Complex.Gamma c * ((1 - c) * Complex.Gamma (1 - c)) := by
            rw [show 2 - c = (1 - c) + 1 by ring,
              Complex.Gamma_add_one (1 - c) (sub_ne_zero.mpr (Ne.symm hc1))]
      _ = (1 - c) * (Complex.Gamma c * Complex.Gamma (1 - c)) := by ring
      _ = (1 - c) * (Real.pi / Complex.sin (Real.pi * c)) := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
  have hΓδ : Complex.Gamma δ * Complex.Gamma (-δ) =
      -((Real.pi / Complex.sin (Real.pi * δ)) / δ) := by
    have hrec : Complex.Gamma (1 - δ) = -δ * Complex.Gamma (-δ) := by
      rw [show 1 - δ = (-δ) + 1 by ring,
        Complex.Gamma_add_one (-δ) (neg_ne_zero.mpr hδ0)]
    calc
      Complex.Gamma δ * Complex.Gamma (-δ) =
          (Complex.Gamma δ * Complex.Gamma (1 - δ)) / (-δ) := by
            rw [hrec]
            field_simp
      _ = (Real.pi / Complex.sin (Real.pi * δ)) / (-δ) := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = -((Real.pi / Complex.sin (Real.pi * δ)) / δ) := by ring_nf
  have hpairCA : (Complex.Gamma (c - a))⁻¹ *
        (Complex.Gamma (a - c + 1))⁻¹ = Complex.sin (Real.pi * (c - a)) / Real.pi := by
    rw [show a - c + 1 = 1 - (c - a) by ring]
    exact invGamma_reflection_pair (c - a)
  have hpairCB : (Complex.Gamma (c - b))⁻¹ *
        (Complex.Gamma (b - c + 1))⁻¹ = Complex.sin (Real.pi * (c - b)) / Real.pi := by
    rw [show b - c + 1 = 1 - (c - b) by ring]
    exact invGamma_reflection_pair (c - b)
  have hpairA := invGamma_reflection_pair a
  have hpairB := invGamma_reflection_pair b
  have hterm₁ :
      (Complex.Gamma c * Complex.Gamma (c - a - b) *
          (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
        (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
          (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) =
      ((1 - c) * (Real.pi / Complex.sin (Real.pi * c))) *
        (-((Real.pi / Complex.sin (Real.pi * δ)) / δ)) *
        (Complex.sin (Real.pi * (c - a)) / Real.pi) *
        (Complex.sin (Real.pi * (c - b)) / Real.pi) := by
    calc
      _ = (Complex.Gamma c * Complex.Gamma (2 - c)) *
          (Complex.Gamma δ * Complex.Gamma (-δ)) *
          ((Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (a - c + 1))⁻¹) *
          ((Complex.Gamma (c - b))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) := by
            dsimp [δ]
            ring_nf
      _ = _ := by simp_all
  have hterm₂ :
      (Complex.Gamma c * Complex.Gamma (a + b - c) *
          (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) *
        (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
          (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) =
      ((1 - c) * (Real.pi / Complex.sin (Real.pi * c))) *
        (-((Real.pi / Complex.sin (Real.pi * δ)) / δ)) *
        (Complex.sin (Real.pi * a) / Real.pi) *
        (Complex.sin (Real.pi * b) / Real.pi) := by
    calc
      _ = (Complex.Gamma c * Complex.Gamma (2 - c)) *
          (Complex.Gamma δ * Complex.Gamma (-δ)) *
          ((Complex.Gamma a)⁻¹ * (Complex.Gamma (1 - a))⁻¹) *
          ((Complex.Gamma b)⁻¹ * (Complex.Gamma (1 - b))⁻¹) := by
            dsimp [δ]
            ring_nf
      _ = _ := by simp_all
  have hratio :
      Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) /
          (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) -
        Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) /
          (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) = 1 := by
    rw [← sub_div, (gauss_connection_sine_identity a b c), div_self (mul_ne_zero hsC hsδ)]
  rw [show c - a - b = δ by rfl] at *
  rw [hterm₁, hterm₂]
  have hfinish :
      ((1 - c) * (Real.pi / Complex.sin (Real.pi * c))) *
          (-((Real.pi / Complex.sin (Real.pi * δ)) / δ)) *
          (Complex.sin (Real.pi * (c - a)) / Real.pi) *
          (Complex.sin (Real.pi * (c - b)) / Real.pi) -
        ((1 - c) * (Real.pi / Complex.sin (Real.pi * c))) *
          (-((Real.pi / Complex.sin (Real.pi * δ)) / δ)) *
          (Complex.sin (Real.pi * a) / Real.pi) *
          (Complex.sin (Real.pi * b) / Real.pi) = (c - 1) / δ := by
    calc
      _ = (c - 1) / δ *
          (Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) /
              (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) -
            Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) /
              (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ))) := by
            field_simp [hsC, hsδ, (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'), hδ0]
            ring
      _ = (c - 1) / δ := by simp_all
  exact hfinish

end

end DOZZ.Proofs
