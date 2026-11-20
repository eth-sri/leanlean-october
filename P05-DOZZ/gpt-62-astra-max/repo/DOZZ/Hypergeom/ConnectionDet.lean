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
  · grind [mul_comm, mul_inv_rev, Complex.Gamma_mul_Gamma_one_sub]
  · have hzint : ∃ n : ℤ, (n : ℂ) = z := by
      by_contra hn
      exact hz ((Complex.mem_integerComplement_iff).2 hn)
    obtain ⟨n, hn⟩ := hzint
    have hsin : Complex.sin (Real.pi * z) = 0 := by
      rw [← hn, mul_comm]
      exact Complex.sin_int_mul_pi n
    have hcases : (∃ m : ℕ, n = -(m : ℤ)) ∨
        (∃ m : ℕ, 1 - n = -(m : ℤ)) := by
      by_cases hn0 : n ≤ 0
      · left
        refine ⟨(-n).toNat, ?_⟩
        omega
      · right
        refine ⟨(n - 1).toNat, ?_⟩
        omega
    rcases hcases with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hz' : z = -(m : ℂ) := by
        calc
          z = (n : ℂ) := hn.symm
          _ = -(m : ℂ) := by exact_mod_cast hm
      grind
    · have h1z : (1 : ℂ) - z = -(m : ℂ) := by
        rw [← hn]
        exact_mod_cast hm
      grind

private lemma gauss_connection_sine_identity (a b c : ℂ) :
    Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) -
        Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) =
      Complex.sin (Real.pi * c) * Complex.sin (Real.pi * (c - a - b)) := by
  set x : ℂ := Real.pi * c
  set y : ℂ := Real.pi * a
  set z : ℂ := Real.pi * b
  have hca : Real.pi * (c - a) = x - y := by dsimp [x, y]; ring
  have hcb : Real.pi * (c - b) = x - z := by dsimp [x, z]; ring
  have hδ : Real.pi * (c - a - b) = x - (y + z) := by dsimp [x, y, z]; ring
  rw [hca, hcb, hδ, Complex.sin_sub, Complex.sin_sub, Complex.sin_sub,
    Complex.sin_add, Complex.cos_add]
  linear_combination (Complex.sin_sq_add_cos_sq x) * Complex.sin y * Complex.sin z

/-- Determinant `det M = (c-1)/δ` of the connection matrix of `gauss_connection_minus/plus`,
corrected as in erratum K1 (see docs/ERRATA-AND-DEVIATIONS.md). Reciprocal Gamma is entire. -/
theorem gauss_connection_det (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
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
    rintro ⟨n, hn⟩
    exact hc n hn.symm
  have hδInt : δ ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    apply hδ n
    exact hn.symm
  have hsC := sin_pi_mul_ne_zero hcInt
  have hsδ := sin_pi_mul_ne_zero hδInt
  have hδ0 : δ ≠ 0 := by
    intro hz
    apply hδ 0
    simpa [δ] using hz
  have hΓc : Complex.Gamma c * Complex.Gamma (2 - c) =
      (1 - c) * (Real.pi / Complex.sin (Real.pi * c)) := by
    calc
      _ =
          Complex.Gamma c * ((1 - c) * Complex.Gamma (1 - c)) := by
            rw [show 2 - c = (1 - c) + 1 by ring,
              Complex.Gamma_add_one (1 - c) (sub_ne_zero.mpr (Ne.symm (by simpa using hc 1)))]
      _ = (1 - c) * (Complex.Gamma c * Complex.Gamma (1 - c)) := by ring
      _ = _ := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
  have hΓδ : Complex.Gamma δ * Complex.Gamma (-δ) =
      -((Real.pi / Complex.sin (Real.pi * δ)) / δ) := by
    have hrec : Complex.Gamma (1 - δ) = -δ * Complex.Gamma (-δ) := by
      rw [show (1 : ℂ) - δ = (-δ) + 1 by ring,
        Complex.Gamma_add_one (-δ) (neg_ne_zero.mpr hδ0)]
    calc
      _ =
          (Complex.Gamma δ * Complex.Gamma (1 - δ)) / (-δ) := by
            rw [hrec]
            field_simp
      _ = (Real.pi / Complex.sin (Real.pi * δ)) / (-δ) := by
            rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = _ := by ring_nf
  have hpairCA : (Complex.Gamma (c - a))⁻¹ *
        (Complex.Gamma (a - c + 1))⁻¹ = Complex.sin (Real.pi * (c - a)) / (Real.pi : ℂ) := by
    rw [show a - c + 1 = 1 - (c - a) by ring]
    exact invGamma_reflection_pair (c - a)
  have hpairCB : (Complex.Gamma (c - b))⁻¹ *
        (Complex.Gamma (b - c + 1))⁻¹ = Complex.sin (Real.pi * (c - b)) / (Real.pi : ℂ) := by
    rw [show b - c + 1 = 1 - (c - b) by ring]
    exact invGamma_reflection_pair (c - b)
  have hpairA := invGamma_reflection_pair a
  have hpairB := invGamma_reflection_pair b
  have hterm₁ :
      (Complex.Gamma c * Complex.Gamma (c - a - b) *
          (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
        (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
          (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) =
      ((1 - c) * ((Real.pi : ℂ) / Complex.sin (Real.pi * c))) *
        (-(((Real.pi : ℂ) / Complex.sin (Real.pi * δ)) / δ)) *
        (Complex.sin (Real.pi * (c - a)) / (Real.pi : ℂ)) *
        (Complex.sin (Real.pi * (c - b)) / (Real.pi : ℂ)) := by
    calc
      _ = (Complex.Gamma c * Complex.Gamma (2 - c)) *
          (Complex.Gamma δ * Complex.Gamma (-δ)) *
          ((Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (a - c + 1))⁻¹) *
          ((Complex.Gamma (c - b))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) := by
            dsimp [δ]
            ring_nf
      _ = _ := by rw [hΓc, hΓδ, hpairCA, hpairCB]
  have hterm₂ :
      (Complex.Gamma c * Complex.Gamma (a + b - c) *
          (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) *
        (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
          (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) =
      ((1 - c) * ((Real.pi : ℂ) / Complex.sin (Real.pi * c))) *
        (-(((Real.pi : ℂ) / Complex.sin (Real.pi * δ)) / δ)) *
        (Complex.sin (Real.pi * a) / (Real.pi : ℂ)) *
        (Complex.sin (Real.pi * b) / (Real.pi : ℂ)) := by
    calc
      _ = (Complex.Gamma c * Complex.Gamma (2 - c)) *
          (Complex.Gamma δ * Complex.Gamma (-δ)) *
          ((Complex.Gamma a)⁻¹ * (Complex.Gamma (1 - a))⁻¹) *
          ((Complex.Gamma b)⁻¹ * (Complex.Gamma (1 - b))⁻¹) := by
            dsimp [δ]
            ring_nf
      _ = _ := by rw [hΓc, hΓδ, hpairA, hpairB]
  have hratio :
      Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) /
          (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) -
        Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) /
          (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) = 1 := by
    rw [← sub_div, (gauss_connection_sine_identity a b c), div_self (mul_ne_zero hsC hsδ)]
  rw [show c - a - b = δ by rfl] at *
  rw [hterm₁, hterm₂]
  calc
    _ = (c - 1) / δ *
        (Complex.sin (Real.pi * (c - a)) * Complex.sin (Real.pi * (c - b)) /
            (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ)) -
          Complex.sin (Real.pi * a) * Complex.sin (Real.pi * b) /
            (Complex.sin (Real.pi * c) * Complex.sin (Real.pi * δ))) := by
          field_simp <;> ring
    _ = _ := by rw [hratio, mul_one]

end DOZZ.Proofs
