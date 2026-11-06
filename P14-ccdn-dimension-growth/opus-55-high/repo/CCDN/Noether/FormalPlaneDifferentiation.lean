/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Tangent differentiation on formal plane branches. Vanishing of successive
tangent derivatives implies local multiplicity below the characteristic. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [CommRing K]

/-- The polynomial tangent vector field, with coordinate j as local parameter. -/
def planeTangent (f : MvPolynomial (Fin 2) K) (j : Fin 2) :
    Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
  (pderiv j.rev f) • pderiv j - (pderiv j f) • pderiv j.rev

/-- The tangent vector field of `f` with local parameter coordinate `j` applied to `h` is
`∂_{j.rev} f * ∂_j h - ∂_j f * ∂_{j.rev} h`. -/
lemma planeTangent_apply
    (f h : MvPolynomial (Fin 2) K) (j : Fin 2) :
    planeTangent f j h = pderiv j.rev f * pderiv j h - pderiv j f * pderiv j.rev h := rfl

end

variable {K : Type*} [Field K]

lemma powerSeries_plane_chain
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K)
    (h : MvPolynomial (Fin 2) K) (j : Fin 2) :
    PowerSeries.derivative (ψ h) =
      ψ (pderiv j h) * PowerSeries.derivative (ψ (X j)) +
      ψ (pderiv j.rev h) * PowerSeries.derivative (ψ (X j.rev)) := by
  have hC (c : K) : ψ (C c) = PowerSeries.C c := ψ.commutes c
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add h l hh hl => simp [map_add, hh, hl]; ring
  | mul_X h k hh =>
    fin_cases j <;> fin_cases k <;>
      simp [map_mul, Derivation.leibniz, smul_eq_mul, hh] <;> ring

/-- Tangent differentiation becomes a unit times formal differentiation at a
smooth point whose chosen coordinate is the parameter. -/
theorem formal_plane_tangent
    (f : MvPolynomial (Fin 2) K)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    (h : MvPolynomial (Fin 2) K) :
    ψ (planeTangent f j h) = ψ (pderiv j.rev f) * PowerSeries.derivative (ψ h) := by
  have hdX : PowerSeries.derivative (ψ (X j)) = 1 := by
    have he := congrArg PowerSeries.derivative hparam
    have hC := ψ.commutes a
    simpa using he
  have hf := powerSeries_plane_chain ψ f j
  rw [hψ, map_zero, hdX, mul_one] at hf
  rw [powerSeries_plane_chain ψ h j, hdX, mul_one, planeTangent_apply, map_sub, map_mul, map_mul]
  linear_combination ψ (pderiv j.rev h) * hf

/-- A unit multiple of d/dX detects multiplicity from its successive constant
terms, as long as the positive integers below the requested order are invertible. -/
lemma powerSeries_weighted_derivatives_vanishing
    (u : PowerSeries K) (hu : IsUnit u) (N : ℕ)
    (hchar : ∀ n, 0 < n → n < N → (n : K) ≠ 0)
    (g : PowerSeries K)
    (hzero : ∀ r < N,
      PowerSeries.constantCoeff ((fun h => u * PowerSeries.derivative h)^[r] g) = 0) :
    PowerSeries.X ^ N ∣ g := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    have ht : PowerSeries.X ^ N ∣ u * PowerSeries.derivative g := by
      apply ih (fun n hn hnN => hchar n hn (by omega))
      intro r hr
      have hh := hzero (r + 1) (by omega)
      simp_all
    have hd := hu.dvd_mul_left.mp ht
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro n hn
    cases n with
    | zero =>
      simpa using
        hzero 0 (by omega)
    | succ n =>
      have he := PowerSeries.X_pow_dvd_iff.mp hd n (by omega)
      rw [PowerSeries.coeff_derivative] at he
      exact (mul_eq_zero.mp he).resolve_right (by grind)

