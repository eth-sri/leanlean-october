/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! Scalar comparisons for ambiguous ideal classes have relative norm
equal to a unit of the base ring. This formulation works directly with
relative ideal norms, so it does not identify the unit obstruction with
the trivial class. -/

namespace CCDN
section
open scoped nonZeroDivisors

variable (R S : Type*) [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]

theorem ambiguous_ideal_scalar_relative_unit
    (σ : S ≃ₐ[R] S) (I : (Ideal S)⁰)
    (hI : ClassGroup.mulEquiv σ.toRingEquiv (ClassGroup.mk0 I) = ClassGroup.mk0 I) :
    ∃ x y : S, ∃ u : Rˣ, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * (I : Ideal S).map σ.toRingHom =
        Ideal.span {y} * (I : Ideal S) ∧
      Algebra.intNorm R S x * (u : R) = Algebra.intNorm R S y := by
  rw [ClassGroup.mulEquiv_mk0] at hI
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hI
  change Ideal.span {x} * (I : Ideal S).map σ.toRingHom =
    Ideal.span {y} * I at hxy
  have hn := congrArg (Ideal.relNorm R) hxy
  simp only [map_mul, Ideal.relNorm_singleton] at hn
  have hnmap : Ideal.relNorm R ((I : Ideal S).map σ.toRingHom) =
      Ideal.relNorm R (I : Ideal S) := Ideal.relNorm_map_algEquiv σ I
  rw [hnmap] at hn
  have hspan := mul_right_cancel₀ (by aesop) hn
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨x, y, u, hx, hy, hxy, hu⟩

section NumberFields
open NumberField
open scoped NumberField

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]

