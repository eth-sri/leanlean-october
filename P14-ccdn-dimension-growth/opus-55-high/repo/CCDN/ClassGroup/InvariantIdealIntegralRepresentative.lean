/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.QuadraticInvariantIdeal
import CCDN.ClassGroup.FractionalIdealConjugation

/-! An invariant fractional ideal has an invariant integral
representative in the same ideal class. Multiplying a denominator by
its conjugate makes the denominator clearing compatible with the
involution. -/

namespace CCDN
section
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- For an involutive ring automorphism `σ` of `R`, every `σ`-invariant invertible fractional ideal
`J` has a `σ`-invariant nonzero integral ideal `I` in the same ideal class. -/
theorem exists_invariant_integral_ideal_representative
    (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (J : (FractionalIdeal R⁰ K)ˣ)
    (hJ : fractionalIdealUnitAction (K := K) σ J = J) :
    ∃ I : (Ideal R)⁰,
      (I : Ideal R).map σ.toRingHom = I ∧
      ClassGroup.mk0 I = ClassGroup.mk K J := by
  let a : R := (J : FractionalIdeal R⁰ K).den
  have ha : a ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (J : FractionalIdeal R⁰ K).den.property
  have hσa : σ a ≠ 0 := by simp_all
  let u : Kˣ := Units.mk0 (algebraMap R K (σ a * a)) (by simp_all)
  let I : Ideal R := Ideal.span {σ a} * (J : FractionalIdeal R⁰ K).num
  have hI : (I : FractionalIdeal R⁰ K) = (toPrincipalIdeal R K u * J :
      (FractionalIdeal R⁰ K)ˣ) := by
    simp [I, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      Units.val_mul, coe_toPrincipalIdeal]
    rw [← (J : FractionalIdeal R⁰ K).den_mul_self_eq_num']
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K (σ a)) *
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) * (J : FractionalIdeal R⁰ K)) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K (σ a * a)) * (J : FractionalIdeal R⁰ K)
    rw [map_mul, map_mul, mul_assoc]
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr (by aesop)⟩
  have hIu : FractionalIdeal.mk0 K I₀ = toPrincipalIdeal R K u * J := Units.ext hI
  have hσu : Units.map
      (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K).toMonoidHom u = u := by
    apply Units.ext
    change (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K)
      (algebraMap R K (σ a * a)) = algebraMap R K (σ a * a)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_mul, hσ, mul_comm]
  have hIfixed : fractionalIdealUnitAction σ (FractionalIdeal.mk0 K I₀) =
      FractionalIdeal.mk0 K I₀ := by
    rw [hIu, map_mul, fractionalIdealUnitAction_principal, hσu, hJ]
  refine ⟨I₀, ?_, ?_⟩
  · apply FractionalIdeal.coeIdeal_inj (K := K) |>.mp
    have h := congrArg (fun U : (FractionalIdeal R⁰ K)ˣ =>
      (U : FractionalIdeal R⁰ K)) hIfixed
    change FractionalIdeal.ringEquivOfRingEquiv K K σ I =
      (I : FractionalIdeal R⁰ K) at h
    simpa [fractionalIdeal_conjugate_coeIdeal] using h
  · rw [← ClassGroup.mk_mk0 K I₀, hIu, map_mul, classGroup_mk_principal, one_mul]

