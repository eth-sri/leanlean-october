/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SingularTangent
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.MvPolynomial
import CCDN.Algebra.ModularPolynomialLift
import CCDN.Determinant.OriginTruncationGenerators
import Mathlib.FieldTheory.Finite.Polynomial

/-! Lift singular local generators from the reduction modulo p. The
remaining error is an explicit multiple of p, with a separate high-order term. -/

namespace CCDN
section
open MvPolynomial

/-- Lift a whole homogeneous generating family without changing its size at
any weight. The error separates the equation, the origin power and a multiple of p. -/
theorem lift_origin_truncation_generators {σ : Type*} {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial σ ℤ) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → MvPolynomial σ (ZMod p))
    (hg : ∀ k j, (g k j).IsHomogeneous k)
    (hspan : ∀ k u, u ∈ idealOfVars σ (ZMod p) ^ k → ∃ c : Fin (r k) → ZMod p,
      u - ∑ j, c j • g k j ∈ originTruncationIdeal (map (Int.castRingHom (ZMod p)) f) k) :
    ∃ G : (k : ℕ) → Fin (r k) → MvPolynomial σ ℤ,
      (∀ k j, (G k j).IsHomogeneous k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (h v w : MvPolynomial σ ℤ),
        v ∈ idealOfVars σ ℤ ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • G k.val j = f * h + v + C (p : ℤ) * w := by
  let π := Int.castRingHom (ZMod p)
  refine ⟨(fun k j => modularPolynomialLift (g k j)),
    (fun k j => modularPolynomialLift_homogeneous _ (hg k j)), ?_⟩
  intro N u
  obtain ⟨c, hc⟩ := origin_layers_generate_truncation _ r g hspan N (map π u)
  obtain ⟨h', hh', v, hv, he⟩ := Submodule.mem_sup.mp hc
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hh'
  let cZ : (k : Fin N) → Fin (r k.val) → ℤ := fun k j => (c k j).val
  let S := ∑ k : Fin N, ∑ j, cZ k j • modularPolynomialLift (g k.val j)
  have hS : map π S = ∑ k : Fin N, ∑ j, c k j • g k.val j := by
    simp only [S, cZ, smul_eq_C_mul, map_sum, map_mul, map_C, map_modularPolynomialLift,
      π, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]
  let D := u - S - f * modularPolynomialLift h - modularPolynomialLift v
  have hlift (q : MvPolynomial σ (ZMod p)) : map π (modularPolynomialLift q) = q :=
    map_modularPolynomialLift q
  obtain ⟨w, hw⟩ := (C_dvd_iff_zmod p D).mpr (by grind)
  refine ⟨cZ, modularPolynomialLift h, modularPolynomialLift v, w,
    modularPolynomialLift_mem_origin_power v hv, ?_⟩
  dsimp [D] at hw
  linear_combination hw

