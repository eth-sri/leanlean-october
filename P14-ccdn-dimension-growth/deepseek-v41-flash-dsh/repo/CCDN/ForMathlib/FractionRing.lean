/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Fraction fields of localizations, polynomial rings and finite extensions

## Main results

* `IsFractionRing.liftOfLocalization`: a nonzero localization of a domain embeds compatibly in any
  fraction field of the domain, which is then a fraction field of the localization
  (`IsFractionRing.isFractionRing_liftOfLocalization`).
* `MvPolynomial.coeffFractionRingEmbedding`: a fraction field of a coefficient domain `A` embeds
  canonically in a fraction field of `MvPolynomial σ A`, compatibly with `A` and its ground field.
* `MvPolynomial.fractionRingCoeffMap`, `MvPolynomial.isFractionRing_fractionRingCoeffMap`:
  enlarging the coefficients to their fraction field does not change the fraction field of a
  polynomial ring.
* `IsFractionRing.exists_ne_zero_mul_mem_range_of_finite`: a finite extension of domains with a
  common fraction field has a nonzero conductor element.
-/

public section


namespace IsLocalization

end IsLocalization

namespace IsFractionRing

end IsFractionRing

namespace MvPolynomial

variable {K A F E σ : Type*} [Field K] [CommRing A] [IsDomain A]
  [Field F] [Field E] [Algebra K A] [Algebra K F] [Algebra K E]
  [Algebra A F] [IsFractionRing A F] [IsScalarTower K A F]
  [Algebra A E] [IsScalarTower K A E]
  [Algebra (MvPolynomial σ A) E] [IsScalarTower A (MvPolynomial σ A) E]
  [IsFractionRing (MvPolynomial σ A) E]

end MvPolynomial

namespace MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

end MvPolynomial

namespace IsFractionRing

/-- A common nonzero denominator for a finite birational extension. -/
theorem exists_ne_zero_mul_mem_range_of_finite
    (R A F : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Field F]
    [Algebra R A] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [IsFractionRing R F] [IsFractionRing A F] [Module.Finite R A] :
    ∃ c : R, c ≠ 0 ∧ ∀ a : A, ∃ r : R,
      algebraMap R A r = algebraMap R A c * a := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  let φ : A →ₐ[R] F := IsScalarTower.toAlgHom R A F
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors R) s (fun a => φ a)
  let N : Submodule R A :=
    Submodule.comap ((c : R) • φ.toLinearMap) (LinearMap.range (Algebra.linearMap R F))
  have hspan : Submodule.span R (s : Set A) ≤ N := by
    apply Submodule.span_le.mpr
    intro a ha
    exact hc a ha
  have hall (a : A) : a ∈ N := by
    apply hspan
    rw [hs]
    trivial
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp c.2, ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hall a
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective A F
  change algebraMap A F (algebraMap R A r) =
    algebraMap A F (algebraMap R A (c : R) * a)
  rw [map_mul, ← IsScalarTower.algebraMap_apply R A F,
    ← IsScalarTower.algebraMap_apply R A F]
  simpa only [LinearMap.smul_apply, Algebra.smul_def, Algebra.linearMap_apply,
    AlgHom.toLinearMap_apply, φ, IsScalarTower.toAlgHom_apply] using hr

end IsFractionRing

