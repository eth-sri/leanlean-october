module

public import Mathlib.FieldTheory.Galois.Profinite
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Chosen integral-closure ramification filtrations at finite Galois levels

For a complete discretely valued field `K` and a finite Galois intermediate
field `E` of an algebraic closure, an existence theorem for the integral
closure of the valuation ring of `K` supplies complete-DVF structures on
`E`.  This file makes one noncomputable choice of such data.  Completeness
then gives uniqueness of the extended valuation, so real lower groups and
Herbrand upper groups can be formed without asking a caller to provide a
filtration. Choice independence is proved in the companion module.
-/

noncomputable section

universe u v y

namespace RamificationTheory.HilbertRamification.FiniteGaloisLevel

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

 theorem chosenIntegralClosureData_exists
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ∃ target : CompleteDVF.{u, 0} E,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        IsIntegralClosure target.valuationSubring
          base.valuationSubring E ∧
          degree base.toDVF target.toDVF =
            ramificationIndex base.toDVF target.toDVF *
              residueDegree base.toDVF target.toDVF :=
  exists_integralClosure_standard_fundamental_identity
    (K := K) (L := E) base

/-- A complete-DVF structure on a finite Galois level, chosen from the
integral-closure existence theorem. -/
noncomputable def chosenIntegralClosureTarget
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    CompleteDVF.{u, 0} E :=
  Classical.choose (chosenIntegralClosureData_exists base E)

/-- The valuation on `chosenIntegralClosureTarget` extends the valuation on the base
complete DVF. -/
theorem chosenIntegralClosureTargetHasExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    base.valuation.HasExtension (chosenIntegralClosureTarget base E).valuation :=
  Classical.choose (Classical.choose_spec (chosenIntegralClosureData_exists base E))

/-- Provides the instance `instChosenIntegralClosureTargetHasExtension`. -/
noncomputable instance instChosenIntegralClosureTargetHasExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    base.valuation.HasExtension (chosenIntegralClosureTarget base E).valuation :=
  chosenIntegralClosureTargetHasExtension base E





/-- Uniqueness of the extended valuation at a finite Galois level, in the
complete-DVF formulation. -/
theorem chosenIntegralClosureTarget_hasUniqueValuationExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ValuedExtension.HasUniqueValuationExtension.{u, v, u, 0, y}
      (base := base) (target := chosenIntegralClosureTarget base E) :=
  hasUniqueValuationExtension_of_finite_separable
    base (chosenIntegralClosureTarget base E)

/-- Uniqueness after forgetting completeness, in the precise universe needed
by the real lower ramification groups. -/
theorem chosenIntegralClosureTarget_hasUniqueDVFValuationExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, u, 0, y}
      base.toDVF (chosenIntegralClosureTarget base E).toDVF :=
  chosenIntegralClosureTarget_hasUniqueValuationExtension base E



/-- The finite-level real upper ramification filtration attached to the chosen
integral-closure valuation. -/
noncomputable def chosenUpperRamificationFiltration
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ℝ → Subgroup Gal(E / K) := fun t =>
  Higher.upperRamificationGroupOfUniqueExtension
    (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
    (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E) t



/-- States the theorem `chosenUpperRamificationFiltration_apply`. -/
@[simp]
theorem chosenUpperRamificationFiltration_apply
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) :
    chosenUpperRamificationFiltration base E t =
      Higher.upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
        (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E) t :=
  rfl









end RamificationTheory.HilbertRamification.FiniteGaloisLevel

end
