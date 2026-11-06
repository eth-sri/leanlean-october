module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Nakayama

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite algebra consequences of Henselian pairs

This file keeps the Nakayama and finite-module completion consequences away
from the lightweight `HenselianDVF` core.
-/

noncomputable section

universe u v

namespace DiscreteValuationField






































































































































































































/-- Same-universe finite modules over a Noetherian adically complete ring are
adically complete. -/
theorem isAdicComplete_of_moduleFinite_sameUniverse
    {R M : Type u} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  refine AdicCompletion.of_bijective_iff.mp ?_
  let e  :=
    (TensorProduct.lid R M).symm.trans
      ((TensorProduct.congr (AdicCompletion.ofLinearEquiv I R)
        (LinearEquiv.refl R M)).trans
        ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R))
  have heq : (e : M →ₗ[R] AdicCompletion I M) = AdicCompletion.of I M := by
    ext x n
    simp [e]
    exact one_smul (R ⧸ (I ^ n • ⊤ : Ideal R))
      (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) x)
  have hebij : Function.Bijective (e : M → AdicCompletion I M) := e.bijective
  rw [← heq]
  exact hebij

/-- A finite module over a Noetherian adically complete ring is adically complete.

This is a universe-polymorphic wrapper around mathlib's tensor-product
finite-module completion theorem. -/
theorem isAdicComplete_of_moduleFinite
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let : Small.{u} M := Module.Finite.small R M
  let  :=
    Module.Finite.of_surjective
      ((Shrink.linearEquiv R M).symm : M →ₗ[R] Shrink.{u} M)
      (Shrink.linearEquiv R M).symm.surjective
  have : IsAdicComplete I (Shrink.{u} M) :=
    isAdicComplete_of_moduleFinite_sameUniverse (I := I)
  exact ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv
    (I := I) (Shrink.linearEquiv R M)















namespace HenselianDVF

variable {K : Type u} [Field K]


























end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
