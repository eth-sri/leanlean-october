module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Different and codifferent for valued finite extensions

This file specializes mathlib's Dedekind-domain different ideal to complete
DVF valuation rings.  The ideal itself remains mathlib's `differentIdeal`; the
extra API here connects it to the chosen valuation rings, the codifferent, and
the local unramified criterion.
-/

noncomputable section

universe u v w x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RamificationTheory
namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The codifferent submodule of the valuation ring extension, i.e. the
trace-dual of the target valuation ring. -/
noncomputable def codifferentSubmodule
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Submodule target.valuationSubring L :=
  Submodule.traceDual base.valuationSubring K
    (1 : Submodule target.valuationSubring L)

omit [FiniteDimensional K L] in
/-- Trace-dual membership written directly as a trace integrality condition. -/
theorem mem_codifferentSubmodule_iff_trace_mul_integral
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    {z : L} :
    z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base target) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a)) := by
  change
    z ∈ Submodule.traceDual base.valuationSubring K
        (1 : Submodule target.valuationSubring L) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a))
  rw [Submodule.mem_traceDual_iff_isIntegral]
  simp [Algebra.traceForm_apply]





























section
variable [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
/-- The different ideal with the torsion-free certificate supplied by finite
separability of complete-DVF extensions. -/
noncomputable def differentIdealOfFiniteSeparable
      :
    Ideal target.valuationSubring :=
  @differentIdeal base.valuationSubring target.valuationSubring
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target))

/-- The finite-separable different ideal agrees with mathlib's `differentIdeal`
whenever a torsion-free instance is already in scope. -/
theorem differentIdealOfFiniteSeparable_eq_differentIdeal
     
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) =
      differentIdeal base.valuationSubring target.valuationSubring := rfl

/-- Finite-separable trace-dual membership written directly as a trace
integrality condition. -/
theorem mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable
     
    {z : L} :
    z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base target) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a)) := by
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  apply RamificationTheory.DiscreteValuationField.ValuedExtension.mem_codifferentSubmodule_iff_trace_mul_integral

/-- The local different/codifferent relation in finite separable complete-DVF
extensions, using the finite-separable different ideal. -/
theorem coeSubmodule_differentIdealOfFiniteSeparable_eq_one_div_codifferent
      :
    IsLocalization.coeSubmodule L (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) =
      1 / (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base target) := by
  unfold differentIdealOfFiniteSeparable
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  change
    IsLocalization.coeSubmodule L
        (differentIdeal base.valuationSubring target.valuationSubring) =
      1 / Submodule.traceDual base.valuationSubring K
        (1 : Submodule target.valuationSubring L)
  apply _root_.coeSubmodule_differentIdeal
end


omit [FiniteDimensional K L] in
/-- The different ideal is nonzero for finite separable torsion-free valuation
ring extensions. -/
theorem differentIdeal_ne_bot
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring ≠ ⊥ := _root_.differentIdeal_ne_bot

omit [FiniteDimensional K L] in
/-- The fraction-field extension attached to a finite separable complete-DVF
extension is separable.  This is kept private to prevent typeclass search from
trying the very general `FractionRing.liftAlgebra` instance globally. -/
private theorem fractionRing_isSeparable_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    letI : FaithfulSMul base.valuationSubring target.valuationSubring :=
      Module.IsTorsionFree.to_faithfulSMul
    letI : FaithfulSMul base.valuationSubring
        (FractionRing target.valuationSubring) := inferInstance
    letI : Algebra (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
    Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := by
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    Module.IsTorsionFree.to_faithfulSMul
  let : FaithfulSMul base.valuationSubring
      (FractionRing target.valuationSubring) := inferInstance
  let fracAlgebra : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let  :=
    @Algebra.toSMul _ _ _ _ fracAlgebra
  let : IsScalarTower base.valuationSubring
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp
      (algebraMap (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring))
      (FractionRing.algEquiv base.valuationSubring K).symm.toRingEquiv =
        RingHom.comp
          (FractionRing.algEquiv target.valuationSubring L).symm.toRingEquiv
          (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors base.valuationSubring)
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply
      base.valuationSubring target.valuationSubring L,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- The finite-separable different ideal is nonzero without separately
providing the module-finiteness, torsion-free, or fraction-field separability
certificates. -/
theorem differentIdealOfFiniteSeparable_ne_bot
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) ≠ ⊥ := by
  unfold differentIdealOfFiniteSeparable
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (RamificationTheory.DiscreteValuationField.ValuedExtension.fractionRing_isSeparable_of_finite_separable base target)
  apply RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdeal_ne_bot































































































omit [FiniteDimensional K L] in
/-- In a local valuation-ring extension, the different is a unit exactly when
the extension is unramified at the target maximal ideal. -/
theorem isUnit_differentIdeal_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    IsUnit (differentIdeal base.valuationSubring target.valuationSubring) ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  constructor
  · intro hunit
    have htop :
        differentIdeal base.valuationSubring target.valuationSubring = ⊤ :=
      Ideal.isUnit_iff.mp hunit
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring := by
      intro hdvd
      have hle  :=
        Ideal.dvd_iff_le.mp hdvd
      rw [htop] at hle
      have hproper : target.maximalIdeal ≠ ⊤ :=
        (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
      apply hproper <;> aesop
    exact (_root_.not_dvd_differentIdeal_iff).1 hnot
  · intro hunram
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring :=
    (_root_.not_dvd_differentIdeal_iff).2 hunram
    rw [Ideal.isUnit_iff]
    by_contra hne
    have hle :
        differentIdeal base.valuationSubring target.valuationSubring ≤
          target.maximalIdeal :=
      IsLocalRing.le_maximalIdeal hne
    exact hnot (Ideal.dvd_iff_le.mpr hle)





















omit [FiniteDimensional K L] in
/-- States the theorem `differentIdeal_eq_top_iff_isUnramifiedAt`. -/
theorem differentIdeal_eq_top_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  rw [← Ideal.isUnit_iff]
  apply RamificationTheory.DiscreteValuationField.ValuedExtension.isUnit_differentIdeal_iff_isUnramifiedAt

section
variable [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
/-- Finite-separable version of the top/different criterion for
unramifiedness. -/
theorem differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
      :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (RamificationTheory.DiscreteValuationField.ValuedExtension.fractionRing_isSeparable_of_finite_separable base target)
  apply RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdeal_eq_top_iff_isUnramifiedAt



















/-- In a monogenic finite separable extension, the derivative of the minimal
polynomial belongs to the different. -/
def aeval_derivative_mem_differentIdeal
     
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤)  := _root_.aeval_derivative_mem_differentIdeal
    base.valuationSubring K L z hz




















/-- In a monogenic finite separable complete-DVF extension, the derivative of
the minimal polynomial belongs to the finite-separable different ideal. -/
theorem aeval_derivative_mem_differentIdealOfFiniteSeparable
     
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    Polynomial.aeval z
        (Polynomial.derivative (minpoly base.valuationSubring z)) ∈
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) := by
  unfold differentIdealOfFiniteSeparable
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  apply RamificationTheory.DiscreteValuationField.ValuedExtension.aeval_derivative_mem_differentIdeal <;> assumption

/-- A monogenic finite separable complete-DVF extension is unramified when
an integral equation for its generator has unit derivative.  The equation
need not be the minimal polynomial: integrally closed divisibility transfers
the unit condition to the derivative of the minimal polynomial, which then
generates the different. -/
theorem isUnramifiedAt_of_aeval_derivative_isUnit
     
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤)
    (P : Polynomial base.valuationSubring)
    (hP : Polynomial.aeval z P = 0)
    (hPderiv :
      IsUnit (Polynomial.aeval z (Polynomial.derivative P))) :
    Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  let  :=
    target_valuationSubring_isIntegralClosure_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring
      target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  obtain ⟨Q, hQ⟩ :=
    minpoly.isIntegrallyClosed_dvd
      (IsIntegralClosure.isIntegral base.valuationSubring L z) hP
  have hderiv :
      Polynomial.aeval z (Polynomial.derivative P) =
        Polynomial.aeval z
            (Polynomial.derivative
              (minpoly base.valuationSubring z)) *
          Polynomial.aeval z Q := by
    rw [hQ, Polynomial.derivative_mul]
    simp
  have hminpolyDeriv :
      IsUnit
        (Polynomial.aeval z
          (Polynomial.derivative
            (minpoly base.valuationSubring z))) := by
    apply isUnit_of_mul_isUnit_left
    rw [← hderiv]
    exact hPderiv
  apply
    (differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
      base target).1
  apply
    (differentIdealOfFiniteSeparable base target).eq_top_of_isUnit_mem
      (aeval_derivative_mem_differentIdealOfFiniteSeparable
        base target z hz)
  exact hminpolyDeriv
end

































































































section Tower

variable {M : Type*} [Field M]
variable [Algebra K M] [Algebra M L]
variable [FiniteDimensional K M] [FiniteDimensional M L]
variable {middle : CompleteDVF M}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]































































end Tower

end ValuedExtension
end DiscreteValuationField
end RamificationTheory

end
