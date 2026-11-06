module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianValuationExtension
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
public import Mathlib.RingTheory.RamificationInertia.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation







variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The canonical integer map from the base valuation ring to the valuation
subring constructed from the actual integral closure.  Its definition uses the
exact pullback theorem for the constructed integral-closure valuation subring,
so no auxiliary alias of the base or target valuation ring is introduced. -/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.valuation hval (a : K)).2 a.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro a b; ext; simp
  map_mul' := by intro a b; ext; simp

omit [FiniteDimensional K L] in
/-- The finite-extension integer map into the integral closure is the ambient algebra map. -/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective.  This is the ring-theoretic input needed to
turn a prime over the base maximal ideal into a nonzero prime of the constructed
integral-closure valuation ring. -/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    Function.Injective
      (integralClosureValuationSubringIntegerMapOfMemOrInv
        (K := K) (L := L) base hval) := by
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  have hvalEq := congrArg
    (fun x :
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval => (x : L)) hab
  change algebraMap K L (a : K) = algebraMap K L (b : K) at hvalEq
  exact hvalEq

/- Numerical defect is a derived quotient; defectlessness itself is the
canonical equality `degree = e * f` defined in `Extensions`.  Positivity
and the fundamental identity are established below only under the hypotheses
needed by the local-Dedekind theorem. -/
omit [FiniteDimensional K L] in
/-- The target maximal ideal lies over the base maximal ideal for any actual
extension of the chosen valuations.  This is the record-free form of the local
map property used by finite-extension invariants. -/
theorem maximalIdeal_liesOver_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation] :
    target.maximalIdeal.LiesOver base.maximalIdeal :=
  target_maximalIdeal_liesOver_base_maximal_of_hasExtension base target

omit [FiniteDimensional K L] in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal.

This is the nontrivial half of locating the center: the center is represented
as `ValuationSubring.idealOfLE`, and its contraction along the canonical map
from the base valuation ring is computed using the `HasExtension` valuation
inequality.  A later Henselian local-integral-closure theorem can combine this
with uniqueness of primes above the base maximal ideal to identify the center
with the maximal ideal of the constructed integral closure. -/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : CompleteDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.valuation)]
  change vL
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) < 1 ↔
    base.valuation (a : K) < 1
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) =
        algebraMap K L (a : K) := by
    rfl
  rw [hcoe]
  exact Valuation.HasExtension.val_map_lt_one_iff base.valuation vL (a : K)

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal.

The proof uses real structure, not a certificate: the constructed valuation
ring is the actual integral closure, hence Dedekind over the base DVR; a prime
whose contraction is the base maximal ideal is nonzero by injectivity of the
canonical integer map, hence maximal by the dimension-one property, and then
equal to the unique maximal ideal because the constructed ring is local. -/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let : Algebra base.valuationSubring B := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain base.valuationSubring K L B
  have hi : Function.Injective i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv_injective
      (K := K) (L := L) base hval
  have hP_ne_bot : P ≠ ⊥ := by
    have hnot_le_bot : ¬ base.maximalIdeal ≤ ⊥ := by
      intro hle
      exact base.maximalIdeal_ne_bot (le_antisymm hle bot_le)
    obtain ⟨a, ha_max, ha_not_bot⟩ := Set.not_subset.mp hnot_le_bot
    have ha_ne_zero : a ≠ 0 := by
      intro ha
      exact ha_not_bot (by simp [ha])
    intro hPbot
    have ha_comap : a ∈ P.comap i := by
      simpa [B, i, hcomap] using ha_max
    have hai_mem : i a ∈ P := by
      simpa [Ideal.mem_comap] using ha_comap
    have hai_zero : i a = 0 := by
      simpa [hPbot] using hai_mem
    exact ha_ne_zero (hi (by simpa using hai_zero))
  exact IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_ne_bot)

omit [FiniteDimensional K L] in
/-- The local-Dedekind fundamental identity in record-free form: for the actual
valuation rings attached to a finite valued field extension, mathlib's
ramification index times mathlib's inertia degree is the field degree. -/
theorem ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring = Module.finrank K L := by
  exact (isDefectless_of_moduleFinite base.toDVF target.toDVF).symm

/-- If the target valuation ring is the integral closure of the base valuation
ring in a finite separable field extension, then the local-Dedekind
ramification identity holds without separately assuming module-finiteness. -/
theorem ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring = Module.finrank K L := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_isIntegralClosure
      (K := K) (L := L) base target
  exact ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
    (K := K) (L := L) base target

























/-- A valued extension whose target is the integral closure is defectless. -/
theorem isDefectless_of_isIntegralClosure
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    ValuedExtension.IsDefectless base.toDVF target.toDVF := by
  change Module.finrank K L =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring
  exact (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
    (K := K) (L := L) base target).symm

omit [FiniteDimensional K L] in
/-- The target maximal ideal lies over the base maximal ideal for a valued
extension. -/
theorem maximalIdeal_liesOver :
    target.maximalIdeal.LiesOver base.maximalIdeal :=
  maximalIdeal_liesOver_of_hasExtension (K := K) (L := L) base target

omit [FiniteDimensional K L] in
/-- Residue degree is the linear rank of the target residue field over the source residue field. -/
theorem residueDegree_eq_finrank_quotient
     :
    letI : target.maximalIdeal.LiesOver base.maximalIdeal :=
      (maximalIdeal_liesOver base target)
    (ValuedExtension.residueDegree base.toDVF target.toDVF) =
      Module.finrank
        (base.valuationSubring ⧸ base.maximalIdeal)
        (target.valuationSubring ⧸ target.maximalIdeal) := by
  exact Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal

omit [FiniteDimensional K L] in
/-- The residue degree of a finite extension is strictly positive. -/
theorem residueDegree_pos
    [Module.Finite base.valuationSubring target.valuationSubring] :
    0 < (ValuedExtension.residueDegree base.toDVF target.toDVF) := by
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    (maximalIdeal_liesOver base target)
  simpa [residueDegree, residueDegree] using
    (target.maximalIdeal.inertiaDeg_pos base.valuationSubring)

omit [FiniteDimensional K L] in
/-- A finite extension of valuation rings induces a finite-dimensional residue
field extension.  This is the source behind using a primitive element for the
residue extension: mathlib's inertia degree is the residue-field `finrank`. -/
theorem residueField_finiteDimensional_of_moduleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional base.residueField target.residueField := by
  have h := residueDegree_pos base target
  rw [residueDegree_eq_finrank_quotient base target] at h
  exact FiniteDimensional.of_finrank_pos h



omit [FiniteDimensional K L] in
/-- The ramification index of a finite extension is nonzero. -/
theorem ramificationIndex_ne_zero
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) ≠ 0 := by
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    (maximalIdeal_liesOver base target)
  simpa [ramificationIndex] using
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      target.maximalIdeal base.maximalIdeal_ne_bot)

omit [FiniteDimensional K L] in
/-- The actual local-Dedekind fundamental identity for the chosen valuation
rings: in the local case, the mathlib ramification index times the mathlib
inertia degree is the field degree. -/
theorem ramificationIndex_mul_residueDegree_eq_degree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) *
        ValuedExtension.residueDegree base.toDVF target.toDVF =
      ValuedExtension.degree base.toDVF target.toDVF := by
  simpa [ramificationIndex, residueDegree,
    ramificationIndex, residueDegree, degree] using
    (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
      (K := K) (L := L) base target)

/-- Integral-closure form of the local-Dedekind degree identity for a valued
finite separable extension. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) *
        ValuedExtension.residueDegree base.toDVF target.toDVF =
      ValuedExtension.degree base.toDVF target.toDVF := by
  simpa [ramificationIndex, residueDegree,
    ramificationIndex, residueDegree, degree] using
    (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
      (K := K) (L := L) base target)










end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
