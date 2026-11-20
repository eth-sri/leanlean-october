module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.Integral

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace ValuationTheory

/-!
# Chevalley's valuation extension theorem

Mathlib has the predicate `Valuation.HasExtension` and the induced valuation
subring/residue-field API.  This file proves the field-extension form of
Chevalley's valuation extension theorem from mathlib's maximal local subring
construction: a local subring of a field is dominated by a valuation subring.
-/

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace Valuation

open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- If a valuation subring `B` of the extension field dominates the base
valuation ring locally, then any base-field element whose image lies in `B`
already lies in the base valuation ring. -/
theorem mem_base_valuationSubring_of_lift_mem
    (vK : _root_.Valuation K ΓK)
    (B : ValuationSubring L)
    (hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring)
    (hlocal : IsLocalHom
      ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB))
    {x : K} (hxB : algebraMap K L x ∈ B.toSubring) :
    x ∈ vK.valuationSubring := by
  let A := vK.valuationSubring
  rcases A.mem_or_inv_mem x with hxA | hxinvA
  · exact hxA
  · by_cases hx0 : x = 0
    · simp [hx0]
    let y : A := ⟨x⁻¹, hxinvA⟩
    let f :=
      (algebraMap A L).codRestrict B.toSubring hB
    let : IsLocalHom f := by
      exact hlocal
    have hfy_unit : IsUnit (f y) := by
      apply IsUnit.of_mul_eq_one (⟨algebraMap K L x, hxB⟩ : B.toSubring)
      ext
      change (algebraMap K L) (x⁻¹) * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hy_val : A.valuation (x⁻¹) = 1 := by
      simpa [y] using (A.valuation_eq_one_iff y).1 (IsUnit.of_map f y hfy_unit)
    have hx_val : A.valuation x = 1 := by
      rw [← inv_inv x, map_inv₀, hy_val, inv_one]
    exact A.mem_of_valuation_le_one x hx_val.le

/-- Chevalley's theorem in valuation-subring form.

For any field extension `L / K`, a valuation subring of `K` admits a dominating
valuation subring of `L`, and the original valuation subring is exactly the
pullback of the extension valuation subring along `K → L`.  This is the
construction-level statement behind `chevalley_hasSomeExtensionTo`; downstream
finite-extension arguments can use the returned subring `B` before passing to
its canonical valuation. -/
theorem exists_extension_valuationSubring
    (vK : _root_.Valuation K ΓK) :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : vK.valuationSubring,
        algebraMap vK.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
        ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ vK.valuationSubring := by
  obtain ⟨B, hB, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing
      (f := algebraMap vK.valuationSubring L)
  refine ⟨B, hB, hlocal, ?_⟩
  intro x
  constructor
  · intro hxB
    exact mem_base_valuationSubring_of_lift_mem vK B hB hlocal hxB
  · intro hxA
    have hxB :=
      hB ⟨x, hxA⟩
    exact hxB

section

variable (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)

/-- Exact pullback of valuation subrings gives a `HasExtension` proof for the
canonical valuation attached to the target valuation subring. -/
theorem hasExtension_valuation_of_valuationSubring_pullback
    (hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
      x ∈ vK.valuationSubring) :
    vK.HasExtension B.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  apply le_antisymm
  · intro x hx
    exact (vK.mem_integer_iff x).2
      ((vK.mem_valuationSubring_iff x).2 ((hpullback x).1 (B.mem_of_valuation_le_one _ hx)))
  · intro x hx
    exact (B.valuation_le_one_iff (algebraMap K L x)).2 ((hpullback x).2 ((vK.mem_valuationSubring_iff x).1
      ((vK.mem_integer_iff x).1 hx)))

/-- A `HasExtension` proof for the canonical valuation attached to a valuation
subring gives exact pullback of valuation subrings. -/
theorem valuationSubring_pullback_of_hasExtension_valuation
    [vK.HasExtension B.valuation] (x : K) :
    algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring := by
  constructor
  · intro hxB
    exact (vK.mem_valuationSubring_iff x).1 ((_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).1 ((B.valuation_le_one_iff (algebraMap K L x)).2 hxB))
  · intro hxK
    exact (B.valuation_le_one_iff (algebraMap K L x)).1 ((_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).2 ((vK.mem_valuationSubring_iff x).2 hxK))

end

/-- Every element integral over the base valuation ring lies in any valuation
ring extending the base valuation.  This is the valuation-theoretic integral
closure bridge used before specializing to complete or Henselian DVFs. -/
theorem integralClosure_mem_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] (z : integralClosure vK.valuationSubring L) :
    (z : L) ∈ vL.valuationSubring := by
  exact Valuation.Integers.mem_of_integral (Valuation.valuationSubring.integers vL) (IsIntegral.tower_top z.property)

/-- The actual integral closure over the base valuation ring has exact
pullback to the base field: a base-field element is integral over the base
valuation ring in the extension field exactly when it already belongs to the
base valuation ring.

This is the construction-level input needed to turn the actual integral
closure into a valuation subring extending `vK` once the Henselian frontier
proves the valuative dichotomy for that integral closure. -/
theorem algebraMap_mem_integralClosure_valuationSubring_iff
    (vK : _root_.Valuation K ΓK) (a : K) :
    algebraMap K L a ∈ (integralClosure vK.valuationSubring L).toSubring ↔
      a ∈ vK.valuationSubring := by
  let A := vK.valuationSubring
  constructor
  · intro ha
    have ha_integral_K : IsIntegral A a := by
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (RingHom.injective _)).mp ha
    rcases IsIntegrallyClosedIn.algebraMap_eq_of_integral
          ha_integral_K with
      ⟨b, hb⟩
    rw [← hb]
    exact b.2
  exact fun ha ↦ algebraMap_mem (integralClosure (↥A) L) ⟨a, ha⟩

section

variable (vK : _root_.Valuation K ΓK)
    (hval : ∀ z : L, z ∈ (integralClosure vK.valuationSubring L).toSubring ∨ z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)

/-- If the actual integral closure over the base valuation ring satisfies the
valuation-ring dichotomy inside the extension field, then it is the underlying
subring of an actual `ValuationSubring L`.

This is not a replacement for the Henselian uniqueness theorem: the remaining
frontier is to prove the dichotomy from Henselian hypotheses.  The theorem
constructs the valuation object that that proof will feed into. -/
def integralClosureValuationSubringOfMemOrInv :
    ValuationSubring L :=
  ValuationSubring.ofSubring
    (integralClosure vK.valuationSubring L).toSubring hval

/-- The Chevalley valuation ring contains every integral element or its inverse. -/
@[simp] theorem mem_integralClosureValuationSubringOfMemOrInv
    (z : L) :
    z ∈ integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      z ∈ (integralClosure vK.valuationSubring L).toSubring :=
  ValuationSubring.mem_ofSubring _ _ z

/-- The valuation subring built from the actual integral closure has exact
base-field pullback. -/
theorem integralClosureValuationSubringOfMemOrInv_pullback
    (a : K) :
    algebraMap K L a ∈
        integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      a ∈ vK.valuationSubring := by
  exact algebraMap_mem_integralClosure_valuationSubring_iff vK a

/-- Once the actual integral closure over the base valuation ring has been
proved to be a valuation subring, its canonical valuation is an extension of
the base valuation. -/
theorem integralClosureValuationSubringOfMemOrInv_hasExtension :
    vK.HasExtension
      (integralClosureValuationSubringOfMemOrInv (L := L) vK hval).valuation := hasExtension_valuation_of_valuationSubring_pullback vK
    (integralClosureValuationSubringOfMemOrInv vK hval)
    (integralClosureValuationSubringOfMemOrInv_pullback vK hval)

end

/-- The valuation subring built from the actual integral closure is the actual
integral closure of the base valuation ring in the extension field.

This removes the earlier packaging gap: after the Henselian frontier supplies
the valuative dichotomy for `integralClosure vK.valuationSubring L`, the
constructed valuation subring carries the canonical extension valuation and
satisfies the defining `IsIntegralClosure` equivalence, not merely equality of
underlying subrings. -/
theorem integralClosureValuationSubringOfMemOrInv_isIntegralClosure
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
    letI : vK.HasExtension B.valuation :=
      integralClosureValuationSubringOfMemOrInv_hasExtension (L := L) vK hval
    IsIntegralClosure B vK.valuationSubring L := by
  let B := integralClosureValuationSubringOfMemOrInv vK hval
  let :=
    integralClosureValuationSubringOfMemOrInv_hasExtension vK hval
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    solve_by_elim [Exists.intro]
  · rintro ⟨y, rfl⟩
    exact (mem_integralClosureValuationSubringOfMemOrInv vK hval ↑y).mp y.property

/-- The integral-closure valuation subring is contained in every valuation
subring whose canonical valuation extends the base valuation. -/
theorem integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    [vK.HasExtension vL] :
    integralClosureValuationSubringOfMemOrInv (L := L) vK hval ≤
      vL.valuationSubring := by
  intro z hz
  refine integralClosure_mem_valuationSubring_of_hasExtension
     vK vL ⟨z, ?_⟩
  exact (mem_integralClosureValuationSubringOfMemOrInv
  vK hval z).1 hz

/-- Construction-level package for the actual integral-closure valuation
subring, including the integral-closure proof itself.  The second witness is
kept explicit so downstream proofs can install it as an instance only where
they need the induced algebra structure from the base valuation ring. -/
theorem exists_integralClosure_valuationSubring_isIntegralClosure_of_forall_mem_or_inv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    ∃ B : ValuationSubring L,
      ∃ hExt : vK.HasExtension B.valuation,
        letI : vK.HasExtension B.valuation := hExt
        B.toSubring = (integralClosure vK.valuationSubring L).toSubring ∧
          IsIntegralClosure B vK.valuationSubring L := by
  let B := integralClosureValuationSubringOfMemOrInv vK hval
  let hExt :=
    integralClosureValuationSubringOfMemOrInv_hasExtension vK hval
  refine ⟨B, hExt, ?_⟩
  exact ⟨rfl, integralClosureValuationSubringOfMemOrInv_isIntegralClosure
     vK hval⟩

/-- A valuation overring of a valuation subring is equal to it when the
corresponding localization prime is the maximal ideal of the smaller valuation
subring.  This is the prime-theoretic comparison bridge used after proving
that an integral closure has a unique prime above the base maximal ideal. -/
theorem valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
    (R S : ValuationSubring L) (hRS : R ≤ S)
    (hcenter :
      ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R) :
    S = R := by
  have hcenter_self :
      ValuationSubring.idealOfLE R R le_rfl = IsLocalRing.maximalIdeal R := by
    ext x
    rfl
  have hle :
      ValuationSubring.idealOfLE R R le_rfl ≤
        ValuationSubring.idealOfLE R S hRS := by
    intro x hx
    rw [hcenter_self] at hx
    rw [hcenter]
    exact hx
  have hOfPrime :
      ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R S hRS) ≤
        ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R R le_rfl) :=
    ValuationSubring.ofPrime_le_of_le (A := R)
      (ValuationSubring.idealOfLE R R le_rfl)
      (ValuationSubring.idealOfLE R S hRS) hle
  have hSR : S ≤ R := by
    intro x hx
    have hx' :
        x ∈ ValuationSubring.ofPrime R
          (ValuationSubring.idealOfLE R S hRS) := by
      rwa [ValuationSubring.ofPrime_idealOfLE R S hRS]
    have hx'' := hOfPrime hx'
    rwa [ValuationSubring.ofPrime_idealOfLE R R le_rfl] at hx''
  exact le_antisymm hSR hRS

section

variable {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL] (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL) [vK.HasExtension vL]

/-- The canonical map from the actual integral closure of the base valuation
ring to any valuation ring extending the base valuation. -/
def integralClosureToValuationSubringOfHasExtension :
    integralClosure vK.valuationSubring L →+* vL.valuationSubring where
  toFun z :=
    ⟨(z : L),
      integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) vK vL z⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' z₁ z₂ := by ext; simp
  map_mul' z₁ z₂ := by ext; simp

/-- The canonical map from the integral closure to an extending valuation ring is inclusion. -/
@[simp] theorem integralClosureToValuationSubringOfHasExtension_apply
    (z : integralClosure vK.valuationSubring L) :
    ((integralClosureToValuationSubringOfHasExtension
      (L := L) vK vL z : vL.valuationSubring) : L) = z :=
  rfl

/-- If an extension valuation ring is finite over the base valuation ring, then
each of its elements is integral over the base valuation ring. -/
theorem valuationSubring_mem_integralClosure_of_moduleFinite
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) :
    (z : L) ∈ integralClosure vK.valuationSubring L := by
  exact ((IsIntegral.of_finite vK.valuationSubring z).map
    (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L))

end

/-- If an extension valuation ring is integral over the base valuation ring,
then every target valuation-ring element lies in the actual integral closure.
This is the construction-level condition needed in the Henselian
finite-extension frontier. -/
theorem valuationSubring_mem_integralClosure_of_isIntegral
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) :
    (z : L) ∈ integralClosure vK.valuationSubring L := by
  exact ((Algebra.IsIntegral.isIntegral z).map
    (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L))

section

variable {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL] (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL) [vK.HasExtension vL]
    [Module.Finite vK.valuationSubring vL.valuationSubring]

/-- The reverse map from a module-finite extension valuation ring into the
actual integral closure. -/
def valuationSubringToIntegralClosureOfModuleFinite :
    vL.valuationSubring →+* integralClosure vK.valuationSubring L where
  toFun z :=
    ⟨(z : L),
      valuationSubring_mem_integralClosure_of_moduleFinite
        (L := L) vK vL z⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' z₁ z₂ := by ext; simp
  map_mul' z₁ z₂ := by ext; simp

/-- Under module finiteness, a valuation-ring element maps to its integral-closure class. -/
@[simp] theorem valuationSubringToIntegralClosureOfModuleFinite_apply
    (z : vL.valuationSubring) :
    ((valuationSubringToIntegralClosureOfModuleFinite
      (L := L) vK vL z : integralClosure vK.valuationSubring L) : L) = z :=
  rfl

end

/-- An extension valuation ring that is integral over the base valuation ring is
the actual integral closure of the base valuation ring in the field extension.
No finite-module certificate is introduced here; the proof is the defining
integral-closure equivalence. -/
theorem valuationSubring_isIntegralClosure_of_isIntegral
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring] :
    IsIntegralClosure vL.valuationSubring vK.valuationSubring L := by
  apply IsIntegralClosure.of_isIntegrallyClosed

/-- If an extension valuation ring is already the actual integral closure in a
finite separable field extension over a Noetherian base valuation ring, then it
is finite over the base valuation ring.  This is the generic finite-extension
input needed before specializing uniqueness of valuation extensions to
Henselian DVFs. -/
theorem moduleFinite_valuationSubring_of_isIntegralClosure
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsNoetherianRing vK.valuationSubring]
    [IsIntegralClosure vL.valuationSubring vK.valuationSubring L] :
    Module.Finite vK.valuationSubring vL.valuationSubring := by
  exact IsIntegralClosure.finite vK.valuationSubring K L vL.valuationSubring

section

variable {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL] (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL) [vK.HasExtension vL]

/-- The target valuation subring lies over the source valuation subring. -/
theorem valuationSubring_liesOver_of_hasExtension :
    (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
      (IsLocalRing.maximalIdeal vK.valuationSubring) :=
  inferInstance

/-- The valuation-subring algebra maps are compatible with the ambient field
algebra map for any chosen valuation extension. -/
theorem valuationSubring_isScalarTower_of_hasExtension :
    IsScalarTower vK.valuationSubring vL.valuationSubring L := by
  apply Valuation.HasExtension.instIsScalarTower_valuationSubring'

end

section Tower

variable {M : Type y} [Field M]
variable [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable {ΓL : Type x} {ΓM : Type z}
variable [LinearOrderedCommGroupWithZero ΓL]
variable [LinearOrderedCommGroupWithZero ΓM]

/-- Valuation extension is transitive in a field tower. -/
theorem hasExtension_trans
    (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL)
    (vM : _root_.Valuation M ΓM)
    [vK.HasExtension vL] [vL.HasExtension vM] :
    vK.HasExtension vM := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp only [Subring.mem_comap]
  rw [IsScalarTower.algebraMap_apply K L M a]
  exact
    (_root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := vL) (vA := vM) (algebraMap K L a)).trans
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := vK) (vA := vL) a)

/-- The valuation-ring algebra maps in a tower agree with the direct
valuation-ring algebra map.  The direct `HasExtension` instance can be supplied
by `hasExtension_trans`. -/
theorem integerMap_comp_of_hasExtension_tower
    (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL)
    (vM : _root_.Valuation M ΓM)
    [vK.HasExtension vL] [vL.HasExtension vM] [vK.HasExtension vM] :
    (algebraMap vL.valuationSubring vM.valuationSubring).comp
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      algebraMap vK.valuationSubring vM.valuationSubring := by
  ext a
  exact (IsScalarTower.algebraMap_apply K L M (a : K)).symm

/-- Residue-field maps in a tower compose to the direct residue-field map.  The
direct `HasExtension` instance can be supplied by `hasExtension_trans`. -/
theorem residueMap_comp_of_hasExtension_tower
    (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL)
    (vM : _root_.Valuation M ΓM)
    [vK.HasExtension vL] [vL.HasExtension vM] [vK.HasExtension vM] :
    (IsLocalRing.ResidueField.map
        (algebraMap vL.valuationSubring vM.valuationSubring)).comp
        (IsLocalRing.ResidueField.map
          (algebraMap vK.valuationSubring vL.valuationSubring)) =
      IsLocalRing.ResidueField.map
        (algebraMap vK.valuationSubring vM.valuationSubring) := by
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ congrArg (⇑(IsLocalRing.residue ↥vM.valuationSubring)) (congrArg (fun f ↦ f a) (integerMap_comp_of_hasExtension_tower vK vL vM)))

end Tower

end Valuation
end DiscreteValuationField

end

end ValuationTheory
