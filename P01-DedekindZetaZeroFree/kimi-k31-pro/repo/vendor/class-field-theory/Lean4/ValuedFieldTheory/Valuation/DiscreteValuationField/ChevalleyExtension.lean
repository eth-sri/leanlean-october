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
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- A valuation on `K` has some extension to the field extension `L / K`.

Chevalley's extension theorem is precisely the general existence theorem for
this predicate under algebraic field-extension hypotheses. -/
def HasSomeExtensionTo (vK : _root_.Valuation K ΓK) : Prop :=
  ∃ ΓL : Type v,
    ∃ _ : LinearOrderedCommGroupWithZero ΓL,
      ∃ vL : _root_.Valuation L ΓL, vK.HasExtension vL

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
    let f : A →+* B.toSubring :=
      (algebraMap A L).codRestrict B.toSubring hB
    let : IsLocalHom f := by
      dsimp [f, A]
      exact hlocal
    have hfy_unit : IsUnit (f y) := by
      apply IsUnit.of_mul_eq_one (⟨algebraMap K L x, hxB⟩ : B.toSubring)
      ext
      change (algebraMap K L) (x⁻¹) * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hy_unit : IsUnit y := IsUnit.of_map f y hfy_unit
    have hy_val : A.valuation (x⁻¹) = 1 := by
      simpa [y] using (A.valuation_eq_one_iff y).1 hy_unit
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
    have hxB :
        algebraMap vK.valuationSubring L
            (⟨x, hxA⟩ : vK.valuationSubring) ∈ B.toSubring :=
      hB ⟨x, hxA⟩
    rw [IsScalarTower.algebraMap_apply vK.valuationSubring K L] at hxB
    simpa using hxB

/-- Exact pullback of valuation subrings gives a `HasExtension` proof for the
canonical valuation attached to the target valuation subring. -/
theorem hasExtension_valuation_of_valuationSubring_pullback
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    (hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
      x ∈ vK.valuationSubring) :
    vK.HasExtension B.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  apply le_antisymm
  · intro x hx
    have hxB : algebraMap K L x ∈ B.toSubring := by
      exact B.mem_of_valuation_le_one _ hx
    have hxA : x ∈ vK.valuationSubring := (hpullback x).1 hxB
    exact (vK.mem_integer_iff x).2
      ((vK.mem_valuationSubring_iff x).2 hxA)
  · intro x hx
    have hxA : x ∈ vK.valuationSubring := by
      exact (vK.mem_valuationSubring_iff x).1
        ((vK.mem_integer_iff x).1 hx)
    have hxB : algebraMap K L x ∈ B.toSubring := (hpullback x).2 hxA
    exact (B.valuation_le_one_iff (algebraMap K L x)).2 hxB

/-- A `HasExtension` proof for the canonical valuation attached to a valuation
subring gives exact pullback of valuation subrings. -/
theorem valuationSubring_pullback_of_hasExtension_valuation
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    [vK.HasExtension B.valuation] (x : K) :
    algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring := by
  constructor
  · intro hxB
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (B.valuation_le_one_iff (algebraMap K L x)).2 hxB
    have hxK_le : vK x ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).1 hx_le
    exact (vK.mem_valuationSubring_iff x).1 hxK_le
  · intro hxK
    have hxK_le : vK x ≤ 1 :=
      (vK.mem_valuationSubring_iff x).2 hxK
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).2 hxK_le
    exact (B.valuation_le_one_iff (algebraMap K L x)).1 hx_le



/-- Every element integral over the base valuation ring lies in any valuation
ring extending the base valuation.  This is the valuation-theoretic integral
closure bridge used before specializing to complete or Henselian DVFs. -/
theorem integralClosure_mem_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] (z : integralClosure vK.valuationSubring L) :
    (z : L) ∈ vL.valuationSubring := by
  have hz_base : IsIntegral vK.valuationSubring (z : L) :=
    z.2
  have hz_target : IsIntegral vL.valuationSubring (z : L) :=
    IsIntegral.tower_top (A := vL.valuationSubring) hz_base
  exact _root_.Valuation.Integers.mem_of_integral
    (_root_.Valuation.valuationSubring.integers (v := vL)) hz_target

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
    have ha_integral_L : IsIntegral A (algebraMap K L a) := ha
    have ha_integral_K : IsIntegral A a := by
      let f : K →ₐ[A] L := IsScalarTower.toAlgHom A K L
      exact (isIntegral_algHom_iff f (RingHom.injective _)).mp ha_integral_L
    have hclosed : IsIntegrallyClosedIn A K :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := A) (K := K)).mp
        inferInstance
    let : IsIntegrallyClosedIn A K := hclosed
    rcases IsIntegrallyClosedIn.algebraMap_eq_of_integral
        (R := A) (A := K) ha_integral_K with
      ⟨b, hb⟩
    rw [← hb]
    exact b.2
  · intro ha
    change algebraMap A L (⟨a, ha⟩ : A) ∈
      (integralClosure A L).toSubring
    exact algebraMap_mem (integralClosure A L) (⟨a, ha⟩ : A)

/-- If the actual integral closure over the base valuation ring satisfies the
valuation-ring dichotomy inside the extension field, then it is the underlying
subring of an actual `ValuationSubring L`.

This is not a replacement for the Henselian uniqueness theorem: the remaining
frontier is to prove the dichotomy from Henselian hypotheses.  The theorem
constructs the valuation object that that proof will feed into. -/
def integralClosureValuationSubringOfMemOrInv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    ValuationSubring L :=
  ValuationSubring.ofSubring
    (integralClosure vK.valuationSubring L).toSubring hval

/-- The Chevalley valuation ring contains every integral element or its inverse. -/
@[simp] theorem mem_integralClosureValuationSubringOfMemOrInv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (z : L) :
    z ∈ integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      z ∈ (integralClosure vK.valuationSubring L).toSubring :=
  ValuationSubring.mem_ofSubring _ _ z

/-- The valuation subring built from the actual integral closure has exact
base-field pullback. -/
theorem integralClosureValuationSubringOfMemOrInv_pullback
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (a : K) :
    algebraMap K L a ∈
        integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      a ∈ vK.valuationSubring := by
  rw [mem_integralClosureValuationSubringOfMemOrInv]
  exact algebraMap_mem_integralClosure_valuationSubring_iff (L := L) vK a

/-- Once the actual integral closure over the base valuation ring has been
proved to be a valuation subring, its canonical valuation is an extension of
the base valuation. -/
theorem integralClosureValuationSubringOfMemOrInv_hasExtension
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    vK.HasExtension
      (integralClosureValuationSubringOfMemOrInv (L := L) vK hval).valuation := by
  exact hasExtension_valuation_of_valuationSubring_pullback vK
    (integralClosureValuationSubringOfMemOrInv (L := L) vK hval)
    (integralClosureValuationSubringOfMemOrInv_pullback (L := L) vK hval)

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
  let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
  let : vK.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension (L := L) vK hval
  change IsIntegralClosure B vK.valuationSubring L
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    refine ⟨⟨z, ?_⟩, ?_⟩
    · exact
        (mem_integralClosureValuationSubringOfMemOrInv
          (L := L) vK hval z).2 hz
    · rfl
  · rintro ⟨y, rfl⟩
    exact
      (mem_integralClosureValuationSubringOfMemOrInv
        (L := L) vK hval (y : L)).1 y.2

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
  have hz_integral :
      z ∈ (integralClosure vK.valuationSubring L).toSubring := by
    exact
      (mem_integralClosureValuationSubringOfMemOrInv
        (L := L) vK hval z).1 hz
  exact integralClosure_mem_valuationSubring_of_hasExtension
    (L := L) vK vL ⟨z, hz_integral⟩





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
    change (IsLocalRing.maximalIdeal R).comap (R.inclusion R le_rfl) =
      IsLocalRing.maximalIdeal R
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















/-- The canonical map from the actual integral closure of the base valuation
ring to any valuation ring extending the base valuation. -/
def integralClosureToValuationSubringOfHasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
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
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    (z : integralClosure vK.valuationSubring L) :
    ((integralClosureToValuationSubringOfHasExtension
      (L := L) vK vL z : vL.valuationSubring) : L) = z :=
  rfl



/-- If an extension valuation ring is finite over the base valuation ring, then
each of its elements is integral over the base valuation ring. -/
theorem valuationSubring_mem_integralClosure_of_moduleFinite
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) :
    (z : L) ∈ integralClosure vK.valuationSubring L := by
  have hz_ring : IsIntegral vK.valuationSubring z :=
    IsIntegral.of_finite vK.valuationSubring z
  have hz_field : IsIntegral vK.valuationSubring
      (algebraMap vL.valuationSubring L z) :=
    hz_ring.map
      (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L)
  rw [mem_integralClosure_iff]
  simpa using hz_field

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
  have hz_ring : IsIntegral vK.valuationSubring z :=
    Algebra.IsIntegral.isIntegral (R := vK.valuationSubring) z
  have hz_field : IsIntegral vK.valuationSubring
      (algebraMap vL.valuationSubring L z) :=
    hz_ring.map
      (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L)
  rw [mem_integralClosure_iff]
  simpa using hz_field

/-- The reverse map from a module-finite extension valuation ring into the
actual integral closure. -/
def valuationSubringToIntegralClosureOfModuleFinite
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
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
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) :
    ((valuationSubringToIntegralClosureOfModuleFinite
      (L := L) vK vL z : integralClosure vK.valuationSubring L) : L) = z :=
  rfl









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
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    refine ⟨integralClosureToValuationSubringOfHasExtension
      (L := L) vK vL ⟨z, hz⟩, ?_⟩
    rfl
  · rintro ⟨y, rfl⟩
    exact valuationSubring_mem_integralClosure_of_isIntegral
      (L := L) vK vL y









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
  let : IsFractionRing vK.valuationSubring K :=
    (_root_.Valuation.valuationSubring.integers (v := vK)).isFractionRing
  let : IsIntegrallyClosed vK.valuationSubring := by
    infer_instance
  exact IsIntegralClosure.finite vK.valuationSubring K L vL.valuationSubring













/-- Chevalley's theorem in construction form, keeping the dominating valuation
subring and the `HasExtension` proof attached to its canonical valuation. -/
theorem exists_extension_valuationSubring_with_hasExtension
    (vK : _root_.Valuation K ΓK) :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : vK.valuationSubring,
        algebraMap vK.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
        (∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ vK.valuationSubring) ∧
        vK.HasExtension B.valuation := by
  obtain ⟨B, hB, hlocal, hpullback⟩ :=
    exists_extension_valuationSubring (L := L) vK
  refine ⟨B, hB, hlocal, hpullback, ?_⟩
  exact hasExtension_valuation_of_valuationSubring_pullback vK B hpullback



/-- Chevalley's construction can be chosen with the integral-closure dominance
made explicit: the produced extension valuation ring contains the actual
integral closure of the base valuation ring in the extension field. -/
theorem exists_extension_valuationSubring_with_integralClosure
    (vK : _root_.Valuation K ΓK) :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : vK.valuationSubring,
        algebraMap vK.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
        (∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ vK.valuationSubring) ∧
        vK.HasExtension B.valuation ∧
        (∀ z : integralClosure vK.valuationSubring L,
          (z : L) ∈ B.toSubring) := by
  obtain ⟨B, hB, hlocal, hpullback, hExt⟩ :=
    exists_extension_valuationSubring_with_hasExtension (L := L) vK
  let : vK.HasExtension B.valuation := hExt
  refine ⟨B, hB, hlocal, hpullback, hExt, ?_⟩
  intro z
  have hz : (z : L) ∈ B.valuation.valuationSubring :=
    integralClosure_mem_valuationSubring_of_hasExtension
      (L := L) vK B.valuation z
  simpa [ValuationSubring.valuationSubring_valuation] using hz

/-- Chevalley's valuation extension can be chosen with both exact pullback of
the valuation ring and containment of the actual integral closure of the base
valuation ring. -/
theorem chevalley_exists_extension_valuation_with_pullback_integralClosure
    (vK : _root_.Valuation K ΓK) :
    ∃ ΓL : Type v,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ _ : vK.HasExtension vL,
            (∀ x : K, algebraMap K L x ∈ vL.valuationSubring ↔
              x ∈ vK.valuationSubring) ∧
            (∀ z : integralClosure vK.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) := by
  obtain ⟨B, _hB, _hlocal, hpullback, hExt, hIntegral⟩ :=
    exists_extension_valuationSubring_with_integralClosure (L := L) vK
  refine ⟨B.ValueGroup, inferInstance, B.valuation, hExt, ?_⟩
  constructor
  · intro x
    simpa [ValuationSubring.valuationSubring_valuation] using hpullback x
  · intro z
    simpa [ValuationSubring.valuationSubring_valuation] using hIntegral z

/-- Chevalley's valuation extension with all construction-level data attached
to the same witness: exact valuation-ring pullback, integral-closure
containment, lies-over for maximal ideals, local valuation-ring map, and
injective residue-field map. -/
theorem chevalley_exists_extension_valuation_with_pullback_integralClosure_local_data
    (vK : _root_.Valuation K ΓK) :
    ∃ ΓL : Type v,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ _ : vK.HasExtension vL,
            (∀ x : K, algebraMap K L x ∈ vL.valuationSubring ↔
              x ∈ vK.valuationSubring) ∧
            (∀ z : integralClosure vK.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) ∧
            (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
              (IsLocalRing.maximalIdeal vK.valuationSubring) ∧
            IsLocalHom
              (algebraMap vK.valuationSubring vL.valuationSubring) ∧
            Function.Injective
              (IsLocalRing.ResidueField.map
                (algebraMap vK.valuationSubring vL.valuationSubring)) := by
  obtain ⟨ΓL, hΓL, vL, hExt, hpullback, hIntegral⟩ :=
    chevalley_exists_extension_valuation_with_pullback_integralClosure
      (L := L) vK
  let : LinearOrderedCommGroupWithZero ΓL := hΓL
  let : vK.HasExtension vL := hExt
  refine ⟨ΓL, inferInstance, vL, inferInstance, hpullback, hIntegral, ?_⟩
  exact ⟨inferInstance, inferInstance,
    map_algebraMap_injective
      (R := vK.valuationSubring) (S := vL.valuationSubring)⟩

/-- Chevalley's valuation extension theorem: every valuation on a field extends
to any field extension.  The extended value group is the canonical value group
of a valuation subring of the extension field supplied by mathlib's maximal
local subring theorem. -/
theorem chevalley_hasSomeExtensionTo
    (vK : _root_.Valuation K ΓK) :
    HasSomeExtensionTo (L := L) vK := by
  obtain ⟨B, _hB, _hlocal, _hpullback, hExt⟩ :=
    exists_extension_valuationSubring_with_hasExtension (L := L) vK
  exact ⟨B.ValueGroup, inferInstance, B.valuation, hExt⟩



/-- The target valuation subring lies over the source valuation subring. -/
theorem valuationSubring_liesOver_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
      (IsLocalRing.maximalIdeal vK.valuationSubring) :=
  inferInstance

/-- The integer map induced by a valuation extension is a local ring homomorphism. -/
theorem integerMap_isLocalHom_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    IsLocalHom (algebraMap vK.valuationSubring vL.valuationSubring) :=
  inferInstance

/-- The valuation-subring algebra maps are compatible with the ambient field
algebra map for any chosen valuation extension. -/
theorem valuationSubring_isScalarTower_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    IsScalarTower vK.valuationSubring vL.valuationSubring L := by
  refine ⟨?_⟩
  intro a b z
  simp only [Algebra.smul_def]
  have hmap :
      (algebraMap vL.valuationSubring L)
          ((algebraMap vK.valuationSubring vL.valuationSubring) a) =
        (algebraMap vK.valuationSubring L) a := by
    rfl
  rw [map_mul, hmap, mul_assoc]















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
  rw [vM.mem_integer_iff, vK.mem_integer_iff]
  rw [IsScalarTower.algebraMap_apply K L M a]
  exact
    (_root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := vL) (vA := vM) (algebraMap K L a)).trans
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := vK) (vA := vL) a)









end Tower



end Valuation
end DiscreteValuationField

end

end ValuationTheory
