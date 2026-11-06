module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Unramified norm subgroups

For a nonarchimedean local field, the norm subgroup of an unramified
extension of degree n is characterized by divisibility of the normalized
valuation by n. This file packages that subgroup, its quotient map, and
the canonical identification of the quotient with ZMod n.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

section
variable (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat)
include K n
/-- The normalized valuation map reduced modulo a positive or zero degree n. -/
noncomputable def valuationModDegree    :=
  (Int.castAddHom (ZMod n)).comp (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K)

/-- Evaluates the normalized valuation map after reduction modulo `n`. -/
@[simp]
theorem valuationModDegree_apply   (x : Additive Kˣ) :
    valuationModDegree K n x =
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n) :=
  rfl

/-- The normalized valuation remains surjective after reduction modulo `n`. -/
theorem valuationModDegree_surjective   :
    Function.Surjective (valuationModDegree K n) := by
  intro z
  rcases ZMod.intCast_surjective z with ⟨m, rfl⟩
  rcases LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact congrArg (fun t : ℤ => (t : ZMod n)) hx

/-- A reduced valuation vanishes exactly when `n` divides the original valuation. -/
theorem valuationModDegree_eq_zero_iff_dvd   (x : Additive Kˣ) :
    valuationModDegree K n x = 0 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x := by
  rw [valuationModDegree_apply]
  apply ZMod.intCast_zmod_eq_zero_iff_dvd










/-- Multiplicative form of the normalized valuation map modulo a degree. -/
noncomputable def valuationModDegreeMulHom    :=
  AddMonoidHom.toMultiplicativeRight (valuationModDegree K n)

/-- Evaluates the multiplicative form of the valuation-modulo-degree map. -/
@[simp]
theorem valuationModDegreeMulHom_apply   (x : Kˣ) :
    valuationModDegreeMulHom K n x =
      Multiplicative.ofAdd
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) : ZMod n) :=
  rfl

/-- The multiplicative valuation-modulo-degree map is surjective. -/
theorem valuationModDegreeMulHom_surjective   :
    Function.Surjective (valuationModDegreeMulHom K n) := by
  intro z
  rcases valuationModDegree_surjective K n (Multiplicative.toAdd z) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  apply Multiplicative.toAdd.injective
  simpa using hx

/-- A unit maps to one exactly when its valuation is divisible by `n`. -/
theorem valuationModDegreeMulHom_eq_one_iff_dvd   (x : Kˣ) :
    valuationModDegreeMulHom K n x = 1 ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  change valuationModDegree K n (Additive.ofMul x) = 0 ↔ _
  apply valuationModDegree_eq_zero_iff_dvd













/-- The unramified norm subgroup of degree `n`: field units whose normalized
valuation lies in `nℤ`. -/
def unramifiedNormSubgroup   : Subgroup Kˣ where
  carrier := {x | (n : Int) ∣
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)}
  one_mem' := by
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (1 : Kˣ))
    rw [show Additive.ofMul (1 : Kˣ) = 0 by rfl, map_zero]
    exact dvd_zero (n : Int)
  mul_mem' := by
    intro x y hx hy
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (x * y))
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y by rfl,
      map_add]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x⁻¹)
    rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x by rfl, map_neg]
    exact dvd_neg.mpr hx

/-- Characterizes the unramified norm subgroup by divisibility of the normalized valuation. -/
theorem mem_unramifiedNormSubgroup_iff   (x : Kˣ) :
    x ∈ unramifiedNormSubgroup K n ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) :=
  Iff.rfl

/-- The quotient map from field units to degree-`n` unramified norm classes. -/
def unramifiedNormClass    :=
  QuotientGroup.mk' (unramifiedNormSubgroup K n)

/-- Every unramified norm class is represented by a field unit. -/
def unramifiedNormClass_surjective    :=
  QuotientGroup.mk'_surjective (unramifiedNormSubgroup K n)








/-- A unit has trivial norm class exactly when its valuation is divisible by the degree. -/
theorem unramifiedNormClass_eq_one_iff   (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := (QuotientGroup.eq_one_iff (N := unramifiedNormSubgroup K n) x).trans
    (mem_unramifiedNormSubgroup_iff K n x)

/-- A unit has trivial norm class exactly when it belongs to the unramified norm subgroup. -/
theorem unramifiedNormClass_eq_one_iff_mem   (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔ x ∈ unramifiedNormSubgroup K n := by
  rw [unramifiedNormClass_eq_one_iff, mem_unramifiedNormSubgroup_iff]

/-- The unramified norm subgroup is the kernel of the multiplicative reduced valuation. -/
theorem unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom   :
    MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n := by
  ext x
  rw [MonoidHom.mem_ker, mem_unramifiedNormSubgroup_iff,
    valuationModDegreeMulHom_eq_one_iff_dvd]








/-- The valuation quotient model
`Kˣ / {x | n ∣ v(x)} ≃ Z/nZ`, in multiplicative notation. -/
noncomputable def unramifiedNormQuotientEquivZMod   :
    Kˣ ⧸ unramifiedNormSubgroup K n ≃* Multiplicative (ZMod n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom K n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (valuationModDegreeMulHom K n)
      (valuationModDegreeMulHom_surjective K n))

/-- The quotient equivalence sends a unit class to its valuation modulo the degree. -/
@[simp]
theorem unramifiedNormQuotientEquivZMod_mk   (x : Kˣ) :
    unramifiedNormQuotientEquivZMod K n (QuotientGroup.mk x) =
      valuationModDegreeMulHom K n x := by
  simp only [unramifiedNormQuotientEquivZMod, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]



















/-- For nonzero degree, the unramified norm quotient has cardinality equal to that degree. -/
theorem unramifiedNormQuotient_card_eq_degree   [NeZero n] :
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n := by
  calc
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) =
        Nat.card (Multiplicative (ZMod n)) :=
      Nat.card_congr (unramifiedNormQuotientEquivZMod K n).toEquiv
    _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
    _ = n := Nat.card_zmod n
end




















































end LocalClassFieldTheory

end
