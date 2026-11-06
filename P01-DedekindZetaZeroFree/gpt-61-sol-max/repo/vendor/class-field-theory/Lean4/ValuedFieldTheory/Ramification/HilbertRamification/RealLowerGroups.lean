module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Real lower ramification groups

This file gives the intrinsic definitions and the elementary structural
facts in the real lower-ramification definition and the lower-ramification base-change law.  It uses
discretely valued fields, not complete discretely valued fields.  The unique
extension hypothesis is stated for `DVF` itself and is used to derive (rather
than assume) preservation of the chosen valuation ring by the Galois group.

The real index is implemented canonically by the maximal-ideal filtration:
the condition at `s` is membership in `m ^ ceil(s + 1)`.  The exponent is
truncated at zero, so the definition extends harmlessly to every real number
and is the full Galois group for `s <= -1`.
-/

noncomputable section

open scoped Pointwise

universe u v w x y

namespace RamificationTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Unique extension of a valuation, at the general DVF level.

This is the direct noncomplete analogue of the existing predicates on
`HenselianDVF` and `CompleteDVF`: every valuation of `L` extending the chosen
base valuation is equivalent to the chosen target valuation. -/
def HasUniqueValuationExtension (base : DVF.{u, v} K)
    (target : DVF.{w, x} L)  :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

section
variable {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
include base target
/-- Pulling the target valuation back along a `K`-automorphism again gives an
extension of the base valuation. -/
theorem algEquiv_comap_valuation_hasExtension
     
    (σ : L ≃ₐ[K] L) :
    base.valuation.HasExtension (target.valuation.comap (σ : L →+* L)) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    simpa [_root_.Valuation.comap, σ.commutes a] using
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

/-- Unique extension makes every `K`-automorphism preserve membership in the
chosen target valuation ring. -/
theorem mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
     
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : L ≃ₐ[K] L) (z : L) :
    z ∈ target.valuation.valuationSubring ↔
      σ z ∈ target.valuation.valuationSubring := by
  let vσ := target.valuation.comap (σ : L →+* L)
  let : base.valuation.HasExtension vσ :=
    algEquiv_comap_valuation_hasExtension
      (base := base) (target := target) σ
  have hsub  :=
    (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation vσ).1
      (huniq vσ)
  change z ∈ target.valuation.valuationSubring ↔ z ∈ vσ.valuationSubring
  rw [hsub]
end


end DVF
end RamificationTheory.DiscreteValuationField

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF

open RamificationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The integral exponent corresponding to a real lower ramification index.

For `s >= -1` this is `ceil (s + 1)`.  The use of `Int.toNat` also makes it
zero for `s <= -1`, which gives the expected constant extension below the
natural indexing range. -/
def realRamificationExponent (s : ℝ)  :=
  (Int.ceil (s + 1)).toNat

/-- States the theorem `realRamificationExponent_mono`. -/
theorem realRamificationExponent_mono :
    Monotone realRamificationExponent := by
  intro s t hst
  apply Int.toNat_le_toNat
  apply Int.ceil_mono
  linarith














/-- States the theorem `realRamificationExponent_nat`. -/
@[simp] theorem realRamificationExponent_nat (n : ℕ) :
    realRamificationExponent (n : ℝ) = n + 1 := by
  simp [realRamificationExponent]

/-- The maximal-ideal power representing the real lower index `s`. -/
def realRamificationIdeal (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ)  :=
  target.maximalIdeal ^ realRamificationExponent s

/-- States the theorem `realRamificationIdeal_antitone`. -/
theorem realRamificationIdeal_antitone {s t : ℝ} (hst : s ≤ t) :
    realRamificationIdeal target t ≤ realRamificationIdeal target s := Ideal.pow_le_pow_right (realRamificationExponent_mono hst)






/-- States the theorem `realRamificationIdeal_nat`. -/
@[simp] theorem realRamificationIdeal_nat (n : ℕ) :
    realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1) := by
  simp [realRamificationIdeal]








section
variable (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
include huniq
/-- The automorphism induced on the target valuation ring by uniqueness of the
valuation extension. -/
def valuationSubringAutOfUniqueExtension
     
    (σ : Gal(L/K)) :
    target.valuationSubring ≃+* target.valuationSubring where
  toFun a :=
    ⟨σ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ (a : L)).1 a.property⟩
  invFun a :=
    ⟨σ⁻¹ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ⁻¹ (a : L)).1 a.property⟩
  left_inv a := by
    ext
    simp
  right_inv a := by
    ext
    simp
  map_mul' a b := by
    ext
    simp
  map_add' a b := by
    ext
    simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_coe`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_coe
     
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    ((valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a :
        target.valuationSubring) : L) = σ (a : L) :=
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_one_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_one_apply
     
    (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq 1 a = a := by
  ext
  simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_mul_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_mul_apply
     
    (σ τ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (σ * τ) a =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ a) := by
  ext
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_inv_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_inv_apply
     
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ⁻¹ a) = a := by
  ext
  simp

/-- A uniquely extended valuation-ring automorphism preserves the maximal
ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
     
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
      a ∈ target.maximalIdeal := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  change e a ∈ target.maximalIdeal ↔ a ∈ target.maximalIdeal
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hea ha
    apply hea <;> aesop
  · intro ha hea
    apply ha <;> aesop

/-- A uniquely extended valuation-ring automorphism preserves every power of
the maximal ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
     
    (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
      a ∈ target.maximalIdeal ^ n := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  have hm :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          target.maximalIdeal = target.maximalIdeal := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ b).2 hb
    · intro ha
      refine ⟨e.symm a, ?_, by simp [e]⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ (e.symm a)).1
          (by simpa [e] using ha)
  have hmap :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          (target.maximalIdeal ^ n) = target.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hm]
  constructor
  · intro ha
    rw [← hmap] at ha
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective).1 ha with
      ⟨b, hb, hba⟩
    have  := e.injective hba
    simpa [this] using hb
  · intro ha
    rw [← hmap]
    apply Ideal.mem_map_of_mem <;> assumption

/-- States the theorem `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`. -/
theorem valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
     
    (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈
          realRamificationIdeal target s ↔
      a ∈ realRamificationIdeal target s := by
  apply valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff

/-- The real lower-ramification definition: the real-index lower ramification
group.  On the natural range `s >= -1`, membership is exactly the condition that
all integral displacements have normalized additive value at least `s + 1`,
expressed intrinsically as membership in `m ^ ceil(s + 1)`. -/
def lowerRamificationGroup
     
    (s : ℝ) : Subgroup Gal(L/K) where
  carrier :=
    {σ | ∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a - a ∈
        realRamificationIdeal target s}
  one_mem' := by
    intro a
    simp
  mul_mem' := by
    intro σ τ hσ hτ a
    have hτa  :=
      hτ a
    have hmapτa  :=
      (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
        (base := base) (target := target) huniq σ s _).2 hτa
    have hσa  :=
      hσ a
    have hdecomp :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (σ * τ) a - a =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq τ a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hmapτa hσa
  inv_mem' := by
    intro σ hσ a
    let b := valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ⁻¹ a
    have hb  :=
      hσ b
    have hab : a - b ∈ realRamificationIdeal target s := by
      simpa [b] using hb
    have hba : b - a ∈ realRamificationIdeal target s := by
      simpa [sub_eq_add_neg, add_comm] using
        (realRamificationIdeal target s).neg_mem hab
    simpa [b] using hba

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff
     
    (s : ℝ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq s ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
  Iff.rfl

/-- At an integral index, the real definition is exactly the usual
`m^(n+1)` displacement condition. -/
theorem mem_lowerRamificationGroup_nat_iff
     
    (n : ℕ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          target.maximalIdeal ^ (n + 1) := by
  simp only [mem_lowerRamificationGroup_iff, realRamificationIdeal_nat]

/-- The real lower-ramification definition: the lower groups are decreasing in their real index. -/
theorem lowerRamificationGroup_antitone
      :
    Antitone (lowerRamificationGroup
      (base := base) (target := target) huniq) := by
  intro s t hst σ hσ a
  exact realRamificationIdeal_antitone (target := target) hst (hσ a)

/-- The real lower-ramification definition: every real lower ramification group is normal. -/
theorem lowerRamificationGroup_normal
     
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro σ hσ τ a
  let b := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq τ⁻¹ a
  have hb :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ b - b ∈
        realRamificationIdeal target s :=
    hσ b
  have hmap  :=
    (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
      (base := base) (target := target) huniq τ s _).2 hb
  have hrewrite :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (τ * σ * τ⁻¹) a - a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) := by
    simp [b, map_sub]
  rwa [hrewrite]
end


/-- Provides the instance `instNormal`. -/
instance lowerRamificationGroup.instNormal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal :=
  lowerRamificationGroup_normal
    (base := base) (target := target) huniq s
















































































































end Higher
end RamificationTheory.HilbertRamification

end
