module

public import ValuedFieldTheory.Ramification.HilbertRamification.Monogeneity
public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Ramification numbers for a general discretely valued field

This file gives the noncomplete version of the ramification number used in
ramification-number theory.  Under the stated unique-extension and
separable-residue hypotheses, the monogenic integral-generator theorem supplies
an integral generator.  We choose that generator internally, so downstream
statements do not carry a generator hypothesis.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

section

variable
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (n : ℕ) (sigma : Gal(L/K))

/-- Elements whose displacement has a fixed maximal-ideal lower bound form a
base valuation-ring subalgebra. -/
def valuationSubringDisplacementSubalgebraOfUniqueExtension :
    Subalgebra base.valuationSubring target.valuationSubring where
  carrier :=
    {a | valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
              huniq sigma (a + b) - (a + b) ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
            huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
            huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
                huniq sigma (a + b) - (a + b) =
          (valuationSubringAutOfUniqueExtension
                huniq sigma a - a) +
            (valuationSubringAutOfUniqueExtension
                huniq sigma b - b) := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _ ha hb
  mul_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
              huniq sigma (a * b) - a * b ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
            huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
            huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
                huniq sigma (a * b) - a * b =
          valuationSubringAutOfUniqueExtension
                huniq sigma a *
              (valuationSubringAutOfUniqueExtension
                  huniq sigma b - b) +
            (valuationSubringAutOfUniqueExtension
                  huniq sigma a - a) * b := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb)
      (Ideal.mul_mem_right _ _ ha)
  algebraMap_mem' := by
    intro r
    change
      valuationSubringAutOfUniqueExtension
              huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) -
          algebraMap base.valuationSubring target.valuationSubring r ∈
        target.maximalIdeal ^ n
    have hcomm :
        valuationSubringAutOfUniqueExtension
              huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) =
          algebraMap base.valuationSubring target.valuationSubring r := by
      apply Subtype.ext
      exact sigma.commutes (r : K)
    rw [hcomm, sub_self]
    exact Ideal.zero_mem _

/-- States the theorem `mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff`. -/
@[simp] theorem mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff (a : target.valuationSubring) :
    a ∈ valuationSubringDisplacementSubalgebraOfUniqueExtension huniq n sigma ↔
      valuationSubringAutOfUniqueExtension huniq sigma a - a ∈
        target.maximalIdeal ^ n :=
  Iff.rfl

end

/-- A displacement bound on a generator extends to every integral polynomial
expression in that generator. -/
theorem valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a z : target.valuationSubring} {n : ℕ} {sigma : Gal(L/K)}
    (ha : valuationSubringAutOfUniqueExtension huniq sigma a - a ∈
        target.maximalIdeal ^ n)
    (hz : z ∈ Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring)) :
    valuationSubringAutOfUniqueExtension huniq sigma z - z ∈
      target.maximalIdeal ^ n := by
  have hle :
      Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring) ≤
        valuationSubringDisplacementSubalgebraOfUniqueExtension
            huniq n sigma := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ha
  exact hle hz

section

variable
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)

/-- Ramification number attached to an integral element, before choosing the
integral generator. -/
def ramificationNumberOfUniqueExtension
    (a : target.valuationSubring) (sigma : Gal(L/K)) : ℕ∞ :=
  IsDiscreteValuationRing.addVal target.valuationSubring
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma a - a)

/-- States the theorem `ramificationNumberOfUniqueExtension_one`. -/
@[simp] theorem ramificationNumberOfUniqueExtension_one
    (a : target.valuationSubring) :
    ramificationNumberOfUniqueExtension huniq a 1 = ⊤ := by
  simp [ramificationNumberOfUniqueExtension]

/-- States the theorem `natCast_le_ramificationNumberOfUniqueExtension_iff`. -/
theorem natCast_le_ramificationNumberOfUniqueExtension_iff
    (a : target.valuationSubring) (sigma : Gal(L/K)) (n : ℕ) :
    (n : ℕ∞) ≤ ramificationNumberOfUniqueExtension huniq a sigma ↔
      valuationSubringAutOfUniqueExtension huniq sigma a - a ∈
        target.maximalIdeal ^ n := (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
    (valuationSubringAutOfUniqueExtension
        huniq sigma a - a) n).symm

/-- The ramification number is independent of the monogenic generator. -/
theorem ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top
    {a b : target.valuationSubring}
    (ha : Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring) = ⊤)
    (hb : Algebra.adjoin base.valuationSubring
      ({b} : Set target.valuationSubring) = ⊤)
    (sigma : Gal(L/K)) :
    ramificationNumberOfUniqueExtension huniq a sigma =
      ramificationNumberOfUniqueExtension huniq b sigma := by
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n han
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at han ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
        huniq han (by rw [ha]; simp)
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hbn
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at hbn ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
        huniq hbn (by rw [hb]; simp)

end

variable [FiniteDimensional K L] [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

variable
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)

/-- The integral generator supplied internally by the monogeneity theorem under
the standing hypotheses. -/
def chosenRamificationGeneratorOfUniqueExtension : target.valuationSubring :=
  Classical.choose
    (exists_valuationSubring_adjoin_eq_top_of_uniqueExtension
      (base := base) (target := target) huniq)

/-- States the theorem `chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top`. -/
theorem chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top :
    Algebra.adjoin base.valuationSubring
        ({chosenRamificationGeneratorOfUniqueExtension huniq} :
          Set target.valuationSubring) = ⊤ :=
  Classical.choose_spec
    (exists_valuationSubring_adjoin_eq_top_of_uniqueExtension huniq)

/-- The canonical ramification number.  Its generator is supplied
internally by the monogenic integral-generator theorem. -/
def intrinsicRamificationNumberOfUniqueExtension
    (sigma : Gal(L/K)) : ℕ∞ :=
  ramificationNumberOfUniqueExtension
    (base := base) (target := target) huniq
    (chosenRamificationGeneratorOfUniqueExtension
      (base := base) (target := target) huniq) sigma

end Higher
end RamificationTheory.HilbertRamification

end
