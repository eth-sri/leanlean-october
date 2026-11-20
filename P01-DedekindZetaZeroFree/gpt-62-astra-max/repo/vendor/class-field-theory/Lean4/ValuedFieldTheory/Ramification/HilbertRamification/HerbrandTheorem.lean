module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberFormula
public import ValuedFieldTheory.Ramification.Herbrand.FixedField
public import ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamification
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberRestriction
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth
public import ValuedFieldTheory.Valuation.LocalRingEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Herbrand's theorem for general discrete valuation fields

This leaf contains the completion-free endpoints of
the Herbrand quotient theorem and the quotient and tower filtration theorems.  The private lemmas below isolate
the finite-group averaging argument used in the quotient-filtration comparison.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField
open RamificationTheory.DiscreteValuationField.HerbrandGroupTheory

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `fixedFieldRamificationIdeal_antitone`. -/
theorem fixedFieldRamificationIdeal_antitone
    (H : Subgroup Gal(L/K)) {s t : ℝ} (hst : s ≤ t) :
    fixedFieldRamificationIdealDVF (target := target) H t ≤
      fixedFieldRamificationIdealDVF (target := target) H s := Ideal.pow_le_pow_right (realRamificationExponent_mono hst)

section

variable
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (H : Subgroup Gal(L/K)) [H.Normal]

/-- States the theorem `fixedFieldLowerRamificationGroup_antitone`. -/
theorem fixedFieldLowerRamificationGroup_antitone :
    Antitone (fixedFieldLowerRamificationGroup huniq H) := fun s t hst q hq a => fixedFieldRamificationIdeal_antitone
      H hst (hq a)

/-- States the theorem `fixedFieldLowerRamificationGroup_normal`. -/
theorem fixedFieldLowerRamificationGroup_normal (s : ℝ) :
    (fixedFieldLowerRamificationGroup huniq H s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro q hq r a
  let b := fixedFieldValuationSubringAutDVF
      huniq H r⁻¹ a
  let eqv := fixedFieldValuationSubringAutDVF
      huniq H r
  have hmap := (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff eqv
      (realRamificationExponent s) _).2 (hq b)
  have hrewrite :
      fixedFieldValuationSubringAutDVF
            huniq H (r * q * r⁻¹) a - a =
        eqv
          (fixedFieldValuationSubringAutDVF
              huniq H q b - b) := by
    simp [eqv, b, map_sub, fixedFieldValuationSubringAutDVF]
  rwa [hrewrite]

/-- The integral fixed-field lower groups, packaged as a lower filtration. -/
def fixedFieldLowerRamificationFiltration :
    AntitoneNormalSubgroupFiltration Gal((fixedFieldDVF (K := K) H)/K) where
  lower n := fixedFieldLowerRamificationGroup
    (base := base) (target := target) huniq H (n : ℝ)
  lower_normal n :=
    fixedFieldLowerRamificationGroup_normal
      (base := base) (target := target) huniq H (n : ℝ)
  antitone := by
    intro m n hmn
    apply fixedFieldLowerRamificationGroup_antitone
        huniq H
    exact_mod_cast hmn

/-- States the theorem `fixedFieldLowerRamificationFiltration_lower`. -/
@[simp] theorem fixedFieldLowerRamificationFiltration_lower (n : ℕ) :
    (fixedFieldLowerRamificationFiltration huniq H).lower n =
      fixedFieldLowerRamificationGroup huniq H (n : ℝ) :=
  rfl

end
noncomputable local instance lowerMembershipDecidable
    {G : Type*} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) (sigma : G) : Decidable (sigma ∈ F.lower n) :=
  Classical.propDecidable _

noncomputable local instance finiteSubgroupFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance finiteQuotientFiberFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    (q : G ⧸ H) : Fintype (NonarchimedeanDepth.QuotientFiber H q) :=
  Fintype.ofFinite _
end Higher
end RamificationTheory.HilbertRamification

end
