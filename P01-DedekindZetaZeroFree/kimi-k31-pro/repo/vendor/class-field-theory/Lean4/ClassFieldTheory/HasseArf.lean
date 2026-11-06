module

public import ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
public import ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
public import ClassFieldTheory.Definitions.HasseArf.IsUpperRamificationJump
public import ClassFieldTheory.Definitions.HasseArf.IsLowerRamificationJump
public import ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
public import ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Mathlib.Algebra.Algebra.Shrink
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Compositum
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristic
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristicStandardCompositum
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.StandardCompositum
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified
public import ValuedFieldTheory.Ramification.LocalField.Core
public import ValuedFieldTheory.Ramification.LocalField.BaseChange
public import ValuedFieldTheory.Ramification.LocalField.Unramified
public import Mathlib.FieldTheory.Fixed
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


























set_option autoImplicit false

/-!
# Hasse--Arf

Reader-facing facade for the Hasse--Arf theorem: upper ramification jumps of
finite Abelian local extensions are integral.  Reusable ramification,
Lubin--Tate, and local reciprocity infrastructure is exported by its owner
libraries rather than through this facade.
-/

/-!
# Hasse--Arf integrality

Filtered local reciprocity identifies the Artin principal-unit step
filtration with the upper ramification filtration.  Since the former changes
only at natural-number indices, every upper jump of a finite Abelian local
extension is integral (with the separate possible endpoint `-1`).
-/

noncomputable section

namespace ClassFieldTheory

universe u v





/-- Successive rational Herbrand values differ by the normalized cardinality
of the next lower ramification group. -/
theorem herbrandFunctionAtLowerIndex_succ
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    herbrandFunctionAtLowerIndex K A (n + 1) =
      herbrandFunctionAtLowerIndex K A n +
        (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) /
          Nat.card (lowerRamificationGroup K A 0) := by
  unfold herbrandFunctionAtLowerIndex
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), add_div]

end ClassFieldTheory

namespace HasseArf

open LocalClassFieldTheory
open RamificationTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher
open LocalFieldTheory
open scoped Pointwise

/-! ## From filtered reciprocity to integral upper jumps -/











/-- The chosen valuation ring of a finite local extension is invariant under
every base-field automorphism. Thus its Mathlib decomposition group is the
entire Galois group. -/
theorem chosenLocalExtension_decompositionSubgroup_eq_top
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K =
      ⊤ := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  apply (Subgroup.eq_top_iff' _).2
  intro σ
  change σ • target.valuation.valuationSubring = target.valuation.valuationSubring
  ext z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact (RamificationTheory.DiscreteValuationField.DVF.mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
    (base := base) (target := target) huniq σ⁻¹ z).symm

/-- At integer indices the lower group defined using Mathlib's valuation
subring action agrees elementwise with the existing local lower group. -/
theorem mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (σ : Gal(L/K))
    (hσ : σ ∈
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) :
    (⟨σ, hσ⟩ :
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) ∈
        ClassFieldTheory.lowerRamificationGroup K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n ↔
      σ ∈ localLowerRamificationGroup K L (n : ℝ) := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  have hact (a : target.valuationSubring) :
      (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a := by
    apply Subtype.ext
    rfl
  change (∀ a : target.valuationSubring,
    (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a - a ∈
      (IsLocalRing.maximalIdeal target.valuationSubring) ^ (n + 1)) ↔
    σ ∈ lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ)
  rw [mem_lowerRamificationGroup_nat_iff]
  simp only [hact]



/-- The finite lower groups in Mathlib's valuation-subring model and in the
existing local filtration have the same elements, after forgetting the
decomposition-subgroup wrapper. -/
noncomputable def chosenLowerRamificationGroupEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    ClassFieldTheory.lowerRamificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n ≃
      localLowerRamificationGroup K L (n : ℝ) := by
  have htop := chosenLocalExtension_decompositionSubgroup_eq_top K L
  refine {
    toFun := fun g =>
      ⟨g.1.1,
        (mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
          K L n g.1.1 g.1.2).mp g.2⟩
    invFun := fun g =>
      ⟨⟨g.1, by rw [htop]; trivial⟩,
        (mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
          K L n g.1 (by rw [htop]; trivial)).mpr g.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro g
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro g
    apply Subtype.ext
    rfl

/-- The public-style lower group has the same cardinality as the original
local lower group at every nonnegative integral index. -/
theorem card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Nat.card (ClassFieldTheory.lowerRamificationGroup K
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n) =
      Nat.card (localLowerRamificationGroup K L (n : ℝ)) :=
  Nat.card_congr (chosenLowerRamificationGroupEquiv K L n)

/-- Successive rational Herbrand values differ by the normalized cardinality
of the next lower group. -/
theorem herbrandFunctionAtLowerIndex_succ
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    ClassFieldTheory.herbrandFunctionAtLowerIndex K A (n + 1) =
    ClassFieldTheory.herbrandFunctionAtLowerIndex K A n +
        (Nat.card (ClassFieldTheory.lowerRamificationGroup K A (n + 1)) : ℚ) /
          Nat.card (ClassFieldTheory.lowerRamificationGroup K A 0) :=
  ClassFieldTheory.herbrandFunctionAtLowerIndex_succ K A n

/-- After the canonical inclusion `ℚ → ℝ`, the rational finite-sum
Herbrand value agrees with the Herbrand function used by local reciprocity. -/
theorem chosenHerbrandFunctionAtLowerIndex_real_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n : ℚ) : ℝ) =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
        (n : ℝ) := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  change ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
      target.valuation.valuationSubring n : ℚ) : ℝ) =
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
      F (n : ℝ)
  induction n with
  | zero =>
      simp only [ClassFieldTheory.herbrandFunctionAtLowerIndex,
        show Finset.Icc (1 : ℕ) 0 = ∅ from by decide,
        Finset.sum_empty, zero_div, Rat.cast_zero,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat_zero]
  | succ n ih =>
      rw [herbrandFunctionAtLowerIndex_succ, Rat.cast_add, Rat.cast_div]
      rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat,
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat_succ]
      rw [← RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat
        F n, ih]
      congr 1
      rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope]
      rw [show F.lower (n + 1) =
        localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) from rfl]
      rw [show F.lower 0 = localLowerRamificationGroup K L (0 : ℝ) by
        unfold F
        rw [lowerRamificationFiltrationOfUniqueExtension_lower]
        unfold localLowerRamificationGroup
        simp only [Nat.cast_zero]]
      rw [card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L (n + 1),
        card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L 0]
      simp only [Rat.cast_natCast, Nat.cast_zero]

/-- For an extension carrying its own compatible local-field valuation, the
chosen integral-closure valuation ring is exactly the canonical one. -/
theorem chosenLocalExtension_valuationSubring_eq_canonical
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring =
      (ValuativeRel.valuation L).valuationSubring := by
  let : (localCompleteDVF K).valuation.HasExtension (ValuativeRel.valuation L) := by
    rw [localCompleteDVF_valuation_eq]
    exact ‹Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)›
  exact ValuationTheory.DiscreteValuationField.ValuedExtension.valuationSubring_eq_of_finite_separable
    (localCompleteDVF K) (chosenLocalExtensionCompleteDVF K L)
      (ValuativeRel.valuation L)



/-- The public piecewise-linear Herbrand function of the chosen valuation
ring agrees at every real index with the existing local Herbrand function. -/
theorem chosenHerbrandFunction_eq_localHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : ℝ) :
    ClassFieldTheory.herbrandFunction K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring s =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  have hcard (m : ℕ) :
      Nat.card (ClassFieldTheory.lowerRamificationGroup K
        target.valuation.valuationSubring m) = Nat.card (F.lower m) := by
    calc
      Nat.card (ClassFieldTheory.lowerRamificationGroup K
          target.valuation.valuationSubring m) =
          Nat.card (localLowerRamificationGroup K L (m : ℝ)) :=
        card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L m
      _ = Nat.card (F.lower m) := rfl
  have hnat (m : ℕ) :
      ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
        target.valuation.valuationSubring m : ℚ) : ℝ) =
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat
          F m := by
    calc
      ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
          target.valuation.valuationSubring m : ℚ) : ℝ) =
          herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq (m : ℝ) :=
        chosenHerbrandFunctionAtLowerIndex_real_eq K L m
      _ =
          RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandValueNat
            F m := by
        change
          RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
            F (m : ℝ) = _
        exact
          RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat
            F m
  have hslope (m : ℕ) :
      ((Nat.card (ClassFieldTheory.lowerRamificationGroup K
        target.valuation.valuationSubring (m + 1)) : ℝ) /
          Nat.card (ClassFieldTheory.lowerRamificationGroup K
            target.valuation.valuationSubring 0)) =
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope
          F m := by
    unfold RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope
    rw [hcard (m + 1), hcard 0]
  change ClassFieldTheory.herbrandFunction K target.valuation.valuationSubring s =
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
      F s
  unfold ClassFieldTheory.herbrandFunction
  by_cases hs : 0 ≤ s
  · rw [ite_eq_left hs]
    dsimp only
    rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_floor
      F hs ⌊s⌋₊ rfl]
    rw [hnat ⌊s⌋₊, hslope ⌊s⌋₊]
  · rw [ite_eq_right hs]
    exact
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos
        F (le_of_lt (lt_of_not_ge hs))).symm

/-- The public piecewise-linear Herbrand function of the canonical valuation
ring agrees at every real index with the existing local Herbrand function. -/
theorem canonicalHerbrandFunction_eq_localHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (s : ℝ) :
    ClassFieldTheory.herbrandFunction K
        (ValuativeRel.valuation L).valuationSubring s =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s := by
  rw [← chosenLocalExtension_valuationSubring_eq_canonical K L]
  exact chosenHerbrandFunction_eq_localHerbrandFunction K L s



















/-! ## Compatible small representatives of finite extensions -/

/-- The algebra structure on the two small representatives, transported from
the original field extension. -/
@[instance_reducible]
noncomputable def shrinkAlgebra
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  ((Shrink.ringEquiv L).symm.toRingHom.comp
    ((algebraMap K L).comp (Shrink.ringEquiv K).toRingHom)).toAlgebra



































end HasseArf

end
