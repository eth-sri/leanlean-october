module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
public import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
public import ValuedFieldTheory.Ramification.Filtration
public import ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Filtered Artin comparison for standard Lubin--Tate levels

This module records the characteristic-independent part of the filtered
Artin comparison for the canonical standard Lubin--Tate tower.

The local Artin image of a lower level's norm subgroup is the kernel of
restriction from a higher level, and powers of the chosen base uniformizer
lie in the Artin kernel.  The source theorem
`standardLubinTateCanonicalUniformizerPrincipalSubgroup_eq_normSubgroup`
identifies the canonical norm subgroup with the canonical
uniformizer-principal subgroup.  Rewriting by this equality and cancelling
the uniformizer factor gives the positive integral Artin comparison;
`standardLubinTateRealUpperRamificationGroup_eq_restrictKer` identifies the
same restriction kernel with the upper ramification group.  Concretely, the
proof composes
`standardLubinTateNormSubgroup_map_artin_eq_restrictKer`,
`standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer`, and
`standardLubinTateRealUpperRamificationGroup_eq_restrictKer`, using the exact
norm formula only as the source-produced rewrite between the first two steps.

No norm-subgroup equality or containment is accepted as a theorem
hypothesis here.  The imported equality is proved from the
changed-uniformizer construction, and the zero-index comparison needs only
the independently known uniformizer norm.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory RamificationTheory.LocalField

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate
open RamificationTheory.HilbertRamification.Higher

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping the kernel of a composite through a surjective first map gives
the kernel of the second map. -/
theorem map_composite_ker_eq_ker_of_surjective
    {A G H : Type*} [Group A] [Group G] [Group H]
    (φ : A →* G) (ψ : G →* H)
    (hφ : Function.Surjective φ) :
    (ψ.comp φ).ker.map φ = ψ.ker := by
  rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq,
    φ.range_eq_top_of_surjective hφ, top_inf_eq]

/-- In a tower of standard Lubin--Tate levels, the Artin image of the lower
level norm subgroup is exactly the kernel of restriction to that level. -/
theorem standardLubinTateNormSubgroup_map_artin_eq_restrictKer
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    {m n : ℕ} (hmn : m ≤ n) :
    let F := standardLocalField K
    let E := standardLubinTateLevelField hπ m
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K E :=
      standardLubinTateLevelField_finiteDimensional hπ m
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K E :=
      standardLubinTateLevelField_isAbelianGalois F hπ m
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    (standardLubinTateNormSubgroup hπ m).map
        (abelianLocalArtinMonoidHom K L) =
      (intermediateFieldRestrictNormalHom E L
        (standardLubinTateLevelField_mono hπ hmn)).ker := by
  let F := standardLocalField K
  let E := standardLubinTateLevelField hπ m
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois F hπ m
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let hEL : E ≤ L := standardLubinTateLevelField_mono hπ hmn
  let φ := abelianLocalArtinMonoidHom K L
  let ψ := intermediateFieldRestrictNormalHom E L hEL
  have hrestrict :
      ψ.comp φ = abelianLocalArtinMonoidHom K E :=
    abelianLocalArtinMonoidHom_restrict K E L hEL
  have hker :
      (ψ.comp φ).ker = standardLubinTateNormSubgroup hπ m := by
    rw [hrestrict, abelianLocalArtinMonoidHom_ker]
    rfl
  calc
    (standardLubinTateNormSubgroup hπ m).map φ =
        (ψ.comp φ).ker.map φ := by rw [hker]
    _ = ψ.ker :=
      map_composite_ker_eq_ker_of_surjective
        φ ψ (abelianLocalArtinMonoidHom_surjective K L)

/-- Every integral power of the chosen standard base uniformizer lies in
the kernel of the standard finite Artin map. -/
theorem standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n : ℕ) :
    let F := standardLocalField K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ≤
      (abelianLocalArtinMonoidHom K L).ker := by
  let F := standardLocalField K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  dsimp only
  rw [abelianLocalArtinMonoidHom_ker]
  change
    Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ≤
      standardLubinTateNormSubgroup hπ n
  exact
    standardLubinTateBaseUniformizerUnit_zpowers_le_normSubgroup hπ n













omit [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
/-- The explicit lower ramification group of a standard Lubin--Tate level
is full at index zero. -/
theorem standardLubinTateRealLowerRamificationGroup_zero_eq_top
    (F : LocalField K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateRealLowerRamificationGroup hπ n 0 = ⊤ := by
  have hparameter :
      standardLubinTateUnitParameterSubgroup F n 0 = ⊤ := by
    apply top_unique
    intro a _ha
    rw [← standardLubinTateUnitParameterChosenRepresentative_spec F n a]
    exact
      (standardLubinTateUnitParameterClass_mem_subgroup_iff
        F n 0 (Nat.zero_le (n + 1))
        (standardLubinTateUnitParameterChosenRepresentative F n a)).2
        (by simp)
  ext σ
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num]
  rw [mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint]
  have hmem : a ∈ standardLubinTateUnitParameterSubgroup F n 0 := by
    rw [hparameter]
    exact Subgroup.mem_top a
  have hge :=
    (standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup
      F hπ n a 0 (Nat.zero_le (n + 1))).2 hmem
  constructor
  · intro _
    exact Subgroup.mem_top _
  · intro _
    simpa only [pow_zero, zero_add] using hge















end LocalClassFieldTheory

end
