module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalClassFieldAxiom
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalHenselianValuation
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import Mathlib.FieldTheory.Galois.Notation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Naturality of fixed-field norm-residue symbols

This file transports norm-restriction and transfer-inclusion naturality
from the closed-subgroup class formation to actual fixed fields in a single
Galois ambient field.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Inclusion of the units of the lower concrete fixed field in the units
of the larger concrete fixed field. -/
def abstractFixedFieldUnitsInclusion
    (K K' : ClosedSubgroup (Gal(Ω / k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (abstractFixedField k Ω K')ˣ :=
  MonoidHom.toAdditive
    (Units.map
      (IntermediateField.inclusion
        (abstractFixedField_le k Ω hK'K)).toRingHom)

/-- The norm-residue symbol on the actual units of a concrete fixed field,
obtained from the abstract class-formation symbol through the canonical
fixed-unit and relative-Galois identifications. -/
def abstractFixedFieldNormResidueSymbol
    (D : DegreeData (Gal(Ω / k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) := by
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  exact
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr).toAddMonoidHom.comp
      ((D.normResidueSymbol (galoisAmbientUnitsRep k Ω)
        v hcf KF E).toAddMonoidHom.comp
        ((finiteNormClassHom (galoisAmbientUnitsRep k Ω)
          K L hLK).comp
          (abstractFixedFieldUnitsEquivGaloisFixed
            k Ω K).toAddMonoidHom))

/-- The ordinary field norm on units between two concrete fixed fields. -/
def abstractFixedFieldNormUnits
    (K K' : ClosedSubgroup (Gal(Ω / k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hK'K)ˣ →+
      Additive (abstractFixedField k Ω K)ˣ :=
  MonoidHom.toAdditive
    (normUnits (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hK'K))

/-- Restriction between the abelianized actual relative Galois groups in a
fixed-field square, transported through the canonical quotient/Galois
equivalences. -/
def abstractFixedFieldAbelianizedRestriction
    (K K' L L' : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K')) →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) :=
  MonoidHom.toAdditive
    ((abstractExtensionQuotientEquivGaloisGroup
      k Ω K L hLK hLnormal).abelianizationCongr.toMonoidHom.comp
      ((normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L).comp
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K' L' hL'K'
          hL'normal).abelianizationCongr.symm.toMonoidHom))

/-- Norm-restriction naturality for actual fixed fields.
Actual Galois restriction is compatible with the ordinary unit norm and
the unit-level norm-residue symbols.  No normality of the intermediate
extension `K'/K` is assumed. -/
theorem abstractFixedFieldNormResidueSymbol_norm_restriction
    [IsSepClosed Ω]
    (D : DegreeData (Gal(Ω / k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K K' L L' : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    letI : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K'
          (le_baseField K')) :=
      relativeTowerQuotientFinite (baseField (Gal(Ω / k))) K K' hK'K
        (le_baseField K)
    (abstractFixedFieldAbelianizedRestriction
        k Ω K K' L L' hLK hL'K' hK'K hL'L).comp
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K' L' hL'K') =
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK).comp
        (abstractFixedFieldNormUnits k Ω K K' hK'K) := by
  let : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K'
        (le_baseField K')) :=
    relativeTowerQuotientFinite (baseField (Gal(Ω / k))) K K' hK'K
      (le_baseField K)
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let K'F : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K', inferInstance⟩
  let T : FiniteAbstractFieldExtension (Gal(Ω / k)) :=
    { field := K'F
      base := KF
      below := hK'K
      finiteQuotient := hK'Kfinite }
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_norm_restriction
      (galoisAmbientUnitsRep k Ω) v hcf
      T L L' hLK hL'K' hL'L)
    (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
      (abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x))
  dsimp only [T, KF, K'F] at h
  let q := abstractExtensionQuotientEquivGaloisGroup
    k Ω K L hLK hLnormal
  let q' := abstractExtensionQuotientEquivGaloisGroup
    k Ω K' L' hL'K' hL'normal
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hLnormal, hLKfinite⟩
  let E' : FiniteGaloisSubextension K'F.field :=
    ⟨L', hL'K', hL'normal, hL'K'finite⟩
  change Additive.ofMul
      (q.abelianizationCongr
        (normResidueNaturalityAbelianizedRestriction K K' L L'
          hLK hL'K' hK'K hL'L
          (q'.abelianizationCongr.symm
            (q'.abelianizationCongr
              (Additive.toMul
                (D.normResidueSymbol
                  (galoisAmbientUnitsRep k Ω) v hcf K'F E'
                  (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
                    (abstractFixedFieldUnitsEquivGaloisFixed
                      k Ω K' x)))))))) =
    Additive.ofMul
      (q.abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol
            (galoisAmbientUnitsRep k Ω) v hcf KF E
            (finiteNormClass (galoisAmbientUnitsRep k Ω) K L hLK
              (abstractFixedFieldUnitsEquivGaloisFixed k Ω K
                (abstractFixedFieldNormUnits
                  k Ω K K' hK'K x))))))
  apply Additive.toMul.injective
  change q.abelianizationCongr _ = q.abelianizationCongr _
  rw [q.abelianizationCongr.apply_eq_iff_eq]
  rw [q'.abelianizationCongr.symm_apply_apply]
  change _ =
    D.normResidueSymbol
      (galoisAmbientUnitsRep k Ω) v hcf KF E
        (finiteReciprocityNaturalityNormMap
          (galoisAmbientUnitsRep k Ω) K K' L L'
          hLK hL'K' hK'K hL'L
          (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
            (abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x))) at h
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass] at h
  have hxFixed :
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x =
        abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K K' hK'K
            (Additive.ofMul (Additive.toMul x)) := by
    rfl
  rw [hxFixed] at h
  rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits
    k Ω K K' hK'K (Additive.toMul x)] at h
  exact congrArg Additive.toMul h

/-! ## Canonical local-field specializations -/

open scoped ValuativeRel

/-- A finite fixed-field square encoding norm-restriction naturality
inside the separable closure of a local field.

The two horizontal extensions are finite Galois.  The vertical base extension
is finite but need not be normal. -/
structure LocalFixedFieldNormRestrictionSquare
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] where
  /-- The subgroup fixing the lower base field. -/
  lowerBase : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the upper base field. -/
  upperBase : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the lower horizontal extension. -/
  lowerTop : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the upper horizontal extension. -/
  upperTop : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The lower top subgroup lies in the lower base subgroup. -/
  lowerTop_le_lowerBase : lowerTop.toSubgroup ≤ lowerBase.toSubgroup
  /-- The upper top subgroup lies in the upper base subgroup. -/
  upperTop_le_upperBase : upperTop.toSubgroup ≤ upperBase.toSubgroup
  /-- The upper base subgroup lies in the lower base subgroup. -/
  upperBase_le_lowerBase : upperBase.toSubgroup ≤ lowerBase.toSubgroup
  /-- The upper top subgroup lies in the lower top subgroup. -/
  upperTop_le_lowerTop : upperTop.toSubgroup ≤ lowerTop.toSubgroup
  /-- The lower horizontal extension subgroup is normal. -/
  lowerNormal :
    (extensionSubgroup lowerBase lowerTop lowerTop_le_lowerBase).Normal
  /-- The upper horizontal extension subgroup is normal. -/
  upperNormal :
    (extensionSubgroup upperBase upperTop upperTop_le_upperBase).Normal
  /-- The lower horizontal extension has finite Galois group. -/
  lowerFinite :
    Finite (lowerBase.toSubgroup ⧸
      extensionSubgroup lowerBase lowerTop lowerTop_le_lowerBase)
  /-- The upper horizontal extension has finite Galois group. -/
  upperFinite :
    Finite (upperBase.toSubgroup ⧸
      extensionSubgroup upperBase upperTop upperTop_le_upperBase)
  /-- The vertical base extension has finite degree. -/
  baseFinite :
    Finite (lowerBase.toSubgroup ⧸
      extensionSubgroup lowerBase upperBase upperBase_le_lowerBase)
  /-- The lower base field is finite over the original local field. -/
  lowerAbsoluteFinite :
    Finite
      ((baseField (Gal(SeparableClosure k / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(SeparableClosure k / k)))
          lowerBase (le_baseField lowerBase))

namespace LocalFixedFieldNormRestrictionSquare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The fixed-field norm-residue symbol for the lower horizontal extension,
induced by the canonical local class formation. -/
def lowerNormResidueSymbol
    (T : LocalFixedFieldNormRestrictionSquare k) :=
  letI := T.lowerNormal
  letI := T.lowerFinite
  letI := T.lowerAbsoluteFinite
  abstractFixedFieldNormResidueSymbol k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.lowerBase T.lowerTop T.lowerTop_le_lowerBase

/-- The ordinary field norm on units along the vertical base extension. -/
def normUnits
    (T : LocalFixedFieldNormRestrictionSquare k) :=
  abstractFixedFieldNormUnits k (SeparableClosure k)
    T.lowerBase T.upperBase T.upperBase_le_lowerBase

end LocalFixedFieldNormRestrictionSquare

/-- A finite fixed-field tower encoding transfer-inclusion naturality
inside the separable closure of a local field.

The total extension is finite Galois.  Normality and finiteness of the upper
part of the tower are derived internally. -/
structure LocalFixedFieldTransferTower
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] where
  /-- The subgroup fixing the base field of the tower. -/
  base : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the intermediate field of the tower. -/
  intermediate : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The subgroup fixing the top field of the tower. -/
  top : ClosedSubgroup (Gal(SeparableClosure k / k))
  /-- The top subgroup lies in the intermediate subgroup. -/
  top_le_intermediate : top.toSubgroup ≤ intermediate.toSubgroup
  /-- The intermediate subgroup lies in the base subgroup. -/
  intermediate_le_base : intermediate.toSubgroup ≤ base.toSubgroup
  /-- The total extension subgroup is normal in the base subgroup. -/
  totalNormal :
    (extensionSubgroup base top
      (top_le_intermediate.trans intermediate_le_base)).Normal
  /-- The total extension has finite Galois group. -/
  totalFinite :
    Finite (base.toSubgroup ⧸
      extensionSubgroup base top
        (top_le_intermediate.trans intermediate_le_base))
  /-- The base field is finite over the original local field. -/
  baseAbsoluteFinite :
    Finite
      ((baseField (Gal(SeparableClosure k / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(SeparableClosure k / k)))
          base (le_baseField base))

namespace LocalFixedFieldTransferTower
