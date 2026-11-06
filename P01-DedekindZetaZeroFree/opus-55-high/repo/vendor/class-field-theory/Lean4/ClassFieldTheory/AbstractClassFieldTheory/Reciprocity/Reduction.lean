module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core
public import GaloisCohomology.Cyclic.IntegralRepUniverse

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: actual reduction maps

This file isolates the field- and quotient-theoretic content of the three
reductions.  In particular, the Sylow reduction uses an
intermediate field which need not be normal over the base.  We therefore
construct its norm map without a normality assumption on the intermediate
extension.

The reciprocity homomorphisms themselves belong to the finite reciprocity equivalence.  The
lemmas below only construct the actual arrows and prove the algebraic diagram
chases which will be applied to those homomorphisms.
-/

noncomputable section

universe u

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm arrow
`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L` for the actual intermediate
field cut out by `S ≤ G(L/K)`.  No normality of `M/K` is used. -/
def intermediateNormMap (A : Rep ℤ G) (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
      L.finite
    FiniteNormQuotient A M L.field hLM →+
      FiniteNormQuotient A K L.field L.below := by
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : Finite (M.toSubgroup ⧸
      extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap A K M L.field L.field
    L.below hLM hMK le_rfl

/-- Representative formula for the nonnormal-intermediate norm arrow. -/
@[simp]
theorem intermediateNormMap_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A (L.intermediateField S)) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (finiteNormClass A (L.intermediateField S) L.field
          (L.field_le_intermediateField S) a) =
      finiteNormClass A K L.field L.below
        (relativeNorm A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  rfl

/-- Inclusion of fixed elements, descended to the two actual norm
quotients.  This is the map `i` in the Sylow argument. -/
def intermediateNormQuotientInclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    FiniteNormQuotient A K L.field L.below →+
      FiniteNormQuotient A (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : (extensionSubgroup K L.field L.below).Normal := L.normal
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturalityNormQuotientInclusion A K (L.intermediateField S)
    L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S)

/-- Representative formula for the inclusion used in the Sylow
reduction. -/
@[simp]
theorem intermediateNormQuotientInclusion_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    L.intermediateNormQuotientInclusion A S
        (finiteNormClass A K L.field L.below a) =
      finiteNormClass A (L.intermediateField S) L.field
        (L.field_le_intermediateField S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  rfl

/-- The exact identity `N_{M/K} ∘ i = [M:K]`, now for an
arbitrary (possibly nonnormal) intermediate field. -/
theorem intermediateNormMap_comp_inclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    ∀ q : FiniteNormQuotient A K L.field L.below,
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (L.intermediateNormQuotientInclusion A S q) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • q := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  intro q
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K
      (L.intermediateField S) (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  refine FiniteNormQuotient.induction_on A K L.field L.below q ?_
  intro a
  rw [intermediateNormQuotientInclusion_finiteNormClass,
    intermediateNormMap_finiteNormClass]
  rw [show relativeNorm A K (L.intermediateField S)
      (L.intermediateField_le_base S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a by
    change relativeNorm A
        (L.intermediateFiniteAbstractExtension S).base
        (L.intermediateFiniteAbstractExtension S).field
        (L.intermediateFiniteAbstractExtension S).below
        (fixedFieldInclusion A
          (L.intermediateFiniteAbstractExtension S).base
          (L.intermediateFiniteAbstractExtension S).field
          (L.intermediateFiniteAbstractExtension S).below a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A
      (L.intermediateFiniteAbstractExtension S) a]
  rfl

end FiniteGaloisSubextension

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inclusion `G(L/M) → G(L/K)` for the actual intermediate field,
obtained from `G(L/M) ≃ S` followed by the subgroup inclusion. -/
def lowerInclusionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S) →*
      L.extensionQuotient :=
  S.subtype.comp (L.lowerQuotientEquiv S).toMonoidHom

/-- Representative formula for the actual lower inclusion. -/
@[simp]
theorem lowerInclusionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerInclusionHom S (QuotientGroup.mk m) =
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below))
          ⟨m.1, L.intermediateField_le_base S m.property⟩ := 
  L.lowerQuotientEquiv_mk_coe S m

/-- Every lower quotient of a cyclic extension is cyclic. -/
theorem lowerQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [IsCyclic L.extensionQuotient] :
    IsCyclic
      ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
  (L.lowerQuotientEquiv S).isCyclic.2 inferInstance

/-- The actual restriction arrow `G(L/K) → G(M/K)` attached to a normal
subgroup `S ◁ G(L/K)`, expressed through the third-isomorphism
identification constructed in `IntermediateExtension`. -/
def upperRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) :=
  (L.upperQuotientEquiv S).toMonoidHom.comp (QuotientGroup.mk' S)

/-- Representative formula for the actual upper restriction arrow. -/
@[simp]
theorem upperRestrictionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperRestrictionHom S
        (QuotientGroup.mk k : L.extensionQuotient) =
      QuotientGroup.mk k := 
  L.upperQuotientEquiv_mk_mk S k

/-- Every upper quotient of a cyclic extension is cyclic. -/
theorem upperQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    [IsCyclic L.extensionQuotient] :
    IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S)) := by
  have hsource : IsCyclic (L.extensionQuotient ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S)
      (QuotientGroup.mk'_surjective S)
  exact (L.upperQuotientEquiv S).isCyclic.1 hsource

/-- Its kernel is exactly the subgroup defining the intermediate field. -/
theorem upperRestrictionHom_eq_one_iff (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperRestrictionHom S q = 1 ↔ q ∈ S := by
  change L.upperQuotientEquiv S
      (L.upperQuotientMk S q) = 1 ↔ q ∈ S
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff q).1
    change L.upperQuotientMk S q = 1
    simp_all
  · intro h
    have hmk : L.upperQuotientMk S q = 1 := by
      change (QuotientGroup.mk' S) q = 1
      exact (QuotientGroup.eq_one_iff q).2 h
    simp_all

/-- The maximal abelian intermediate field in the first reduction is the
actual field cut out by the commutator subgroup of `G(L/K)`. -/
def abelianIntermediateField (L : FiniteGaloisSubextension K) :
    ClosedSubgroup G :=
  L.intermediateField (commutator L.extensionQuotient)

/-- Normality of the maximal abelian intermediate extension. -/
instance abelianIntermediateField_normalInstance
    (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.abelianIntermediateField
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal := by
  change (extensionSubgroup K
    (L.intermediateField (commutator L.extensionQuotient))
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal
  exact L.intermediateField_normal
    (commutator L.extensionQuotient) inferInstance

/-- Restriction to the maximal abelian intermediate field. -/
def abelianRestrictionHom (L : FiniteGaloisSubextension K) :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
        (L.intermediateField_le_base
          (commutator L.extensionQuotient)) :=
  L.upperRestrictionHom (commutator L.extensionQuotient)

/-- The first reduction's exact upper-row assertion: the kernel of
restriction to `L^ab` is the commutator subgroup. -/
theorem abelianRestrictionHom_eq_one_iff
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.abelianRestrictionHom q = 1 ↔
      q ∈ commutator L.extensionQuotient :=
  L.upperRestrictionHom_eq_one_iff (commutator L.extensionQuotient) q

/-- A jointly faithful family of quotient coordinates gives a jointly
faithful family of actual restriction maps to the corresponding
intermediate fields. -/
theorem upperRestrictionHom_jointlyFaithful
    (L : FiniteGaloisSubextension K)
    {I : Type*} {C : I → Type*} [∀ i, Group (C i)]
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    (q : L.extensionQuotient) :
    (∀ i, L.upperRestrictionHom (MonoidHom.ker (f i)) q = 1) ↔
      q = 1 := by
  constructor
  · intro hq
    have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
      rw [Subgroup.mem_iInf]
      intro i
      exact (L.upperRestrictionHom_eq_one_iff
        (MonoidHom.ker (f i)) q).1 (hq i)
    simp_all
  simp_all

/-- A finite abelian `G(L/K)` supplies the actual cyclic intermediate
extensions used in the second reduction.  The coordinate kernels have
trivial intersection, and the corresponding groups `G(Mᵢ/K)` are finite
cyclic. -/
theorem exists_cyclicIntermediateFields
    (L : FiniteGaloisSubextension K)
    [IsMulCommutative L.extensionQuotient] :
    ∃ (I : Type 0) (_ : Fintype I) (m : I → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i,
          L.extensionQuotient →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ ∧
        (∀ i, IsCyclic
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) ∧
        (∀ i, Finite
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) := by
  let : CommGroup L.extensionQuotient :=
    open scoped IsMulCommutative in inferInstance
  obtain ⟨I, hI, m, hm, f, hf, hfaithful⟩ :=
    finiteCommGroup_exists_jointlyFaithful_cyclic_factors
      L.extensionQuotient
  let : Fintype I := hI
  refine ⟨I, hI, m, hm, f, hf, hfaithful, ?_, ?_⟩
  · intro i
    let e : L.extensionQuotient ⧸ MonoidHom.ker (f i) ≃*
        Multiplicative (ZMod (m i)) :=
      QuotientGroup.quotientKerEquivOfSurjective (f i) (hf i)
    have hsource : IsCyclic
        (L.extensionQuotient ⧸ MonoidHom.ker (f i)) :=
      e.isCyclic.2 inferInstance
    exact (L.upperQuotientEquiv (MonoidHom.ker (f i))).isCyclic.1 hsource
  · intro i
    exact L.intermediateField_finite (MonoidHom.ker (f i))

/-! ## The maximal unramified subextension in the third reduction -/

/-- The inertia subgroup of `G(L/K)`: the image of `I_K` in the actual
finite quotient.  Its fixed field is `L ∩ K̃` in the notation of. -/
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))

omit [IsTopologicalGroup G] in
/-- The inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map. -/
theorem inertiaImage_normal (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal := 
  (inferInstance : (D.fieldInertiaWithin K).Normal).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

/-- The inertia image in a finite Galois quotient is normal. -/
instance inertiaImage_normalInstance (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal :=
  L.inertiaImage_normal D

/-- The actual maximal unramified subextension `M = L ∩ K̃`. -/
def maximalUnramifiedSubextension (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : ClosedSubgroup G :=
  L.intermediateField (L.inertiaImage D)

/-- The constructed `M/K` is unramified. -/
theorem maximalUnramifiedSubextension_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk (L.maximalUnramifiedSubextension D) K
      (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D := by
  change (DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D
  rw [(DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).isUnramified_iff_inertia_le D]
  intro x hx
  let k : K.toSubgroup := ⟨x, hx.1⟩
  have hkI : k ∈ D.fieldInertiaWithin K := 
    hx.2
  have hkS :
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D :=
    ⟨k, hkI, rfl⟩
  have hkP : k ∈ L.intermediateSubgroup (L.inertiaImage D) := by
    change (QuotientGroup.mk'
      (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D
    exact hkS
  exact ⟨k, hkP, rfl⟩

/-- The complementary extension `L/M` is totally ramified, i.e.
`f_{L/M}=1`. -/
theorem maximalUnramifiedSubextension_isTotallyRamified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk L.field
      (L.maximalUnramifiedSubextension D)
      (L.field_le_intermediateField (L.inertiaImage D))).IsTotallyRamified D := by
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  change (DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).IsTotallyRamified D
  rw [(DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).isTotallyRamified_iff_image_le D]
  rintro z ⟨x, hxM, rfl⟩
  let xK : K.toSubgroup := ⟨x, hMK hxM⟩
  have hxP : xK ∈ L.intermediateSubgroup S := by
    rw [← L.extensionSubgroup_intermediateField_eq S]
    exact (mem_extensionSubgroup_iff K M hMK xK).2 hxM
  change (QuotientGroup.mk'
    (extensionSubgroup K L.field L.below)) xK ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (extensionSubgroup K L.field L.below)) at hxP
  obtain ⟨i, hiI, hi⟩ := hxP
  have hiH : i⁻¹ * xK ∈ extensionSubgroup K L.field L.below :=
    QuotientGroup.eq.mp hi
  have hiL : i.1⁻¹ * x ∈ L.field.toSubgroup := 
    (mem_extensionSubgroup_iff K L.field L.below (i⁻¹ * xK)).1 hiH
  refine ⟨i.1⁻¹ * x, hiL, ?_⟩
  simp_all

end FiniteGaloisSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- In the cyclic case, the lower norm arrow for
`L / (L ∩ K̃) / K` is injective by the order calculation from.
This specializes the actual cardinality proof in the reciprocity reduction exact row to the
inertia-image intermediate field. -/
theorem maximalUnramified_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [IsCyclic L.extensionQuotient] :
    let S := L.inertiaImage D
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : Finite
        (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      L.intermediateField_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
      simpa only using L.finite
    Function.Injective
      (abstractReciprocityNormMap A K M L.field hLM hMK) := by
  dsimp only
  let S := L.inertiaImage D
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let : (extensionSubgroup K L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let : (extensionSubgroup K M hMK).Normal :=
    L.intermediateField_normal S inferInstance
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  let : IsCyclic
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.lowerQuotient_isCyclic S
  let : IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.upperQuotient_isCyclic S
  obtain ⟨gKL, hgKL⟩ := IsCyclic.exists_generator
    (α := L.extensionQuotient)
  obtain ⟨gML, hgML⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ extensionSubgroup M L.field hLM)
  obtain ⟨gKM, hgKM⟩ := IsCyclic.exists_generator
    (α := K.toSubgroup ⧸ extensionSubgroup K M hMK)
  exact abstractReciprocity_cyclicTower_normMap_injective
    A hcf K M L.field hLM hMK gKL hgKL gML hgML gKM hgKM

end FiniteGaloisSubextension

/-- The diagram chase used twice in the first reduction.  The
middle vertical arrow is surjective when the two outside vertical arrows
are surjective, the top-right arrow is surjective, and the bottom row is
exact. -/
theorem abstractReciprocity_surjective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) :
    Function.Surjective r := by
  intro b
  obtain ⟨q₁, hq₁⟩ := hr₁ (pB b)
  obtain ⟨q, hq⟩ := hpQ q₁
  have hzero : pB (b - r q) = 0 := by
    simp_all
  obtain ⟨b₀, hb₀⟩ := (hexact (b - r q)).mp hzero
  obtain ⟨q₀, hq₀⟩ := hr₀ b₀
  refine ⟨iQ q₀ + q, ?_⟩
  simp_all

/-- The diagram chase in the third reduction.  If both outside
reciprocity arrows are bijective and the first lower arrow is injective,
then the middle reciprocity arrow is bijective. -/
theorem abstractReciprocity_bijective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) :
    Function.Bijective r := by
  refine ⟨?_, abstractReciprocity_surjective_of_exact_diagram
    iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hpzero : pB (r q) = 0 := by rw [hq, map_zero]
  have hr₁zero : r₁ (pQ q) = 0 := by
    rw [← hright q]
    exact hpzero
  have hpQzero : pQ q = 0 := by
    apply hr₁.1
    simpa using hr₁zero
  obtain ⟨q₀, hq₀⟩ := (hexactQ q).mp hpQzero
  have hiBzero : iB (r₀ q₀) = 0 := by
    calc
      iB (r₀ q₀) = r (iQ q₀) := (hleft q₀).symm
      _ = r q := by rw [hq₀]
      _ = 0 := hq
  have hr₀zero : r₀ q₀ = 0 := by
    apply hiB
    simpa using hiBzero
  have hq₀zero : q₀ = 0 := by
    apply hr₀.1
    simpa using hr₀zero
  simp_all

/-- Every additive homomorphism from a group into an abelian group kills
the commutator subgroup.  This is the automatic inclusion in the kernel
statement of the first reduction. -/
theorem abstractReciprocity_commutator_mem_kernel
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) :
    r (Additive.ofMul q) = 0 := by
  let rMul : Q →* Multiplicative B :=
    { toFun := fun x => Multiplicative.ofAdd (r (Additive.ofMul x))
      map_one' := r.map_zero
      map_mul' := r.map_add }
  have hker : q ∈ rMul.ker :=
    Abelianization.commutator_subset_ker rMul hq
  change Multiplicative.ofAdd (r (Additive.ofMul q)) = 1 at hker
  simp_all

/-- Exact remaining kernel calculation in the first reduction.  For the
actual maximal abelian intermediate field, commutativity of the right square
and injectivity of its reciprocity arrow identify the kernel of the middle
arrow with the commutator subgroup. -/
theorem abstractReciprocity_abelianReduction_kernel
    {K : ClosedSubgroup G} {B : Type*} {C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (L : FiniteGaloisSubextension K)
    (p : B →+ C)
    (r : Additive L.extensionQuotient →+ B)
    (rAb : Additive
        (K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
          (L.intermediateField_le_base
            (commutator L.extensionQuotient))) →+ C)
    (hright : ∀ q,
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)))
    (hrAb : Function.Injective rAb)
    (q : L.extensionQuotient) :
    r (Additive.ofMul q) = 0 ↔
      q ∈ commutator L.extensionQuotient := by
  constructor
  · intro hq
    have hzero :
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) = 0 := by
      rw [← hright q, hq, map_zero]
    have hresAdd :
        Additive.ofMul (L.abelianRestrictionHom q) = 0 := by
      apply hrAb
      simpa using hzero
    have hres : L.abelianRestrictionHom q = 1 := by
      simp_all
    exact (L.abelianRestrictionHom_eq_one_iff q).1 hres
  · exact abstractReciprocity_commutator_mem_kernel r q
