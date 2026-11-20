module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Intermediate extensions from actual quotient subgroups

For the three reductions in the proof of the abstract reciprocity theorem, this file supplies the finite Galois correspondence in the
direction used by the construction.  If `L / K` is a packaged finite Galois extension
and `S ≤ G(L/K)`, its inverse image in `G_K` is realized as an actual closed
intermediate field `M`.

Closedness is proved from the explicit decomposition of the inverse image
as the finite union of right `G_L`-cosets.  The two Galois-group
identifications are then obtained from the actual restriction map and the
first and third isomorphism theorems; no correspondence certificate is
assumed.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inverse image in `G_K` of a subgroup of `G(L/K)`. -/
def intermediateSubgroup (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup := S.comap L.extensionQuotientMk

omit [IsTopologicalGroup G] in
/-- Membership in the intermediate subgroup is characterized by membership of
the underlying ambient element. -/
@[simp]
theorem mem_intermediateSubgroup_iff
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (k : K.toSubgroup) :
    k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/-- The original `G_L` lies in every inverse-image subgroup. -/
theorem extensionSubgroup_le_intermediateSubgroup
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup K L.field L.below ≤ L.intermediateSubgroup S := by
  intro x hx
  apply (L.mem_intermediateSubgroup_iff S x).2
  rw [((L.extensionQuotientMk_eq_one_iff x).2 hx)]
  exact S.one_mem

/-- The `G_L`-coset classified by `q ∈ G(L/K)`, defined canonically as a
fiber of the quotient map.  In particular, its public definition does not
choose a representative of `q`. -/
def intermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  {x | L.extensionQuotientMk x = q}

/-- A representative-based description used only to prove topological facts
about the canonical quotient fiber. -/
 def representativeIntermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  (fun x : K.toSubgroup =>
      x * Quotient.out (L.extensionQuotientMulEquiv q)) ''
    (extensionSubgroup K L.field L.below : Set K.toSubgroup)

omit [IsTopologicalGroup G] in
/-- Membership in the canonical coset is equality with its quotient class. -/
theorem mem_intermediateCoset_iff (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ L.intermediateCoset q ↔
      L.extensionQuotientMk x = q :=
  Iff.rfl

omit [IsTopologicalGroup G] in
private theorem mem_representativeIntermediateCoset_iff
    (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ representativeIntermediateCoset L q ↔
      L.extensionQuotientMk x = q := by
  let := L.normal
  constructor
  · rintro ⟨h, hh, rfl⟩
    apply L.extensionQuotientMulEquiv.injective
    simpa using hh
  · intro hx
    have hxout :
        (QuotientGroup.mk' (extensionSubgroup K L.field L.below)) x =
          (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) := by
      calc
        _ =
              L.extensionQuotientMulEquiv (L.extensionQuotientMk x) :=
          (L.extensionQuotientMk_apply x).symm
        _ = L.extensionQuotientMulEquiv q :=
          congrArg L.extensionQuotientMulEquiv hx
        _ = (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) :=
          (Quotient.out_eq' (L.extensionQuotientMulEquiv q)).symm
    refine ⟨x / Quotient.out (L.extensionQuotientMulEquiv q), (QuotientGroup.eq_iff_div_mem.mp hxout), ?_⟩
    simp

omit [IsTopologicalGroup G] in
private theorem intermediateCoset_eq_representativeIntermediateCoset
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.intermediateCoset q = representativeIntermediateCoset L q := by
  ext x
  exact (mem_representativeIntermediateCoset_iff L q x).symm

omit [IsTopologicalGroup G] in
/-- The inverse image of `S` is literally the finite union of the `G_L`
cosets indexed by the elements of `S`. -/
theorem intermediateSubgroup_eq_iUnion_cosets
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S : Set K.toSubgroup) =
      ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion₂.mpr ⟨
      L.extensionQuotientMk x, ((L.mem_intermediateSubgroup_iff S x).1 hx), ?_⟩
    solve_by_elim [Iff.mpr]
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hqS, hxq⟩
    apply (L.mem_intermediateSubgroup_iff S x).2
    rw [(mem_intermediateCoset_iff L q x).1 hxq]
    exact hqS

/-- Every coset in the preceding union is closed: it is the image of the
closed subgroup `G_L ≤ G_K` under right translation. -/
theorem intermediateCoset_isClosed (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : IsClosed (L.intermediateCoset q) := by
  rw [intermediateCoset_eq_representativeIntermediateCoset]
  exact isClosedMap_mul_right
    (Quotient.out (L.extensionQuotientMulEquiv q)) _
    (extensionSubgroup_isClosed K L.field L.below)

section

variable (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)

/-- Closedness of the inverse image, proved by its finite coset
decomposition rather than postulated as a Galois-correspondence property. -/
theorem intermediateSubgroup_isClosed :
    IsClosed (L.intermediateSubgroup S : Set K.toSubgroup) := by
  rw [intermediateSubgroup_eq_iUnion_cosets]
  exact (Set.toFinite _).isClosed_biUnion fun q _ => intermediateCoset_isClosed L q

/-- The closed intermediate field cut out by `S ≤ G(L/K)`. -/
def intermediateField : ClosedSubgroup G where
  toSubgroup := (L.intermediateSubgroup S).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (L.intermediateSubgroup S : Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (intermediateSubgroup_isClosed L S)

/-- The constructed intermediate field lies over `K`. -/
theorem intermediateField_le_base :
    (L.intermediateField S).toSubgroup ≤ K.toSubgroup := by
  rintro _ ⟨m, hm, rfl⟩
  exact m.property

/-- Pulling the constructed field back to `G_K` recovers exactly the
inverse-image subgroup. -/
theorem extensionSubgroup_intermediateField_eq :
    extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) =
      L.intermediateSubgroup S := by
  ext <;> simp [extensionSubgroup, intermediateField, Subgroup.mem_subgroupOf]

/-- The constructed field is intermediate: `L ≤ M`. -/
theorem field_le_intermediateField :
    L.field.toSubgroup ≤ (L.intermediateField S).toSubgroup := by
  intro x hx
  exact Exists.intro ⟨x, L.below hx⟩ ⟨extensionSubgroup_le_intermediateSubgroup L S ((mem_extensionSubgroup_iff K L.field L.below ⟨x, L.below hx⟩).mpr hx), rfl⟩

/-- The extension subgroup for `L/M` is the pullback of `G_L ◁ G_K`
along `G_M → G_K`. -/
theorem extensionSubgroup_over_intermediate_eq_comap :
    extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) =
      (extensionSubgroup K L.field L.below).comap
        (Subgroup.inclusion (L.intermediateField_le_base S)) := by
  rfl

/-- `L/M` is normal because it is obtained by restricting the normal
subgroup `G_L ◁ G_K` to `G_M`. -/
theorem extensionSubgroup_over_intermediate_normal :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal := by
  rw [extensionSubgroup_over_intermediate_eq_comap]
  infer_instance

end

/-- The extension subgroup over an intermediate field is normal in the intermediate subgroup. -/
instance extensionSubgroup_over_intermediate_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
  L.extensionSubgroup_over_intermediate_normal S

section

variable (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)

/-- The lower extension `L/M` is finite. -/
theorem extension_over_intermediate_finite :
    Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) := by
  let := L.finite
  exact FiniteGaloisSubextension.finite_extension_over_intermediate
    L.below (L.intermediateField_le_base S)
      (L.field_le_intermediateField S)

/-- The intermediate extension `M/K` is finite, since its subgroup contains
the finite-index subgroup `G_L`. -/
theorem intermediateField_finite :
    Finite (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)) := by
  rw [extensionSubgroup_intermediateField_eq]
  let :=
    @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
      (extensionSubgroup K L.field L.below) L.finite
  let :=
    Subgroup.finiteIndex_of_le (L.extensionSubgroup_le_intermediateSubgroup S)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The generally non-Galois finite extension `L^S/K` attached to an
arbitrary subgroup `S ≤ G(L/K)`.  Normality is deliberately absent from this
bundle; clients that only need finite-extension invariants should use this
rather than forcing `S` through `intermediateFiniteGalois`. -/
def intermediateFiniteAbstractExtension :
    DegreeData.FiniteAbstractExtension G where
  field := L.intermediateField S
  base := K
  below := L.intermediateField_le_base S
  finiteQuotient := L.intermediateField_finite S

end

omit [IsTopologicalGroup G] in
/-- A normal subgroup `S ◁ G(L/K)` has normal inverse image in `G_K`. -/
theorem intermediateSubgroup_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : (L.intermediateSubgroup S).Normal := by
  apply hS.comap

section

variable (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)

/-- Hence `M/K` is normal whenever `S` is normal. -/
theorem intermediateField_normal
    (hS : S.Normal) :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal := by
  rw [extensionSubgroup_intermediateField_eq]
  exact L.intermediateSubgroup_normal S hS

/-- The actual finite Galois extension `L/M`. -/
def lowerFiniteGalois :
    FiniteGaloisSubextension (L.intermediateField S) where
  field := L.field
  below := L.field_le_intermediateField S
  normal := L.extensionSubgroup_over_intermediate_normal S
  finite := L.extension_over_intermediate_finite S

/-- If `S` is normal, the actual finite Galois extension `M/K`. -/
def intermediateFiniteGalois (hS : S.Normal) :
    FiniteGaloisSubextension K where
  field := L.intermediateField S
  below := L.intermediateField_le_base S
  normal := L.intermediateField_normal S hS
  finite := L.intermediateField_finite S

/-- Restriction from `G_M` to the subgroup `S ≤ G(L/K)`.  The codomain
membership proof is supplied by the defining inverse-image equation for
`M`. -/
def lowerRestrictionHom :
    (L.intermediateField S).toSubgroup →* S :=
  (L.extensionQuotientMk.comp
      (Subgroup.inclusion (L.intermediateField_le_base S))).codRestrict S
    (by
      intro m
      apply (L.mem_intermediateSubgroup_iff S _).1
      rw [← extensionSubgroup_intermediateField_eq L S]
      exact
        (mem_extensionSubgroup_iff K (L.intermediateField S)
          (L.intermediateField_le_base S)
          (Subgroup.inclusion (L.intermediateField_le_base S) m)).2
          m.property)

/-- The lower restriction homomorphism evaluates by restricting the underlying
ambient automorphism. -/
@[simp]
theorem lowerRestrictionHom_apply_coe
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) =
      L.extensionQuotientMk
        (Subgroup.inclusion (L.intermediateField_le_base S) m) :=
  rfl

/-- Every element of `S` is represented by an element of `G_M`; hence the
restriction map is onto. -/
theorem lowerRestrictionHom_surjective :
    Function.Surjective (L.lowerRestrictionHom S) := by
  intro s
  rcases L.extensionQuotientMk_surjective s.1 with ⟨k, hk⟩
  have hkP : k ∈ L.intermediateSubgroup S := by
    apply (L.mem_intermediateSubgroup_iff S k).2
    rw [hk]
    exact s.property
  refine ⟨(⟨k.1, ⟨k, hkP, rfl⟩⟩), ?_⟩
  apply Subtype.ext
  exact hk

/-- The kernel of restriction is exactly `G_L` viewed inside `G_M`. -/
theorem lowerRestrictionHom_ker :
    MonoidHom.ker (L.lowerRestrictionHom S) =
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  ext m
  simp
  constructor
  · intro hm
    simpa using congrArg Subtype.val hm
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    apply Subtype.ext
    simp_all

/-- The first actual Galois-group identification used:
`G(L/M) ≃ S`. -/
noncomputable def lowerQuotientEquiv :
    (L.lowerFiniteGalois S).extensionQuotient ≃* S := by
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  exact (L.lowerFiniteGalois S).extensionQuotientMulEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))

/-- Representative formula for `G(L/M) ≃ S`. -/
@[simp]
theorem lowerQuotientEquiv_mk
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) =
      L.lowerRestrictionHom S m := by
  rfl

end

/-- The same representative formula after forgetting the subtype `S`; this
is the form used when composing restriction maps in the reduction diagram. -/
@[simp]
theorem lowerQuotientEquiv_mk_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) : S) :
          L.extensionQuotient) =
      L.extensionQuotientMk
        ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  apply congrArg L.extensionQuotientMk
  exact Subtype.ext (rfl)

omit [IsTopologicalGroup G] in
/-- Mapping the inverse image of `S` back to `G(L/K)` recovers `S`
itself. -/
theorem intermediateSubgroup_map_quotient_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S).map L.extensionQuotientMk = S := Subgroup.map_comap_eq_self_of_surjective
    L.extensionQuotientMk_surjective S

/-- The subgroup attached to the intermediate extension is normal. -/
instance intermediateSubgroup_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] : (L.intermediateSubgroup S).Normal :=
  L.intermediateSubgroup_normal S hS

/-- The field represented by a normal intermediate subgroup is a normal subextension. -/
instance intermediateField_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal :=
  L.intermediateField_normal S hS

/-- The third-isomorphism identification used in the normal-subextension
diagram: `G(L/K)/S ≃ G(M/K)`. -/
def upperQuotient (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Type _ :=
  L.extensionQuotient ⧸ S

/-- The upper quotient over an intermediate field carries its canonical group structure. -/
instance upperQuotient_groupInstance (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Group (L.upperQuotient S) := by
  change Group (L.extensionQuotient ⧸ S)
  infer_instance

section

variable (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) [S.Normal]

/-- Comparison with the group-library presentation of the upper quotient. -/
def upperQuotientMulEquiv :
    L.upperQuotient S ≃* (L.extensionQuotient ⧸ S) :=
  MulEquiv.refl _

/-- The canonical projection to the named upper quotient. -/
def upperQuotientMk :
    L.extensionQuotient →* L.upperQuotient S :=
  QuotientGroup.mk' S

end

omit [IsTopologicalGroup G] in
/-- The named upper quotient projection agrees with the underlying quotient-group projection. -/
@[simp]
theorem upperQuotientMk_apply (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperQuotientMulEquiv S (L.upperQuotientMk S q) =
      (QuotientGroup.mk q : L.extensionQuotient ⧸ S) :=
  rfl

variable (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) [S.Normal]

/-- The third-isomorphism identification, with both source and target kept
behind their named finite-Galois quotient boundaries. -/
noncomputable def upperQuotientEquiv :
    L.upperQuotient S ≃*
      (L.intermediateFiniteGalois S inferInstance).extensionQuotient := by
  let H := extensionSubgroup K L.field L.below
  let P := L.intermediateSubgroup S
  let π := L.extensionQuotientMk
  have hmap := L.intermediateSubgroup_map_quotient_eq S
  letI : H.Normal := L.normal
  letI : P.Normal := L.intermediateSubgroup_normal S inferInstance
  letI : (P.map π).Normal := by rw [hmap]; infer_instance
  exact (L.upperQuotientMulEquiv S).trans
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      ((QuotientGroup.quotientQuotientEquivQuotient H P (L.extensionSubgroup_le_intermediateSubgroup S)).trans
        ((QuotientGroup.quotientMulEquivOfEq (L.extensionSubgroup_intermediateField_eq S).symm).trans
          (L.intermediateFiniteGalois S inferInstance).extensionQuotientMulEquiv.symm)))

/-- Representative formula for `G(L/K)/S ≃ G(M/K)`. -/
@[simp]
theorem upperQuotientEquiv_mk_mk (k : K.toSubgroup) :
    L.upperQuotientEquiv S
        (L.upperQuotientMk S (L.extensionQuotientMk k)) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k := by
  rfl

end FiniteGaloisSubextension

end
end ClassFormation
