module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
Constructs the transfer map for intermediate Galois quotients and relates it to Frobenius
restriction and norm naturality.
-/

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators
open MulAction

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The inclusion `G(L/K') → G(L/K)` induced by `K' ⊆ K`. -/
def transferNormNaturalityIntermediateInclusion
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') →*
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  finiteReciprocityNaturalityRestriction K K' L L (hLK'.trans hK'K) hLK'
    hK'K le_rfl

/--
Establishes the identity `transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
(QuotientGroup.mk k') = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateInclusion_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

/-- The inclusion of finite Galois groups attached to an intermediate field
is injective. -/
theorem transferNormNaturalityIntermediateInclusion_injective
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Function.Injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply (mem_extensionSubgroup_iff K' L hLK' (k'⁻¹ * l')).2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        extensionSubgroup K L (hLK'.trans hK'K) :=
    QuotientGroup.eq.mp h
  simp_all

/-- The copy of `G(L/K')` inside `G(L/K)`. -/
def transferNormNaturalityIntermediateSubgroup
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Subgroup (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) :=
  (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).range

/-- The canonical identification of `G(L/K')` with its image in
`G(L/K)`. -/
def transferNormNaturalityIntermediateQuotientEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ≃*
      transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K :=
  MulEquiv.ofBijective
    (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).rangeRestrict
    ⟨fun _ _ h =>
        transferNormNaturalityIntermediateInclusion_injective K K' L hLK' hK'K
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateQuotientEquiv_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
      (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

end DegreeData

namespace DegreeData

end DegreeData

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The finite reciprocity equivalence factored through the maximal abelian quotient.  This
is the horizontal reciprocity arrow in transfer--norm naturality. -/
def transferNormNaturalityAbelianizedReciprocity
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Additive (Abelianization
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) →+
      FiniteNormQuotient A K.field L hLK :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift
      (AddMonoidHom.toMultiplicativeRight
        (D.finiteReciprocityHom A v hAxiom K L hLK)))

/--
Establishes the identity `D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
(Additive.ofMul (Abelianization.of q)) = D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul
q)`.
-/
@[simp]
theorem transferNormNaturalityAbelianizedReciprocity_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul q) := 
  Abelianization.lift_apply_of
    (AddMonoidHom.toMultiplicativeRight
      (D.finiteReciprocityHom A v hAxiom K L hLK)) q

end DegreeData

end Representation


section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The invariant carrier used by `extensionFixedRepresentation` is
canonically the ambient fixed subgroup `A_L`. -/
def transferNormNaturalityExtensionFixedEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, by
    intro l
    let s : extensionSubgroup K L hLK :=
      ⟨Subgroup.inclusion hLK l, l.2⟩
    exact a.2 s⟩
  invFun a := ⟨a.1, by
    rintro ⟨k, hk⟩
    exact a.2 ⟨k.1, hk⟩⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
ambientFixedAddSubgroup A L) : A.V) = a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
      ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1
= a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_symm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1 =
      a.1 :=
  rfl

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed choice of right-coset representatives for the intermediate
subgroup in `G(L/K)`. -/
 def chosenTransferNormNaturalityRightTransversal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K).RightTransversal :=
  ⟨Set.range Quotient.out, Subgroup.isComplement_range_right Quotient.out_eq'⟩

/-- Multiplication gives the right-coset decomposition
`G(L/K') × T ≃ G(L/K)` used. -/
 def transferNormNaturalityRightCosetProductEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
        (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
          Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  (Equiv.prodCongr
      (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K).toEquiv
      (Equiv.refl _)).trans
    (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K).2.equiv.symm

@[simp]
private theorem transferNormNaturalityRightCosetProductEquiv_apply
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t) =
      transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r * t.1 :=
  rfl

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient action on the invariant carrier agrees with the relative
coset action used to define the norm. -/
theorem transferNormNaturality_relativeCosetAction_eq_extensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK
        (transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a) q =
      ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 := by
  let := hnormal
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl

/-- Restricting the quotient action to `G(L/K')` agrees with the relative
coset action for `L | K'`. -/
theorem transferNormNaturality_relativeCosetAction_intermediate
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :
    relativeCosetAction A K' L hLK'
        (transferNormNaturalityExtensionFixedEquiv A K L
          (hLK'.trans hK'K) hLnormal a) r =
      ((extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
          (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r) a).1 := by
  refine QuotientGroup.induction_on r ?_
  intro k'
  rfl

/-- The element of `A_L` obtained by summing the conjugates indexed by a
right transversal for `G(L/K')` in `G(L/K)`.  Its `L | K'` norm is the
`L | K` norm of the original element. -/
def transferNormNaturalityNormWitness
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  exact eA (∑ t : (T : Set _), E.ρ t.1 (eA.symm a))

private theorem transferNormNaturality_extensionAction_product
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t)) a =
      (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
        ((extensionFixedRepresentation A K L
          (hLK'.trans hK'K) hLnormal).ρ t.1 a) := by
  simp

/-- The norm identity underlying the right vertical arrow of transfer--norm naturality.  It is the additive form of the product calculation. -/
theorem transferNormNaturality_norm_doubleCoset_formula
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    fixedFieldInclusion A K K' hK'K
        (relativeNorm A K L (hLK'.trans hK'K) a) =
      relativeNorm A K' L hLK'
        (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let : Fintype (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) := Fintype.ofFinite _
  let : Fintype (K'.toSubgroup ⧸
      extensionSubgroup K' L hLK') := Fintype.ofFinite _
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  let aE := eA.symm a
  let valHom : E.V →+ A.V :=
    (ambientFixedAddSubgroup A L).subtype.comp eA.toAddMonoidHom
  apply Subtype.ext
  simp only [fixedFieldInclusion_coe, relativeNorm_apply_coe,
    relativeNormValue]
  have ha : eA aE = a := eA.apply_symm_apply a
  have hwitness :
      eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) =
        ∑ t : (T : Set (K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE := by
    rfl
  have hE :
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
        ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
    calc
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
          ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityRightCosetProductEquiv
              K K' L hLK' hK'K p) aE :=
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K).sum_comp
          (fun q => E.ρ q aE) |>.symm
      _ = ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityIntermediateInclusion
              K K' L hLK' hK'K p.1) (E.ρ p.2.1 aE) := by
        apply Fintype.sum_congr
        intro p
        exact transferNormNaturality_extensionAction_product
          A K K' L hLK' hK'K aE p.1 p.2
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
            ∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))),
              E.ρ (transferNormNaturalityIntermediateInclusion
                K K' L hLK' hK'K r) (E.ρ t.1 aE) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
        simp
  calc
    (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K),
      relativeCosetAction A K L (hLK'.trans hK'K) a q) =
        ∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), (E.ρ q aE).1 := by
      apply Fintype.sum_congr
      intro q
      rw [← ha]
      exact transferNormNaturality_relativeCosetAction_eq_extensionAction
        A K L (hLK'.trans hK'K) hLnormal aE q
    _ = (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE).1 := by
      change (∑ q, valHom (E.ρ q aE)) = valHom (∑ q, E.ρ q aE)
      simp
    _ = (∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 :=
      congrArg Subtype.val hE
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 := by
      change valHom (∑ r,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)) =
        ∑ r, valHom
          (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE))
      simp
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        relativeCosetAction A K' L hLK'
          (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
      apply Fintype.sum_congr
      intro r
      rw [← hwitness]
      have hr := transferNormNaturality_relativeCosetAction_intermediate
        A K K' L hLK' hK'K
        (eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a)) r
      calc
        _ = relativeCosetAction A K' L hLK'
            (eA (eA.symm
              (transferNormNaturalityNormWitness A K K' L hLK' hK'K a))) r := by
          simpa only [E, eA] using hr.symm
        _ = relativeCosetAction A K' L hLK'
            (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
          rw [eA.apply_symm_apply]

/-- The right vertical arrow of transfer--norm naturality: inclusion `A_K → A_{K'}`
descended to the actual finite norm quotients. -/
def transferNormNaturalityNormQuotientInclusion
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))] :
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      FiniteNormQuotient A K' L hLK' := by
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let targetClass : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A K' L hLK' :=
    (finiteNormClassHom A K' L hLK').comp
      (fixedFieldInclusion A K K' hK'K)
  refine finiteNormQuotientLift A K L (hLK'.trans hK'K) targetClass ?_
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A K' L hLK' _).2
  refine ⟨transferNormNaturalityNormWitness A K K' L hLK' hK'K a, ?_⟩
  exact (transferNormNaturality_norm_doubleCoset_formula
    A K K' L hLK' hK'K a).symm

/-- The transfer-side map sends a finite norm class to the class of its fixed-field inclusion. -/
@[simp]
theorem transferNormNaturality_normQuotientInclusion_finiteNormClass
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (x : ambientFixedAddSubgroup A K) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K
        (finiteNormClass A K L (hLK'.trans hK'K) x) =
      finiteNormClass A K' L hLK'
        (fixedFieldInclusion A K K' hK'K x) := by
  rfl

namespace DegreeData
