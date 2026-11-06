module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Finite abelian classification by norm subgroups

The first paragraph of the finite classification proof uses the two restriction maps
from the Galois group of a compositum.  This file constructs those maps on
the actual finite quotients and proves that they are jointly injective.
This is the group-theoretic source of the implication that a reciprocity
class which restricts trivially to both subextensions is already trivial on
their compositum.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

local instance extensionQuotient_normal
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

local instance representedQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.finite

/-- Additive subgroups which are open for the explicitly declared norm
topology.  The topology is part of the predicate, so no ambient topology
instance is changed outside the finite abelian classification theorem. -/
def NormOpenAddSubgroup (A : Rep ℤ G) (K : ClosedSubgroup G) :=
  {H : AddSubgroup (ambientFixedAddSubgroup A K) //
    IsNormOpen A K (H : Set (ambientFixedAddSubgroup A K))}

/-- Norm-open subgroups inherit the literal inclusion order of their
underlying additive subgroups.  This instance is stated explicitly because
`NormOpenAddSubgroup` is an opaque boundary type, not a transparent alias. -/
instance normOpenAddSubgroupPartialOrder (A : Rep ℤ G)
    (K : ClosedSubgroup G) : PartialOrder (NormOpenAddSubgroup A K) :=
  PartialOrder.lift (fun H => H.1) (fun _ _ h => Subtype.ext h)

/-- The actual map in the finite abelian classification theorem, `L ↦ N_{L/K} A_L`, with openness
carried by the codomain rather than assumed. -/
def normSubgroupMap (A : Rep ℤ G)
    (L : FiniteAbelianSubextension K) : NormOpenAddSubgroup A K := by
  refine ⟨L.normSubgroup A, ?_⟩
  simpa [FiniteAbelianSubextension.normSubgroup,
    FiniteGaloisSubextension.normSubgroup] using
    ClassFormation.normSubgroup_isOpen A K
      L.toFiniteGaloisExtension

/-- Establishes the identity `(L.normSubgroupMap A).1 = L.normSubgroup A`. -/
@[simp]
theorem normSubgroupMap_val
    (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    (L.normSubgroupMap A).1 = L.normSubgroup A :=
  rfl



/-- The finite classification compositum argument, isolated as a private diagram chase.
The final public theorem supplies the three bijectivity facts directly from
finite reciprocity; they are not exposed as hypotheses of the classification.
-/
private theorem normSubgroup_compositum_eq_inf_of_reciprocity_bijective
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field)
    (hbij₁ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below))
    (hbij₂ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below))
    (hbijP : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K (L₁.compositum L₂).field
        (L₁.compositum L₂).below)) :
    (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A := by
  let P := L₁.compositum L₂
  let hP₁ : P.field.toSubgroup ≤ L₁.field.toSubgroup := by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₁.field.toSubgroup
    exact inf_le_left
  let hP₂ : P.field.toSubgroup ≤ L₂.field.toSubgroup := by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₂.field.toSubgroup
    exact inf_le_right
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field K.field le_rfl) :=
    (FiniteGaloisSubextension.refl K.field).finite
  apply le_antisymm
  · exact normSubgroup_compositum_le_inf A L₁ L₂
  · intro a ha
    have ha₁ : a ∈ finiteNormSubgroup A K.field L₁.field L₁.below := by
      simpa [FiniteAbelianSubextension.normSubgroup] using ha.1
    have ha₂ : a ∈ finiteNormSubgroup A K.field L₂.field L₂.below := by
      simpa [FiniteAbelianSubextension.normSubgroup] using ha.2
    let z : FiniteNormQuotient A K.field P.field P.below :=
      finiteNormClass A K.field P.field P.below a
    obtain ⟨σ, hσ⟩ := hbijP.2 z
    have hz₁ :
        abstractReciprocityNormProjection A K.field L₁.field P.field hP₁ L₁.below z =
          0 := by
      rw [abstractReciprocityNormProjection_finiteNormClass]
      exact (finiteNormClass_eq_zero_iff A K.field L₁.field L₁.below a).2 ha₁
    have hz₂ :
        abstractReciprocityNormProjection A K.field L₂.field P.field hP₂ L₂.below z =
          0 := by
      rw [abstractReciprocityNormProjection_finiteNormClass]
      exact (finiteNormClass_eq_zero_iff A K.field L₂.field L₂.below a).2 ha₂
    have hnat₁ := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK L₁.field P.field L₁.below P.below hP₁
    have hnat₂ := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK L₂.field P.field L₂.below P.below hP₂
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hnat₁ hnat₂
    have hres₁ :
        (abstractReciprocityRestriction K.field L₁.field P.field hP₁
          L₁.below).toAdditive
            σ = 0 := by
      apply hbij₁.1
      calc
        D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below
            ((abstractReciprocityRestriction K.field L₁.field P.field hP₁
              L₁.below).toAdditive σ) =
            abstractReciprocityNormProjection A K.field L₁.field P.field hP₁
              L₁.below
                (D.finiteReciprocityHom A v hAxiom K P.field P.below σ) := by
                  exact (DFunLike.congr_fun hnat₁ σ).symm
        _ = abstractReciprocityNormProjection A K.field L₁.field P.field hP₁
              L₁.below z := congrArg _ hσ
        _ = 0 := hz₁
        _ = D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below 0 :=
          (map_zero _).symm
    have hres₂ :
        (abstractReciprocityRestriction K.field L₂.field P.field hP₂
          L₂.below).toAdditive
            σ = 0 := by
      apply hbij₂.1
      calc
        D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below
            ((abstractReciprocityRestriction K.field L₂.field P.field hP₂
              L₂.below).toAdditive σ) =
            abstractReciprocityNormProjection A K.field L₂.field P.field hP₂
              L₂.below
                (D.finiteReciprocityHom A v hAxiom K P.field P.below σ) := by
                  exact (DFunLike.congr_fun hnat₂ σ).symm
        _ = abstractReciprocityNormProjection A K.field L₂.field P.field hP₂
              L₂.below z := congrArg _ hσ
        _ = 0 := hz₂
        _ = D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below 0 :=
          (map_zero _).symm
    have hleft :
        abstractReciprocityRestriction K.field L₁.field P.field hP₁
          L₁.below σ.toMul =
          1 := by
      exact congrArg Additive.toMul hres₁
    have hright :
        abstractReciprocityRestriction K.field L₂.field P.field hP₂
          L₂.below σ.toMul =
          1 := by
      exact congrArg Additive.toMul hres₂
    have hσMul : σ.toMul = 1 := by
      let k : K.field.toSubgroup := Quotient.out σ.toMul
      have hkleft : k ∈ extensionSubgroup K.field L₁.field L₁.below := by
        apply (QuotientGroup.eq_one_iff k).1
        have := hleft
        rw [← Quotient.out_eq' σ.toMul] at this
        exact this
      have hkright : k ∈ extensionSubgroup K.field L₂.field L₂.below := by
        apply (QuotientGroup.eq_one_iff k).1
        have := hright
        rw [← Quotient.out_eq' σ.toMul] at this
        exact this
      have hkP : k ∈ extensionSubgroup K.field P.field P.below := by
        apply (mem_extensionSubgroup_iff K.field P.field P.below k).2
        exact ⟨
          (mem_extensionSubgroup_iff K.field L₁.field L₁.below k).1 hkleft,
          (mem_extensionSubgroup_iff K.field L₂.field L₂.below k).1 hkright⟩
      calc
        σ.toMul = QuotientGroup.mk k := (Quotient.out_eq' σ.toMul).symm
        _ = 1 := (QuotientGroup.eq_one_iff k).2 hkP
    have hσzero : σ = 0 := by
      apply Additive.ext
      exact hσMul
    have hz : z = 0 := by
      calc
        z = D.finiteReciprocityHom A v hAxiom K P.field P.below σ := hσ.symm
        _ = D.finiteReciprocityHom A v hAxiom K P.field P.below 0 :=
          congrArg _ hσzero
        _ = 0 := map_zero _
    change a ∈ finiteNormSubgroup A K.field P.field P.below
    exact (finiteNormClass_eq_zero_iff A K.field P.field P.below a).1 hz

/-- Restriction along an inclusion of finite abelian subextensions.  The
proof-dependent raw quotient map is transported through the two named
quotient boundaries here and nowhere in its callers. -/
def restriction
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂) :
    L₂.extensionQuotient →* L₁.extensionQuotient := by
  letI : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
  letI : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
  exact L₁.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction K L₁.field L₂.field h₁₂ L₁.below).comp
      L₂.extensionQuotientMulEquiv.toMonoidHom)

/--
Establishes the identity `restriction h₁₂ (L₂.extensionQuotientMk k) = L₁.extensionQuotientMk k`.
-/
@[simp]
theorem restriction_mk
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (k : K.toSubgroup) :
    restriction h₁₂ (L₂.extensionQuotientMk k) =
      L₁.extensionQuotientMk k := by
  apply L₁.extensionQuotientMulEquiv.injective
  simp [restriction]

/-- Restriction from the actual Galois quotient of `L₁L₂ / K` to that of
`L₁ / K`. -/
def compositumRestrictionLeft
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L₁ L₂ : FiniteAbelianSubextension K) :
    (L₁.compositum L₂).extensionQuotient →* L₁.extensionQuotient :=
  restriction (L₁.le_compositum_left L₂)

/-- Restriction from the actual Galois quotient of `L₁L₂ / K` to that of
`L₂ / K`. -/
def compositumRestrictionRight
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L₁ L₂ : FiniteAbelianSubextension K) :
    (L₁.compositum L₂).extensionQuotient →* L₂.extensionQuotient :=
  restriction (L₁.le_compositum_right L₂)

/--
Establishes the identity `compositumRestrictionLeft L₁ L₂ ((L₁.compositum L₂).extensionQuotientMk
k) = L₁.extensionQuotientMk k`.
-/
@[simp]
theorem compositumRestrictionLeft_mk
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L₁ L₂ : FiniteAbelianSubextension K) (k : K.toSubgroup) :
    compositumRestrictionLeft L₁ L₂
        ((L₁.compositum L₂).extensionQuotientMk k) =
      L₁.extensionQuotientMk k := by
  exact restriction_mk (L₁.le_compositum_left L₂) k

/--
Establishes the identity `compositumRestrictionRight L₁ L₂ ((L₁.compositum L₂).extensionQuotientMk
k) = L₂.extensionQuotientMk k`.
-/
@[simp]
theorem compositumRestrictionRight_mk
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L₁ L₂ : FiniteAbelianSubextension K) (k : K.toSubgroup) :
    compositumRestrictionRight L₁ L₂
        ((L₁.compositum L₂).extensionQuotientMk k) =
      L₂.extensionQuotientMk k := by
  exact restriction_mk (L₁.le_compositum_right L₂) k





/-! ## Recovering a field from the order of its finite quotient -/

/-- If one finite abelian extension is contained in another and their
actual Galois quotients have the same finite cardinality, then the fields
are equal.  This is the group-theoretic final step in the injectivity
finite classification argument, where equality of cardinalities comes from finite reciprocity.
-/
theorem eq_of_le_of_extensionQuotient_card_eq
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (hcard : Nat.card L₂.extensionQuotient =
      Nat.card L₁.extensionQuotient) :
    L₁ = L₂ := by
  let r := restriction h₁₂
  have hrSurjective : Function.Surjective r := by
    simpa [r, restriction] using
      L₁.extensionQuotientMulEquiv.symm.surjective.comp
        ((abstractReciprocityRestriction_surjective K L₁.field L₂.field
          h₁₂ L₁.below).comp
            L₂.extensionQuotientMulEquiv.surjective)
  have hrBijective : Function.Bijective r :=
    (Nat.bijective_iff_surjective_and_card r).2
      ⟨hrSurjective, hcard⟩
  apply le_antisymm h₁₂
  intro g hg
  let k : K.toSubgroup := ⟨g, L₁.below hg⟩
  have hrOne : r (L₂.extensionQuotientMk k) = 1 := by
    rw [show r (L₂.extensionQuotientMk k) =
      L₁.extensionQuotientMk k by exact restriction_mk h₁₂ k]
    apply L₁.extensionQuotientMulEquiv.injective
    rw [map_one, L₁.extensionQuotientMk_apply]
    apply (QuotientGroup.eq_one_iff k).2
    exact (mem_extensionSubgroup_iff K L₁.field L₁.below k).2 hg
  have hkOne : L₂.extensionQuotientMk k = 1 := by
    apply hrBijective.1
    simpa [r] using hrOne
  have hkOneRaw := congrArg L₂.extensionQuotientMulEquiv hkOne
  simp only [L₂.extensionQuotientMk_apply, map_one] at hkOneRaw
  exact (mem_extensionSubgroup_iff K L₂.field L₂.below k).1
    ((QuotientGroup.eq_one_iff k).1 hkOneRaw)

/-- The order-reversing finite classification argument, kept private until the public
the finite abelian classification theorem supplies the compositum formula and the two reciprocity
bijectivities from finite reciprocity. -/
private theorem le_iff_normSubgroup_le_of_compositum_and_reciprocity
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field)
    (hcomp : (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A)
    (hbijP : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K (L₁.compositum L₂).field
        (L₁.compositum L₂).below))
    (hbij₂ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below)) :
    L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A := by
  constructor
  · exact normSubgroup_antitone A
  · intro hnorm
    let P := L₁.compositum L₂
    have hNP : P.normSubgroup A = L₂.normSubgroup A := by
      calc
        P.normSubgroup A = L₁.normSubgroup A ⊓ L₂.normSubgroup A := hcomp
        _ = L₂.normSubgroup A := inf_eq_right.mpr hnorm
    let hPfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) :=
      P.finite
    let hL₂finite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L₂.field L₂.below) :=
      L₂.finite
    let hPNormFinite : Finite
        (FiniteNormQuotient A K.field P.field P.below) :=
      Finite.of_surjective
        (D.finiteReciprocityHom A v hAxiom K P.field P.below) hbijP.2
    let hL₂NormFinite : Finite
        (FiniteNormQuotient A K.field L₂.field L₂.below) :=
      Finite.of_surjective
        (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below) hbij₂.2
    have hnormCard :
        Nat.card (FiniteNormQuotient A K.field P.field P.below) =
          Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below) := by
      apply Nat.card_congr
      exact ((finiteNormQuotientConcreteEquiv A K.field P.field P.below).trans
        ((QuotientAddGroup.quotientAddEquivOfEq (by
          simpa [FiniteAbelianSubextension.normSubgroup] using hNP)).trans
          (finiteNormQuotientConcreteEquiv A K.field L₂.field L₂.below).symm)).toEquiv
    have hPcard :
        Nat.card P.extensionQuotient =
          Nat.card (FiniteNormQuotient A K.field P.field P.below) := by
      change Nat.card (Additive P.extensionQuotient) =
        Nat.card (FiniteNormQuotient A K.field P.field P.below)
      exact Nat.card_congr (Equiv.ofBijective _ hbijP)
    have hL₂card :
        Nat.card L₂.extensionQuotient =
          Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below) := by
      change Nat.card (Additive L₂.extensionQuotient) =
        Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below)
      exact Nat.card_congr (Equiv.ofBijective _ hbij₂)
    have hcard : Nat.card P.extensionQuotient =
        Nat.card L₂.extensionQuotient :=
      hPcard.trans (hnormCard.trans hL₂card.symm)
    have hL₂P : L₂ = P :=
      eq_of_le_of_extensionQuotient_card_eq
        (le_compositum_right L₁ L₂) hcard
    rw [hL₂P]
    exact le_compositum_left L₁ L₂



end FiniteAbelianSubextension

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G} [IsTopologicalGroup G]

local instance classification_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

local instance classification_abelianExtension_normal
    (M : FiniteAbelianSubextension K) :
    (extensionSubgroup K M.field M.below).Normal :=
  M.normal

local instance classification_abelianExtension_finite
    (M : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) :=
  M.finite

/-- The original finite Galois field lies below the abelian class-field
candidate cut out inside it. -/
theorem classFieldCandidate_field_le
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    E.field.toSubgroup ≤
      (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field.toSubgroup := by
  rw [classFieldCandidate_field A E H rE]
  exact E.field_le_intermediateField
    (reciprocityPreimageSubgroup A E H rE)

/-- Restriction from `E/K` to its class-field candidate is trivial exactly
on the pulled-back subgroup used to define that candidate. -/
theorem classFieldCandidate_restriction_eq_one_iff
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (q : E.extensionQuotient) :
    abstractReciprocityRestriction K
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field E.field
        (classFieldCandidate_field_le E A H rE)
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).below q = 1 ↔
      q ∈ reciprocityPreimageSubgroup A E H rE := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let k : K.toSubgroup := Quotient.out q
  rw [← Quotient.out_eq' q]
  constructor
  · intro hk
    have hkM : k ∈ extensionSubgroup K M.field M.below :=
      (QuotientGroup.eq_one_iff k).1 hk
    have hkMfield : k.1 ∈ M.field.toSubgroup :=
      (mem_extensionSubgroup_iff K M.field M.below k).1 hkM
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup := by
      rw [← classFieldCandidate_field A E H rE]
      exact hkMfield
    have hkIntermediateSubgroup :
        k ∈ extensionSubgroup K (E.intermediateField S)
          (E.intermediateField_le_base S) :=
      (mem_extensionSubgroup_iff K (E.intermediateField S)
        (E.intermediateField_le_base S) k).2 hkIntermediate
    rw [E.extensionSubgroup_intermediateField_eq S] at hkIntermediateSubgroup
    exact hkIntermediateSubgroup
  · intro hkS
    have hkIntermediateSubgroup : k ∈ E.intermediateSubgroup S := hkS
    rw [← E.extensionSubgroup_intermediateField_eq S] at hkIntermediateSubgroup
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup :=
      (mem_extensionSubgroup_iff K (E.intermediateField S)
        (E.intermediateField_le_base S) k).1 hkIntermediateSubgroup
    have hkMfield : k.1 ∈ M.field.toSubgroup := by
      rw [classFieldCandidate_field A E H rE]
      exact hkIntermediate
    apply (QuotientGroup.eq_one_iff k).2
    exact (mem_extensionSubgroup_iff K M.field M.below k).2 hkMfield

/-- The finite classification surjectivity diagram chase.  The final public theorem feeds
`rE` and its compatibility from finite reciprocity, so neither appears as an
assumption of the classification endpoint. -/
private theorem classFieldCandidate_normSubgroup_eq_of_reciprocity
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K.field E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (hcompatE : ∀ q : E.extensionQuotient,
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q))
    (hbijM : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).below)) :
    (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).normSubgroup A = H := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field K.field le_rfl) :=
    (FiniteGaloisSubextension.refl K.field).finite
  have hnat := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EKK M.field E.field M.below E.below hEM
  rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
    finiteReciprocityNaturalityRestriction_sameBase_eq_restriction]
      at hnat
  ext a
  have haClass :=
    reciprocityClass_mem_preimageSubgroup_iff A E H hEH rE a
  let zE : FiniteNormQuotient A K.field E.field E.below :=
    finiteNormClass A K.field E.field E.below a
  let ab : Additive (Abelianization E.extensionQuotient) := rE zE
  let q : E.extensionQuotient := Quotient.out ab.toMul
  let zM : FiniteNormQuotient A K.field M.field M.below :=
    finiteNormClass A K.field M.field M.below a
  have hab : Additive.ofMul (Abelianization.of q) = ab := by
    apply Additive.ext
    exact Quotient.out_eq' ab.toMul
  have hrecE :
      D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) = zE := by
    rw [← hcompatE q, hab, AddEquiv.symm_apply_apply]
  have hcomm :
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) = zM := by
    calc
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) =
        abstractReciprocityNormProjection A K.field M.field E.field hEM M.below
          (D.finiteReciprocityHom A v hAxiom K E.field E.below
            (Additive.ofMul q)) := by
              exact (DFunLike.congr_fun hnat (Additive.ofMul q)).symm
      _ = abstractReciprocityNormProjection A K.field M.field E.field hEM M.below zE :=
        congrArg _ hrecE
      _ = zM := by
        rw [abstractReciprocityNormProjection_finiteNormClass]
  change a ∈ finiteNormSubgroup A K.field M.field M.below ↔ a ∈ H
  constructor
  · intro haM
    have hzM : zM = 0 :=
      (finiteNormClass_eq_zero_iff A K.field M.field M.below a).2 haM
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      apply hbijM.1
      calc
        D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) = zM := hcomm
        _ = 0 := hzM
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          (map_zero _).symm
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 := by
      exact congrArg Additive.toMul hresZero
    apply haClass.1
    have hqS :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).1
        hresOne
    convert hqS using 1; rfl
  · intro haH
    have hqS : q ∈ S := by
      apply haClass.2 at haH
      convert haH using 1; rfl
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).2 hqS
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      exact congrArg Additive.ofMul hresOne
    have hzM : zM = 0 := by
      calc
        zM = D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) := hcomm.symm
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          congrArg _ hresZero
        _ = 0 := map_zero _
    exact (finiteNormClass_eq_zero_iff A K.field M.field M.below a).1 hzM



end FiniteGaloisSubextension
end ClassFormation

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {D : DegreeData G} {A : Rep ℤ G}

/-- finite reciprocity specialized to an actual finite abelian extension.
The two halves are supplied by the general Sylow surjectivity argument and
the cyclic-coordinate injectivity argument; no bijectivity premise is
exposed by the finite abelian classification theorem. -/
private theorem reciprocityEquiv_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  let : (extensionSubgroup K.field L.field L.below).Normal := L.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) := L.finite
  let : IsMulCommutative L.toFiniteGaloisExtension.extensionQuotient :=
    L.commutative
  exact ⟨
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K L.toFiniteGaloisExtension,
    v.abstractReciprocity_finiteReciprocityHom_surjective
      hcf hAxiom K L.toFiniteGaloisExtension⟩

/-- The first displayed formula in the finite abelian classification theorem: the norm subgroup of the compositum is
the intersection of the two norm subgroups.  This is the first paragraph
of the finite classification proof, with finite reciprocity supplying all three vertical
isomorphisms. -/
theorem normSubgroup_compositum
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A := by
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  exact normSubgroup_compositum_eq_inf_of_reciprocity_bijective
    D A v hAxiom K L₁ L₂
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₁)
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₂)
      (reciprocityEquiv_bijective
        v hcf hAxiom K (L₁.compositum L₂))

/-- The order-reversal assertion in the finite abelian classification theorem: field inclusion is exactly reverse inclusion of norm
subgroups. -/
theorem le_iff_normSubgroup_le
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A := by
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  exact le_iff_normSubgroup_le_of_compositum_and_reciprocity
    D A v hAxiom K L₁ L₂
      (normSubgroup_compositum v hcf K L₁ L₂)
      (reciprocityEquiv_bijective
        v hcf hAxiom K (L₁.compositum L₂))
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₂)

/-- The forward map in the finite abelian classification theorem is injective. -/
theorem normSubgroupMap_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) :
    Function.Injective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) := by
  intro L₁ L₂ h
  have hnorm : L₁.normSubgroup A = L₂.normSubgroup A := by
    exact congrArg Subtype.val h
  apply le_antisymm
  · apply (le_iff_normSubgroup_le v hcf K L₁ L₂).2
    rw [hnorm]
  · apply (le_iff_normSubgroup_le v hcf K L₂ L₁).2
    rw [hnorm]

/-- The kernel equality in the surjectivity surjectivity step.  Starting
from `N_E ≤ H`, pull `H / N_E` back through the actual norm-residue symbol
of finite reciprocity and take its fixed field.  The norm subgroup of that concrete
finite abelian candidate is exactly `H`. -/
theorem classFieldCandidate_normSubgroup_eq
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H) :
    let rE := D.normResidueSymbol A v hcf K E
    (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).normSubgroup A = H := by
  dsimp only
  let : (extensionSubgroup K.field E.field E.below).Normal := E.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  let rE := D.normResidueSymbol A v hcf K E
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  have hcompatE (q : E.extensionQuotient) :
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) := by
    simpa only [rE, DegreeData.normResidueSymbol, AddEquiv.symm_symm] using
      D.abstractReciprocityEquiv_apply_of A v hcf K E q
  exact
    FiniteGaloisSubextension.classFieldCandidate_normSubgroup_eq_of_reciprocity
      D A v hAxiom K E H hEH rE hcompatE
        (reciprocityEquiv_bijective
          v hcf hAxiom K M)

/-- Every open subgroup in the norm topology is the norm subgroup of an
actual finite abelian extension.  The extension is the fixed field of the
literal preimage of `H / N_E` under the norm-residue symbol of finite reciprocity.
-/
theorem normSubgroupMap_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) :
    Function.Surjective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) := by
  intro H
  obtain ⟨E, hEH⟩ := normOpenAddSubgroup_contains_finiteNormSubgroup
    A K.field H.1 H.2
  let : (extensionSubgroup K.field E.field E.below).Normal := E.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite
  let rE := D.normResidueSymbol A v hcf K E
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H.1 rE
  have hM : M.normSubgroup A = H.1 := by
    simpa only [rE, M] using
      classFieldCandidate_normSubgroup_eq
        v hcf K E H.1 hEH
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact hM

/-- The norm-subgroup map of the finite abelian classification theorem is bijective. -/
theorem normSubgroupMap_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) :
    Function.Bijective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) :=
  ⟨normSubgroupMap_injective v hcf K,
    normSubgroupMap_surjective v hcf K⟩

/-- **the finite abelian classification theorem.** Finite abelian extensions of the base are order-isomorphic
to the opposite poset of norm-open subgroups. -/
noncomputable def normSubgroupOrderIso
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) :
    FiniteAbelianSubextension K.field ≃o (NormOpenAddSubgroup A K.field)ᵒᵈ where
  toEquiv := Equiv.ofBijective (normSubgroupMap A)
    (normSubgroupMap_bijective v hcf K)
  map_rel_iff' := by
    intro L₁ L₂
    change L₂.normSubgroup A ≤ L₁.normSubgroup A ↔ L₁ ≤ L₂
    exact (le_iff_normSubgroup_le v hcf K L₁ L₂).symm

/--
The defining evaluation formula for `normSubgroupOrderIso` is `(OrderDual.ofDual
(normSubgroupOrderIso v hcf K L)).1 = L.normSubgroup A`.
-/
@[simp]
theorem normSubgroupOrderIso_apply
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    (OrderDual.ofDual (normSubgroupOrderIso v hcf K L)).1 =
      L.normSubgroup A :=
  rfl



end FiniteAbelianSubextension
end ClassFormation

end
