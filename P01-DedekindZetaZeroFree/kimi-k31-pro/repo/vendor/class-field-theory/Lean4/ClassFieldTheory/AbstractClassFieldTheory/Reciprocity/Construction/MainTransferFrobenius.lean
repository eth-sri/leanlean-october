module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory

/-!
# The abstract reciprocity construction, transfer--norm naturality: Frobenius fibers

This module continues the geometric transfer construction with the chosen
norm-orbit representatives, fiber calculations, fixed-field arithmetic, and
the final Frobenius transfer formula.
-/

noncomputable section

open scoped BigOperators

open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace Internal





end Internal

end transferFrobeniusGeometry

section transferOrbitNorms

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace Internal



end Internal

end transferOrbitNorms

section transferFrobeniusFibers

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Canonical identification of the two realizations of
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusIntermediateEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) ≃*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL :=
  MulEquiv.ofBijective
    (D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl).rangeRestrict
    ⟨fun _ _ h => D.transferNormNaturalityFrobeniusTowerMap_injective
        E L hL (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion E.below k')`.
-/
@[simp]
theorem transferNormNaturalityFrobeniusIntermediateEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (k' : E.field.field.toSubgroup) :
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion E.below k') := rfl

/-- A divisibility fact in `ℤ̂` used to recognize every transfer term as
a positive Frobenius element over `K'`. -/
theorem transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat
    (f N : ℕ) (hf : 0 < f) (hN : 0 < N) (z : ZHat)
    (h : f • z = N • (1 : ZHat)) :
    ∃ n : ℕ, 0 < n ∧ z = n • (1 : ZHat) := by
  have hRange : N • (1 : ZHat) ∈
      (zHatMulNat f).toAddMonoidHom.range := by
    refine ⟨z, ?_⟩
    change f • z = N • (1 : ZHat)
    exact h
  have hKer : N • (1 : ZHat) ∈
      (zHatReduction f hf).toAddMonoidHom.ker := by
    rw [← zHatMulNat_range_eq_ker_reduction f hf]
    exact hRange
  have hmod : (N : ZMod f) = 0 := by
    change zHatReduction f hf (N • (1 : ZHat)) = 0 at hKer
    rw [map_nsmul] at hKer
    have hredOne : zHatReduction f hf (1 : ZHat) = 1 := by
      rfl
    simpa [hredOne] using hKer
  have hdiv : f ∣ N := (ZMod.natCast_eq_zero_iff N f).1 hmod
  let n := N / f
  have hN_eq : N = f * n := (Nat.mul_div_cancel' hdiv).symm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hN hdiv) hf
  refine ⟨n, hn, ?_⟩
  apply zHatMulNat_injective hf
  change f • z = f • (n • (1 : ZHat))
  rw [h, smul_smul, ← hN_eq]

/-- The element `τ⁻¹ σ ^ f(τ) τ` of `H` attached to one double coset in
the transfer formula on `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTerm
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  exact ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem H σ.1 q.out⟩

/-- The transfer term pulled back from `H` to
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTermPreimage
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    E.field.field.toSubgroup ⧸ D.extensionInertiaWithin E.field.field L hL :=
  (D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL).symm
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q)

/-- The pullback of each double-coset term has strictly positive integral
normalized degree, as asserted. -/
theorem transferNormNaturalityFrobeniusTransferTermPreimage_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree E.field L hL
        (D.transferNormNaturalityFrobeniusTransferTermPreimage
          E L hL σ q) =
          (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let := H.fintypeQuotientOfFiniteIndex
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let N := m * D.frobeniusExponent E.base L (hL.trans E.below) σ
  let u := D.transferNormNaturalityFrobeniusTransferTermPreimage
    E L hL σ q
  let f := (E.residueDegree : ℕ)
  let : Finite (orbit (Subgroup.zpowers σ.1) q.out) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : 0 < f := E.residueDegree.property
  have hm : 0 < m := by
    have hm0 : Function.minimalPeriod (σ.1 • ·) q.out ≠ 0 :=
      NeZero.ne _
    simpa [m] using Nat.pos_of_ne_zero hm0
  have hN : 0 < N := Nat.mul_pos hm
    (D.frobeniusExponent_pos E.base L (hL.trans E.below) σ)
  have hu :
      D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl u =
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1 := by
    exact congrArg Subtype.val
      ((D.transferNormNaturalityFrobeniusIntermediateEquiv
        E L hL).apply_symm_apply
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q))
  have hconj :
      D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q).1 =
        D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m) := by
    change D.extensionNormalizedDegree E.base L (hL.trans E.below)
        (q.out.out⁻¹ * σ.1 ^ m * q.out.out) = _
    rw [map_mul, map_mul, map_inv]
    simp [mul_comm]
  have hdegree : f •
      (D.extensionNormalizedDegree E.field L hL u).toAdd =
        N • (1 : ZHat) := by
    calc
      f • (D.extensionNormalizedDegree E.field L hL u).toAdd =
          (D.extensionNormalizedDegree E.base L (hL.trans E.below)
            (D.finiteReciprocityNaturalityFrobeniusTowerMap
              E.base.field E.field.field L L
              (hL.trans E.below) hL E.below le_rfl u)).toAdd := by
        symm
        exact D.finiteReciprocityNaturalityFrobeniusTowerMap_degree
          E L L (hL.trans E.below) hL le_rfl u
      _ = (D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m)).toAdd := by rw [hu, hconj]
      _ = N • (1 : ZHat) := by
        rw [map_pow,
          D.extensionNormalizedDegree_frobenius_eq_pow
            E.base L (hL.trans E.below) σ]
        change m •
            (D.frobeniusExponent E.base L (hL.trans E.below) σ •
              (1 : ZHat)) = N • (1 : ZHat)
        rw [smul_smul]
  obtain ⟨n, hn, hnEq⟩ :=
    transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat f N hf hN
      (D.extensionNormalizedDegree E.field L hL u).toAdd hdegree
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.ext
  exact hnEq

/-- The actual Frobenius lift over `K'` represented by one term of the
transfer product. -/
noncomputable def transferNormNaturalityTransferFrobeniusLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.FrobeniusElements E.field L hL :=
  ⟨D.transferNormNaturalityFrobeniusTransferTermPreimage
      E L hL σ q,
    D.transferNormNaturalityFrobeniusTransferTermPreimage_degree
      E L hL σ q⟩

/--
Establishes the identity `(D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 =
D.transferNormNaturalityFrobeniusTransferTermPreimage E L hL σ q`.
-/
@[simp]
theorem transferNormNaturalityTransferFrobeniusLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    (D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q).1 =
      D.transferNormNaturalityFrobeniusTransferTermPreimage
        E L hL σ q := rfl

/-- The Frobenius lift attached to a transfer orbit maps to the transfer
term `τ⁻¹ σ^f τ` in `G(\widetilde L/K)`. -/
theorem transferNormNaturalityTransferFrobeniusLift_towerMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl
        (D.transferNormNaturalityTransferFrobeniusLift
          E L hL σ q).1 =
      (D.transferNormNaturalityFrobeniusTransferTerm
        E L hL σ q).1 := by
  exact congrArg Subtype.val
    ((D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL).apply_symm_apply
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q))

/-- The closed subgroup generated by a transfer Frobenius lift maps onto
the closed subgroup generated by the corresponding transfer term. -/
theorem transferNormNaturalityTransferFrobeniusLift_closure_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl
    (D.frobeniusClosure E.field L hL β).toSubgroup.map f =
      (closedSubgroupGenerated
        ({(D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1} : Set
            (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
              (hL.trans E.below))) : Subgroup
                (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
                  (hL.trans E.below))) := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let fc := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let u := (D.transferNormNaturalityFrobeniusTransferTerm
    E L hL σ q).1
  have hβu : f β.1 = u :=
    D.transferNormNaturalityTransferFrobeniusLift_towerMap
      E L hL σ q
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ Γβ.toSubgroup at hx
    have hx' : x ∈
        (closedSubgroupGenerated
          ({(D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q).1} : Set
        (E.field.field.toSubgroup ⧸
          D.extensionInertiaWithin E.field.field L hL))).toSubgroup := by
      simpa only [Γβ, DegreeData.frobeniusClosure, Set.range_unique] using hx
    have hmap := map_mem_closedSubgroupGenerated_singleton
      fc (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 hx'
    change f x ∈
      (closedSubgroupGenerated ({f β.1} : Set P) : Subgroup P) at hmap
    rw [hβu] at hmap
    exact hmap
  · have hK'compact : CompactSpace E.field.field.toSubgroup :=
      isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
    let : CompactSpace E.field.field.toSubgroup := hK'compact
    let : IsClosed
        (D.extensionInertiaWithin E.field.field L hL :
          Set E.field.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.field L hL
    let : IsClosed (D.extensionInertiaWithin E.base.field L
        (hL.trans E.below) : Set E.base.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
    have hmapClosed : IsClosed
        ((Γβ.toSubgroup.map f : Subgroup P) : Set P) := by
      have hrange : ((Γβ.toSubgroup.map f : Subgroup P) : Set P) =
          Set.range (fun x : Γβ => f x.1) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x.1, x.2, rfl⟩
      rw [hrange]
      have hclosed :=
        ((isCompact_univ (X := Γβ)).image
          (fc.continuous.comp continuous_subtype_val)).isClosed
      change IsClosed
        ((fun x : Γβ => fc.toMonoidHom x.1) '' Set.univ) at hclosed
      have hclosed' :
          IsClosed (Set.range (fun x : Γβ => fc.toMonoidHom x.1)) := by
        simpa only [Set.image_univ] using hclosed
      have hfc : fc.toMonoidHom = f := by
        rfl
      rw [hfc] at hclosed'
      exact hclosed'
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hβmem : β.1 ∈ Γβ.toSubgroup := by
        have hgen : β.1 ∈
            (closedSubgroupGenerated ({β.1} : Set _) : Subgroup _) :=
          Subgroup.le_topologicalClosure _
            (Subgroup.subset_closure (by simp))
        simpa [Γβ, β, DegreeData.frobeniusClosure] using hgen
      exact ⟨β.1, hβmem, hβu⟩
    · exact hmapClosed

/-- For a transfer orbit represented by `t`, the absolute subgroup fixed
by its Frobenius lift over `K'` is the stabilizer of the norm coset
`t⁻¹ G_Σ`.  This is the intersection
`G_K' ∩ t⁻¹ G_Σ t`. -/
theorem transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let kM : extensionSubgroup E.base.field E.field.field E.below :=
      ⟨Subgroup.inclusion E.below k', k'.2⟩
    k' ∈ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL β)
          (D.frobeniusFixedField_le E.field L hL β) ↔
      kM ∈ MulAction.stabilizer
        (extensionSubgroup E.base.field E.field.field E.below)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
            (D.frobeniusFixedField_le E.base L
              (hL.trans E.below) σ)) := by
  dsimp only
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let P' := E.field.field.toSubgroup ⧸
    D.extensionInertiaWithin E.field.field L hL
  let f : P' →* P := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let t : P := q.out.out
  let tK : E.base.field.toSubgroup := Quotient.out t
  let u : P :=
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q).1
  let Cu : Subgroup P :=
    (closedSubgroupGenerated ({u} : Set P) : Subgroup P)
  let Cpow : Subgroup P :=
    (closedSubgroupGenerated ({σ.1 ^ m} : Set P) : Subgroup P)
  let c : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t }
  let ci : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t⁻¹).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t⁻¹ }
  have hc_apply (y : P) : c y = t * y * t⁻¹ := rfl
  have hci_apply (y : P) : ci y = t⁻¹ * y * t := by
    change t⁻¹ * y * (t⁻¹)⁻¹ = t⁻¹ * y * t
    rw [inv_inv]
  have hclosureMap : Γβ.toSubgroup.map f = Cu := by
    simpa [Γβ, Cu, u, β, f] using
      D.transferNormNaturalityTransferFrobeniusLift_closure_map
        E L hL σ q
  have hpow : Cpow = Γ.toSubgroup ⊓ MulAction.stabilizer P q.out := by
    simpa [Cpow, Γ, DegreeData.frobeniusClosure, m] using
      closedSubgroupGenerated_pow_eq_inf_stabilizer
        H hHclosed σ.1 q.out
  have hcu : c u = σ.1 ^ m := by
    change t * (t⁻¹ * σ.1 ^ m * t) * t⁻¹ = σ.1 ^ m
    simp [mul_assoc]
  have hcig : ci (σ.1 ^ m) = u := by
    rw [hci_apply]
    rfl
  have hVeq : MulAction.stabilizer P q.out =
      H.map (MulAut.conj t).toMonoidHom := by
    have hx : q.out = t • (QuotientGroup.mk 1 : P ⧸ H) := by
      symm
      change QuotientGroup.mk (t * 1) = q.out
      rw [mul_one]
      exact Quotient.out_eq' q.out
    rw [hx, stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  have hclosure_iff (x : P') :
      x ∈ Γβ.toSubgroup ↔ c (f x) ∈ Γ.toSubgroup := by
    constructor
    · intro hx
      have hfx : f x ∈ Cu := by
        rw [← hclosureMap]
        exact ⟨x, hx, rfl⟩
      have hcx := map_mem_closedSubgroupGenerated_singleton c u hfx
      rw [hcu] at hcx
      change c (f x) ∈ Cpow at hcx
      rw [hpow] at hcx
      exact hcx.1
    · intro hx
      have hfxH : f x ∈ H := ⟨x, rfl⟩
      have hcfxV : c (f x) ∈ MulAction.stabilizer P q.out := by
        rw [hVeq]
        exact ⟨f x, hfxH, rfl⟩
      have hcfx : c (f x) ∈ Cpow := by
        rw [hpow]
        exact ⟨hx, hcfxV⟩
      have hcix := map_mem_closedSubgroupGenerated_singleton
        ci (σ.1 ^ m) hcfx
      rw [hcig] at hcix
      have hif : ci (c (f x)) = f x := by
        rw [hci_apply, hc_apply]
        simp [mul_assoc]
      rw [hif] at hcix
      have hmap : f x ∈ Γβ.toSubgroup.map f := by
        rw [hclosureMap]
        exact hcix
      exact (Subgroup.mem_map_iff_mem
        (D.transferNormNaturalityFrobeniusTowerMap_injective
          E L hL)).mp hmap
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let kM : extensionSubgroup E.base.field E.field.field E.below :=
    ⟨Subgroup.inclusion E.below k', k'.2⟩
  rw [D.extensionSubgroup_frobeniusFixedField E.field L hL β]
  change QuotientGroup.mk k' ∈ Γβ.toSubgroup ↔ _
  rw [hclosure_iff]
  rw [mem_relativeNormDoubleCoset_stabilizer_iff
    E.base.field E.field.field S hSK E.below tK⁻¹ kM]
  let zK : E.base.field.toSubgroup :=
    tK * Subgroup.inclusion E.below k' * tK⁻¹
  have htz : c (f (QuotientGroup.mk k')) = QuotientGroup.mk zK := by
    change t * QuotientGroup.mk (Subgroup.inclusion E.below k') * t⁻¹ =
      QuotientGroup.mk zK
    have htK : (QuotientGroup.mk tK : P) = t := Quotient.out_eq' t
    rw [← htK]
    rfl
  rw [htz]
  rw [← D.mem_frobeniusFixedSubgroupWithin_iff E.base L
    (hL.trans E.below) σ zK]
  rw [← D.extensionSubgroup_frobeniusFixedField E.base L
    (hL.trans E.below) σ]
  rw [mem_extensionSubgroup_iff]
  change zK.1 ∈ S.toSubgroup ↔ _
  simp [zK, kM, tK, mul_assoc]

/-- The pointwise fixed-subgroup calculation above, upgraded to the
literal subgroup equality used to identify the stabilizer-coset fiber in
the transfer formula with the norm fiber. -/
theorem transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let e := transferNormNaturalityIntermediateAbsoluteEquiv
      E.base.field E.field.field E.below
    (extensionSubgroup E.field.field
      (D.frobeniusFixedField E.field L hL β)
        (D.frobeniusFixedField_le E.field L hL β)).map e.toMonoidHom =
      MulAction.stabilizer
        (extensionSubgroup E.base.field E.field.field E.below)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
            (D.frobeniusFixedField_le E.base L
              (hL.trans E.below) σ)) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  ext kM
  obtain ⟨k', rfl⟩ := e.surjective kM
  change e k' ∈ Subgroup.map e.toMonoidHom _ ↔ _
  have hmem : e k' ∈ Subgroup.map e.toMonoidHom
      (extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))
        (D.frobeniusFixedField_le E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))) ↔
      k' ∈ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q))
        (D.frobeniusFixedField_le E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) :=
    Subgroup.mem_map_iff_mem e.injective
  rw [hmem]
  exact D.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    E L hL σ q k'

end DegreeData

namespace Internal

/-- For each transfer double coset, the quotient by the fixed subgroup of
its Frobenius factor is the stabilizer-coset fiber in the corresponding
norm double coset. -/
 noncomputable def chosenTransferNormNaturalityTransferNormFiberEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    E.field.field.toSubgroup ⧸ extensionSubgroup E.field.field
        (D.frobeniusFixedField E.field L hL β)
          (D.frobeniusFixedField_le E.field L hL β) ≃
      (extensionSubgroup E.base.field E.field.field E.below) ⧸
        MulAction.stabilizer
          (extensionSubgroup E.base.field E.field.field E.below)
          (QuotientGroup.mk tK⁻¹ :
            E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S
              (D.frobeniusFixedField_le E.base L
                (hL.trans E.below) σ)) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  let Sβsubgroup := extensionSubgroup E.field.field
    (D.frobeniusFixedField E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q))
    (D.frobeniusFixedField_le E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q))
  have hEq := D.transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    E L hL σ q
  exact (leftCosetEquivOfMulEquiv e Sβsubgroup).trans
    (Subgroup.quotientEquivOfEq hEq)

@[simp]
private theorem chosenTransferNormNaturalityTransferNormFiberEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    Internal.chosenTransferNormNaturalityTransferNormFiberEquiv
        D E L hL σ q (QuotientGroup.mk k') =
      QuotientGroup.mk
        (transferNormNaturalityIntermediateAbsoluteEquiv
          E.base.field E.field.field E.below k') := by
  unfold chosenTransferNormNaturalityTransferNormFiberEquiv
  rfl

end Internal

end transferFrobeniusFibers

section transferNormFibers

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace Internal





end Internal

end transferNormFibers

section transferredFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData





end DegreeData

end transferredFixedFields

section transferNormArithmetic

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : Type 0`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData





end DegreeData

end transferNormArithmetic

section frobeniusTransfer

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData





end DegreeData
end frobeniusTransfer
end

end ClassFormation
