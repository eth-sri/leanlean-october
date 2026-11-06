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

section
variable (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
include D E L hL hLnormal hL'normal
/-- Canonical identification of the two realizations of
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusIntermediateEquiv
      :
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
     
    (k' : E.field.field.toSubgroup) :
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion E.below k') := rfl
end


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

section
variable (D : DegreeData G) [IsTopologicalGroup G]
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
include D E L hL hLnormal hL'normal σ q
/-- The element `τ⁻¹ σ ^ f(τ) τ` of `H` attached to one double coset in
the transfer formula on `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTerm
      :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  exact ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem H σ.1 q.out⟩

/-- The transfer term pulled back from `H` to
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTermPreimage
      :
    E.field.field.toSubgroup ⧸ D.extensionInertiaWithin E.field.field L hL :=
  (D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL).symm
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q)

/-- The pullback of each double-coset term has strictly positive integral
normalized degree, as asserted. -/
theorem transferNormNaturalityFrobeniusTransferTermPreimage_degree
      :
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
      :
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
      :
    (D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q).1 =
      D.transferNormNaturalityFrobeniusTransferTermPreimage
        E L hL σ q := rfl
end


























































































































































































































































































































































end DegreeData

namespace Internal



































































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
