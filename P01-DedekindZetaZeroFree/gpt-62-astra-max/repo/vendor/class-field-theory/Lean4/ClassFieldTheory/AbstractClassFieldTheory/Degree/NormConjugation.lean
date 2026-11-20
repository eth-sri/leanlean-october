module

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws
public import GaloisCohomology.Cyclic.IntegralRepUniverse

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
# Conjugation and relative norms

These are the field-conjugation and norm identities used in the abstract reciprocity construction and theorem.  They belong before the reciprocity construction: their proofs
use only the actual relative norm and the conjugation action.
-/

noncomputable section

open scoped BigOperators

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation preserves inclusions of abstract fields. -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  simp at hx ⊢
  exact hLK hx

section

variable [ContinuousMul G] (K : ClosedSubgroup G) (s : G)

/-- Conjugation by `s⁻¹` identifies a field subgroup with the subgroup
representing its right conjugate `K^s`. -/
def conjugateSubgroupEquiv :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    rw [conjugateClosedSubgroup_mem]
    convert k.2 using 1
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Establishes the identity `(conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s`. -/
@[simp]
theorem conjugateSubgroupEquiv_apply_coe (k : K.toSubgroup) :
    (conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s :=
  rfl

end

section

variable [ContinuousMul G] (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)

/-- Conjugation carries the subgroup for `L/K` exactly to the subgroup for
`L^s/K^s`. -/
theorem map_extensionSubgroup_conjugate :
    (extensionSubgroup K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    simp
    simpa [mul_assoc] using hk
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · apply MulEquiv.apply_symm_apply

/-- Conjugation identifies the relative coset spaces even when the
extension is not normal. -/
noncomputable def relativeConjugateCosetEquiv :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := extensionSubgroup K L hLK
    let Hs := extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
    rw [← (map_extensionSubgroup_conjugate K L hLK s)]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      simp
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        simpa using hez
      simpa [heq] using hz)

/--
Establishes the identity `relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem relativeConjugateCosetEquiv_mk
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

end

/-- A conjugate of a Galois extension is Galois. -/
instance conjugateExtension_normal [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal := by
  rw [← map_extensionSubgroup_conjugate K L hLK s]
  exact Subgroup.Normal.map hLnormal
    (conjugateSubgroupEquiv K s).toMonoidHom
    (conjugateSubgroupEquiv K s).surjective

/-- The left vertical isomorphism in the conjugation diagram of
norm--conjugation naturality, `τ ↦ s⁻¹τs`. -/
noncomputable def finiteReciprocityNaturalityConjugation
    [ContinuousMul G] (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  QuotientGroup.congr
    (extensionSubgroup K L hLK)
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s))
    (conjugateSubgroupEquiv K s)
    (map_extensionSubgroup_conjugate K L hLK s)

variable [ContinuousMul G] (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)

/--
Establishes the identity `finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem finiteReciprocityNaturalityConjugation_mk
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) := QuotientGroup.congr_mk' _ _ _ _ k

/-- Conjugation preserves finiteness of the Galois quotient. -/
theorem finite_conjugateExtension
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (relativeConjugateCosetEquiv K L hLK s)

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Conjugation intertwines the two relative coset actions. -/
private theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L hLK s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp [relativeConjugateCosetEquiv_mk]

/-- Relative norms commute with the right conjugation used in the second
diagram of norm--conjugation naturality:
`N_{L^s/K^s}(a^s) = N_{L/K}(a)^s`. -/
theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e := relativeConjugateCosetEquiv K L hLK s
  let conjugateFintype :=
    Fintype.ofEquiv (K.toSubgroup ⧸ extensionSubgroup K L hLK) e
  have hconjugateFintype : Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) = conjugateFintype :=
    Subsingleton.elim _ _
  apply Subtype.ext
  simp only [relativeNorm_apply_coe, relativeNormValue,
    conjugateFixedElement_coe]
  rw [hconjugateFintype]
  calc
    _ =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := (e.sum_comp (relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a))).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      solve_by_elim [Finset.sum_congr, relativeCosetAction_conjugate]
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]

end Representation

end
end ClassFormation
