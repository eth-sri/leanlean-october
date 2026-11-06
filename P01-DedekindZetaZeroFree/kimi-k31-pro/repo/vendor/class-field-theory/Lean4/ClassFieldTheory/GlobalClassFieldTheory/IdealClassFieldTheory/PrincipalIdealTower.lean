module

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Galois structure on a conjugate-stable abelian tower

The principal ideal theorem uses two successive finite abelian class fields.
The upper field is Galois over the original base once its absolute Galois
subgroup is stable under conjugation by the base subgroup.  This file packages
that actual subgroup statement as a finite Galois subextension, so that the
commutator-intermediate-field and transfer APIs can be applied to the tower.
-/

noncomputable section

universe u

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation KummerTheory

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {K : ClosedSubgroup G}

section Conjugation

variable [ContinuousMul G]



/-- Conjugating both endpoints of a finite abelian extension produces
the actual conjugate finite abelian extension. -/
def conjugateFiniteAbelianSubextension
    (L : FiniteAbelianSubextension K) (s : G) :
    FiniteAbelianSubextension (conjugateClosedSubgroup K s) where
  toFiniteGaloisExtension :=
    { field := conjugateClosedSubgroup L.field s
      below := conjugateClosedSubgroup_mono L.below s
      normal := by
        let :
            (CyclicCohomology.extensionSubgroup K L.field L.below).Normal :=
          L.normal
        infer_instance
      finite := by
        let : Finite
            (K.toSubgroup ⧸
              CyclicCohomology.extensionSubgroup K L.field L.below) :=
          L.finite
        exact finite_conjugateExtension K L.field L.below s }
  commutative := by
    let : (CyclicCohomology.extensionSubgroup K L.field L.below).Normal :=
      L.normal
    let e :=
      finiteReciprocityNaturalityConjugation K L.field L.below s
    refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    calc
      e x' * e y' = e (x' * y') := (map_mul e x' y').symm
      _ = e (y' * x') := congrArg e (L.commutative.is_comm.comm _ _)
      _ = e y' * e x' := map_mul e y' x'

@[simp]
theorem conjugateFiniteAbelianSubextension_field
    (L : FiniteAbelianSubextension K) (s : G) :
    (conjugateFiniteAbelianSubextension L s).field =
      conjugateClosedSubgroup L.field s :=
  rfl

/-- Two successive finite abelian extensions form a finite Galois extension
over the original base when the top-field subgroup is stable under conjugation
by every element of the base subgroup. -/
def galoisSubextensionOfConjugateStableAbelianTower
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (hstable : ∀ s : K.toSubgroup,
      conjugateClosedSubgroup M.field s.1 = M.field) :
    FiniteGaloisSubextension K where
  field := M.field
  below := M.below.trans L.below
  normal := by
    refine Subgroup.Normal.mk ?_
    intro q hq r
    apply
      (mem_extensionSubgroup_iff
        K M.field (M.below.trans L.below) _).2
    have hqM : (q : G) ∈ M.field :=
      (mem_extensionSubgroup_iff
        K M.field (M.below.trans L.below) q).1 hq
    have hqConj :
        (q : G) ∈ conjugateClosedSubgroup M.field (r : G) := by
      rw [hstable r]
      exact hqM
    exact
      (conjugateClosedSubgroup_mem M.field (r : G) (q : G)).1 hqConj
  finite := by
    let : Finite
        (L.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup L.field M.field M.below) :=
      M.finite
    let : Finite
        (K.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K L.field L.below) :=
      L.finite
    exact
      FiniteGaloisSubextension.finite_extension_trans M.below L.below

@[simp]
theorem galoisSubextensionOfConjugateStableAbelianTower_field
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (hstable : ∀ s : K.toSubgroup,
      conjugateClosedSubgroup M.field s.1 = M.field) :
    (galoisSubextensionOfConjugateStableAbelianTower
      L M hstable).field = M.field :=
  rfl

end Conjugation

section MaximalAbelianIntermediate

variable [IsTopologicalGroup G]

/-- The intermediate field fixed by the commutator of a finite Galois
extension, bundled as the actual maximal finite abelian subextension. -/
def maximalAbelianSubextension
    (P : FiniteGaloisSubextension K) :
    FiniteAbelianSubextension K :=
  FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe
    P (commutator P.extensionQuotient) le_rfl

@[simp]
theorem maximalAbelianSubextension_field
    (P : FiniteGaloisSubextension K) :
    (maximalAbelianSubextension P).field =
      P.abelianIntermediateField :=
  FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field
    P (commutator P.extensionQuotient) le_rfl





end MaximalAbelianIntermediate

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
