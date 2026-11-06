module

public import Mathlib

public import ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.LocalMultiplicativeCompletion
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteGaloisAbelianization
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Profinite local reciprocity

The absolute Artin map constructed from the compatible finite reciprocity
maps is transported from the fixed separable closure to Mathlib's usual
algebraic-closure absolute Galois group.  Its canonical extension to the
topological profinite completion is then automatically onto.  Injectivity
is supplied by the arithmetic cofinality consequence of the finite local
existence theorem.
-/

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Restriction to the separable closure gives the canonical topological
identification between the usual and separable absolute Galois groups. -/
noncomputable def standardToSeparableAbsoluteGaloisEquiv  :=
  RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv K

/-- The induced canonical identification from the separable absolute
topological abelianization to Mathlib's usual one. -/
noncomputable def separableToStandardAbsoluteAbelianizationEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃ₜ*
      _root_.Field.absoluteGaloisGroupAbelianization K :=
  (topologicalAbelianizationCongr
    (standardToSeparableAbsoluteGaloisEquiv K)).symm

/-- The separable model makes the standard absolute abelianization totally disconnected. -/
noncomputable instance standardLocalAbsoluteAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (_root_.Field.absoluteGaloisGroupAbelianization K) :=
  Homeomorph.totallyDisconnectedSpace
    (separableToStandardAbsoluteAbelianizationEquiv K).toHomeomorph

/-- The standard absolute abelianization is compact via the separable-model equivalence. -/
noncomputable instance standardLocalAbsoluteAbelianization_compactSpace :
    CompactSpace (_root_.Field.absoluteGaloisGroupAbelianization K) :=
  Homeomorph.compactSpace
    (separableToStandardAbsoluteAbelianizationEquiv K).toHomeomorph














/-- The usual absolute Galois topological abelianization, packaged as a stable
profinite group. -/
noncomputable def standardLocalAbsoluteAbelianProfinite
    (K : Type) [Field K] : ProfiniteGrp :=
  ProfiniteGrp.of (_root_.Field.absoluteGaloisGroupAbelianization K)

/-- The canonical extension of the separable absolute Artin map to the
open-finite-quotient completion of the local multiplicative group. -/
noncomputable def separableProfiniteLocalReciprocityHom  :=
  topologicalProfiniteCompletionLift
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)

/-- The separable reciprocity lift agrees with the Artin map on canonical completion points. -/
@[simp]
theorem separableProfiniteLocalReciprocityHom_map (a : Kˣ) :
    separableProfiniteLocalReciprocityHom K
        (topologicalProfiniteCompletionMap Kˣ a) =
      separableAbsoluteLocalArtinMap K a :=
  topologicalProfiniteCompletionLift_map
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K) a











/-- The separable profinite reciprocity homomorphism is onto. -/
def separableProfiniteLocalReciprocityHom_surjective  :=
  topologicalProfiniteCompletionLift_surjective_of_denseRange
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)
    (separableAbsoluteLocalArtinMap_denseRange K)

/-- Finite local existence makes the separable profinite reciprocity
homomorphism one-to-one. -/
def separableProfiniteLocalReciprocityHom_injective  :=
  topologicalProfiniteCompletionLift_injective_of_preimage_cofinal
    (localAbsoluteAbelianProfinite K)
    (separableAbsoluteLocalArtinMap K)
    (separableAbsoluteLocalArtinMap_preimage_cofinal K)

/-- Profinite local reciprocity for the fixed separable closure. -/
noncomputable def separableProfiniteLocalReciprocity :
    TopologicalProfiniteCompletion Kˣ ≃ₜ*
      localAbsoluteAbelianProfinite K :=
  { Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (separableProfiniteLocalReciprocityHom K)
        ⟨separableProfiniteLocalReciprocityHom_injective K,
          separableProfiniteLocalReciprocityHom_surjective K⟩)
      (separableProfiniteLocalReciprocityHom K).continuous_toFun with
    map_mul' := (separableProfiniteLocalReciprocityHom K).map_mul }

/-- The separable reciprocity equivalence has the same underlying map as its lifted homomorphism. -/
@[simp]
theorem separableProfiniteLocalReciprocity_apply
    (x : TopologicalProfiniteCompletion Kˣ) :
    separableProfiniteLocalReciprocity K x =
      separableProfiniteLocalReciprocityHom K x :=
  rfl

/-- The forward transport from the separable to the usual absolute
topological abelianization, as a continuous homomorphism. -/
noncomputable def separableToStandardAbsoluteAbelianizationHom :
    localAbsoluteAbelianProfinite K →ₜ*
      standardLocalAbsoluteAbelianProfinite K :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (separableToStandardAbsoluteAbelianizationEquiv K)

/-- The absolute local Artin map with Mathlib's usual algebraic-closure
absolute Galois group as target. -/
noncomputable def absoluteLocalArtinMap  :=
  (separableToStandardAbsoluteAbelianizationHom K).comp
    (separableAbsoluteLocalArtinMap K)















/-- The usual absolute local Artin map has dense image. -/
theorem absoluteLocalArtinMap_denseRange :
    DenseRange (absoluteLocalArtinMap K) := by
  let e := separableToStandardAbsoluteAbelianizationEquiv K
  change DenseRange (fun a => e (separableAbsoluteLocalArtinMap K a))
  exact e.surjective.denseRange.comp
    (separableAbsoluteLocalArtinMap_denseRange K) e.continuous

/-- The canonical homomorphism from the topological profinite completion of
`K×` to the usual absolute Galois topological abelianization. -/
noncomputable def profiniteLocalReciprocityHom  :=
  topologicalProfiniteCompletionLift
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K)



















/-- Dense range of the absolute Artin map and compactness of the completion
make the profinite reciprocity homomorphism onto. -/
def profiniteLocalReciprocityHom_surjective  :=
  topologicalProfiniteCompletionLift_surjective_of_denseRange
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K)
      (absoluteLocalArtinMap_denseRange K)














/-- The profinite reciprocity homomorphism is the unique continuous
homomorphism extending the absolute local Artin map. -/
def profiniteLocalReciprocityHom_unique
    (f : TopologicalProfiniteCompletion Kˣ →ₜ*
      standardLocalAbsoluteAbelianProfinite K)
    (hf : f.comp (topologicalProfiniteCompletionMap Kˣ) =
      absoluteLocalArtinMap K)  :=
  topologicalProfiniteCompletionLift_unique
    (standardLocalAbsoluteAbelianProfinite K) (absoluteLocalArtinMap K) f hf

/-- The canonical lift to the usual absolute abelianization is transport of
the corresponding separable lift. -/
theorem profiniteLocalReciprocityHom_eq_transport :
    profiniteLocalReciprocityHom K =
      (separableToStandardAbsoluteAbelianizationHom K).comp
        (separableProfiniteLocalReciprocityHom K) := by
  symm
  apply profiniteLocalReciprocityHom_unique K
  apply ContinuousMonoidHom.ext
  intro a
  change
    separableToStandardAbsoluteAbelianizationEquiv K
        (separableProfiniteLocalReciprocityHom K
          (topologicalProfiniteCompletionMap Kˣ a)) =
      absoluteLocalArtinMap K a
  rw [separableProfiniteLocalReciprocityHom_map]
  rfl

/-- The canonical lift to the usual absolute abelianization is one-to-one. -/
theorem profiniteLocalReciprocityHom_injective :
    Function.Injective (profiniteLocalReciprocityHom K) := by
  rw [profiniteLocalReciprocityHom_eq_transport K]
  exact (separableToStandardAbsoluteAbelianizationEquiv K).injective.comp
    (separableProfiniteLocalReciprocityHom_injective K)

/-- **Profinite local reciprocity.** The topological profinite completion of
the local multiplicative group is canonically continuously isomorphic to the
topological abelianization of Mathlib's usual absolute Galois group. -/
noncomputable def profiniteLocalReciprocity :
    TopologicalProfiniteCompletion Kˣ ≃ₜ*
      standardLocalAbsoluteAbelianProfinite K :=
  { Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (profiniteLocalReciprocityHom K)
        ⟨profiniteLocalReciprocityHom_injective K,
          profiniteLocalReciprocityHom_surjective K⟩)
      (profiniteLocalReciprocityHom K).continuous_toFun with
    map_mul' := (profiniteLocalReciprocityHom K).map_mul }

/-- The standard reciprocity equivalence has the same underlying map as its lifted homomorphism. -/
@[simp]
theorem profiniteLocalReciprocity_apply
    (x : TopologicalProfiniteCompletion Kˣ) :
    profiniteLocalReciprocity K x =
      profiniteLocalReciprocityHom K x :=
  rfl














































































































end LocalClassFieldTheory

end
