module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality
public import GaloisCohomology.ProfiniteIntegers.TopologicalGeneration
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Transfer--norm Frobenius geometry

For a finite Galois extension and an intermediate field, this module builds the
Frobenius-side subgroup and orbit equivalences used in transfer--norm
naturality.  The reusable orbit and double-coset constructions are isolated in
`DoubleCosetOrbitGeometry`.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology
open CategoryTheory


open scoped BigOperators
open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal] :
    (extensionSubgroup K' L hLK').Normal := by
  have hcomap : extensionSubgroup K' L hLK' =
      (extensionSubgroup K L (hLK'.trans hK'K)).comap
        (Subgroup.inclusion hK'K) := by
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData
