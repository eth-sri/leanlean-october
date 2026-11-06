module

public import ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtin
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Finite reciprocity as an isomorphism of diagrams

The open normal subgroups of the absolute abelianized Galois group index
three covariant finite diagrams: its finite quotients, the corresponding
finite abelian Galois groups, and the corresponding norm quotients.  This
file packages the canonical finite-stage identifications as natural
isomorphisms.
-/

noncomputable section

open CategoryTheory

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
 abbrev AbsoluteFiniteIndex :=
  OpenNormalSubgroup (localAbsoluteAbelianProfinite K)

noncomputable local instance finiteDiagramNormQuotientTopologicalSpace
    (E L : Type) [Field E] [Field L] [Algebra E L]
    [TopologicalSpace E] :
    TopologicalSpace (NormQuotient E L) := by
  change TopologicalSpace (Eˣ ⧸ localNormSubgroup E L)
  infer_instance

local instance finiteDiagramNormQuotientIsTopologicalGroup
    (L : Type) [Field L] [Algebra K L] :
    IsTopologicalGroup (NormQuotient K L) := by
  change IsTopologicalGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance






omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Inclusion of open normal subgroups gives the corresponding inclusion of
finite norm subgroups. -/
theorem absoluteFiniteNormSubgroup_mono
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) :
    localNormSubgroup K (absoluteFiniteQuotientField K N) ≤
      localNormSubgroup K (absoluteFiniteQuotientField K M) := by
  let E := absoluteFiniteQuotientField K M
  let F := absoluteFiniteQuotientField K N
  let hEF : E ≤ F :=
    absoluteFiniteQuotientField_antitone (K := K) hNM
  let EAlgebra : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : SMul E F :=
    @Algebra.toSMul _ _ _ _ EAlgebra
  let : Module E F :=
    @Algebra.toModule _ _ _ _ EAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E F := FiniteDimensional.right K E F
  change localNormSubgroup K F ≤ localNormSubgroup K E
  exact LocalFieldTheory.normSubgroup_le_of_tower K E F

/-- The first isomorphism theorem for a finite coordinate of the absolute
Artin map, with its kernel identified with the corresponding norm subgroup. -/
noncomputable def absoluteFiniteArtinQuotientEquiv
    (N : AbsoluteFiniteIndex K) :
    NormQuotient K (absoluteFiniteQuotientField K N) ≃ₜ*
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) := by
  letI : DiscreteTopology
      (NormQuotient K (absoluteFiniteQuotientField K N)) :=
    normQuotient_discrete K (absoluteFiniteQuotientField K N)
  letI : DiscreteTopology
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen'
  let e : NormQuotient K (absoluteFiniteQuotientField K N) ≃*
      (localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) :=
    normQuotientEquivOfSurjective
      (absoluteFiniteArtinMap K N).toMonoidHom
      (absoluteFiniteArtinMap_surjective K N)
      (absoluteFiniteArtinMap_ker K N)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- States the theorem `absoluteFiniteArtinQuotientEquiv_mk`. -/
@[simp]
theorem absoluteFiniteArtinQuotientEquiv_mk
    (N : AbsoluteFiniteIndex K) (a : Kˣ) :
    absoluteFiniteArtinQuotientEquiv K N
        (normClass K
          (absoluteFiniteQuotientField K N) a) =
      absoluteFiniteArtinMap K N a := by
  exact normQuotientEquivOfSurjective_normClass
    (absoluteFiniteArtinMap K N).toMonoidHom
    (absoluteFiniteArtinMap_surjective K N)
    (absoluteFiniteArtinMap_ker K N) a

/-- The transition map on norm quotients induced by a tower of fixed fields. -/
noncomputable def normQuotientTransition
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) :
    NormQuotient K (absoluteFiniteQuotientField K N) →ₜ*
      NormQuotient K (absoluteFiniteQuotientField K M) := by
  letI : DiscreteTopology
      (NormQuotient K (absoluteFiniteQuotientField K N)) :=
    normQuotient_discrete K (absoluteFiniteQuotientField K N)
  let f : NormQuotient K (absoluteFiniteQuotientField K N) →*
      NormQuotient K (absoluteFiniteQuotientField K M) :=
    normQuotientMapOfLE K
      (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField K M)
      (absoluteFiniteNormSubgroup_mono K hNM)
  exact
    { f with
      continuous_toFun := continuous_of_discreteTopology }

/-- States the theorem `normQuotientTransition_mk`. -/
@[simp]
theorem normQuotientTransition_mk
    {N M : AbsoluteFiniteIndex K} (hNM : N ≤ M) (a : Kˣ) :
    normQuotientTransition K hNM
        (normClass K
          (absoluteFiniteQuotientField K N) a) =
      normClass K
        (absoluteFiniteQuotientField K M) a := by
  exact normQuotientMapOfLE_normClass K
    (absoluteFiniteQuotientField K N)
    (absoluteFiniteQuotientField K M)
    (absoluteFiniteNormSubgroup_mono K hNM) a








end LocalClassFieldTheory

end
