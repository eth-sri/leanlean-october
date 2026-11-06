module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.Instances
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.H0
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.HMinusOne
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Finite-support decompositions of actual ideles

For a finite set `S` of finite places, this file identifies the actual
subgroup `I_K^S` with the product of all archimedean local groups, the
full multiplicative groups at places in `S`, and the local unit groups
away from `S`.  The construction is componentwise and uses the genuine
restricted-product membership condition.

For a finite family of base places in a Galois extension, it also
assembles the local tensor-algebra decomposition and proves its
equivariance for the full Galois action.  Finally, the concrete
unramified local class-field theorem is transported through Shapiro to
show that every unramified induced integer-unit block has trivial
`H⁰` and `H⁻¹`.
-/

open scoped NumberField RestrictedProduct ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u

variable {F : Type u} [Field F] [NumberField F]

section FiniteTensorFamily

universe uK uL uι

variable {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual scalar-extended local tensor factors over a family of
base places. -/
abbrev LocalTensorFamily {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :=
  ∀ i, (LocalTensorAlgebra (L := L) (d i).base)ˣ

/-- The componentwise induced-module action on a local block family. -/
@[reducible]
def localBlockFamilyAction {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily d) := by
  letI : ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI : ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
  exact piMulDistribMulAction (L ≃ₐ[K] L)
    (fun i ↦ LocalPlaceBlock
      (d i).base (d i).base_isNontrivial
      (d i).extension)

end FiniteTensorFamily

section UnramifiedLocalUnits

/-- Outside the ramified support, the local integer-unit factor has
trivial low-degree Tate cohomology.  This generator-explicit form is the
one needed after restricting a global cyclic generator to a decomposition
group. -/
theorem unramifiedLocalIntegerUnitsHerbrand_subsingleton
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel ell] [UniformSpace ell]
    [IsUniformAddGroup ell]
    [IsNonarchimedeanLocalField ell]
    [Valuation.HasExtension
      (ValuativeRel.valuation k) (ValuativeRel.valuation ell)]
    [IsIntegralClosure 𝒪[ell] 𝒪[k] ell]
    [Module.Finite 𝒪[k] 𝒪[ell]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      k ell]
    (g : Gal(ell / k))
    (hg : ∀ σ : Gal(ell / k),
      σ ∈ Subgroup.zpowers g) :
    letI :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        k ell
    Subsingleton
        (HerbrandH0 (Gal(ell / k)) 𝒪[ell]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(ell / k)) 𝒪[ell]ˣ g) := by
  exact
    (unramified_units_tateCohomology_and_norm_surjective_for_generator
      k ell g hg).1
