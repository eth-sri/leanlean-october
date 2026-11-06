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
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

















set_option autoImplicit false

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
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u

variable {F : Type u} [Field F] [NumberField F]

section
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
include S
/-- The finite local factors occurring in `I_F^S`: arbitrary local
elements on `S`, and integral local units away from `S`. -/
abbrev FiniteSPlaceFactors
      :=
  (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S},
      (v.1.adicCompletion F)ˣ) ×
    (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (v.1.adicCompletionIntegers F).units)

/-- The complete product model for `I_F^S`, including every
archimedean component. -/
abbrev IdeleSPlaceFactors
      :=
  InfiniteIdeleGroup F × FiniteSPlaceFactors (F := F) S

/-- Assemble prescribed local factors into a finite idele.  Restricted
product membership follows because the only possibly nonintegral
components lie in the finite set `S`. -/
noncomputable def finiteIdeleOfSPlaceFactors
     
    (x : FiniteSPlaceFactors (F := F) S) :
    FiniteIdeleGroup F := by
  classical
  let f : ∀ v : HeightOneSpectrum (𝓞 F),
      (v.adicCompletion F)ˣ :=
    fun v ↦ if hv : v ∈ S then
      x.1 ⟨v, hv⟩
    else
      (x.2 ⟨v, hv⟩ :
        (v.adicCompletion F)ˣ)
  refine ⟨f, S.eventually_cofinite_notMem.mono ?_⟩
  intro v hv
  simp only [f, dite_eq_right hv]
  exact (x.2 ⟨v, hv⟩).2

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_mem
     
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    finiteIdeleOfSPlaceFactors S x v = x.1 ⟨v, hv⟩ := by
  simp [finiteIdeleOfSPlaceFactors, hv]

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_notMem
     
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    finiteIdeleOfSPlaceFactors S x v =
      (x.2 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) := by
  simp [finiteIdeleOfSPlaceFactors, hv]

/-- The finite part of the actual `S`-idele group is exactly the
displayed product of local multiplicative groups and local unit groups. -/
noncomputable def finiteSupportedAtEquivSPlaceFactors
      :
    FiniteIdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      FiniteSPlaceFactors (F := F) S where
  toFun a :=
    ⟨fun v ↦ a.1 v.1,
      fun v ↦ ⟨a.1 v.1, a.2 v.1 v.2⟩⟩
  invFun x :=
    ⟨finiteIdeleOfSPlaceFactors S x, by
      intro v hv
      rw [finiteIdeleOfSPlaceFactors_apply_notMem S x v hv]
      exact (x.2 ⟨v, hv⟩).2⟩
  left_inv a := by
    apply Subtype.ext
    ext v
    by_cases hv : v ∈ S
    · simp [finiteIdeleOfSPlaceFactors_apply_mem, hv]
    · simp [finiteIdeleOfSPlaceFactors_apply_notMem, hv]
  right_inv x := by
    apply Prod.ext
    · funext v
      exact finiteIdeleOfSPlaceFactors_apply_mem S x v.1 v.2
    · funext v
      apply Subtype.ext
      exact finiteIdeleOfSPlaceFactors_apply_notMem S x v.1 v.2
  map_mul' a b := by
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl

/-- The actual finite-support decomposition:

`I_F^S ≃ I_{F,∞} × (∏_{v∈S} F_vˣ) ×
  (∏_{v∉S} O_vˣ)`.
-/
noncomputable def ideleSupportedAtEquivInfiniteProd
      :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      InfiniteIdeleGroup F ×
        FiniteIdeleGroup.supportedAt (K := F) (S : Set _) where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual `S`-idele group identified with its complete family of
archimedean, unrestricted finite, and integral finite local factors. -/
noncomputable def ideleSupportedAtEquivSPlaceFactors
      :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      IdeleSPlaceFactors (F := F) S :=
  (ideleSupportedAtEquivInfiniteProd S).trans
    ((MulEquiv.refl (InfiniteIdeleGroup F)).prodCongr
      (finiteSupportedAtEquivSPlaceFactors S))

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_infinite
     
    (a : IdeleGroup.supportedAt (K := F) (S : Set _)) :
    (ideleSupportedAtEquivSPlaceFactors S a).1 = a.1.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_inside
     
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) :
    (ideleSupportedAtEquivSPlaceFactors S a).2.1 v =
      a.1.2 v.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_outside_coe
     
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    ((ideleSupportedAtEquivSPlaceFactors S a).2.2 v :
        (v.1.adicCompletion F)ˣ) =
      a.1.2 v.1 :=
  rfl
end


section FiniteTensorFamily

universe uK uL uι

variable {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]




















/-- The componentwise induced-module action on a local block family. -/
@[reducible]
noncomputable def localBlockFamilyAction {ι : Type uι}
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






























section InducedOutsideSBlock

universe uG

variable {G : Type uG} [Group G] [Fintype G]




























































































































end InducedOutsideSBlock

end UnramifiedLocalUnits

end
