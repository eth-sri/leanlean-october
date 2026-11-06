module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FieldUnitsHerbrand
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.IntegerUnitsHerbrand
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisCohomology

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# The local class-field axiom

For a cyclic extension of nonarchimedean local fields, the actual Tate
cohomology of `Lˣ` has cardinalities `[L : K]` in degree zero and `1` in
degree minus one.
-/

noncomputable section

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

section
variable (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
include g hg
/-- The integer-unit Herbrand witness used by the local class-field axiom,
including the proof that its Herbrand quotient is one. -/
theorem exists_localIntegerUnitsHerbrandDefinedAndEqOne
      :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
      @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup
      (K := K) (L := L) with ⟨cV, hcV⟩
  rcases exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
      (K := K) (L := L) g hg with ⟨cH, hcH⟩
  rcases exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel
      (K := K) (L := L) with ⟨cU, hcU⟩
  let n  := max cV (max cH cU)
  have hcVn : cV ≤ n := le_max_left cV (max cH cU)
  have hrest : max cH cU ≤ n := le_max_right cV (max cH cU)
  have hcHn : cH ≤ n := le_trans (le_max_left cH cU) hrest
  have hcUn : cU ≤ n := le_trans (le_max_right cH cU) hrest
  rcases hcV n hcVn with ⟨V, hV, _hVprincipal⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  have hcoh := hcH n hcHn V hV
  rcases hcU n hcUn V hV g hg hcoh.1 hcoh.2 with ⟨hU, hUone⟩
  exact ⟨hU, hUone⟩

/-- Canonical choice of the integer-unit finiteness witness constructed by
the local normal-basis argument. -/
private def localIntegerUnitsHerbrandDefined
       :=
  Classical.choose (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

private def localIntegerUnitsHerbrandQuotient_eq_one
       :=
  Classical.choose_spec (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

/-- Finiteness of actual unit Tate `H⁰`, produced from the same local
normal-basis witness as the cardinality theorem. -/
theorem localFieldUnitsTateH0FiniteOfGenerator
      :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  unitsTateH0FiniteOfIntegerUnitsHerbrand K L g hg
    (localIntegerUnitsHerbrandDefined K L g hg)

/-- The local class-field-axiom theorem for a specified generator of the cyclic Galois group. -/
theorem localFieldUnits_tate_card_of_generator
      :
    letI := localFieldUnitsTateH0FiniteOfGenerator K L g hg
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := fieldUnits_tate_card_of_integerUnits_herbrand_eq_one
    K L g hg (localIntegerUnitsHerbrandDefined K L g hg)
      (localIntegerUnitsHerbrandQuotient_eq_one K L g hg)
end






















end
end LocalClassFieldTheory
