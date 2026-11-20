module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import GaloisCohomology.Cyclic.TateComparison
public import GaloisCohomology.Cyclic.TateH0.Invariants

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.TateH0.NormImage` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory
open CategoryTheory

noncomputable section

universe u

section

variable (K L : Type) [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)]

/-- The group-cohomological norm endomorphism on the actual unit representation. -/
def unitsNormLinearMap : Additive Lˣ →ₗ[ℤ] Additive Lˣ :=
  (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap

/-- The additive unit norm is fixed by the Galois action. -/
lemma unitsNorm_mem_invariants (x : Additive Lˣ) :
    unitsNormLinearMap K L x ∈ unitsInvariantSubmodule K L := fun σ => Representation.self_norm_apply (Rep.ofAlgebraAutOnUnits K L).ρ σ x

/-- The norm map, codomain-restricted to invariant units. -/
def unitsNormToInvariantsLinearMap : Additive Lˣ →ₗ[ℤ] unitsInvariantSubmodule K L :=
  (unitsNormLinearMap K L).codRestrict (unitsInvariantSubmodule K L)
    (unitsNorm_mem_invariants K L)

/-- Norm image inside invariant units. -/
def unitsTateH0NormSubmodule : Submodule ℤ (unitsInvariantSubmodule K L) :=
  LinearMap.range (unitsNormToInvariantsLinearMap K L)

/-- The standard degree-zero Tate object, expressed as the arithmetic quotient
of invariant units by the representation norm image. -/
def tateUnitsH0IsoInvariantsQuotient :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 ≅
      ModuleCat.of ℤ
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let S : ShortComplex (ModuleCat ℤ) :=
    .mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  let eK :=
    LinearEquiv.ofEq _ _ (groupCohomology.d₀₁_ker_eq_invariants A)
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        unitsTateH0NormSubmodule K L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  exact TateCohomology.isoZeroBoundary A ≪≫
    S.moduleCatHomologyIso ≪≫ ((Submodule.Quotient.equiv _ _ eK hboundary).toModuleIso)

end

/-- The value of the additive unit norm map is the field norm of the underlying unit. -/
theorem unitsNormLinearMap_apply_val (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     (Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) : Lˣ).1) =
      algebraMap K L (Algebra.norm K (x : L)) := by
  rw [← groupCohomology.norm_ofAlgebraAutOnUnits_eq x]
  rfl

/-- A finite sum of additive units corresponds to the product of their underlying units. -/
@[simp]
lemma additive_toMul_finset_sum_units {ι : Type*} (L : Type*) [Field L]
    (s : Finset ι) (f : ι → Additive Lˣ) :
    Additive.toMul (Finset.sum s f) =
      Finset.prod s (fun i => Additive.toMul (f i)) := by
  rfl

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The additive subgroup of `Additive Kˣ` attached to the multiplicative norm subgroup. -/
def additiveNormSubgroup :
    AddSubgroup (Additive Kˣ) :=
  (localNormSubgroup K L).toAddSubgroup

/-- The additive norm subgroup is the kernel of the norm-quotient map. -/
lemma additiveNormSubgroup_eq_ker_quotient_map :
    additiveNormSubgroup K L =
      (MonoidHom.toAdditive (normClass K L)).ker := by
  ext x
  change Additive.toMul x ∈ localNormSubgroup K L ↔
    Additive.ofMul (normClass K L (Additive.toMul x)) = 0
  constructor
  · intro hx
    exact congrArg Additive.ofMul
      ((normClass_eq_one_iff K L (Additive.toMul x)).mpr
        (MonoidHom.mem_range.mp hx))
  · intro hx
    exact MonoidHom.mem_range.mpr
      ((normClass_eq_one_iff K L (Additive.toMul x)).mp
        (Additive.ofMul.injective hx))

end

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The invariant-unit equivalence sends the additive unit norm to the field norm. -/
lemma invariantsUnitsAddEquivBaseUnits_unitsNorm_apply
    (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     invariantsUnitsAddEquivBaseUnits K L
        (unitsNormToInvariantsLinearMap K L (Additive.ofMul x))) =
      Additive.ofMul (normUnits K L x) := by
  let := AlgEquiv.fintype K L
  apply Additive.toMul.injective
  ext
  apply FaithfulSMul.algebraMap_injective K L
  rw [invariantsUnitsAddEquivBaseUnits_spec]
  exact (unitsNormLinearMap_apply_val K L x).trans (rfl)

/-- The invariant-unit equivalence maps the Tate norm submodule onto the additive norm subgroup. -/
lemma invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).toAddSubgroup.map
        (invariantsUnitsAddEquivBaseUnits K L).toAddMonoidHom) =
      additiveNormSubgroup K L := by
  let := AlgEquiv.fintype K L
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    change Additive.toMul
        (invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L z)) ∈ localNormSubgroup K L
    let a : Lˣ := Additive.toMul z
    rw [show z = Additive.ofMul a by cases z; rfl]
    have hmap :=
      congrArg Additive.toMul
        (invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L a)
    rw [hmap]
    exact ⟨a, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K L at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨unitsNormToInvariantsLinearMap K L (Additive.ofMul x), ⟨Additive.ofMul x, rfl⟩, ?_⟩
    calc
      _
          = Additive.ofMul (normUnits K L x) :=
            invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L x
      _ = Additive.ofMul (Additive.toMul y) := congrArg Additive.ofMul hx
      _ = y := by rfl

/-- The multiplicative invariant-unit equivalence maps Tate norms onto field norms. -/
lemma invariantsUnitsEquivBaseUnits_map_tateNormSubmodule :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).map
        (invariantsUnitsEquivBaseUnits K L : unitsInvariantSubmodule K L →ₗ[ℤ] Additive Kˣ)) =
      (additiveNormSubgroup K L).toIntSubmodule := by
  solve_by_elim [invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup, Submodule.toAddSubgroup_injective]

end
end CyclicCohomology
