module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Arithmetic normalization of global reciprocity

The valuation used by the local class-formation implementation is the
logarithm of the multiplicative absolute value.  Consequently its
distinguished element of value `1` is the inverse of a DVR uniformizer.
The resulting field-facing reciprocity map sends a usual uniformizer to
geometric Frobenius.

The arithmetic global norm-residue symbol uses the opposite
normalization: a DVR uniformizer maps to arithmetic Frobenius and a
ramified cyclotomic unit `u` acts by `u⁻¹`.  For an abelian target the two
normalizations differ by the canonical inversion automorphism.  This file
records that normalization explicitly, including its topology and its
local-global compatibility.  Thus no sign convention is hidden in an
unbundled equality.
-/

open scoped IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

 theorem arithmeticNormIdeleClassIsMulCommutative
    (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] arithmeticNormIdeleClassIsMulCommutative

/-- Inversion as a topological multiplicative automorphism of a
commutative topological group. -/
def commutativeGroupInversionContinuousMulEquiv
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    G ≃ₜ* G :=
  { MulEquiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }

section FiniteGalois

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The global norm-residue homomorphism with arithmetic
Frobenius normalization, for an arbitrary finite Galois extension. -/
def arithmeticGlobalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) :=
  (MulEquiv.inv
      (Abelianization (Gal(L / K)))).toMonoidHom.comp
    (globalNormResidueAbelianizationMonoidHom K L)

end FiniteGalois

section FiniteAbelian

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The global norm-residue homomorphism in arithmetic Frobenius
normalization for a finite abelian extension. -/
def arithmeticGlobalNormResidueMonoidHom :
    IdeleClassGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalNormResidueMonoidHom K L)

/-- Arithmetic normalization evaluates by inverting the geometric global
norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_apply
    (c : IdeleClassGroup K) :
    arithmeticGlobalNormResidueMonoidHom K L c =
      (globalNormResidueMonoidHom K L c)⁻¹ := by
  rfl

/-- Arithmetic normalization leaves the global norm kernel unchanged. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_ker :
    (arithmeticGlobalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  simp only [MonoidHom.mem_ker,
    arithmeticGlobalNormResidueMonoidHom_apply, inv_eq_one]
  exact globalNormResidueMonoidHom_eq_one_iff K L c

/-- Arithmetic global norm-residue as a homeomorphic multiplicative
equivalence of the native norm quotient with the finite Krull Galois
group. -/
def arithmeticGlobalNormResidueContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Gal(L / K) :=
  (globalNormResidueContinuousMulEquiv K L).trans
    (commutativeGroupInversionContinuousMulEquiv
      (Gal(L / K)))

/-- The chosen finite-place Artin homomorphism in arithmetic
normalization.  A usual local uniformizer therefore maps to arithmetic
Frobenius. -/
def arithmeticChosenFinitePlaceArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v)

omit [NumberField L] in
/-- Arithmetic finite-place Artin symbols are inverses of the geometric
chosen local symbols. -/
@[simp]
theorem arithmeticChosenFinitePlaceArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticChosenFinitePlaceArtinMonoidHom K L v x =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹ := by
  rfl

/-- Finite-place local-global compatibility in arithmetic
normalization. -/
theorem
    arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (v : HeightOneSpectrum (𝓞 K)) :
    (arithmeticGlobalNormResidueMonoidHom K L).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      arithmeticChosenFinitePlaceArtinMonoidHom K L v := by
  apply MonoidHom.ext
  intro x
  change
    (globalNormResidueMonoidHom K L
      (IdeleGroup.finitePlaceIdeleClass v x))⁻¹ =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹
  simpa only [MonoidHom.comp_apply] using
    congrArg (fun σ : Gal(L / K) => σ⁻¹)
      (DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
          (K := K) (L := L) v) x)

/-- The idèle-level global Artin product in arithmetic normalization. -/
def arithmeticGlobalArtinMonoidHom :
    IdeleGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalArtinMonoidHom (K := K) (L := L))

omit [FiniteDimensional K L] in
/-- The arithmetic global Artin symbol is the inverse of the geometric global
Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    arithmeticGlobalArtinMonoidHom K L a =
      (globalArtinMonoidHom (K := K) (L := L) a)⁻¹ := by
  rfl

/-- The arithmetic global Artin symbol of a finite one-place idèle is
literally the arithmetic chosen local Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (finitePlaceIdele v x) =
      arithmeticChosenFinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_finitePlaceIdele,
    arithmeticChosenFinitePlaceArtinMonoidHom_apply]

/-- Descending the arithmetic local-product Artin map through principal
idèles gives the arithmetic global norm-residue homomorphism literally. -/
theorem
    arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin :
    (arithmeticGlobalNormResidueMonoidHom K L).comp
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)) =
      arithmeticGlobalArtinMonoidHom K L := by
  apply MonoidHom.ext
  intro a
  change
    (globalNormResidueMonoidHom K L
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a))⁻¹ =
      (globalArtinMonoidHom (K := K) (L := L) a)⁻¹
  simpa only [MonoidHom.comp_apply] using
    congrArg (fun σ : Gal(L / K) => σ⁻¹)
      (DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K) (L := L)) a)
