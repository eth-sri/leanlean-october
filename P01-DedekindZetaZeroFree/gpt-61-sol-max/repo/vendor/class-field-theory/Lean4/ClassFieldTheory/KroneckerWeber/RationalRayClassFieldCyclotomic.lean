module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicRayNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The rational ray class field as an actual cyclotomic field

For a nonzero natural number `m`, the selected ray class field for the
rational modulus `(m)` is isomorphic over `ℚ` to the actual cyclotomic
field `CyclotomicField m ℚ`.

The field comparison is obtained from the exact idèle-class norm-range
equality.  We also retain the topological content of global reciprocity:

`Gal(ℚ(μ_m) / ℚ) ≃ₜ* C_ℚ / C_ℚ^m`.

Thus the result is an equality of actual class fields and not merely an
equality of degrees or an abstract comparison of finite groups.
-/

open scoped Classical IsMulCommutative NumberField Cyclotomic

noncomputable section

namespace KroneckerWeber

open GlobalClassFieldTheory
open GlobalClassFieldTheory.GlobalClassFields
open GlobalClassFieldTheory.Reciprocity
open NumberField IsDedekindDomain

noncomputable local instance rationalCyclotomicLevelIsAbelianGalois
    (n : ℕ+) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel n) :=
  IsCyclotomicExtension.isAbelianGalois {(n : ℕ)} ℚ
    (KummerTheory.rationalCyclotomicLevel n)

 noncomputable def
    galoisContinuousMulEquivRayClassGroupOfNormRangeEq
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    (r : RayClass.Modulus ℚ)
    (h : (_root_.ideleClassNorm ℚ L).range =
      RayClass.Modulus.congruenceSubgroup r) :
    Gal(L / ℚ) ≃ₜ* RayClass.RayClassGroup r := by
  letI : (_root_.ideleClassNorm ℚ L).range.Normal :=
    h ▸ inferInstance
  letI : DiscreteTopology (RayClass.RayClassGroup r) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup r)
  let reciprocity :
      Gal(L / ℚ) ≃*
        (IdeleClassGroup ℚ ⧸
          (_root_.ideleClassNorm ℚ L).range) :=
    AddEquiv.toMultiplicative (globalReciprocityEquiv ℚ L)
  exact
    { reciprocity.trans
        (QuotientGroup.quotientMulEquivOfEq h) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }































































































































section NonzeroOrder

variable (m : ℕ) [NeZero m]

local instance : NeZero (m : ℚ) :=
  ⟨by exact_mod_cast (NeZero.ne m)⟩

noncomputable local instance :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨m, NeZero.pos m⟩

noncomputable local instance :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨m, NeZero.pos m⟩














noncomputable local instance rationalCyclotomicFieldIsCyclotomicExtension :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

noncomputable local instance rationalCyclotomicFieldIsAbelianGalois :
    IsAbelianGalois ℚ (CyclotomicField m ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {m} ℚ
    (CyclotomicField m ℚ)

noncomputable local instance rationalCyclotomicLevelIdeleClassNormRangeNormal :
    (_root_.ideleClassNorm ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)).range.Normal := by
  rw [
    rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
      m (NeZero.ne m)]
  infer_instance

noncomputable local instance rationalCyclotomicFieldIdeleClassNormRangeNormal :
    (_root_.ideleClassNorm ℚ (CyclotomicField m ℚ)).range.Normal := by
  rw [
    rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
      m (NeZero.ne m)]
  infer_instance
























































































































































/-- Topological global reciprocity for the actual finite level inside the
rational cyclotomic closure.  The target is the idelic rational ray class
group modulo `(m)`, transported along the exact norm-range equality. -/
noncomputable def
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
    :
    Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩ / ℚ) ≃ₜ*
      RayClass.RayClassGroup (RayClass.rationalModulus m) :=
  galoisContinuousMulEquivRayClassGroupOfNormRangeEq
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)
      (RayClass.rationalModulus m)
      (rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
        m (NeZero.ne m))

/-- Evaluation of finite-level rational cyclotomic reciprocity is inverse
global norm-residue reciprocity followed by the exact ray norm-range
transport. -/
@[simp]
theorem
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_apply
    (σ :
      Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩ / ℚ)) :
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
        m σ =
      QuotientGroup.quotientMulEquivOfEq
          (rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
            m (NeZero.ne m))
        (Additive.toMul
          ((globalNormResidueEquiv
              ℚ
              (KummerTheory.rationalCyclotomicLevel
                ⟨m, NeZero.pos m⟩)).symm
            (Additive.ofMul σ))) := by
  rfl



























































































































































































































/-- Topological global reciprocity for the actual rational cyclotomic
field, with target the rational ray class group modulo `(m)`. -/
noncomputable def
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup
    :
    Gal(CyclotomicField m ℚ / ℚ) ≃ₜ*
      RayClass.RayClassGroup (RayClass.rationalModulus m) :=
  galoisContinuousMulEquivRayClassGroupOfNormRangeEq
      (CyclotomicField m ℚ) (RayClass.rationalModulus m)
      (rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
        m (NeZero.ne m))

/-- The ordinary cyclotomic character, retaining the finite Krull
topology on the actual Galois group and the discrete topology on
`(ℤ/mℤ)ˣ`. -/
noncomputable def
    rationalCyclotomicGaloisContinuousMulEquivZModUnits
    :
    Gal(CyclotomicField m ℚ / ℚ) ≃ₜ*
      (ZMod m)ˣ := by
  exact
    { IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Forgetting topology from the cyclotomic character recovers the
standard `galEquivZMod` map literally. -/
@[simp]
theorem
    rationalCyclotomicGaloisContinuousMulEquivZModUnits_apply
    (σ : Gal(CyclotomicField m ℚ / ℚ)) :
    rationalCyclotomicGaloisContinuousMulEquivZModUnits
        m σ =
      IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ) σ := by
  rfl

/-- Evaluation of rational cyclotomic reciprocity is inverse global
norm-residue reciprocity followed by transport along the exact
cyclotomic norm-range equality. -/
@[simp]
theorem
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup_apply
    (σ : Gal(CyclotomicField m ℚ / ℚ)) :
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup
        m σ =
      QuotientGroup.quotientMulEquivOfEq
          (rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
            m (NeZero.ne m))
        (Additive.toMul
          ((globalNormResidueEquiv
              ℚ (CyclotomicField m ℚ)).symm
            (Additive.ofMul σ))) := by
  rfl


















end NonzeroOrder

end KroneckerWeber

end
