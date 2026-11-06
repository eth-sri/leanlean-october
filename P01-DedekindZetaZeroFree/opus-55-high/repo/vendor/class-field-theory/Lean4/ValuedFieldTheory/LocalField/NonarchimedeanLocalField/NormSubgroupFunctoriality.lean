module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Functoriality of finite-extension norm subgroups

The local existence proof repeatedly enlarges a finite extension and replaces
finite extensions by isomorphic realizations.  This file records the resulting
identities for unit norms and their images in the base field.
-/


namespace LocalFieldTheory

open LocalFieldTheory

/-- Enlarging the top field in a finite tower can only shrink its norm
subgroup in the base field. -/
theorem normSubgroup_le_of_tower
    (K M L : Type) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional M L] :
    localNormSubgroup K L ≤ localNormSubgroup K M := by
  rintro x ⟨y, rfl⟩
  refine ⟨normUnits M L y, ?_⟩
  exact normUnits_tower K M L y

/-- The norm on units is unchanged after replacing a finite extension by an
isomorphic realization. -/
theorem normUnits_algEquiv
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (x : Lˣ) :
    normUnits K M (Units.mapEquiv e.toMulEquiv x) = normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv e (x : L)

/-- Norm subgroups are unchanged after replacing an extension by an
isomorphic realization. -/
theorem normSubgroup_algEquiv
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) :
    localNormSubgroup K M = localNormSubgroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : Lˣ := Units.mapEquiv e.symm.toMulEquiv y
    refine ⟨z, ?_⟩
    have hz : Units.mapEquiv e.toMulEquiv z = y := 
      (Units.mapEquiv e.toMulEquiv).apply_symm_apply y
    calc
      normUnits K L z =
          normUnits K M (Units.mapEquiv e.toMulEquiv z) :=
        (normUnits_algEquiv K L M e z).symm
      _ = normUnits K M y := congrArg (normUnits K M) hz
  · rintro ⟨x, rfl⟩
    refine ⟨Units.mapEquiv e.toMulEquiv x, ?_⟩
    exact normUnits_algEquiv K L M e x
