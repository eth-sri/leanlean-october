module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Functoriality of finite-extension norm subgroups

The local existence proof repeatedly enlarges a finite extension and replaces
finite extensions by isomorphic realizations.  This file records the resulting
identities for unit norms and their images in the base field.
-/

noncomputable section

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
  apply normUnits_tower

variable (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M)

/-- The norm on units is unchanged after replacing a finite extension by an
isomorphic realization. -/
theorem normUnits_algEquiv (x : Lˣ) :
    normUnits K M (Units.mapEquiv e.toMulEquiv x) = normUnits K L x := by
  exact Units.ext (Algebra.norm_eq_of_algEquiv e ↑x)

include e in
/-- Norm subgroups are unchanged after replacing an extension by an
isomorphic realization. -/
theorem normSubgroup_algEquiv :
    localNormSubgroup K M = localNormSubgroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Exists.intro ((Units.mapEquiv e.symm.toMulEquiv) y) (Trans.trans (Eq.symm (normUnits_algEquiv K L M e ((Units.mapEquiv e.symm.toMulEquiv) y))) (congrArg (⇑(normUnits K M)) (MulEquiv.apply_symm_apply (Units.mapEquiv e.toMulEquiv) y)))
  · rintro ⟨x, rfl⟩
    solve_by_elim [normUnits_algEquiv, Units.mapEquiv, Exists.intro]

end LocalFieldTheory

end
