module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence` Lean module. -/

namespace RamificationTheory

open ValuationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

variable (K : Type u) [Field K]

section FiniteExtension

variable {L : Type v} [Field L] [Algebra K L]

local instance fieldRangeIsScalarTower
    (i : L →ₐ[K] AlgebraicClosure K) :
    IsScalarTower K (AlgHom.fieldRange i) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl



/-- Normality of `L/K` transports to the embedded field range `i(L)`. -/
instance normal_fieldRangeOfExtension
    (i : L →ₐ[K] AlgebraicClosure K) [Normal K L] :
    Normal K (AlgHom.fieldRange i) :=
  Normal.of_algEquiv (AlgEquiv.ofInjectiveField i)



end FiniteExtension

end absoluteGaloisGroup
end Field

namespace DiscreteValuationField
namespace HenselianDVF
