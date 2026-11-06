module

public import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.RamificationIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The totally ramified cyclotomic endpoint

This file packages the actual integral-closure complete-DVF model as a totally ramified extension.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedRamificationEndpointAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedRamificationEndpointScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl



end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
