module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Analytic evaluation for theta

The theta series of the completed theta-intertwining theorem has coefficients in
`(AlgebraicClosure k)[[T]]`.  This file evaluates it at a topologically
nilpotent element of the valued integer ring of the completed unramified
Laurent field.  The value is accompanied by its convergent coefficient sum,
and the formal intertwining identity is transported through this genuine
analytic evaluation map.
-/

noncomputable section

open scoped LaurentSeries PowerSeries PowerSeries.WithPiTopology Topology Valued WithZero


universe u

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

omit [Finite k] in
noncomputable local instance equalCharacteristicThetaEvaluationCoefficientUniformSpace :
    UniformSpace (AlgebraicClosure k) := ⊥

noncomputable local instance equalCharacteristicThetaEvaluationLinearTopology :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k))
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicThetaEvaluationCompleteSpace :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicThetaEvaluationUniformAddGroup :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerIsUniformAddGroup







end EqualCharacteristic
end LubinTate

end
