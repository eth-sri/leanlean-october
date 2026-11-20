module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Cardinality under inertia scalar restriction

This is the finite-cardinality consequence of the inertia-subgroup cardinality formula used when
the base completion is identified with a concrete local field.
-/

noncomputable section

universe u v w

namespace HilbertRamification
namespace ValuationSubring

open RamificationTheory.HilbertRamification.ValuationSubring

variable {K : Type u} {M : Type v} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]

end ValuationSubring
end HilbertRamification

end
