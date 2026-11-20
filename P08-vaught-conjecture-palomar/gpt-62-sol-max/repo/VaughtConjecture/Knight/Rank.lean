/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import Mathlib.SetTheory.Ordinal.Basic
public import VaughtConjecture.Approximation.Prolongation
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.ReductModel

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value

universe w

namespace KnightRealization

/-- The model class is closed under reduction (`IsModel.reduct`, #101/#112): the reduct-closure
hypothesis of the generic layer, discharged once for Knight. -/
theorem isModelClass_reduct {δ δ' : LimitStage} (h : δ ≤ δ') {N : Type w}
    (R' : KnightRealization δ' N) (hR' : IsModelClass R') : IsModelClass (R'.reduct h) :=
  hR'.reduct h

end KnightRealization

end VaughtConjecture.Knight
