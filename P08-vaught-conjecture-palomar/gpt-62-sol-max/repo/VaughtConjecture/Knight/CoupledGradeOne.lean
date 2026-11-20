/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledBountifulReduction

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

open CellScheme.restrictFace (toCell belowMap pushGraded)

theorem selfVis_max {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by grind

end VaughtConjecture.Knight
