/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- The actual cut lies strictly below the actual cap (the endpoint margin). -/
theorem cut_actual_lt_cap : R.cut R.vactL < R.vact R.cap := by
  rw [R.cut_actual]
  exact (Finset.sup_lt_iff R.cap_pos).mpr fun i _ => R.margin i

end Ref

end CappedDonor

end VaughtConjecture.Knight
