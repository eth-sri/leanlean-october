/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRelease

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n : ℕ} {P : SemScheme n} {j : ℕ}

theorem completeAt_future (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : Cell P.scheme)
    (hd : j < P.scheme.grade d) : CellScheme.complete a u d = a d :=
  CellScheme.complete_future a u d ((min_le_left _ _).trans_lt hd)

section Barrier

variable {F : Type*} [Fintype F]

open Classical in
/-- The maximum includes every designated non-top field, irrespective of birth grade. -/
def nonTopMax (T : F → Prop) (a : F → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun d => ¬ T d).sup a

theorem le_nonTopMax {T : F → Prop} (a : F → ExtOrd) {d : F} (hd : ¬ T d) :
    a d ≤ nonTopMax T a := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

/-- Activation after clipping the cutoff pins all old non-top fields literally.
There is no exception for future fields or fields above the LOW threshold. -/
theorem clipped_activation {T : F → Prop} {a a' : F → ExtOrd} {b γ : ExtOrd}
    (hcap : ∀ d, min (a' d) γ = min (a d) γ)
    (hactive : nonTopMax T a' < min b γ) :
    (∀ d, ¬ T d → a' d = a d) ∧ nonTopMax T a' = nonTopMax T a ∧
      nonTopMax T a < b := by
  classical
  have hfix : ∀ d, ¬ T d → a' d = a d := by
    intro d hd
    exact (eq_of_capAgree_of_lt (hcap d)
      (((le_nonTopMax a' hd).trans_lt hactive).trans_le (min_le_right _ _))).symm
  have hM : nonTopMax T a' = nonTopMax T a := by
    apply Finset.sup_congr rfl
    grind
  grind

theorem clipped_cutoff_cap (b γ : ExtOrd) : min (min b γ) γ = min b γ := by simp

end Barrier

end

end VaughtConjecture.Knight.LowOnly
