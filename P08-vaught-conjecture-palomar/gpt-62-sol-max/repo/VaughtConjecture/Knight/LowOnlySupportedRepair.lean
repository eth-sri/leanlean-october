/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyTerminal
public import VaughtConjecture.Knight.CanonicalPairedInverse

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref

open CanonicalPairedInverse

noncomputable section

variable {n K j : ℕ} {P C : SemScheme n}

namespace Family

variable (F : Family P C K)

theorem private_fibre (hj : 1 ≤ j) : F.terminalContext.Fibre j
    (fun d : C.scheme.below (effC n j) => .inr (.inl d.1))
    (RespectsSemanticsBelow C.rows (effC n j)) := by
  refine F.terminalContext.fibre_of_patch hj (F.zero_admissible j) (fun hs => hs.lawfulC) ?_
  intro s p γ hs hp hγ hag
  obtain ⟨t, ht, he, hc⟩ := F.private_lift hs hp (hγ.mono (min_le_left _ _)) hag
  exact ⟨t, ht, congrFun he, fun d => (State.capEq_iff_profile.mp hc d).symm⟩

theorem donor_fibre (hj : 1 ≤ j) : F.terminalContext.Fibre j
    (fun d : P.scheme.below (effC n j) => .inl d.1)
    (RespectsSemanticsBelow P.rows (effC n j)) := by
  refine F.terminalContext.fibre_of_patch hj (F.zero_admissible j) (fun hs => hs.lawfulP) ?_
  intro s p γ hs hp hγ hag
  obtain ⟨t, ht, he, hc⟩ := F.donor_lift hs hp (hγ.mono (min_le_left _ _)) hag
  exact ⟨t, ht, congrFun he, fun d => (State.capEq_iff_profile.mp hc d).symm⟩

end Family

end

end VaughtConjecture.Knight.LowOnly
