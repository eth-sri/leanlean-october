/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- Decode uniformly at short owners; consume a separately proved decoded
locality only at exceptional owners. No full decoded lawfulness, global bottom
reflection, or shortness of the inherited long rows is assumed. -/
theorem map_respects_of_short_or_local
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : Witness (gTop K) ν)
    (hc : ∀ c : D.below BJ,
      (∀ d : D.below (D.cell c.1), Short (D.grade c.1) (sem.E c.1 d)) ∨
      TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1)
        (sem.E c.1)
        (fun d => min (ν (r (CellScheme.below.incl c d))) (ν (r c)))) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) := by
  apply hr.map_of_locality hK hν
  intro c
  rcases hc c with hs | hl
  · exact map_capped_locality
      (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
      (p := fun d => r (CellScheme.below.incl c d))
      (fun d => d.2.2) (hK c) hs (hr.orderly c).symm (hr.locality c) hν
  · exact hl

end VaughtConjecture.Knight.SharpWitnessComposition
