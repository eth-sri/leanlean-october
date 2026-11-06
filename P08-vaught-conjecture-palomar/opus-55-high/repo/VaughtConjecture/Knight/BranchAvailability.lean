/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlackCutPasting

/-! # Branching availability and face-aware retuning

A complete, coded, consistent and bountiful binary scheme with two controllers at the
same graded index separates locality from availability. Its controller labels `a,b`
jointly dominate a proper label `max a b`.

Two actual respecting labellings have a non-respecting cellwise paste, even at a cut
with an extra grade of visibility and agreement on both proper cells. More strongly,
no output can preserve every accidentally agreeing coordinate and retain global capped
agreement. The protected collection in that no-go is not a face.

Face-aware retuning succeeds: change the unprotected controller choices along with the
proper value. `paste_retunes_attained_cover` is the index-independent order lemma; the
binary instance gives unrestricted bountifulness of this regression domain. It does not
assert semantic sufficiency for arbitrary controller families or solve mixed-row sections.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

namespace BranchAvailability

def indices (d : Fin 5) : Finset (Fin 2) × ℕ :=
  match d.val with
  | 0 => ({0}, 1)
  | 1 => ({1}, 1)
  | 4 => (Finset.univ, 2)
  | _ => (Finset.univ, 1)

theorem binary_plan : Plan.IsPlan (Finset.univ : Finset (Fin 2))
    {∅, {0}, {1}, Finset.univ} := by
  apply Plan.IsPlan.step (a := 0) (b := 1)
    (Q := {∅, {1}}) (R := {∅, {0}}) (by decide) (by decide) (by decide)
  · convert Plan.IsPlan.singleton (1 : Fin 2) using 1
    decide
  · convert Plan.IsPlan.singleton (0 : Fin 2) using 1
    decide
  all_goals decide

/-- Two proper singletons, two competing full grade-one controllers, and a mute top. -/
abbrev scheme : CellScheme (ι := Fin 2) Finset.univ where
  plan := {∅, {0}, {1}, Finset.univ}
  isPlan := binary_plan
  card := 5
  cell := indices
  cell_mem := by decide

/-- A positive source in block `n`, visible at grade one. -/
noncomputable def source (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + 1)

noncomputable def row (c d : Fin 5) : ExtOrd :=
  match c.val with
  | 0 | 1 => source 1
  | 2 => if d.val = 3 then source 1 else source 2
  | 3 => if d.val = 2 then source 1 else source 2
  | _ => ⊥

/-- Two controller values and their common proper maximum; the top cell stays mute. -/
noncomputable def label (a b : ExtOrd) (d : Fin 5) : ExtOrd :=
  match d.val with
  | 0 | 1 => max a b
  | 2 => a
  | 3 => b
  | _ => ⊥

noncomputable def num (n : ℕ) : ExtOrd := ofOrd (n : Ordinal)

@[local simp] private theorem num_le (m n : ℕ) : num m ≤ num n ↔ m ≤ n := by
  simp only [num, ofOrd_le_ofOrd, Nat.cast_le]

@[local simp] private theorem num_lt (m n : ℕ) : num m < num n ↔ m < n := by
  simp only [num, ofOrd_lt_ofOrd, Nat.cast_lt]

/-- Two actual respecting labellings with different availability witnesses. -/
noncomputable def first : Fin 5 → ExtOrd := label (num 5) (num 1)

end BranchAvailability

end VaughtConjecture.Knight
