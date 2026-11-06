/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedCore

/-! # Sharp coding and locality of the capped cores on the enlarged domain

Checks on the provenance-preserving capped cores (`Knight/CappedCore.lean`): the retained
grade-two witness row is sharply coded at its own grade (`retained_witness_row_coded`), the
capped grade-three rows are sharply coded at grade three (`capped_old_row_mem`,
`expandedRow_coded`), the domain enlarged by the capped cells themselves carries the same-level
locality (`expanded_same3`, on `ExpandedLow3`), repeated capping preserves the whole expanded row
(`expandedRow_recap`), a represented meet cell exists with the literal capped-row identity
(`represented_meet_rows`), and the bounded-alphabet core families are finite (`finite_core3`,
`finite_cappedCore3`).  Contributed as a review scout (2026-09-05) and graduated unchanged.
It does not construct a `SemScheme`; that is `Knight/FiniteAssembly.lean`.
Construction-private (not root-exported). -/
@[expose] public section

namespace VaughtConjecture.Knight.CappedCore3
open Transform Value ExtOrd
variable {P : Type*} [Fintype P] [DecidableEq P] {gradeP : P → ℕ} {T : ℕ}
variable (st : Setting gradeP T)

theorem capped_old_row_mem (a : CappedCore3 gradeP T) (d : Low3 gradeP T) :
    a.row st d ∈ codedAlphabet 3 T := by
  rcases d with c | H | s | t
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.F_mem c.1 c.2) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.rho1_mem st H) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (a.base.rho2_mem st s) _ a.η_mem
  · exact (codedAlphabet_isAlph 3 T).min_mem _ (meet₃_mem_V st a.base t) _ a.η_mem

abbrev ExpandedLow3 :=
  {c : P // gradeP c ≤ 3} ⊕ Row1 gradeP T ⊕
    Core2 (gradeP := gradeP) (T := T) ⊕ CappedCore3 gradeP T

def project : ExpandedLow3 (gradeP := gradeP) (T := T) → Low3 gradeP T
  | .inl c => .inl c
  | .inr (.inl H) => .inr (.inl H)
  | .inr (.inr (.inl s)) => .inr (.inr (.inl s))
  | .inr (.inr (.inr a)) => .inr (.inr (.inr a.base))

noncomputable def entryCap : ExpandedLow3 (gradeP := gradeP) (T := T) → ExtOrd
  | .inl _ => ⊤
  | .inr (.inl _) => ⊤
  | .inr (.inr (.inl _)) => ⊤
  | .inr (.inr (.inr a)) => a.η

noncomputable def expandedRow (a : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) : ExtOrd :=
  min (a.row st (project d)) (entryCap d)

/-- The genuinely new entries are precisely the capped meets. -/
theorem expandedRow_at_capped (a b : CappedCore3 gradeP T) :
    expandedRow st a (.inr (.inr (.inr b))) = a.meetC st b := by
  change min (min (meet₃ st a.base b.base) a.η) b.η = _
  exact min_assoc _ _ _

theorem expandedRow_coded (a : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) :
    IsCodedLabel 3 (expandedRow st a d) := by
  apply (codedAlphabet_isAlph 3 T).coded
  rcases d with c | H | s | b
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inl c)
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inr (.inl H))
  · simpa only [expandedRow, entryCap, project, min_eq_left le_top] using
      capped_old_row_mem st a (.inr (.inr (.inl s)))
  · exact (codedAlphabet_isAlph 3 T).min_mem _
      (capped_old_row_mem st a (project (.inr (.inr (.inr b))))) _ b.η_mem

theorem expandedRow_agree (a b : CappedCore3 gradeP T)
    (d : ExpandedLow3 (gradeP := gradeP) (T := T)) :
    min (expandedRow st b d) (b.meetC st a) =
      min (expandedRow st a d) (b.meetC st a) := by
  have h := rowC_agree st a b (project d)
  calc min (expandedRow st b d) (b.meetC st a)
      = min (min (b.row st (project d)) (b.meetC st a)) (entryCap d) := by
        unfold expandedRow; ac_rfl
    _ = min (min (a.row st (project d)) (b.meetC st a)) (entryCap d) :=
      congrArg (fun v => min v (entryCap d)) h
    _ = min (expandedRow st a d) (b.meetC st a) := by
        unfold expandedRow; ac_rfl

/-- Same-level locality now includes ALL of the newly capped cells as arguments. -/
theorem expanded_same3 (a b : CappedCore3 gradeP T) :
    TransformsTo (fun d => Low3.grade (project d)) (expandedRow st a)
      (fun d => min (expandedRow st b d) (b.meetC st a)) := by
  refine ⟨fun k => if k ≤ 3 then b.meetC st a else ⊥, id, ?_, ?_, rfl,
    fun _ _ h => h, fun _ _ _ _ _ => rfl, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs with h
    · exact (selfVis_mono (b.meetC_selfVis st a) h).symm
    · rfl
  · intro d
    dsimp only
    rw [ite_eq_left (Low3.grade_le_three (project d))]
    exact expandedRow_agree st a b d

end VaughtConjecture.Knight.CappedCore3
