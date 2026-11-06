module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunBoundary

/-!
# Linear shape of a canonical T₁ word after a cyclic shift

Shift the unique ML edge to the end-to-start boundary. The resulting word has
no internal ML transition, hence its L letters form an initial interval.
-/

@[expose] public noncomputable section

open Finset

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ} {l : Fin (n + 1)}
/-- Reindex slots cyclically so that the right endpoint of the unique ML edge
is at position zero. -/
def t1RunShift (i : T1PairIndex n l) : Equiv.Perm (Fin (n + 1)) :=
  finCycle (t1EdgeRight i.edge)

/-- The shifted Boolean word, with its unique ML edge at the seam. -/
def t1ShiftedWord (i : T1PairIndex n l) (k : Fin (n + 1)) : Bool :=
  i.w (t1RunShift i k)
end

section
variable {n : ℕ} {l : Fin (n + 1)} (i : T1PairIndex n l)
theorem t1RunShift_commute (k : Fin (n + 1)) :
    t1RunShift i (finRotate (n + 1) k) =
      finRotate (n + 1) (t1RunShift i k) := by
  simp only [t1RunShift, finCycle_apply, finRotate_apply]
  ac_rfl

theorem t1RunShift_zero  : t1RunShift i 0 = t1EdgeRight i.edge := by
  simp [t1RunShift]

theorem t1RunShift_last  : t1RunShift i (Fin.last n) = t1EdgeLeft i.edge := by
  apply (finRotate (n + 1)).injective
  calc
    finRotate (n + 1) (t1RunShift i (Fin.last n)) =
        t1RunShift i (finRotate (n + 1) (Fin.last n)) :=
      (t1RunShift_commute i (Fin.last n)).symm
    _ = t1EdgeRight i.edge := by simp [t1RunShift_zero]
    _ = finRotate (n + 1) (t1EdgeLeft i.edge) :=
      (t1EdgeLeft_rotate i.edge).symm

theorem t1ShiftedWord_boundary  :
    t1ShiftedWord i 0 = true ∧ t1ShiftedWord i (Fin.last n) = false := by
  constructor
  · change i.w (t1RunShift i 0) = true
    rw [t1RunShift_zero]
    exact i.hright
  · change i.w (t1RunShift i (Fin.last n)) = false
    rw [t1RunShift_last]
    exact i.hleft

/-- The shifted word has no ordinary ML edge. -/
theorem t1ShiftedWord_no_ordinaryML (k : Fin n) :
    ¬ (t1ShiftedWord i k.castSucc = false ∧
      t1ShiftedWord i k.succ = true) := by
  rintro ⟨hfalse, htrue⟩
  have hsucc : finRotate (n + 1) k.castSucc = k.succ := by
    simp
  have hnext : i.w (finRotate (n + 1) (t1RunShift i k.castSucc)) = true := by
    rw [← t1RunShift_commute, hsucc]
    tauto
  have hleft := i.hunique (t1RunShift i k.castSucc) hfalse hnext
  have hlast := t1RunShift_last i
  have  := (t1RunShift i).injective (hleft.trans hlast.symm)
  simp_all

/-- The true/false indicator of the shifted word is antitone in the ordinary
linear order. -/
theorem t1ShiftedWord_antitone  :
    Antitone (fun k => if t1ShiftedWord i k then (1 : ℕ) else 0) := by
  apply Fin.antitone_iff_succ_le.mpr
  grind [t1ShiftedWord, decide, False.elim, t1ShiftedWord_no_ordinaryML]

/-- The unique LM edge becomes the end of the initial true interval after the
cyclic shift. -/
theorem t1ShiftedWord_true_iff_le_end (k : Fin (n + 1)) :
    t1ShiftedWord i k = true ↔ k ≤ (t1RunShift i).symm (t1PairRunEnd i) := by
  let e := (t1RunShift i).symm (t1PairRunEnd i)
  have hshift : t1RunShift i e = t1PairRunEnd i := by grind
  have he : t1ShiftedWord i e = true ∧
      t1ShiftedWord i (finRotate (n + 1) e) = false := by
    constructor
    · change i.w (t1RunShift i e) = true
      rw [hshift]
      exact (t1PairRunEnd_spec i).1
    · change i.w (t1RunShift i (finRotate (n + 1) e)) = false
      rw [t1RunShift_commute, hshift]
      exact (t1PairRunEnd_spec i).2
  have heLast : e ≠ Fin.last n := by
    intro heq
    simp_all [t1ShiftedWord_boundary]
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last heLast
  have hsuccFalse : t1ShiftedWord i j.succ = false := by
    have hrot : finRotate (n + 1) e = j.succ := by
      rw [← hj]
      simp
    simp_all
  have hmono := t1ShiftedWord_antitone i
  constructor
  · by_contra hle
    have hsuccle : j.succ ≤ k := by grind
    have hleval := hmono hsuccle
    simp_all
  · intro hle
    have hleval := hmono hle
    grind
end

end PottsDiscontinuity.BetheAnsatz
