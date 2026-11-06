module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunBoundary

/-!
# Linear shape of a canonical T₁ word after a cyclic shift

Shift the unique ML edge to the end-to-start boundary. The resulting word has
no internal ML transition, hence its L letters form an initial interval.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- Reindex slots cyclically so that the right endpoint of the unique ML edge
is at position zero. -/
noncomputable def t1RunShift {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l)  :=
  finCycle (t1EdgeRight i.edge)

/-- The shifted Boolean word, with its unique ML edge at the seam. -/
noncomputable def t1ShiftedWord {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) (k : Fin (n + 1))  :=
  i.w (t1RunShift i k)

section

variable {n : ℕ}
include n

theorem t1EdgeLeft_rotate  (e : Option (Fin n)) :
    finRotate (n + 1) (t1EdgeLeft e) = t1EdgeRight e := by
  cases e with
  | none => exact finRotate_last
  | some a => exact finRotate_of_lt a.isLt

section

variable {l : Fin (n + 1)} (i : T1PairIndex n l)
include i

theorem t1RunShift_commute   (k : Fin (n + 1)) :
    t1RunShift i (finRotate (n + 1) k) =
      finRotate (n + 1) (t1RunShift i k) := by
  simp only [t1RunShift, finCycle_apply, finRotate_apply]
  ac_rfl

theorem t1RunShift_zero   : t1RunShift i 0 = t1EdgeRight i.edge := by
  simp [t1RunShift]

theorem t1RunShift_last   : t1RunShift i (Fin.last n) = t1EdgeLeft i.edge := Equiv.injective (finRotate (n + 1))
                                                                               (Trans.trans
                                                                                 (Trans.trans (Eq.symm (t1RunShift_commute i (Fin.last n)))
                                                                                   (Eq.mpr (congrArg (fun _a => (t1RunShift i) _a = t1EdgeRight i.edge) finRotate_last)
                                                                                     (Eq.mpr (congrArg (fun _a => _a = t1EdgeRight i.edge) (t1RunShift_zero i)) (Eq.refl (t1EdgeRight i.edge)))))
                                                                                 (Eq.symm (t1EdgeLeft_rotate i.edge)))

theorem t1ShiftedWord_boundary   :
    t1ShiftedWord i 0 = true ∧ t1ShiftedWord i (Fin.last n) = false := by
  constructor
  · change i.w (t1RunShift i 0) = true
    rw [t1RunShift_zero]
    exact i.hright
  · change i.w (t1RunShift i (Fin.last n)) = false
    rw [t1RunShift_last]
    exact i.hleft

/-- The shifted word has no ordinary ML edge. -/
theorem t1ShiftedWord_no_ordinaryML   (k : Fin n) :
    ¬ (t1ShiftedWord i k.castSucc = false ∧
      t1ShiftedWord i k.succ = true) := by
  rintro ⟨hfalse, htrue⟩
  
  have hsucc : finRotate (n + 1) k.castSucc = k.succ := by
    simp
  
  
  
  have heq  :=
    (i.hunique (t1RunShift i k.castSucc) hfalse (by
                                                                 rw [← t1RunShift_commute, hsucc]
                                                                 exact htrue)).trans (t1RunShift_last i).symm
  
  exact Fin.castSucc_ne_last k ((t1RunShift i).injective heq)

/-- The true/false indicator of the shifted word is antitone in the ordinary
linear order. -/
theorem t1ShiftedWord_antitone   :
    Antitone  fun k => if t1ShiftedWord i k then (1 : ℕ) else 0  := by
  apply Fin.antitone_iff_succ_le.mpr
  intro k
  cases h0 : t1ShiftedWord i k.castSucc <;>
    cases h1 : t1ShiftedWord i k.succ
  · decide
  · grind [t1ShiftedWord_no_ordinaryML]
  · decide
  · decide

/-- The unique LM edge becomes the end of the initial true interval after the
cyclic shift. -/
theorem t1ShiftedWord_true_iff_le_end   (k : Fin (n + 1)) :
    t1ShiftedWord i k = true ↔ k ≤ (t1RunShift i).symm (t1PairRunEnd i) := by
  let e := (t1RunShift i).symm (t1PairRunEnd i)
  have hshift : t1RunShift i e = t1PairRunEnd i := by simp [e]
  have he : t1ShiftedWord i e = true ∧
      t1ShiftedWord i (finRotate (n + 1) e) = false := by
    constructor
    · change i.w (t1RunShift i e) = true
      rw [hshift]
      exact (t1PairRunEnd_spec i).1
    · change i.w (t1RunShift i (finRotate (n + 1) e)) = false
      rw [t1RunShift_commute]
      rw [hshift]
      exact (t1PairRunEnd_spec i).2
  have heLast : e ≠ Fin.last n := by
    intro heq
    have hboundary := (t1ShiftedWord_boundary i).2
    simp_all
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last heLast
  have hsuccFalse : t1ShiftedWord i j.succ = false := by
    have hrot : finRotate (n + 1) e = j.succ := by
      rw [← hj]
      exact finRotate_of_lt j.isLt
    simp_all
  have hmono := t1ShiftedWord_antitone i
  constructor
  · intro hk
    by_contra hle
    
    
    
    have hleval := hmono ((Fin.castSucc_lt_iff_succ_le).mp (by rw [hj]; exact (lt_of_not_ge hle)))
    simp_all
  · intro hle
    have hleval := hmono hle
    aesop

end

end

end PottsDiscontinuity.BetheAnsatz
