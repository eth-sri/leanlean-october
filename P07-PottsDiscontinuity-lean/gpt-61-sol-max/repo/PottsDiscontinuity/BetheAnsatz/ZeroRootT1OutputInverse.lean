module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputIndex

/-!
# Reconstructing a canonical T₁ pair from its output index

For an output permutation and a choice of ML-left slot, the original word is
the cyclic interval from the right endpoint through the output zero slot.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- The cyclic shift whose coordinate zero is the right endpoint of an edge. -/
def t1OutputShift {n : ℕ} (edge : Option (Fin n))  :=
  finCycle (t1EdgeRight edge)

section

variable {n : ℕ} (edge : Option (Fin n))


theorem t1OutputShift_commute 
    (k : Fin (n + 1)) :
    t1OutputShift edge (finRotate (n + 1) k) =
      finRotate (n + 1) (t1OutputShift edge k) := by
  simp only [t1OutputShift, finCycle_apply, finRotate_apply]
  ac_rfl

theorem t1OutputShift_zero  :
    t1OutputShift edge 0 = t1EdgeRight edge := by
  simp [t1OutputShift]

theorem t1OutputShift_last  :
    t1OutputShift edge (Fin.last n) = t1EdgeLeft edge := Equiv.injective (finRotate (n + 1))
                                                           (Trans.trans
                                                             (Trans.trans (Eq.symm (t1OutputShift_commute edge (Fin.last n)))
                                                               (Eq.mpr (congrArg (fun _a => (t1OutputShift edge) _a = t1EdgeRight edge) finRotate_last)
                                                                 (Eq.mpr (congrArg (fun _a => _a = t1EdgeRight edge) (t1OutputShift_zero edge)) (Eq.refl (t1EdgeRight edge)))))
                                                             (Eq.symm (t1EdgeLeft_rotate edge)))

end

/-- The shifted coordinate of a slot. -/
def t1OutputCoordinate {n : ℕ} (edge : Option (Fin n)) (k : Fin (n + 1))  := (t1OutputShift edge).symm k

theorem t1OutputCoordinate_rotate {n : ℕ} (edge : Option (Fin n))
    (k : Fin (n + 1)) :
    t1OutputCoordinate edge (finRotate (n + 1) k) =
      finRotate (n + 1) (t1OutputCoordinate edge k) := by
  
  simpa [t1OutputCoordinate] using (congrArg (t1OutputShift edge).symm
                                      (t1OutputShift_commute edge (t1OutputCoordinate edge k))).symm

/-- The word of the pair represented by an output index. -/
def t1OutputWord {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l)
    (k : Fin (n + 1))  :=
  decide (t1OutputCoordinate o.edge k ≤ t1OutputCoordinate o.edge (o.σ.symm l))

/-- Enumerate the cyclic interval of true letters from the edge's right slot to
the output zero slot. -/
def t1OutputPath {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l)  :=
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  List.ofFn  fun q : Fin (e.val + 1) =>
    t1OutputShift o.edge (t1RunPathIndex e q) 

section

variable {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l)


theorem t1OutputEndCoordinate_ne_last  :
    t1OutputCoordinate o.edge (o.σ.symm l) ≠ Fin.last n := by
  intro he
  have hshift := (t1OutputShift o.edge).apply_symm_apply (o.σ.symm l)
  change (t1OutputShift o.edge).symm (o.σ.symm l) = Fin.last n at he
  rw [he, t1OutputShift_last] at hshift
  exact o.hleft hshift

theorem t1OutputWord_right  : t1OutputWord o (t1EdgeRight o.edge) = true := by
  simp only [t1OutputWord, t1OutputCoordinate]
  rw [← t1OutputShift_zero o.edge]
  simp

theorem t1OutputWord_left  : t1OutputWord o (t1EdgeLeft o.edge) = false := by
  grind [t1OutputCoordinate, t1OutputWord, t1OutputEndCoordinate_ne_last, t1OutputShift_last]

theorem t1OutputWord_end  : t1OutputWord o (o.σ.symm l) = true := by
  simp [t1OutputWord]

theorem t1OutputWord_end_rotate  :
    t1OutputWord o (finRotate (n + 1) (o.σ.symm l)) = false := by
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have he : e ≠ Fin.last n := t1OutputEndCoordinate_ne_last o
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last he
  have hrot : finRotate (n + 1) e = j.succ := by
    rw [← hj]
    exact finRotate_of_lt j.isLt
  have hcoord :
      t1OutputCoordinate o.edge (finRotate (n + 1) (o.σ.symm l)) = j.succ := by
    grind [t1OutputCoordinate_rotate]
  have hnot : ¬ j.succ ≤ e := by
    grind
  change decide (t1OutputCoordinate o.edge (finRotate (n + 1) (o.σ.symm l)) ≤ e) = false
  rw [hcoord]
  simp [hnot]

theorem t1OutputWord_uniqueML  (k : Fin (n + 1))
    (hfalse : t1OutputWord o k = false)
    (htrue : t1OutputWord o (finRotate (n + 1) k) = true) :
    k = t1EdgeLeft o.edge := by
  let q := t1OutputCoordinate o.edge k
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  have hqnot : ¬ q ≤ e := by
    grind +locals
  have hnext : t1OutputCoordinate o.edge (finRotate (n + 1) k) ≤ e := by
    grind +locals
  have hcoord : t1OutputCoordinate o.edge (finRotate (n + 1) k) =
      finRotate (n + 1) q := t1OutputCoordinate_rotate o.edge k
  by_cases hlast : q = Fin.last n
  · calc
      k = t1OutputShift o.edge q :=
        (t1OutputShift o.edge).apply_symm_apply k |>.symm
      _ = t1OutputShift o.edge (Fin.last n) := congrArg _ hlast
      _ = t1EdgeLeft o.edge := t1OutputShift_last o.edge
  · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hrot : finRotate (n + 1) q = j.succ := by
      rw [← hj]
      exact finRotate_of_lt j.isLt
    grind

theorem t1OutputPath_nonempty  : t1OutputPath o ≠ [] := by
  simp_all [t1OutputPath]

theorem t1OutputPath_head  :
    (t1OutputPath o).headD 0 = t1EdgeRight o.edge := by
  simp_all [t1OutputPath, t1RunPathIndex, t1OutputShift_zero]

theorem t1OutputPath_last  :
    (t1OutputPath o).getLast (t1OutputPath_nonempty o) = o.σ.symm l := by
  let e := t1OutputCoordinate o.edge (o.σ.symm l)
  
  have hindex : t1RunPathIndex e (Fin.last e.val) = e := by
    
    rfl
  unfold t1OutputPath
  rw [ List.getLast_ofFn_succ
          fun q  => t1OutputShift o.edge (t1RunPathIndex e q)  , hindex]
  exact (t1OutputShift o.edge).apply_symm_apply (o.σ.symm l)

end

/-- The input permutation recovered by undoing all swaps of the output path. -/
noncomputable def t1OutputInputPerm {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l)  :=
  o.σ * (zeroRootZipperPerm (t1OutputPath o))⁻¹

/-- Reconstruct the canonical input word, permutation, and unique ML edge. -/
noncomputable def t1OutputInput {n : ℕ} {l : Fin (n + 1)}
    (o : T1OutputIndex n l) : T1PairIndex n l where
  σ := t1OutputInputPerm o
  w := t1OutputWord o
  edge := o.edge
  hσ := by
    let path := t1OutputPath o
    let ρ := zeroRootZipperPerm path
    have hρend : ρ (o.σ.symm l) = t1EdgeRight o.edge := by
      have h := zeroRootZipperPerm_getLast_eq_headD path (t1OutputPath_nonempty o)
      rw [t1OutputPath_last] at h
      rw [t1OutputPath_head] at h
      exact h
    have hρsymm : ρ.symm (t1EdgeRight o.edge) = o.σ.symm l := by
      grind
    change (o.σ * ρ⁻¹) (t1EdgeRight o.edge) = l
    calc
      _ = o.σ (ρ.symm (t1EdgeRight o.edge)) := by simp 
      _ = o.σ (o.σ.symm l) := by rw [hρsymm]
      _ = l := o.σ.apply_symm_apply l
  hleft := t1OutputWord_left o
  hright := t1OutputWord_right o
  hunique := t1OutputWord_uniqueML o

section

variable {n : ℕ} {l : Fin (n + 1)} (o : T1OutputIndex n l)


theorem t1OutputInput_runEnd  : t1PairRunEnd (t1OutputInput o) = o.σ.symm l := let i := t1OutputInput o;
                                                                               Eq.symm
                                                                                 ((Classical.choose_spec (t1PairIndex_existsUnique_LM i)).right ((Equiv.symm o.σ) l)
                                                                                   ⟨t1OutputWord_end o, t1OutputWord_end_rotate o⟩)

theorem t1OutputPath_eq_inputPath  :
    t1OutputPath o = t1PairZipperPath (t1OutputInput o) := by
  unfold t1OutputPath t1PairZipperPath t1ShiftedRunEnd t1RunShift
    t1OutputCoordinate t1OutputShift
  rw [t1OutputInput_runEnd]
  rfl

theorem t1OutputInput_outputPerm  :
    (zeroRootZipperRun (t1PairZipperPath (t1OutputInput o))
      ((t1OutputInput o).σ, (t1OutputInput o).w)).1 = o.σ := by
  rw [zeroRootZipperRun_perm]
  rw [← t1OutputPath_eq_inputPath]
  simp only [t1OutputInput, t1OutputInputPerm]
  group

end

end PottsDiscontinuity.BetheAnsatz
