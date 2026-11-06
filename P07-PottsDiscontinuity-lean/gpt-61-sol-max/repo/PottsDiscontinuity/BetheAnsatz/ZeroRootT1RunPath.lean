module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunShape
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperRun

/-!
# A concrete zipper path for a canonical T₁ word

In the cyclicly shifted coordinates, the L slots are the initial interval
through the unique LM edge. Enumerating that interval gives a zipper path in
the original cyclic coordinates.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- The unique LM endpoint expressed in the shifted coordinates. -/
noncomputable def t1ShiftedRunEnd {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l)  :=
  (t1RunShift i).symm (t1PairRunEnd i)

/-- View an initial interval index as a slot of the full cyclic word. -/
def t1RunPathIndex {n : ℕ} (e : Fin (n + 1))
    (q : Fin (e.val + 1)) : Fin (n + 1) :=
  ⟨q.val, by omega⟩

/-- The L-run beginning at the zero-root slot, in cyclic order. -/
noncomputable def t1PairZipperPath {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l)  :=
  List.ofFn  fun q : Fin ((t1ShiftedRunEnd i).val + 1) =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q) 

private theorem zipperPathAdjacent_ofFn {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1))
    (hstep : ∀ j : Fin m, f j.succ = finRotate (n + 1) (f j.castSucc)) :
    zipperPathAdjacent (List.ofFn f) := by
  induction m with
  | zero => simp [zipperPathAdjacent]
  | succ m ih =>
      simp only [List.ofFn_succ]
      constructor
      · simpa using hstep 0
      · 
        simpa only [List.ofFn_succ] using (by
                                             grind : zipperPathAdjacent
            (List.ofFn  fun j  => f j.succ ))

section

variable {n : ℕ} {l : Fin (n + 1)} (i : T1PairIndex n l)
include i

theorem t1PairZipperPath_nodup  : (t1PairZipperPath i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b hab
  
  apply Fin.ext
  simpa [t1RunPathIndex] using congrArg Fin.val ((t1RunShift i).injective hab)

theorem t1PairZipperPath_adjacent  : zipperPathAdjacent (t1PairZipperPath i) := by
  let e := t1ShiftedRunEnd i
  
  
  apply zipperPathAdjacent_ofFn (fun j =>
                                   t1RunShift i (t1RunPathIndex e j))
  intro q
  
  
  change t1RunShift i (t1RunPathIndex e q.succ) =
    finRotate (n + 1) (t1RunShift i (t1RunPathIndex e q.castSucc))
  rw [(by
         have hlt : (t1RunPathIndex e q.castSucc).val < n := by
           grind +locals
         have hstep := finRotate_of_lt hlt
         aesop : t1RunPathIndex e q.succ =
      finRotate (n + 1) (t1RunPathIndex e q.castSucc))]
  exact t1RunShift_commute i _

theorem t1PairZipperPath_letters  (k : Fin (n + 1))
    (hk : k ∈ t1PairZipperPath i) : i.w k = true := by
  change k ∈ List.ofFn  fun q  =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q)  at hk
  rw [List.mem_ofFn'] at hk
  obtain ⟨q, rfl⟩ := hk
  
  
  simpa [t1ShiftedWord] using  (t1ShiftedWord_true_iff_le_end i
                                                  (t1RunPathIndex (t1ShiftedRunEnd i) q)).2 (by
                                                                                               grind +locals) 

theorem t1PairZipperPath_covers  :
    ∀ k, i.w k = true → k ∈ t1PairZipperPath i := by
  intro k hk
  let q := (t1RunShift i).symm k
  
  have hle : q ≤ t1ShiftedRunEnd i :=
    (t1ShiftedWord_true_iff_le_end i q).1 (by
                                             change i.w (t1RunShift i q) = true
                                             aesop)
  let q' : Fin ((t1ShiftedRunEnd i).val + 1) :=
    ⟨q.val, by  omega⟩
  have hindex : t1RunPathIndex (t1ShiftedRunEnd i) q' = q := rfl
  
  exact (List.mem_ofFn' (fun q  =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q)) k).2
      (Set.mem_range.mpr ⟨q',  by
                                 grind ⟩)

theorem t1PairZipperPath_nonempty  : t1PairZipperPath i ≠ [] := by
  simp_all [t1PairZipperPath]

theorem t1PairZipperPath_head  :
    (t1PairZipperPath i).headD 0 = t1EdgeRight i.edge := by
  change (List.ofFn  fun q  =>
    t1RunShift i (t1RunPathIndex (t1ShiftedRunEnd i) q) ).headD 0 = _
  
  simp [t1RunPathIndex, t1RunShift_zero]

end

theorem zeroRootZipperRun_root_at_last {n : ℕ}
    (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) {l : Fin (n + 1)}
    (hne : path ≠ []) (hroot : σ (path.headD 0) = l) :
    (zeroRootZipperRun path (σ, w)).1 (path.getLast hne) = l := by
  induction path generalizing σ w with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil =>
          assumption
      | cons b rest =>
          simp_all [zeroRootZipperRun]

/-- The last path slot is the unique LM endpoint in the original cyclic
coordinates. -/
noncomputable def t1PairZipperPathLast {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l)  :=
  (t1PairZipperPath i).getLast (t1PairZipperPath_nonempty i)

section

variable {n : ℕ} {l : Fin (n + 1)} (i : T1PairIndex n l)


theorem t1PairZipperPathLast_eq_runEnd  : t1PairZipperPathLast i = t1PairRunEnd i := by
  let e := t1ShiftedRunEnd i
  
  have hindex : t1RunPathIndex e (Fin.last e.val) = e := by
    
    rfl
  unfold t1PairZipperPathLast t1PairZipperPath
  rw [ List.getLast_ofFn_succ
          fun q  => t1RunShift i (t1RunPathIndex e q)  , hindex]
  exact (t1RunShift i).apply_symm_apply (t1PairRunEnd i)

/-- Zipping the canonical run sends the zero root to its unique LM endpoint. -/
theorem t1PairZipperRun_root  :
    (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (t1PairRunEnd i) = l := by
  have hroot : i.σ ((t1PairZipperPath i).headD 0) = l := by
    rw [t1PairZipperPath_head]
    exact i.hσ
  
  rw [← t1PairZipperPathLast_eq_runEnd i]
  exact  zeroRootZipperRun_root_at_last (t1PairZipperPath i) i.σ i.w
           (t1PairZipperPath_nonempty i) hroot 

end

/-- The zipper run preserves the regularized zero-root term. -/
theorem t1PairZipperRun_preserves {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (i : T1PairIndex n l) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
      (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 =
    zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w := zeroRootZipperRun_preserves hc x p hp hinj l hpl hBE (t1PairZipperPath i) i.σ i.w (t1PairZipperPath_nodup i)
                                                              (t1PairZipperPath_letters i) (t1PairZipperPath_adjacent i) (t1PairZipperPath_nonempty i)
                                                              (Eq.mpr (congrArg (fun _a => i.σ _a = l) (t1PairZipperPath_head i)) i.hσ)

/-- Every letter is M after the full T₁ zipper run. -/
theorem t1PairZipperRun_word_eq_false {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    ∀ k, (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 k = false := by
                                                                              solve_by_elim [_root_.PottsDiscontinuity.BetheAnsatz.zeroRootZipperRun_word_eq_false, _root_.PottsDiscontinuity.BetheAnsatz.t1PairZipperPath_covers]

end PottsDiscontinuity.BetheAnsatz
