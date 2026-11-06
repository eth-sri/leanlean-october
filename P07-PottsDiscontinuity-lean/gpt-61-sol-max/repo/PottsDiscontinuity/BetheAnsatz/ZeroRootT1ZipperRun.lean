module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperSeamStep

/-!
# A finite zero-root zipper run

A zipper path is a non-repeating cyclic list of L slots, beginning at the slot
carrying the zero root. Consecutive slots follow the cyclic successor. Every
adjacent move and the final flip preserve the regularized word term.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- Consecutive vertices of a zipper path are cyclic successors. -/
def zipperPathAdjacent {n : ℕ} : List (Fin (n + 1)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b = finRotate (n + 1) a ∧ zipperPathAdjacent (b :: rest)

/-- Apply each zipper edge in order, then flip the final zero-root letter. -/
def zeroRootZipperRun {n : ℕ} : List (Fin (n + 1)) →
     Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)  →
    Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)
  | [], state => state
  | [a], (σ, w) => (σ, Function.update w a false)
  | a :: b :: rest, (σ, w) =>
      zeroRootZipperRun (b :: rest)
        (σ * Equiv.swap a b, Function.update w a false)

/-- If every L slot occurs on the path, the zipper run ends at the all-M word. -/
theorem zeroRootZipperRun_word_eq_false {n : ℕ}
    (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool)
    (hcover : ∀ k, w k = true → k ∈ path) :
    ∀ k, (zeroRootZipperRun path (σ, w)).2 k = false := by
  induction path generalizing σ w with
  | nil =>
      aesop
  | cons a tail ih =>
      cases tail with
      | nil =>
          intro k
          by_cases hka : k = a
          · subst k
            simp [zeroRootZipperRun]
          · 
            simp [zeroRootZipperRun, hka, (by
                                             grind : w k ≠ true)]
      | cons b rest =>
          
          
          have htail := ih (σ * Equiv.swap a b) (Function.update w a false) (by
                                                      grind)
          intro k
          simpa [zeroRootZipperRun] using htail k

/-- A zipper run preserves the regularized word term, under a root at the
first path slot and L letters along the path. -/
theorem zeroRootZipperRun_preserves {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p)
    (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hnodup : path.Nodup)
    (hletters : ∀ k, k ∈ path → w k = true)
    (hadj : zipperPathAdjacent path) (hnonempty : path ≠ [])
    (hroot : σ (path.headD 0) = l) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (zeroRootZipperRun path (σ, w)).1 (zeroRootZipperRun path (σ, w)).2 =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  induction path generalizing σ w with
  | nil => contradiction
  | cons a tail ih =>
      have hσa : σ a = l := by simpa using hroot
      cases tail with
      | nil =>
          
          simpa [zeroRootZipperRun] using
             zeroRootRegularizedWordTerm_flipRoot (N := N) (c := c) x p l σ w a
              hσa hpl 
      | cons b rest =>
          
          
          
          have hpathShape : b = finRotate (n + 1) a ∧
              zipperPathAdjacent (b :: rest) := by
            simpa [zipperPathAdjacent] using hadj
          rcases hpathShape with ⟨hstepIndex, htailAdj⟩
          
          
          let σ' := σ * Equiv.swap a b
          let w' := Function.update w a false
          
          
          
          
          
          have htail := ih σ' w'  (List.nodup_cons.mp hnodup).2  (by
                                               grind) htailAdj (by simp) (by
                                                                             simpa using (by
                                                                                            aesop : σ' b = l))
          calc
            zeroRootRegularizedWordTerm (N := N) c x p l
                (zeroRootZipperRun (b :: rest) (σ', w')).1
                (zeroRootZipperRun (b :: rest) (σ', w')).2 =
              zeroRootRegularizedWordTerm (N := N) c x p l σ' w' := htail
            _ = zeroRootRegularizedWordTerm (N := N) c x p l σ w :=  by
                                                                       simpa [σ', hstepIndex] using
                                                                          zeroRootRegularizedWordTerm_zipper_cyclic (N := N) hc x p hp hinj
                                                                           l hpl hBE σ w a hσa (hletters a (by simp)) (by rw [← hstepIndex]; exact  hletters b (by simp) )  

end PottsDiscontinuity.BetheAnsatz
