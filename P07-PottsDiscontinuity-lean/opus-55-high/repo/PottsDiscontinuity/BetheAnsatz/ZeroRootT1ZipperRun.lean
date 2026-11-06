module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperSeamStep

/-!
# A finite zero-root zipper run

A zipper path is a non-repeating cyclic list of L slots, beginning at the slot
carrying the zero root. Consecutive slots follow the cyclic successor. Every
adjacent move and the final flip preserve the regularized word term.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ}
/-- Consecutive vertices of a zipper path are cyclic successors. -/
def zipperPathAdjacent  : List (Fin (n + 1)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b = finRotate (n + 1) a ∧ zipperPathAdjacent (b :: rest)

/-- Apply each zipper edge in order, then flip the final zero-root letter. -/
def zeroRootZipperRun  : List (Fin (n + 1)) →
    (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)) →
    Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)
  | [], state => state
  | [a], (σ, w) => (σ, Function.update w a false)
  | a :: b :: rest, (σ, w) =>
      zeroRootZipperRun (b :: rest)
        (σ * Equiv.swap a b, Function.update w a false)

/-- If every L slot occurs on the path, the zipper run ends at the all-M word. -/
theorem zeroRootZipperRun_word_eq_false (path : List (Fin (n + 1))) (σ : Equiv.Perm (Fin (n + 1)))
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
          · simp_all [zeroRootZipperRun]
          · have hnot : w k ≠ true := by
              intro hw
              have hk : k ∈ [a] := by tauto
              simp_all
            simp_all [zeroRootZipperRun]
      | cons b rest =>
          let w' := Function.update w a false
          have hcover' : ∀ k, w' k = true → k ∈ b :: rest := by
            intro k hk
            have hka : k ≠ a := by
              grind
            have hkw : w k = true := by aesop
            have hkin : k ∈ a :: b :: rest := by tauto
            simp_all
          tauto
end

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
      have hσa : σ a = l := by tauto
      cases tail with
      | nil =>
          simpa [zeroRootZipperRun] using
            (zeroRootRegularizedWordTerm_flipRoot x p l σ w a
              hσa hpl)
      | cons b rest =>
          have hnd := List.nodup_cons.mp hnodup
          have htailNodup := hnd.2
          have hpathShape : b = finRotate (n + 1) a ∧
              zipperPathAdjacent (b :: rest) := by
            tauto
          rcases hpathShape with ⟨hstepIndex, htailAdj⟩
          let σ' := σ * Equiv.swap a b
          let w' := Function.update w a false
          have htermStep : zeroRootRegularizedWordTerm (N := N) c x p l σ' w' =
              zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
            simpa [σ', w', hstepIndex] using
              (zeroRootRegularizedWordTerm_zipper_cyclic hc x p hp hinj
                l hpl hBE σ w a hσa (by tauto) (by grind))
          have hσ'b : σ' b = l := by
            simp [σ', Equiv.Perm.mul_apply, Equiv.swap_apply_right, hσa]
          have htailLetters : ∀ k, k ∈ b :: rest → w' k = true := by
            intro k hk
            have hka : k ≠ a := by
              grind
            simpa [w', Function.update_of_ne hka] using hletters k (by tauto)
          have htailNe : (b :: rest) ≠ [] := by simp
          have htailRoot : σ' ((b :: rest).headD 0) = l := by
            tauto
          calc
            zeroRootRegularizedWordTerm c x p l
                (zeroRootZipperRun (b :: rest) (σ', w')).1
                (zeroRootZipperRun (b :: rest) (σ', w')).2 =
              zeroRootRegularizedWordTerm c x p l σ' w' := (ih σ' w' htailNodup htailLetters htailAdj htailNe htailRoot)
            _ = zeroRootRegularizedWordTerm c x p l σ w := htermStep

end PottsDiscontinuity.BetheAnsatz
