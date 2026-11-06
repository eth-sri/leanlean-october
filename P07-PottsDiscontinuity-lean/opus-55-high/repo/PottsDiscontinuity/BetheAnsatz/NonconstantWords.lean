module

public import PottsDiscontinuity.BetheAnsatz.WordRotation

/-!
# Every nonconstant word cancels

The finite line either contains an ordinary ML transition, or its end letters
form the boundary ML transition. The latter is moved by toroidal rotation.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A nonconstant Boolean word has an ordinary ML edge or a boundary ML edge. -/
theorem nonconstant_word_has_ML {n : ℕ} (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true) ∨
      (w (Fin.last n) = false ∧ w 0 = true) := by
  by_cases he : ∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true
  · simp_all
  have hm : Antitone (fun k => if w k then (1 : ℕ) else 0) := by
    apply Fin.antitone_iff_succ_le.mpr
    grind
  have hfirst : w 0 = true := by
    by_contra h
    apply hM
    funext k
    have hk := hm (Fin.zero_le k)
    simp_all
  have hlast : w (Fin.last n) = false := by
    by_contra h
    apply hL
    funext k
    have hk := hm (Fin.le_last k)
    grind
  simp_all

section
variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (n + 2) → ℤ) (p : Fin (n + 2) → ℝ) (hp : ∀ j, z (p j) ≠ 1) (hBE : BetheEquations N (anisotropy c) p)
include c hc x p hp hBE
/-- Companion Lemma `lem:2`, word by word, including the periodic boundary edge. -/
theorem sum_wordTerm_eq_zero_of_nonconstant (w : Fin (n + 2) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∑ σ, wordTerm (N := N) c x p σ w) = 0 := by
  rcases nonconstant_word_has_ML w hL hM with ⟨a, ha, hb⟩ | ⟨ha, hb⟩
  · exact sum_wordTerm_eq_zero_of_adjacentML hc x p hp w a ha hb
  · exact sum_wordTerm_eq_zero_of_boundaryML hc x p hp hBE w ha hb

/-- Only the two constant words survive in the total word expansion. -/
theorem sum_wordTerms_eq_constant_words  :
    (∑ w : Fin (n + 2) → Bool, ∑ σ, wordTerm (N := N) c x p σ w) =
      (∑ σ, wordTerm (N := N) c x p σ (fun _ => true)) +
        ∑ σ, wordTerm (N := N) c x p σ (fun _ => false) := by
  have hne : (fun _ : Fin (n + 2) => true) ≠ (fun _ => false) := by
    grind
  rw [← Finset.sum_subset (show ({(fun _ => true), (fun _ => false)} :
    Finset (Fin (n + 2) → Bool)) ⊆ univ by simp)]
  · simp_all
  simp_all [sum_wordTerm_eq_zero_of_nonconstant]
end

end PottsDiscontinuity.BetheAnsatz
