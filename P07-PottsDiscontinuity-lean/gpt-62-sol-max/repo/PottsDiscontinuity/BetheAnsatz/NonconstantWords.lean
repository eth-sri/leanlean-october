module

public import PottsDiscontinuity.BetheAnsatz.WordRotation

/-!
# Every nonconstant word cancels

The finite line either contains an ordinary ML transition, or its end letters
form the boundary ML transition. The latter is moved by toroidal rotation.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A nonconstant Boolean word has an ordinary ML edge or a boundary ML edge. -/
theorem nonconstant_word_has_ML {n : ℕ} (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true) ∨
      (w (Fin.last n) = false ∧ w 0 = true) := by
  by_cases he : ∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true
  · exact Or.inl he
  right
  have hm : Antitone (fun k => if w k then (1 : ℕ) else 0) := by
    apply Fin.antitone_iff_succ_le.mpr
    intro a
    cases h0 : w a.castSucc <;> cases h1 : w a.succ
    · decide
    · exact False.elim (he ⟨a, h0, h1⟩)
    · decide
    · decide
  have hfirst : w 0 = true := by
    by_contra h
    have h0 := Bool.eq_false_of_not_eq_true h
    apply hM
    funext k
    have hk := hm (Fin.zero_le k)
    cases hw : w k <;> simp only [hw, h0, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    omega
  have hlast : w (Fin.last n) = false := by
    by_contra h
    have h0 := Bool.eq_true_of_not_eq_false h
    apply hL
    funext k
    have hk := hm (Fin.le_last k)
    cases hw : w k <;> simp only [hw, h0, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    omega
  exact ⟨hlast, hfirst⟩

/-- Companion Lemma `lem:2`, word by word, including the periodic boundary edge. -/
theorem sum_wordTerm_eq_zero_of_nonconstant {N n : ℕ} {c : ℝ} (hc : 2 < c) (r : WordWeights (n+1))
    (x : Fin (n + 2) → ℤ) (p : Fin (n + 2) → ℝ) (hr : r.Compatible (anisotropy c) p)
    (hBE : BetheEquations N (anisotropy c) p) (w : Fin (n + 2) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∑ σ, wordTerm (N := N) c r x p σ w) = 0 := by
  rcases nonconstant_word_has_ML w hL hM with ⟨a, ha, hb⟩ | ⟨ha, hb⟩
  · exact sum_wordTerm_eq_zero_of_adjacentML hc r x p hr w a ha hb
  · exact sum_wordTerm_eq_zero_of_boundaryML hc r x p hr hBE w ha hb

end PottsDiscontinuity.BetheAnsatz
