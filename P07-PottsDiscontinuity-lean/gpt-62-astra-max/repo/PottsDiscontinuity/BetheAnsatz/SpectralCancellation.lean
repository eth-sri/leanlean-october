module
public import PottsDiscontinuity.BetheAnsatz.SpectralWords
public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.GapReindex

/-! # Pairwise cancellation at a movable spectral parameter

The gauge in the word expansion depends on the positions and the word, not
on the permutation. It can be taken outside the sum in which the two-body
scattering factors cancel.
-/
@[expose] public section
open Finset Complex Classical
namespace PottsDiscontinuity.BetheAnsatz
noncomputable section
variable {n : ℕ}

private lemma coefficient_swap {e : Equiv.Perm (Fin (n+1))} {a : Fin (n+1)}
    {l m : Fin (n+1) → ℂ} (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool)
    (ha : w a = false) (hb : w (e a) = true) {r : ℂ}
    (hr : m (σ a) * l (σ (e a)) - 1 = r * (m (σ (e a)) * l (σ a) - 1)) :
    (∏ k, wordEdgeFactor e (l ∘ σ) (m ∘ σ) w k) = r *
      ∏ k, wordEdgeFactor e (l ∘ ↑(σ * Equiv.swap a (e a))) (m ∘ ↑(σ * Equiv.swap a (e a))) w k := by
  let F := fun π => wordEdgeFactor e (l ∘ π) (m ∘ π) w
  let s := Equiv.swap a (e a)
  rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase univ _ (mem_univ a), ← mul_assoc]
  congr 1
  · simpa [F,s,wordEdgeFactor,ha,hb,Equiv.Perm.mul_apply] using hr
  apply prod_congr rfl; intro k hk
  have h2 := fun h => (mem_erase.mp hk).1 (e.injective h)
  simp only [F,s,wordEdgeFactor,Function.comp_apply,Equiv.Perm.mul_apply]; grind

/-- Swapping momenta is equivalent to swapping their two coordinates. -/
theorem planeWave_swap {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) (a b : Fin n) :
    planeWave p (σ * Equiv.swap a b) x = planeWave p σ (fun k => x (Equiv.swap a b k)) := by
  unfold planeWave
  simpa using Equiv.prod_comp (Equiv.swap a b) (fun k => Complex.exp (I * (p (σ k)) * (x (Equiv.swap a b k))))

section
variable {N n : ℕ} {Δ : ℝ} (hc : Δ < -1) {v : ℂ} (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hBE : BetheEquations N Δ p) (σ : Equiv.Perm (Fin (n + 1))) (hp : ∀ j, z (p j) ≠ v)
    (w : Fin (n + 1) → Bool) (a : Fin n) (ha : w a.castSucc = false) (hb : w a.succ = true)

include ha hb in
/-- At an ordinary ML edge both selected coordinates are the same integer. -/
theorem wordPhase_adjacent_swap :
    planeWave p (σ * Equiv.swap a.castSucc a.succ) (wordPositions N x w) =
      planeWave p σ (wordPositions N x w) := by
  change planeWave p (σ * Equiv.swap a.castSucc a.succ)
    (fun k => if w k then cyclicPredecessorPositions N x k else x k) =
    planeWave p σ (fun k => if w k then cyclicPredecessorPositions N x k else x k)
  rw [planeWave_swap]
  congr 1
  aesop


def wordTerm {N : ℕ} (Δ : ℝ) (v : ℂ) (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) :=
  amplitude Δ p σ * wordCoefficient (fun j => rowL Δ v (z (p j))) (fun j => rowM Δ v (z (p j))) σ w *
    planeWave p σ (wordPositions N x w)

private lemma wordTerm_adjacent_swap {N : ℕ} {Δ : ℝ} (hc : Δ < -1) {v : ℂ}
    (x : Fin (n+1) → ℤ) (p : Fin (n+1) → ℝ) (hp : ∀ j, z (p j) ≠ v)
    (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    wordTerm (N := N) Δ v x p (σ * Equiv.swap a.castSucc a.succ) w = - wordTerm (N := N) Δ v x p σ w := by
  have hrot : finRotate _ a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hs := coefficient_swap (l := (fun j => rowL Δ v (z (p j)))) (m := (fun j => rowM Δ v (z (p j)))) σ w ha
    (hrot.symm ▸ hb) (row_scattering hc (hp _) (hp _))
  rw [hrot] at hs
  unfold wordTerm wordCoefficient
  rw [wordPhase_adjacent_swap x p σ w a ha hb, amplitude_adjacent_swap hc p σ (by simp), hs]; ring

include hc hp ha hb in
/-- Every word with an ordinary ML edge contributes zero after the permutation sum. -/
theorem sum_wordTerm_eq_zero_of_adjacentML :
    (∑ σ, wordTerm (N := N) Δ v x p σ w) = 0 := by
  have h : (∑ σ, wordTerm (N := N) Δ v x p σ w) =
      ∑ σ, wordTerm (N := N) Δ v x p (σ * Equiv.swap a.castSucc a.succ) w :=
    (Equiv.sum_comp (Equiv.mulRight (Equiv.swap a.castSucc a.succ)) _).symm
  grind [wordTerm_adjacent_swap hc x p hp _ w a ha hb, Finset.sum_neg_distrib]

/-- Rotating the word and coordinates rotates the selected endpoint tuple. -/
theorem wordPositions_rotate {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)
    (w : Fin (n + 1) → Bool) :
    wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate (n + 1) k)) =
      cyclicSuccessorPositions N (wordPositions N x w) := by
  funext k
  simp only [wordPositions, cyclicPredecessor_successor, cyclicSuccessorPositions]
  by_cases hw : w (finRotate _ k) = true
  · simp only [hw, ↓reduceIte]
    exact (congrFun (cyclicSuccessor_predecessor N x) k).symm
  · grind

private theorem wordCoefficient_rotate {l m : Fin (n+1) → ℂ} (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) :
    wordCoefficient l m (σ * finRotate _) (fun k => w (finRotate _ k)) = wordCoefficient l m σ w :=
  Equiv.prod_comp _ (wordEdgeFactor (finRotate _) (l ∘ σ) (m ∘ σ) w)

include hc hBE in
/-- The full word term obeys the toroidal rotation, including its boundary phase. -/
theorem wordTerm_rotate :
    wordTerm (N := N) Δ v (cyclicSuccessorPositions N x) p (σ * finRotate (n + 1))
      (fun k => w (finRotate (n + 1) k)) = wordTerm (N := N) Δ v x p σ w := by
  have h := amplitude_planeWave_rotate hc p hBE σ
    (wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate _ k)))
  grind [wordPositions_rotate, cyclicPredecessor_successor, wordCoefficient_rotate, wordTerm]

include hc hBE in
/-- The permutation sum of a word equals that of its cyclic rotation. -/
theorem sum_wordTerm_rotate :
    (∑ σ, wordTerm (N := N) Δ v (cyclicSuccessorPositions N x) p σ
      (fun k => w (finRotate (n + 1) k))) = ∑ σ, wordTerm (N := N) Δ v x p σ w := by
  calc
    _ = ∑ σ, wordTerm (N := N) Δ v (cyclicSuccessorPositions N x) p
        (σ * finRotate _) (fun k => w (finRotate _ k)) :=
      (Equiv.sum_comp (Equiv.mulRight (finRotate _)) _).symm
    _ = _ := Finset.sum_congr rfl fun σ _ => wordTerm_rotate hc x p hBE σ w

end

variable {N n : ℕ} {Δ : ℝ} (hc : Δ < -1) {v : ℂ} (x : Fin (n + 2) → ℤ) (p : Fin (n + 2) → ℝ)
    (hp : ∀ j, z (p j) ≠ v) (hBE : BetheEquations N Δ p) (w : Fin (n + 2) → Bool)

include hc hp hBE in
/-- The boundary ML edge cancels by moving it to the last ordinary edge. -/
theorem sum_wordTerm_eq_zero_of_boundaryML
    (ha : w (Fin.last (n + 1)) = false) (hb : w 0 = true) :
    (∑ σ, wordTerm (N := N) Δ v x p σ w) = 0 := by
  rw [← sum_wordTerm_rotate hc x p hBE w]
  apply sum_wordTerm_eq_zero_of_adjacentML hc _ p hp
    (fun k => w (finRotate _ k)) (Fin.last n)
  · simp_all
  · simpa using hb

/-- A nonconstant Boolean word has an ordinary ML edge or a boundary ML edge. -/
theorem nonconstant_word_has_ML {n : ℕ} (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true) ∨
      (w (Fin.last n) = false ∧ w 0 = true) := by
  by_cases he : ∃ a : Fin n, w a.castSucc = false ∧ w a.succ = true
  · exact Or.inl he
  right
  have hm : Antitone (fun k => if w k then 1 else 0) := by
    apply Fin.antitone_iff_succ_le.mpr
    grind
  have hfirst : w 0 = true := by
    by_contra h
    apply hM
    funext k
    have hk := hm (Fin.zero_le k)
    grind
  have hlast : w (Fin.last n) = false := by
    by_contra h
    apply hL
    funext k
    have hk := hm (Fin.le_last k)
    grind
  grind

include hc hp hBE in
/-- Companion Lemma `lem:2`, word by word, including the periodic boundary edge. -/
theorem sum_wordTerm_eq_zero_of_nonconstant
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    (∑ σ, wordTerm (N := N) Δ v x p σ w) = 0 := by
  rcases nonconstant_word_has_ML w hL hM with ⟨a, ha, hb⟩ | ⟨ha, hb⟩
  · solve_by_elim [sum_wordTerm_eq_zero_of_adjacentML]
  · exact sum_wordTerm_eq_zero_of_boundaryML hc x p hp hBE w ha hb

end
end PottsDiscontinuity.BetheAnsatz
