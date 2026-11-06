module
public import Mathlib

public import PottsDiscontinuity.SixVertex.Cor34Spectral

/-!
# Arrow-flip symmetry of the six-vertex blocks

The global arrow flip sends a row state to its complement.  This file records the resulting
conjugacy between the blocks with `n` and `N - n` up arrows, and hence equality of their
Perron–Frobenius roots.
-/

@[expose] public section

open Finset Matrix PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Counting the elements of a set and its complement up to `t` partitions `Iic t`. -/
theorem cnt_compl_add_cnt (x : Finset (Fin N)) (t : Fin N) :
    cnt xᶜ t + cnt x t = t.val + 1 := by
  
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Iic t) (p := fun i  => i ∈ x)
  have h₁ : (Finset.Iic t).filter (fun i => i ∈ x) = x.filter (· ≤ t) := by
    grind
  have h₂ : (Finset.Iic t).filter (fun i => ¬ i ∈ x) = xᶜ.filter (· ≤ t) := by
    
    aesop
  rw [h₁, h₂] at h
  simpa [cnt, Nat.add_comm] using h

/-- Interlacing is invariant under simultaneous complementation of the two states. -/
theorem interlaced_compl_iff (x y : Finset (Fin N)) :
    Interlaced xᶜ yᶜ ↔ Interlaced x y := by
  rw [interlaced_iff, interlaced_iff]
  have hsize (hcard : xᶜ.card = yᶜ.card) : x.card = y.card := by
    have hx := Finset.card_compl x
    have hy := Finset.card_compl y
    rw [Fintype.card_fin] at hx hy
    
    have hxle := Finset.card_le_univ x
    have hyle := Finset.card_le_univ y
    rw [Fintype.card_fin] at hxle hyle
    omega
  constructor
  · rintro ⟨hcard, hcounts | hcounts⟩
    · grind [cnt_compl_add_cnt]
    · grind [cnt_compl_add_cnt]
  · rintro ⟨hcard, hcounts | hcounts⟩
    · refine ⟨?_, Or.inr fun t => ?_⟩
      · have hx : xᶜ.card = N - x.card := by
          have hx := Finset.card_compl x
          simp_all
        have hy : yᶜ.card = N - y.card := by
          have hy := Finset.card_compl y
          simp_all
        rw [hx, hy]
        exact congrArg (fun k  => N - k) hcard
      have hct := hcounts t
      have hx := cnt_compl_add_cnt x t
      have hy := cnt_compl_add_cnt y t
      exact ⟨by omega, by omega⟩
    · refine ⟨?_, Or.inl fun t => ?_⟩
      · have hx : xᶜ.card = N - x.card := by
          have hx := Finset.card_compl x
          simp_all
        have hy : yᶜ.card = N - y.card := by
          have hy := Finset.card_compl y
          simp_all
        rw [hx, hy]
        exact congrArg (fun k  => N - k) hcard
      have hct := hcounts t
      have hx := cnt_compl_add_cnt x t
      have hy := cnt_compl_add_cnt y t
      exact ⟨by omega, by omega⟩

/-- Complementation preserves every transfer-matrix entry. -/
theorem transferMatrix_compl (c : ℝ) (x y : Finset (Fin N)) :
    transferMatrix N c xᶜ yᶜ = transferMatrix N c x y := by
  
  have hdist : (univ.filter fun i => Psi xᶜ i ≠ Psi yᶜ i).card =
      (univ.filter fun i => Psi x i ≠ Psi y i).card := by
    apply congrArg Finset.card
    ext i
    simp only [mem_filter]
    have hx : Psi xᶜ i = -Psi x i := by
      by_cases hi : i ∈ x <;> simp [Psi, hi]
    have hy : Psi yᶜ i = -Psi y i := by
      by_cases hi : i ∈ y <;> simp [Psi, hi]
    rw [hx, hy]
    simp
  rw [transferMatrix_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · have hcompl : xᶜ ≠ yᶜ := by
      simp_all
    
    have hinter  := interlaced_compl_iff x y
    grind

/-- Complementation identifies the `n`-particle and `(N-n)`-particle state spaces. -/
noncomputable def stateComplement {n : ℕ} (hn : n ≤ N) :
    State N n ≃ State N (N - n) where
  toFun x := ⟨x.1ᶜ, by rw [Finset.card_compl, x.2, Fintype.card_fin]⟩
  invFun x := ⟨x.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin]; omega⟩
  left_inv x := by apply Subtype.ext; exact compl_compl x.1
  right_inv x := by apply Subtype.ext; exact compl_compl x.1

/-- The two blocks related by global arrow flip are conjugate by `stateComplement`. -/
theorem transferBlock_compl_reindex (c : ℝ) {n : ℕ} (hn : n ≤ N) :
    transferBlock N c (N - n) =
      Matrix.reindex (stateComplement (N := N) hn) (stateComplement (N := N) hn)
        (transferBlock N c n) := by
  ext x y
  
  change transferMatrix N c x.1 y.1 = _
  rw [← transferMatrix_compl (N := N) c x.1 y.1]
  congr 2

/-- Reindexing a real matrix by a finite equivalence preserves its spectrum. -/
theorem spectrum_reindex_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℝ) :
    spectrum ℝ (Matrix.reindex e e A) = spectrum ℝ A := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_reindex,
    Matrix.mem_spectrum_iff_isRoot_charpoly]

/-- Arrow-flip symmetry of the block Perron–Frobenius eigenvalues. -/
theorem pfRoot_transferBlock_compl (c : ℝ) {n : ℕ} (hn : n ≤ N) :
    pfRoot (transferBlock N c n) = pfRoot (transferBlock N c (N - n)) := by
  grind [pfRoot, transferBlock_compl_reindex, spectrum_reindex_eq]

end PottsDiscontinuity.SixVertex
