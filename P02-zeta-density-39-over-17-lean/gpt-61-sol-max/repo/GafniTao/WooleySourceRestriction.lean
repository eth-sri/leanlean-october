module
import Mathlib
public import GafniTao.WooleySourceMean

@[expose] public section

/-!
# Exact residue restrictions for Wooley's source sequences

Equations (3.2)--(3.4), and the translation step (4.2)--(4.5), repeatedly
replace a finitely supported coefficient sequence by its restriction to one
residue class.  This file performs that operation on the actual integer-indexed
source sequence and proves that the source residue masses and exponential sums
are exactly the ordinary masses and sums of the restricted sequence.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

section
variable (gamma : WooleySourceSequence)
    (q : ℕ) (xi : ZMod q)
include gamma q xi

/-- The coefficient sequence restricted to the residue class `xi mod q`. -/
def wooleySourceResidueSequence  : WooleySourceSequence :=
  gamma.filter fun n : ℤ => (n : ZMod q) = xi

@[simp] theorem wooleySourceResidueSequence_apply
     (n : ℤ) :
    wooleySourceResidueSequence gamma q xi n =
      if (n : ZMod q) = xi then gamma n else 0 :=
  rfl

theorem wooleySourceResidueSequence_support
     :
    (wooleySourceResidueSequence gamma q xi).support =
      gamma.support.filter fun n : ℤ => (n : ZMod q) = xi :=
  rfl

/-- Equation (4.3) at the coefficient-mass level, before the harmless affine
reindexing of the selected progression. -/
theorem wooleySourceMassSq_residueSequence
     :
    wooleySourceMassSq (wooleySourceResidueSequence gamma q xi) =
      wooleySourceResidueMassSq gamma q xi := by
  unfold wooleySourceMassSq wooleySourceResidueMassSq
  rw [wooleySourceResidueSequence_support]
  apply Finset.sum_congr rfl
  simp_all
end


section
variable {k q qH : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (xi : ZMod qH)
include k q qH phi gamma alpha xi

/-- The global polynomial sum of the restricted sequence is the source
residue-class polynomial sum, with no error or change of normalization. -/
theorem wooleySourcePolynomialSum_residueSequence
     :
    wooleySourcePolynomialSum phi
        (wooleySourceResidueSequence gamma qH xi) alpha =
      wooleySourcePolynomialResidueSum phi gamma alpha xi := by
  unfold wooleySourcePolynomialSum wooleySourcePolynomialResidueSum
  rw [wooleySourceResidueSequence_support]
  apply Finset.sum_congr rfl
  simp_all

/-- Consequently the normalized global sum of a residue restriction is
literally the normalized residue sum in (3.4). -/
theorem wooleySourceNormalizedPolynomialSum_residueSequence
     :
    wooleySourceNormalizedPolynomialSum phi
        (wooleySourceResidueSequence gamma qH xi) alpha =
      wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi := by
  unfold wooleySourceNormalizedPolynomialSum
    wooleySourceNormalizedPolynomialResidueSum
  rw [wooleySourceMassSq_residueSequence,
    wooleySourcePolynomialSum_residueSequence]
end


/-- A residue-class sequence is zero precisely when its source residue mass
is zero.  This makes the zero branch in (3.4) explicit. -/
theorem wooleySourceResidueSequence_eq_zero_iff
    (gamma : WooleySourceSequence) (q : ℕ) (xi : ZMod q) :
    wooleySourceResidueSequence gamma q xi = 0 ↔
      wooleySourceResidueMassSq gamma q xi = 0 := by
  rw [← wooleySourceMassSq_residueSequence]
  constructor
  · intro h
    rw [h]
    simp [wooleySourceMassSq]
  · intro h
    apply Finsupp.ext
    intro n
    by_contra hn
    have hmem : n ∈ (wooleySourceResidueSequence gamma q xi).support :=
      Finsupp.mem_support_iff.mpr hn
    have hterm : 0 < ‖wooleySourceResidueSequence gamma q xi n‖ ^ 2 := by
      exact sq_pos_of_pos (norm_pos_iff.mpr hn)
    have hle : ‖wooleySourceResidueSequence gamma q xi n‖ ^ 2 ≤
        wooleySourceMassSq (wooleySourceResidueSequence gamma q xi) := by
      unfold wooleySourceMassSq
      exact Finset.single_le_sum
        (fun m _ => sq_nonneg ‖wooleySourceResidueSequence gamma q xi m‖)
        hmem
    rw [h] at hle
    linarith

/-- Modulo one there is a single residue class, so its mass is the global
mass. -/
theorem wooleySourceResidueMassSq_mod_one
    (gamma : WooleySourceSequence) (xi : ZMod 1) :
    wooleySourceResidueMassSq gamma 1 xi = wooleySourceMassSq gamma := by
  have hxi : xi = 0 := Subsingleton.elim _ _
  subst xi
  unfold wooleySourceResidueMassSq wooleySourceMassSq
  have hf : gamma.support.filter (fun n : ℤ => (n : ZMod 1) = 0) =
      gamma.support := by
    exact Finset.filter_eq_self.mpr fun n hn => Subsingleton.elim _ _
  rw [hf]

section
variable {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q)
    (xi : ZMod 1)
include k q phi gamma alpha xi

/-- Modulo one the residue sum is the global sum. -/
theorem wooleySourcePolynomialResidueSum_mod_one
     :
    wooleySourcePolynomialResidueSum phi gamma alpha xi =
      wooleySourcePolynomialSum phi gamma alpha := by
  have hxi : xi = 0 := Subsingleton.elim _ _
  subst xi
  unfold wooleySourcePolynomialResidueSum wooleySourcePolynomialSum
  have hf : gamma.support.filter (fun n : ℤ => (n : ZMod 1) = 0) =
      gamma.support := by
    exact Finset.filter_eq_self.mpr fun n hn => Subsingleton.elim _ _
  rw [hf]

/-- Modulo one the normalized residue sum is the normalized global sum. -/
theorem wooleySourceNormalizedPolynomialResidueSum_mod_one
     :
    wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi =
      wooleySourceNormalizedPolynomialSum phi gamma alpha := by
  unfold wooleySourceNormalizedPolynomialResidueSum
    wooleySourceNormalizedPolynomialSum
  rw [wooleySourceResidueMassSq_mod_one,
    wooleySourcePolynomialResidueSum_mod_one]
end





