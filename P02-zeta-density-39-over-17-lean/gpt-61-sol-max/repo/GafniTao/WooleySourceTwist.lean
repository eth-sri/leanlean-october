module
import Mathlib
public import GafniTao.WooleySourceAffine

@[expose] public section

/-!
# Unit twists of Wooley source coefficients

The coefficient sequence in Wooley (7.14)--(7.16) is obtained by multiplying
an affine pullback by an additive character.  This file isolates the exact
finite-support operation and proves that a unit-modulus twist preserves the
support and every `L²` mass.  These are equalities, not estimates.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Multiply a finitely supported source sequence by an arbitrary function.
The support certificate records that multiplication cannot create support. -/
def wooleySourceTwist (gamma : WooleySourceSequence) (phase : ℤ → ℂ) :
    WooleySourceSequence :=
  Finsupp.onFinset gamma.support (fun n => gamma n * phase n) (by simp_all)

section
variable (gamma : WooleySourceSequence) (phase : ℤ → ℂ)
include gamma phase

@[simp] theorem wooleySourceTwist_apply
     (n : ℤ) :
    wooleySourceTwist gamma phase n = gamma n * phase n := by
  simp [wooleySourceTwist]

/-- A nowhere-zero phase preserves the support literally. -/
theorem wooleySourceTwist_support
    
    (hphase : ∀ n, phase n ≠ 0) :
    (wooleySourceTwist gamma phase).support = gamma.support := by aesop

section
variable (hphase : ∀ n, ‖phase n‖ = 1)
include hphase

/-- Unit-modulus twisting preserves total coefficient mass. -/
theorem wooleySourceMassSq_twist
     :
    wooleySourceMassSq (wooleySourceTwist gamma phase) =
      wooleySourceMassSq gamma := by
  have hne : ∀ n, phase n ≠ 0 := fun n => norm_ne_zero_iff.mp (by
    rw [hphase n]
    norm_num)
  unfold wooleySourceMassSq
  rw [wooleySourceTwist_support gamma phase hne]
  simp_all

/-- Unit-modulus twisting preserves every residue-class coefficient mass. -/
theorem wooleySourceResidueMassSq_twist
     (q : ℕ) (xi : ZMod q) :
    wooleySourceResidueMassSq (wooleySourceTwist gamma phase) q xi =
      wooleySourceResidueMassSq gamma q xi := by
  have hne : ∀ n, phase n ≠ 0 := fun n => norm_ne_zero_iff.mp (by
    rw [hphase n]
    norm_num)
  unfold wooleySourceResidueMassSq
  rw [wooleySourceTwist_support gamma phase hne]
  simp_all
end
end


theorem WooleySourceSequence.Admissible.twist
    {gamma : WooleySourceSequence} (hgamma : gamma.Admissible)
    (phase : ℤ → ℂ) (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    (wooleySourceTwist gamma phase).Admissible := by
  intro n
  rw [wooleySourceTwist_apply, norm_mul]
  calc
    ‖gamma n‖ * ‖phase n‖ ≤ ‖gamma n‖ * 1 :=
      mul_le_mul_of_nonneg_left (hphase n) (norm_nonneg _)
    _ ≤ 1 := by simpa using hgamma n

section
variable {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
include k q phi

section
variable (alpha : Fin k → ZMod q) (n : ℤ)
include alpha n

theorem wooleySourcePolynomialPhase_norm
     :
    ‖wooleySourcePolynomialPhase phi alpha n‖ = 1 := by
  simp [wooleySourcePolynomialPhase, ZMod.stdAddChar_apply]

theorem wooleySourcePolynomialPhase_ne_zero
     :
    wooleySourcePolynomialPhase phi alpha n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [wooleySourcePolynomialPhase_norm]
  norm_num
end


theorem wooleySourcePolynomialPhase_zero
     (n : ℤ) :
    wooleySourcePolynomialPhase phi (0 : Fin k → ZMod q) n = 1 := by
  simp [wooleySourcePolynomialPhase]
end





