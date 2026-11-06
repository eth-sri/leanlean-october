/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SmoothAffineResidueClasses
import CCDN.Surface.CongruenceCutoff

/-! A coherent choice of proper auxiliaries for every finite
smooth residue family. The structure stores conclusions of the determinant
theorem; its existence is proved from the equation. -/

namespace CCDN
section
open MvPolynomial Finset

section
variable {n : ℕ}

/-- The restriction of a family of smooth residues, indexed by the primes of `P`, to a subset
`Q ⊆ P`. -/
def SmoothAffineResidueFamily.restrict {f : MvPolynomial (Fin n) ℤ}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

/-- The unique family of smooth residues indexed by the empty set of primes. -/
def emptySmoothAffineResidueFamily (f : MvPolynomial (Fin n) ℤ) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

end

/-- A choice, for every finite set `P` of primes and every family `r` of smooth residues of `f`
modulo the primes of `P`, of a nonzero integer polynomial that is not divisible by `f` over `ℚ`,
has degree at most `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)` (with `d` the degree of `f`
and `p` ranging over `P`) and vanishes at every integer zero of `f` in the box of radius `B`
lying in the residue classes `r`. -/
structure SurfaceCongruenceFamily (f : MvPolynomial (Fin 3) ℤ) (B A : ℝ) where
  /-- The auxiliary polynomial attached to a set `P` of primes and smooth residues modulo
  `P`. -/
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → MvPolynomial (Fin 3) ℤ
  /-- Every auxiliary is nonzero. -/
  nonzero : ∀ P hP r, auxiliary P hP r ≠ 0
  /-- No auxiliary is divisible by `f` over `ℚ`. -/
  proper : ∀ P hP r, ¬ map (Int.castRingHom ℚ) f ∣
    map (Int.castRingHom ℚ) (auxiliary P hP r)
  /-- The degree of the auxiliary attached to `P` is at most
  `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)`. -/
  degree_le : ∀ P hP r, ((auxiliary P hP r).totalDegree : ℝ) ≤
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) + 1) * (1 + Real.log B + ∑ p ∈ P, Real.log p)
  /-- The auxiliary attached to `P` and `r` vanishes at the integer zeros of `f` in the box
  that lie in the residue classes `r`. -/
  vanishes : ∀ P hP r x, x ∈ affineCongruencePoints f B P (smoothResidueIntegerLift r) →
    eval x (auxiliary P hP r) = 0

variable {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ} (F : SurfaceCongruenceFamily f B A)

/-- The auxiliary polynomial of a congruence family attached to the empty set of primes: it
vanishes at every integer zero of `f` in the box. -/
def SurfaceCongruenceFamily.initial
    : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

/-- The auxiliary attached to the empty set of primes is `F.initial`, whatever the (unique)
residue family and primality proof. -/
lemma SurfaceCongruenceFamily.initial_eq
    (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f := by
    funext p
    grind
  rw [he]
  rfl

