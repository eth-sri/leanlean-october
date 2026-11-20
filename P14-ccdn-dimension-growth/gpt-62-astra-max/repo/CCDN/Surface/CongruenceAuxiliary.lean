/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.SmoothBoxAuxiliary

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

variable {n : ℕ}

/-- The integer zeros of `f` in the box of radius `B` that are congruent to `a p` modulo `p`,
coordinatewise, for every `p ∈ P`. -/
def affineCongruencePoints (f : IntegerPolynomial n)
    (B : ℝ) (P : Finset ℕ) (a : ℕ → IntPoint n) : Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter (fun x =>
    eval x f = 0 ∧ ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j)

/-- A point lies in `affineCongruencePoints f B P a` exactly when it lies in the box of radius
`B`, is a zero of `f` and is congruent to `a p` modulo every `p ∈ P`. -/
lemma mem_affineCongruencePoints {f : IntegerPolynomial n}
    {B : ℝ} {P : Finset ℕ} {a : ℕ → IntPoint n} {x : IntPoint n} :
    x ∈ affineCongruencePoints f B P a ↔
      InBox x B ∧ eval x f = 0 ∧
        ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j := by
  classical
  simp only [affineCongruencePoints, mem_filter, mem_integerBox]

end
end CCDN
