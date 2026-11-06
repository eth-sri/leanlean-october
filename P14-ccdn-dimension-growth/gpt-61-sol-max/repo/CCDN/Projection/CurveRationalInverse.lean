/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import CCDN.Height.PrimitivePairReconstruction
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Birational projection coordinates admit a rational inverse in the original
coordinate ring. Its denominator cuts out all possible noninjective fibers.
This module gives no bound on the degree of that denominator;
`ExceptionalCount` converts a denominator of degree `D` into at most `d * D`
exceptional points. -/

public section
namespace CCDN
open MvPolynomial

/-- Polynomial reconstruction gives injectivity at every source point where
the denominator is nonzero. -/
theorem projection_injective_off_reconstruction {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (Q : MvPolynomial σ K) (P : τ → MvPolynomial σ K)
    (hP : ∀ i, aeval a Q * X i - aeval a (P i) ∈ I)
    (z w : τ → K) (hz : z ∈ idealZeroLocus I) (hw : w ∈ idealZeroLocus I)
    (hQ : eval z (aeval a Q) ≠ 0)
    (he : (fun j => eval z (a j)) = (fun j => eval w (a j))) : z = w := by
  have hev (p : MvPolynomial σ K) : eval z (aeval a p) = eval w (aeval a p) := by
    change eval z (eval₂ C a p) = eval w (eval₂ C a p)
    rw [← eval_assoc, ← eval_assoc]
    change eval (fun j => eval z (a j)) p = eval (fun j => eval w (a j)) p
    rw [he]
  funext i
  apply mul_left_cancel₀ hQ
  have hz' := hz _ (hP i)
  have hw' := hw _ (hP i)
  simp only [eval_sub, eval_mul, eval_X, sub_eq_zero] at hz' hw'
  rw [hz', hev (P i), hev Q]
  exact hw'.symm

end CCDN
