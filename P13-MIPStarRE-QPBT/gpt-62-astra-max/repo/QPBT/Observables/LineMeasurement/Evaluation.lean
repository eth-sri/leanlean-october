module

public import QPBT.Observables.WinImplications.LowDegree

/-!
# Evaluation of line polynomials at a sampled point

This module records the elementary calculus of the partial evaluation
`evalOpt` of a coefficient-list line polynomial at a point: the evaluation of
a sum is the sum of the evaluations whenever both summands evaluate, a summand
of an evaluating sum evaluates whenever the other summand does, the value is
unique, and nothing evaluates at a point off the line. These facts underlie
the manipulation of the evaluation classes in items 2 and 3 of the
expanded-line consistency lemma.

Every declaration below is a formalization-only auxiliary: the source uses
these facts about evaluation without stating them.

## References

The evaluation classes `[eval_u(·) = a]` are `def:ideg-deg-polynomials`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:51-58`. They are
manipulated in `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Coefficient-list evaluation is additive in the coefficient list. This
is the additivity behind the convolution of `def:expanded-line-measurement`. -/
theorem evalCoefficient_add {K : Type*} [Semiring K] {n : ℕ} (c d : Fin n → K)
    (t : K) : evalCoefficient (c + d) t = evalCoefficient c t + evalCoefficient d t := by
  unfold evalCoefficient
  rw [← Finset.sum_add_distrib]
  congr 1 with i
  simp [add_mul]

variable {L : LdParams} {c : ℕ}

section

variable {line : LineDesc L} {f g : DegPoly L c} {u : LdPoint L}

/-- The sum of two evaluating line polynomials evaluates to the sum of
their values. This is why the convolution outcome `f = f' + f''` evaluates
whenever both convolution factors do. -/
theorem EvaluatesTo.add {a b : ScalarQ L}
    (hf : EvaluatesTo line f u a) (hg : EvaluatesTo line g u b) :
    EvaluatesTo line (f + g) u (a + b) :=
  ⟨hf.1, fun t ht => by rw [evalCoefficient_add, hf.2 t ht, hg.2 t ht]⟩

/-- If a sum and its second summand evaluate, the first summand evaluates to
the difference of their values. This is the converse direction used to identify
the convolution fibers of an evaluation class. -/
theorem EvaluatesTo.left_of_add {s b : ScalarQ L}
    (hfg : EvaluatesTo line (f + g) u s) (hg : EvaluatesTo line g u b) :
    EvaluatesTo line f u (s - b) :=
  ⟨hfg.1, fun t ht => by
    have h := hfg.2 t ht
    rw [evalCoefficient_add, hg.2 t ht] at h
    exact eq_sub_of_add_eq h⟩

end

section

variable (line : LineDesc L) (u : LdPoint L) (f : DegPoly L c)

/-- The partial evaluation returns `some a` exactly when the polynomial
evaluates to `a`. This is the characterization that makes `evalOpt` the total
form of the evaluation classes of `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_some_iff (a : ScalarQ L) :
    evalOpt line u f = some a ↔ EvaluatesTo line f u a := by
  constructor
  · intro h
    unfold evalOpt at h
    by_cases hex : ∃ a : ScalarQ L, EvaluatesTo line f u a
    · simp [*] at h
      rw [← h]
      exact Classical.choose_spec hex
    · rw [dif_neg hex] at h
      exact absurd h (by simp)
  · apply WinImplications.evalOpt_eq_some_of_evaluatesTo

/-- The partial evaluation returns `none` exactly when no value is
determined. This is the outcome that completes the evaluation classes to a
measurement, written `[eval_u(·) = ⊥]` in `def:ideg-deg-polynomials`. -/
theorem evalOpt_eq_none_iff :
    evalOpt line u f = none ↔ ¬ ∃ a : ScalarQ L, EvaluatesTo line f u a := by
  unfold evalOpt
  split_ifs with hex <;> simp [hex]

end

section

variable {line : LineDesc L} {u : LdPoint L}

end

end MIPStarRE.QPBT
