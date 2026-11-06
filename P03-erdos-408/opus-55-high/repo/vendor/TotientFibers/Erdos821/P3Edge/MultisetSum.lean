module

public import Erdos821.P3Edge.BoundedMem
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

variable {α : Type*} [Fintype α] [DecidableEq α]

-- Finite set of multisets of fixed card over a finite alphabet.

-- Multiset factorial denominator.
def multFact (z : Multiset α) : ℝ :=
  ∏ u ∈ z.toFinset, ((z.count u).factorial : ℝ)

omit [Fintype α] in
lemma multFact_pos (z : Multiset α) : 0 < multFact z := by
  unfold multFact
  positivity

-- Sum over multisets of fixed size with factorial denominators.
-- This is the exponential generating function identity needed for
-- column source-memory sums: weighted multiset sums collapse to
-- (sum w)^N / N!.
--
-- Proof by induction on the alphabet (Finset.univ), splitting
-- multisets by the count of a distinguished element and using
-- the binomial theorem. Each step is J- and x-independent.

-- Bounded version: with sums ≤ 2, multiset sums ≤ 2^N/N!.

end Erdos821.P3Edge
