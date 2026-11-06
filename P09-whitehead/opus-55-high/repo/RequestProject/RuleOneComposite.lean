import RequestProject.LemmaStructural


/-!
# Rule 1 for one extra generator, without any hypothesis

Rule 1 of the operation `T` of Lemma 3.9 replaces an extra generator `z` by a commutator
`[a_z,b_z]`.  The paper performs it in three moves: freely adjoin `b_z`, adjoin the stable
letter `a_z` with `a_z b_z a_z⁻¹ = z b_z`, and eliminate `z` through `z = [a_z,b_z]`.  The
stable-letter move requires that the two elements `b_z` and `z b_z` have infinite order, and
the paper checks this "by killing `G(P)`".

This file verifies that remark in the combinatorial model and assembles the two extension
moves into a single sequence of moves, so that rule 1 of Lemma 3.9 is available **with no
hypothesis at all**.

* `FiniteChains.not_isOfFinOrder_newGen`, `FiniteChains.not_isOfFinOrder_mul_newGen` — after
  freely adjoining `b`, both `b` and `z b` have infinite order, as seen by the homomorphism
  which kills the old generators and sends `b` to a generator of `ℤ`;
* `FiniteChains.ruleOnePath` — **rule 1 for one extra generator as a sequence of moves**, and
  `FiniteChains.generates_ruleOnePath`, `FiniteChains.isCockcroft_ruleOnePath` — equation
  (3.3) and the preservation of the Cockcroft property for it.
-/
