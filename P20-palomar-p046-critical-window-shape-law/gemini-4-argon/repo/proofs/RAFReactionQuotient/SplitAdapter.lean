module

public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def splitToOrdered {n : ℕ} (r : Reaction n) : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩

theorem split_concat {n : ℕ} (r : Reaction n) :
    concatMolecule (reactionLeft r) (reactionRight r) (splitToOrdered r).property =
      reactionProduct r := by
  refine molecule_ext ((molLength_moleculeOfCode _ _ _).trans ?_)
    ((concat_code (reactionLeft r) (reactionRight r) (splitToOrdered r).property).trans ?_)
  · rw [molLength_reactionLeft, molLength_reactionRight, reaction_length_add, molLength_reactionProduct]
  · unfold displayedConcat
    rw [molLength_reactionRight]
    exact Nat.mul_comm _ _ ▸ Nat.div_add_mod r.2.1.val (2 ^ reactionRightLength r)

def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical (splitToOrdered r)

theorem splitToQuotient_lhs {n t : ℕ} (r : Reaction n) :
    (repositoryCRS n t).lhs (splitToQuotient r) = (binaryPolymerCRS n t).lhs r :=
  canonical_lhs (splitToOrdered r)

theorem splitToQuotient_rhs {n t : ℕ} (r : Reaction n) :
    (repositoryCRS n t).rhs (splitToQuotient r) = (binaryPolymerCRS n t).rhs r := by
  rw [splitToQuotient, canonical_rhs]
  exact congrArg singleton (split_concat r)

theorem split_closure_eq_quotient {n : ℕ} (t : ℕ)
    (S : Finset (Reaction n)) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image splitToQuotient) k =
      revClosureAt (binaryPolymerCRS n t) S k :=
  closureAt_image _ _ splitToQuotient splitToQuotient_lhs splitToQuotient_rhs rfl S k

end RAFReactionQuotient
