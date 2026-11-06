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
  apply molecule_ext
  · calc
      molLength (concatMolecule (reactionLeft r) (reactionRight r)
          (splitToOrdered r).property) =
          molLength (reactionLeft r) + molLength (reactionRight r) := by
            rfl
      _ = reactionLeftLength r + reactionRightLength r := by
        simp_all
      _ = reactionProductLength r := reaction_length_add r
  · have hc := concat_code (reactionLeft r) (reactionRight r)
      (splitToOrdered r).property
    rw [hc]
    unfold displayedConcat
    rw [molLength_reactionRight]
    change r.2.1.val / 2 ^ reactionRightLength r * 2 ^ reactionRightLength r +
      r.2.1.val % 2 ^ reactionRightLength r = r.2.1.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod r.2.1.val $ 2 ^ reactionRightLength r

def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical $ splitToOrdered r

variable {n t : ℕ} (r : Reaction n)

theorem splitToQuotient_lhs  :
    (repositoryCRS n t).lhs (splitToQuotient r) = (binaryPolymerCRS n t).lhs r :=
  canonical_lhs $ splitToOrdered r

theorem splitToQuotient_rhs  :
    (repositoryCRS n t).rhs (splitToQuotient r) = (binaryPolymerCRS n t).rhs r := by
  rw [splitToQuotient, canonical_rhs]
  change {concatMolecule (reactionLeft r) (reactionRight r) _} = {reactionProduct r}
  rw [split_concat]


theorem split_closure_eq_quotient {n : ℕ} (t : ℕ)
    (S : Finset $ Reaction n) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image splitToQuotient) k =
      revClosureAt (binaryPolymerCRS n t) S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [revClosureAt, ih, revClosureStep]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and, RevEnabledLhs, RevEnabledRhs, splitToQuotient_lhs, splitToQuotient_rhs]

end RAFReactionQuotient
