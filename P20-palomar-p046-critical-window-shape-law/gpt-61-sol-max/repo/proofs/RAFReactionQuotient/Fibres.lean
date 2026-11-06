
import proofs.RAFReactionQuotient.QuotientMap




namespace RAFReactionQuotient

variable {n : ℕ}
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source


variable (r : Reaction n)

def splitToOrdered   : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩

theorem split_concat   :
    concatMolecule (reactionLeft r) (reactionRight r) (splitToOrdered r).property =
      reactionProduct r := by
  apply molecule_ext
  · change molLength (reactionLeft r) + molLength (reactionRight r) = _
    simpa using reaction_length_add r
  · rw [concat_code (reactionLeft r) (reactionRight r) (splitToOrdered r).property]
    unfold displayedConcat
    simp
    rw [Nat.mul_comm]
    exact Nat.div_add_mod r.2.1.val (2 ^ reactionRightLength r)

def splitToQuotient    :=
  canonical (splitToOrdered r)

variable {t : ℕ} (r : Reaction n)

theorem splitToQuotient_lhs  :
    (repositoryCRS n t).lhs (splitToQuotient r) = (binaryPolymerCRS n t).lhs r :=
  canonical_lhs (splitToOrdered r)

theorem splitToQuotient_rhs  :
    (repositoryCRS n t).rhs (splitToQuotient r) = (binaryPolymerCRS n t).rhs r := by
  rw [splitToQuotient, canonical_rhs]
  change {concatMolecule (reactionLeft r) (reactionRight r) _} = {reactionProduct r}
  rw [split_concat]

variable (t : ℕ)

theorem split_closure_eq_quotient (S : Finset (Reaction n)) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image splitToQuotient) k =
      revClosureAt (binaryPolymerCRS n t) S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [revClosureAt, revClosureStep, ih, Finset.image_biUnion,
      RevEnabledLhs, RevEnabledRhs, splitToQuotient_lhs, splitToQuotient_rhs]




theorem split_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)).card ≤ 2 := by
  let a : OrderedChannel n := ⟨j.val,j.property.1⟩
  let b : OrderedChannel n := ⟨j.val.swap, by dsimp; omega⟩
  calc
    _ ≤ ({a,b} : Finset _).card := Finset.card_le_card_of_injOn (f := splitToOrdered) (by
      intro r hr
      have hv := canonical_val_cases (splitToOrdered r)
      change (splitToQuotient r).val = _ ∨ (splitToQuotient r).val = _ at hv
      rw [(Finset.mem_filter.mp hr).2] at hv
      rcases hv with hv | hv
      · have : splitToOrdered r = a := Subtype.ext hv.symm
        simp_all
      · have : splitToOrdered r = b := Subtype.ext (congrArg Prod.swap hv.symm)
        simp_all) (by
      intro r _ s _ he
      have hp : reactionProduct r = reactionProduct s := by
        grind [splitToOrdered, split_concat]
      have hl : reactionLeftLength r = reactionLeftLength s := by
        grind [splitToOrdered, molLength_reactionLeft]
      ext <;> simp_all [reactionProduct, reactionLeftLength]; aesop)
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

end RAFReactionQuotient
