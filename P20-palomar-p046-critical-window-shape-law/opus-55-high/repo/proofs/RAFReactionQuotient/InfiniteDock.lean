module

public import proofs.RAFReactionQuotient.InfiniteSource
public import proofs.RAFReactionQuotient.Surjectivity
public import proofs.RAFReactionQuotient.CommutingUniqueness
public import proofs.RAFReactionQuotient.SeedBulk
public import proofs.HordijkSteelThreshold.SplitModel

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

variable {n : ℕ}

variable (r : OrderedChannel n)

noncomputable def orderedCoordinate   : List Bool × ℕ :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

theorem orderedCoordinate_split  (r : Reaction n) :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r := by
  apply Prod.ext
  · exact reaction_words_append r
  rfl

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  obtain ⟨r,rfl⟩ := splitToOrdered_surjective n q
  obtain ⟨s,rfl⟩ := splitToOrdered_surjective n j
  rw [orderedCoordinate_split,orderedCoordinate_split] at he
  exact congrArg splitToOrdered $ literalSplitCoordinate_injective n he

noncomputable def quotientCoordinate  (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.val,j.property.1⟩

theorem quotientCoordinate_injective (n : ℕ) : Function.Injective (@quotientCoordinate n) := by
  intro j k he
  exact Subtype.ext $ congrArg (fun q : OrderedChannel n => q.val)
    (orderedCoordinate_injective n he)

theorem word_comm_iff  (u v : Molecule n) :
    moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
  constructor
  · intro he
    have hc := congrArg binaryWordCode he
    simpa only [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
      displayedConcat] using hc
  · intro hc
    apply binaryWordCode_injective_length $ by grind
    simpa only [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
      displayedConcat] using hc

theorem canonicalIndex_ordered   :
    canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r) := by
  have ht : (moleculeWord r.val.1 ++ moleculeWord r.val.2).take (molLength r.val.1) =
      moleculeWord r.val.1 := by rw [← moleculeWord_length r.val.1]; simp
  have hd : (moleculeWord r.val.1 ++ moleculeWord r.val.2).drop (molLength r.val.1) =
      moleculeWord r.val.2 := by rw [← moleculeWord_length r.val.1]; simp
  unfold canonical
  split
  · rename_i h
    have hn : ¬ (molLength r.val.2 < molLength r.val.1 ∧
        moleculeWord r.val.1 ++ moleculeWord r.val.2 =
          moleculeWord r.val.2 ++ moleculeWord r.val.1) := by
      rintro ⟨hl,hc⟩
      rcases h with h | h
      · exact h $ (word_comm_iff _ _).mp hc
      omega
    simp only [canonicalIndex,orderedCoordinate,List.length_append,moleculeWord_length]
    rw [ite_eq_right $ by simp_all]
    rfl
  · rename_i h
    have hl := noncanonical_strict_lengths r h
    have hc :=
      Classical.byContradiction $ fun hn => h $ Or.inl hn
    have hw := (word_comm_iff _ _).mpr hc
    simp only [canonicalIndex,orderedCoordinate,List.length_append,moleculeWord_length]
    aesop


theorem canonicalIndex_split  (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  rw [← orderedCoordinate_split]
  exact canonicalIndex_ordered _


noncomputable abbrev quotientModel : SplitModel where
  C := RepositoryChannel
  c := quotientCoordinate
  π := splitToQuotient
  g := canonicalIndex
  hc := quotientCoordinate_injective
  hg _ := canonicalIndex_split

end RAFReactionQuotient
