module

public import proofs.RAFReactionQuotient.InfiniteSource
public import proofs.RAFReactionQuotient.Surjectivity
public import proofs.RAFReactionQuotient.CommutingUniqueness
public import proofs.RAFReactionQuotient.SeedBulk

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def orderedCoordinate {n : ℕ} (r : OrderedChannel n) : List Bool × ℕ :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

theorem orderedCoordinate_split {n : ℕ} (r : Reaction n) :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r :=
  Prod.ext (reaction_words_append r) (molLength_reactionLeft r)

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  obtain ⟨r, rfl⟩ := splitToOrdered_surjective n q
  obtain ⟨s, rfl⟩ := splitToOrdered_surjective n j
  rw [orderedCoordinate_split, orderedCoordinate_split] at he
  exact congrArg splitToOrdered (literalSplitCoordinate_injective n he)

noncomputable def quotientCoordinate {n : ℕ} (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.val, j.property.1⟩

theorem canonicalIndex_split {n : ℕ} (s : Reaction n) :
    canonicalIndex (literalSplitCoordinate s) = quotientCoordinate (splitToQuotient s) := by
  rw [← orderedCoordinate_split]
  let r := splitToOrdered s
  have hwcomm (u v : Molecule n) :
      moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
        displayedConcat u v = displayedConcat v u :=
    ⟨fun h => by simpa only [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length, displayedConcat]
      using congrArg binaryWordCode h,
     fun h => binaryWordCode_injective_length (by simp [Nat.add_comm])
       (by simpa only [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length, displayedConcat] using h)⟩
  have hv : 0 < molLength r.1.2 := Nat.succ_pos _
  have ht : (moleculeWord r.1.1 ++ moleculeWord r.1.2).take (molLength r.1.1) = moleculeWord r.1.1 := by
    rw [← moleculeWord_length r.1.1]; simp
  have hd : (moleculeWord r.1.1 ++ moleculeWord r.1.2).drop (molLength r.1.1) = moleculeWord r.1.2 := by
    rw [← moleculeWord_length r.1.1]; simp
  change canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r)
  unfold canonical; split <;> rename_i h
  · simp only [canonicalIndex, orderedCoordinate, ht, hd, List.length_append, moleculeWord_length,
      Nat.add_sub_cancel_left]
    rw [ite_eq_right]
    · rfl
    · rintro ⟨_, _, hl, hc⟩
      exact h.elim (fun h => h ((hwcomm _ _).mp hc)) (by unfold moleculePrecedes; omega)
  · have hw := (hwcomm _ _).mpr (Classical.byContradiction fun hn => h (Or.inl hn))
    simp only [canonicalIndex, orderedCoordinate, ht, hd, List.length_append, moleculeWord_length,
      Nat.add_sub_cancel_left]
    rw [ite_eq_left ⟨Nat.succ_pos _, by omega, noncanonical_strict_lengths r h, hw⟩]
    exact Prod.ext hw rfl

theorem infinite_quotient_restriction_map (n : ℕ) (a : I) :
    (infiniteSplitPi a).map (fun ω j => ω (quotientCoordinate j)) = quotientStaticMeasure n a := by
  have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  have hinj : Function.Injective (@quotientCoordinate n) :=
    fun _ _ he => Subtype.ext (congrArg (fun q : OrderedChannel n => q.1) (orderedCoordinate_injective n he))
  rw [(hi.precomp hinj).map_fun_eq_pi_map fun j => (measurable_pi_apply (quotientCoordinate j)).aemeasurable]
  simp_rw [infiniteSplitPi, Measure.infinitePi_map_eval]
  rfl

end RAFReactionQuotient
