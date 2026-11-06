
import proofs.RAFReactionQuotient.InfiniteSource
import proofs.RAFReactionQuotient.Surjectivity
import proofs.RAFReactionQuotient.CommutingUniqueness
import proofs.RAFReactionQuotient.SeedBulk
import proofs.HordijkSteelThreshold.RecordCylinderDeficit
import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.HordijkSteelThreshold.SplitPrefixIndependence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders




namespace RAFReactionQuotient

open MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

variable {n : ℕ}

noncomputable def orderedCoordinate  (r : OrderedChannel n)  :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

variable (r : Reaction n)

theorem orderedCoordinate_split   :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r := by
  apply Prod.ext
  · exact reaction_words_append r
  · exact molLength_reactionLeft r

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  obtain ⟨r,rfl⟩ := splitToOrdered_surjective n q
  obtain ⟨s,rfl⟩ := splitToOrdered_surjective n j
  grind [literalSplitCoordinate_injective, orderedCoordinate_split]

noncomputable def quotientCoordinate  (j : RepositoryChannel n)  :=
  orderedCoordinate ⟨j.val,j.property.1⟩



theorem word_comm_iff  (u v : Molecule n) :
    moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
  have := binaryWordCode_injective_length
    (s := moleculeWord u ++ moleculeWord v) (t := moleculeWord v ++ moleculeWord u) (by grind)
  grind [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length, displayedConcat]

theorem canonicalIndex_ordered  (r : OrderedChannel n) :
    canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r) := by
  
  have hv : 0 < molLength r.val.2 := Nat.succ_pos _
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
      grind [word_comm_iff]
    simp only [canonicalIndex, orderedCoordinate, List.length_append, moleculeWord_length]
    simp
    simp_all only
    rfl
  · rename_i h
    
    
    have hw := (word_comm_iff r.val.1 r.val.2).mpr (by tauto)
    simp only [canonicalIndex,orderedCoordinate,ht,hd,List.length_append,moleculeWord_length]
    simp
    rw [ite_eq_left ⟨Nat.succ_pos _,by omega,by
                                               grind [List.append_inj, moleculeWord_injective, moleculeWord_length],hw⟩]
    exact Prod.ext hw rfl

theorem infinite_quotient_restriction_map (n : ℕ) (a : I) :
    (infiniteSplitPi a).map (fun ω j => ω (quotientCoordinate j)) = quotientStaticMeasure n a := (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => ambientCoordLaw a)
    (by
       intro j k he
       exact Subtype.ext (congrArg (fun q : OrderedChannel n => q.val)
         (orderedCoordinate_injective n he)))).trans (Measure.infinitePi_eq_pi _)


variable (a : I)

noncomputable def quotientInfiniteMeasure   :=
  (infiniteSplitPi a).map quotientField

noncomputable instance quotientInfinite_probability (a : I) :
    IsProbabilityMeasure (quotientInfiniteMeasure a) := by
  unfold quotientInfiniteMeasure
  infer_instance

theorem quotientSurvival_eq  : quotientSurvival a =
    quotientInfiniteMeasure a {field | ReversibleUnbounded 2 field} := by
  rw [quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
    (measurableSet_reversibleUnbounded 2)]
  rfl

theorem quotientClosure_pullback {n L : ℕ} (q : _) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions (fun r => q (splitToQuotient r))) := by
  rw [← quotientClosure_OR]
  congr 2
  ext j
  simpa only [fieldOR, exists_eq_left] using
    (splitToQuotient_surjective n).exists (p := fun k => k = j ∧ q k)


variable (n L : ℕ)

theorem quotientClosure_restriction  (ω : SplitField) :
    quotientClosure n L (quotientOpen (fun j => ω (quotientCoordinate j))) =
      temporaryReactionClosure L (restrictedSplitReactions n (quotientField ω)) := by
  rw [quotientClosure_pullback]
  congr 1
  ext r
  simp [staticOpenReactions, restrictedSplitReactions]
  unfold quotientField
  apply Iff.of_eq
  simpa [literalSplitCoordinate] using congrArg ω ((orderedCoordinate_split r ▸ canonicalIndex_ordered (splitToOrdered r)).symm)



variable (L K : ℕ)

def quotientEscapeEvent   :=
  {q | ∃ x ∈ quotientClosure (2*(K+L)) L (quotientOpen q), K+L < (moleculeWord x).length}

theorem quotient_escape_measure_eq  (a : I) :
    quotientStaticMeasure _ a (quotientEscapeEvent L K) =
      quotientInfiniteMeasure a (reversibleEscapeEvent L K) := by
  let z0 := 2*(K+L)
  rw [← infinite_quotient_restriction_map z0 a,
    Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent L K)]
  congr 1
  ext ω
  change (∃ x ∈ quotientClosure _ L (quotientOpen fun j => ω (quotientCoordinate j)),
    K+L < (moleculeWord x).length) ↔
    ∃ w, K+L < w.length ∧ FiniteReversibleGenerated z0 L (quotientField ω) w
  rw [quotientClosure_restriction]
  simp only [finiteReversible_iff_literalClosure]
  aesop


end RAFReactionQuotient
