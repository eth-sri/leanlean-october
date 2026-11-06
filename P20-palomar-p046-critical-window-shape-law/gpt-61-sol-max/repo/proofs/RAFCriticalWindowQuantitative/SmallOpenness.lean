import proofs.HordijkSteelThreshold.StaticEventContinuity
import proofs.RAFCriticalWindowQuantitative.SparseClosure
import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure
import proofs.HordijkSteelThreshold.StaticSurvivalContinuity
import proofs.RAFReactionQuotient.SurvivalContinuity


namespace RAFCriticalWindowQuantitative

open Classical HordijkSteelThreshold MeasureTheory unitInterval

variable (J : Type*)

variable [Fintype J] (a : I)

theorem finite_support_open_probability   (T : Finset J) :
    (Measure.pi (fun _ : J => ambientCoordLaw a)) {ω | ∀ j ∈ T, ω j} = toNNReal a^T.card := by
  change (Measure.pi fun _ : J => ambientCoordLaw a) ((T : Set J).pi fun _ => {P | P}) = _
  simp [ambientCoordLaw]

theorem finite_many_open_probability   (r : ℕ) :
    (Measure.pi (fun _ : J => ambientCoordLaw a))
      {ω | r ≤ (Finset.univ.filter (ω)).card} ≤
      (Fintype.card J).choose r*toNNReal a^r := by
  let μ := Measure.pi fun _ : J => ambientCoordLaw a
  let P := (Finset.univ : Finset J).powersetCard r
  have hs : {ω : _ | r ≤ (Finset.univ.filter ω).card} ⊆
      ⋃ T ∈ P, {ω | ∀ j ∈ T, ω j} := by
    intro ω hω
    obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hω
    refine Set.mem_iUnion.mpr ⟨T,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · measurability
    grind
  calc
    _ ≤ μ (⋃ T ∈ P, {ω | ∀ j ∈ T, ω j}) := measure_mono hs
    _ ≤ ∑ T ∈ P, μ {ω | ∀ j ∈ T, ω j} := measure_biUnion_finset_le _ _
    _ = ∑ _T ∈ P, (toNNReal a : ENNReal)^r := by
      apply Finset.sum_congr rfl
      grind [finite_support_open_probability]
    _ = _ := by simp [P]

open RAFReactionQuotient RAF.Polymer
open OverlapCorrectedRAF.Source

def sparseWitnessCap (r : ℕ)  := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ)  := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ)  := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

variable (a : I) (r : ℕ)

theorem split_sparse_probability  :
    staticSurvival a ≤ splitSparseCoefficient r*toNNReal a^r := by
  let K := 2^(r+1)
  let N := 2*(K+2)
  have hs : staticEscapeEvent 2 K ⊆
      {ω | r ≤ (Finset.univ.filter ω).card} := by
    intro ω hω
    obtain ⟨x,hx,hlen⟩ := hω
    rw [moleculeWord_length] at hlen
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp
      ((lt_of_le_of_lt (Nat.le_add_right K 2) hlen).trans_le (sparse_closure_length N (staticOpenReactions ω) x hx))
    exact (Nat.lt_of_succ_lt_succ this).le
  apply (staticSurvival_le_finite_escape a K).trans
  apply (measure_mono hs).trans
  simpa +instances [staticReactionMeasure, splitSparseCoefficient, sparseWitnessCap, ENNReal.instPartialOrder] using
    finite_many_open_probability (Reaction N) a r

abbrev quotient_sparse_probability   := by
  let K := 2^(r+1)
  let N := 2*(K+2)
  
  apply (quotientSurvival_le_finite_escape a K).trans
  exact (measure_mono (by
                        intro ω hω
                        obtain ⟨x,hx,hlen⟩ := hω
                        rw [moleculeWord_length] at hlen
                        have := (Nat.pow_lt_pow_iff_right (by decide)).mp
                          ((lt_of_le_of_lt (Nat.le_add_right K 2) hlen).trans_le (quotient_sparse_closure_length N (quotientOpen ω) x hx))
                        exact (Nat.lt_of_succ_lt_succ this).le)).trans (finite_many_open_probability (RepositoryChannel N) a r)

abbrev split_sparse_real   := by
  
  simpa using ENNReal.toReal_mono (by finiteness) (split_sparse_probability a r)

abbrev quotient_sparse_real   := by
  
  simpa using ENNReal.toReal_mono (by finiteness) (quotient_sparse_probability a r)


end RAFCriticalWindowQuantitative
