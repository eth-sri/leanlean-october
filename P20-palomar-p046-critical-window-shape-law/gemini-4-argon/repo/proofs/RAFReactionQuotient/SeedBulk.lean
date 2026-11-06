module

public import proofs.RAFReactionQuotient.ProductDomination
public import proofs.RAFReactionQuotient.History
public import proofs.RAFReactionQuotient.Fibres
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi (fun _ : RepositoryChannel n => ambientCoordLaw a)

noncomputable def quotientOpen {n : ℕ} (ω : RepositoryChannel n → Prop) :
    Finset (RepositoryChannel n) := Finset.univ.filter ω

theorem quotientOpen_OR {n : ℕ} (ω : Reaction n → Prop) :
    quotientOpen (fieldOR splitToQuotient ω) =
      (staticOpenReactions ω).image splitToQuotient := by
  ext j; simp [quotientOpen, fieldOR, staticOpenReactions, and_comm]

theorem quotientClosure_OR {n L : ℕ} (ω : Reaction n → Prop) :
    quotientClosure n L (quotientOpen (fieldOR splitToQuotient ω)) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
  rw [quotientOpen_OR]; ext x
  simp only [mem_quotientClosure, mem_temporaryReactionClosure, split_closure_eq_quotient]

theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : RepositoryChannel n → Prop =>
      m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)) :=
  fun _ _ hxy hy => lt_of_le_of_lt (Nat.mul_le_mul_left m (Finset.card_le_card (quotientClosure_mono n L
    fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy j (Finset.mem_filter.mp hj).2⟩))) hy

end RAFReactionQuotient
