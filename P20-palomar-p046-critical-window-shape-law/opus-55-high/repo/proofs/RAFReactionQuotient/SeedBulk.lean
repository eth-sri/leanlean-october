module

public import proofs.RAFReactionQuotient.ProductDomination
public import proofs.RAFReactionQuotient.History
public import proofs.RAFReactionQuotient.Fibres
public import proofs.HordijkSteelThreshold.StaticClosureMass

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Antitone E) :
    (Measure.pi $ fun j => ambientCoordLaw $ c j) {ω | E ω} ≤
      (Measure.pi $ fun j => ambientCoordLaw $ a j) {ω | E ω} := by
  have := product_increasing_mono a c hac (¬ E ·) fun x y h hx hy => hx $ hE h hy
  simp only [← Set.compl_ofPred, prob_compl_eq_one_sub (Set.toFinite _).measurableSet] at this
  exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).1 this

noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi (fun _ : RepositoryChannel n => ambientCoordLaw a)

variable {n : ℕ}

noncomputable def quotientOpen  (ω : RepositoryChannel n → Prop) :
    Finset (RepositoryChannel n) := Finset.univ.filter ω

theorem quotientOpen_OR  (ω : Reaction n → Prop) :
    quotientOpen (fieldOR splitToQuotient ω) =
      (staticOpenReactions ω).image splitToQuotient := by
  ext j
  simp [quotientOpen,fieldOR,staticOpenReactions,and_comm]


theorem quotientClosure_OR {n L : ℕ} (ω : Reaction n → Prop) :
    quotientClosure n L (quotientOpen $ fieldOR splitToQuotient ω) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
  rw [quotientOpen_OR]
  ext x
  simp only [mem_quotientClosure,mem_temporaryReactionClosure,split_closure_eq_quotient]

theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : RepositoryChannel n → Prop =>
      m*(quotientClosure n L $ quotientOpen ω).card < (m-1)*Fintype.card (Molecule n)) := by
  intro x y hxy hy
  have hs : quotientOpen x ⊆ quotientOpen y := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩
  have hc := Nat.mul_le_mul_left m $ Finset.card_le_card $ quotientClosure_mono n L hs
  omega

end RAFReactionQuotient
