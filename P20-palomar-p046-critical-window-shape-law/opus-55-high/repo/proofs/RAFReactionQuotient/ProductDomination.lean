module

public import proofs.RAFReactionQuotient.ORDistribution
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

/-- Finite inhomogeneous Bernoulli product laws are ordered on increasing events. -/
theorem product_increasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    (Measure.pi $ fun j => ambientCoordLaw $ a j) {ω | E ω} ≤
      (Measure.pi $ fun j => ambientCoordLaw $ c j) {ω | E ω} := by
  choose b hb using fun j => exists_sprinkling_increment $ hac j
  let μ : J → Measure (Prop × Prop) := fun j =>
    (ambientCoordLaw $ a j).prod $ ambientCoordLaw $ b j
  have hleft : (Measure.pi μ).map (fun ω j => (ω j).1) =
      Measure.pi (ambientCoordLaw $ a ·) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun (_ : J) (z : Prop × Prop) => z.1)
      (fun _ => measurable_fst.aemeasurable)]
    aesop
  have hunion : (Measure.pi μ).map (fun ω j => (ω j).1 ∨ (ω j).2) =
      Measure.pi (ambientCoordLaw $ c ·) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun _ z => z.1 ∨ z.2)
      (fun _ => (measurable_of_finite _).aemeasurable)]
    simp only [μ, ambientCoordLaw_union, hb]
  rw [← hleft, ← hunion,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  apply measure_mono
  intro ω hω
  exact hE (fun _ h => Or.inl h) hω

noncomputable def halfParameter (a : I) : I := ⟨(a : ℝ)/2, by
  constructor
  · exact div_nonneg a.property.1 $ by norm_num
  · have := a.property.2; linarith⟩

theorem fibreParameter_half_le {R J : Type*} [Fintype R]
    (π : R → J) (a : I) (j : J)
    (hm : (Finset.univ.filter $ fun r => π r = j).card ≤ 2) :
    fibreParameter π (halfParameter a) j ≤ a := by
  change (fibreParameter π (halfParameter a) j) ≤ (a : ℝ)
  have ha0 := a.property.1
  let m := (Finset.univ.filter $ fun r => π r = j).card
  change 1-(1-a/2)^m ≤ (a : ℝ)
  have hm' : m ≤ 2 := hm
  interval_cases m <;> norm_num <;> nlinarith

end RAFReactionQuotient
