
import proofs.HordijkSteelThreshold.AmbientIndependence
import proofs.HordijkSteelThreshold.RandomBaseSprinkling
import Mathlib.MeasureTheory.Constructions.Pi




namespace HordijkSteelThreshold

open MeasureTheory unitInterval

variable (a b : I)

def sprinklingParameter   := σ (σ a * σ b)

theorem sprinklingParameter_value  :
    sprinklingParameter a b = a + (1-a)*(b : ℝ) := by
  simp_all [sprinklingParameter]; grind

/-- Exact law of the union of two independent Bernoulli coordinates. -/
theorem ambientCoordLaw_union  :
    ((ambientCoordLaw a).prod (ambientCoordLaw b)).map (fun p : _ => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton False)]
  have he : (fun p : _ => p.1 ∨ p.2) ⁻¹' {False} =
      {False} ×ˢ {False} := by measurability
  rw [he, Measure.prod_prod]
  simp [ambientCoordLaw, sprinklingParameter]
  rfl

open Classical RAF.Polymer

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · refine ⟨0, ?_⟩
    grind [sprinklingParameter]
  · have hlt : (a : ℝ) < c := show a < c from lt_of_le_of_ne hac he
    have hd : 0 < 1-(a : ℝ) := by grind
    let b : I := ⟨(c-a)/(1-a), by
      constructor
      · positivity
      · apply (div_le_one hd).mpr
        have hc := c.property.2
        linarith⟩
    refine ⟨b, ?_⟩
    grind [sprinklingParameter_value]

/-- Finite inhomogeneous Bernoulli product laws are ordered on increasing events. -/
theorem product_increasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : _) (hE : Monotone E) :
    (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} := by
  choose b hb using fun j => exists_sprinkling_increment (hac j)
  let μ  := fun j =>
    (ambientCoordLaw (a j)).prod (ambientCoordLaw (b j))
  
  have hleft : (Measure.pi μ).map (fun ω j => (ω j).1) =
      Measure.pi fun j => ambientCoordLaw (a j) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun _ z => z.1)
      fun _ => measurable_fst.aemeasurable]
    simp [μ]
  have hunion : (Measure.pi μ).map (fun ω j => (ω j).1 ∨ (ω j).2) =
      Measure.pi fun j => ambientCoordLaw (c j) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun _ z => z.1 ∨ z.2)
      fun _ => (by measurability)]
    simp [μ, ambientCoordLaw_union, hb]
  rw [← hleft, ← hunion,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  apply measure_mono
  intro ω hω
  exact hE (fun _ h => Or.inl h) hω

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : _) (hE : Antitone E) :
    (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} := by
  have hi := tsub_le_tsub_left (product_increasing_mono a c hac (fun ω => ¬ E ω) (by tauto)) 1
  simpa only [← prob_compl_eq_one_sub (Set.toFinite _).measurableSet,
    Set.compl_ofPred, not_not] using hi

variable (N : ℕ)

abbrev static_increasing_event_mono {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :=
  product_increasing_mono (fun _ : Reaction N => a) (fun _ => c) (fun _ => hac)
    (fun ω => P (staticOpenReactions ω)) (by
      intro x y hxy
      exact hP (Finset.monotone_filter_right _ fun r _ => @hxy r))

abbrev static_decreasing_event_mono {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Antitone P) :=
  product_decreasing_mono (fun _ : Reaction N => a) (fun _ => c) (fun _ => hac)
    (fun ω => P (staticOpenReactions ω)) (by
      intro x y hxy
      exact hP (Finset.monotone_filter_right _ fun r _ => @hxy r))

end HordijkSteelThreshold
