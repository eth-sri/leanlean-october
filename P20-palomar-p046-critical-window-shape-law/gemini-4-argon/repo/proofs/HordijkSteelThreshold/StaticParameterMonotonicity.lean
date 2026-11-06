module

public import proofs.HordijkSteelThreshold.InfiniteSprinklingLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · exact ⟨0, Subtype.ext (by rw [sprinklingParameter_value]; simp [he])⟩
  · have hlt : (a : ℝ) < c := lt_of_le_of_ne hac (Subtype.ext_iff.not.mp he)
    have hd : 0 < 1 - (a : ℝ) := by have := c.2.2; linarith
    refine ⟨⟨((c : ℝ) - a) / (1 - (a : ℝ)), by positivity, (div_le_one hd).mpr (by have := c.2.2; linarith)⟩,
      Subtype.ext ?_⟩
    rw [sprinklingParameter_value]; dsimp; field_simp; nlinarith

theorem product_increasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} := by
  choose b hb using fun j => exists_sprinkling_increment (hac j)
  let μ j := (ambientCoordLaw (a j)).prod (ambientCoordLaw (b j))
  have : ∀ j, IsProbabilityMeasure (μ j) := fun j => by dsimp [μ]; infer_instance
  have h1 : (Measure.pi μ).map (fun ω j => (ω j).1) = Measure.pi (fun j => ambientCoordLaw (a j)) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun _ (z : Prop × Prop) => z.1) fun _ => measurable_fst.aemeasurable]
    simp [μ]
  have h2 : (Measure.pi μ).map (fun ω j => (ω j).1 ∨ (ω j).2) = Measure.pi (fun j => ambientCoordLaw (c j)) := by
    rw [Measure.pi_map_pi (μ := μ) (f := fun _ (z : Prop × Prop) => z.1 ∨ z.2) fun _ => (measurable_of_finite _).aemeasurable]
    simp only [μ, ambientCoordLaw_union, hb]
  rw [← h1, ← h2, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  exact measure_mono fun _ h => hE (fun _ => Or.inl) h

theorem static_increasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :
    staticReactionMeasure N a {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N c {ω | P (staticOpenReactions ω)} := by
  simp only [staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact product_increasing_mono _ _ (fun _ => hac) _ fun x y hxy =>
    hP fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy r (Finset.mem_filter.mp hr).2⟩

end HordijkSteelThreshold
