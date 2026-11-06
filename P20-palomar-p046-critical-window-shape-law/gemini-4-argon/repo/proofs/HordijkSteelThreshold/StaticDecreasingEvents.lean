module

public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Antitone E) :
    (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} := by
  have hi := product_increasing_mono a c hac (fun ω => ¬ E ω) fun _ _ hxy hx hy => hx (hE hxy hy)
  have hc (q : J → I) : (Measure.pi (fun j => ambientCoordLaw (q j))) {ω | E ω} =
      1 - (Measure.pi (fun j => ambientCoordLaw (q j))) {ω | ¬ E ω} := by
    rw [show {ω | E ω} = {ω | ¬ E ω}ᶜ by ext; simp,
      measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _), measure_univ]
  rw [hc a, hc c]
  exact tsub_le_tsub_left hi 1

theorem static_decreasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Antitone P) :
    staticReactionMeasure N c {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | P (staticOpenReactions ω)} := by
  simp only [staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact product_decreasing_mono _ _ (fun _ => hac) _ fun x y hxy =>
    hP fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy r (Finset.mem_filter.mp hr).2⟩

end HordijkSteelThreshold
