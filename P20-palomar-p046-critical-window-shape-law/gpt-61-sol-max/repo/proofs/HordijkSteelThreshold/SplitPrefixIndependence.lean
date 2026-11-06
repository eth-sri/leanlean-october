
import proofs.HordijkSteelThreshold.InfiniteStaticLaw




namespace HordijkSteelThreshold
open MeasureTheory ProbabilityTheory unitInterval

abbrev SplitField := (List Bool × ℕ) → Prop

variable (P : Finset (List Bool × ℕ)) (E : Set SplitField)

def SplitPrefixDetermined  : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

variable (a : I)

theorem split_prefix_event_representation 
    (hE : SplitPrefixDetermined P E) :
    ∃ e : (P → Prop) → Prop, E = {ω | e (fun z => ω z.val)} := by
  let extend : (P → Prop) → SplitField := fun η z => if h : z ∈ P then η ⟨z,h⟩ else False
  refine ⟨fun η => extend η ∈ E, ?_⟩
  ext ω
  apply hE
  intro z hz
  simp [extend,hz]

theorem split_prefix_failure_measure  (P T : _)
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1-toNNReal a^T.card) := by
  let z0 := MeasurableSet.singleton True
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  have hi : iIndepFun (fun z ω => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  have ht := hi.indepFun_finset P T hPT measurable_pi_apply
  let g : (T → Prop) → Prop := fun η => ¬ ∀ z, η z
  have hind := ht.comp (measurable_of_finite e) (measurable_of_finite g)
  have hp := hind.measure_inter_preimage_eq_mul {True} {True}
    z0 z0
  have hfail : infiniteSplitPi a {ω | ¬ ∀ z ∈ T, ω z} =
      1-toNNReal a^T.card := by
    
    change infiniteSplitPi a {ω | ∀ z ∈ T, ω z}ᶜ = _
    rw [measure_compl (by measurability) (measure_ne_top _ _), measure_univ]
    congr 1
    simpa [infiniteSplitPi, Set.pi, ambientCoordLaw] using
      (Measure.infinitePi_pi (μ := fun _ : List Bool × ℕ => ambientCoordLaw a)
        (s := T) (t := fun _ => {True}) fun _ _ => MeasurableSet.singleton True)
  measurability

end HordijkSteelThreshold
