module

public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

abbrev SplitField := (List Bool × ℕ) → Prop

variable (P : Finset $ List Bool × ℕ) (E : Set SplitField)

def SplitPrefixDetermined  : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

variable (a : I)

theorem split_support_open_measure  (T : Finset $ List Bool × ℕ) :
    infiniteSplitPi a {ω | ∀ z ∈ T, ω z} = (toNNReal a : ENNReal)^T.card := by
  have := Measure.infinitePi_pi (fun _ : List Bool × ℕ => ambientCoordLaw a) (s := T)
    (t := fun _ => {True}) fun _ _ => .singleton True
  simp_all [infiniteSplitPi, Set.pi, ambientCoordLaw]

theorem split_prefix_event_representation
    (hE : SplitPrefixDetermined P E) :
    ∃ e : (P → Prop) → Prop, E = {ω | e $ fun z => ω z.val} := by
  let extend : (P → Prop) → SplitField := fun η z => if h : z ∈ P then η ⟨z,h⟩ else False
  refine ⟨fun η => extend η ∈ E, ?_⟩
  ext ω
  apply hE
  grind


theorem split_prefix_failure_measure  (P T : Finset $ List Bool × ℕ)
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^T.card) := by
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  have hp := (((iIndepFun_infinitePi (P := fun _ : List Bool × ℕ => ambientCoordLaw a)
    fun _ => measurable_id).indepFun_finset P T hPT measurable_pi_apply).comp
    (measurable_of_finite e) (measurable_of_finite fun η : T → Prop => ¬ ∀ z, η z)
    ).measure_inter_preimage_eq_mul {True} {True} (.singleton True) $ .singleton True
  have hm : MeasurableSet {ω : SplitField | ∀ z ∈ T, ω z} := by
    convert MeasurableSet.pi T.countable_toSet fun _ _ => MeasurableSet.singleton True
    simp [Set.pi]
  rw [← split_support_open_measure, ← prob_compl_eq_one_sub hm]
  subst he
  convert hp using 3 <;> first | rfl | (ext; simp)

end HordijkSteelThreshold
