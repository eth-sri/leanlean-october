module

public import proofs.RAF.Concrete.PolymerCRS
public import Mathlib
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section

namespace HordijkSteelThreshold
open MeasureTheory unitInterval MeasureTheory.Measure

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

/-- A finite catalogue of independent channels. -/
noncomputable abbrev finiteFieldLaw {J : Type*} [Fintype J] (a : I) : Measure (J → Prop) :=
  Measure.pi (fun _ => ambientCoordLaw a)

noncomputable def openChannels {J : Type*} [Fintype J] (q : J → Prop) : Finset J :=
  @Finset.filter J q (fun _ => Classical.propDecidable _) Finset.univ

@[simp] theorem mem_openChannels {J : Type*} [Fintype J] (q : J → Prop) (j : J) :
    j ∈ openChannels q ↔ q j := by simp [openChannels]

@[simp] theorem ambientCoordLaw_false (p : I) :
    ambientCoordLaw p {False} = toNNReal (σ p) := by
  simp [ambientCoordLaw]

theorem measure_le_add_of_cover {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E A B : Set Ω} {u v : ENNReal} (h : E ⊆ A ∪ B) (hA : μ A ≤ u) (hB : μ B ≤ v) :
    μ E ≤ u+v := by grw [measure_mono h, measure_union_le, hA, hB]

/-- A uniform union bound with one possible witness in a finite list of events. -/
theorem measure_le_card_mul {Ω J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Set Ω} {δ : ENNReal} (s : Finset J) (B : J → Set Ω)
    (cover : ∀ ω ∈ E, ∃ j ∈ s, ω ∈ B j) (bound : ∀ j ∈ s, μ (B j) ≤ δ) :
    μ E ≤ (s.card : ENNReal)*δ :=
  (measure_mono (t := ⋃ j ∈ s, B j) fun ω h => (by simp_all)).trans
    ((measure_biUnion_finset_le s B).trans (by simpa [nsmul_eq_mul] using s.sum_le_card_nsmul _ _ bound))

@[simp] theorem ambientCoordLaw_true (p : I) : ambientCoordLaw p {True} = toNNReal p := by
  simp [ambientCoordLaw]

def blockEvent {J : Type*} (T : Finset J) (b : Prop) : Set (J → Prop) :=
  (T : Set J).pi fun _ => {b}

theorem iid_block {J : Type*} (p : I) (T : Finset J) (P : Prop) :
    MeasurableSet (blockEvent T P) ∧
      (Measure.infinitePi fun _ : J => ambientCoordLaw p) (blockEvent T P) =
        (ambientCoordLaw p {P})^T.card := by
  exact ⟨.pi T.countable_toSet (by simp), by simp [blockEvent, infinitePi_pi]⟩

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro q
  obtain rfl | rfl := Classical.propComplete q
  · rw [show ({True} : Set Prop) = {False}ᶜ by ext; simp]
    simp only [measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _), measure_univ, h]
  · exact h


/-- Use the same uniform coordinate for both thresholds. -/
theorem product_increasing_mono {J : Type*} [Fintype J] {a c : I} (hac : a ≤ c)
    {E : (J → Prop) → Prop} (hE : Monotone E) :
    finiteFieldLaw a {ω | E ω} ≤ finiteFieldLaw c {ω | E ω} := by
  let μ := Measure.pi (fun _ : J => (volume : Measure I))
  have h (p : I) : finiteFieldLaw p {ω | E ω} = μ {ω | E (fun j => ω j ≤ p)} := by
    have hm : Measurable (fun x : I => x ≤ p) := measurableSet_setOfPred.mp measurableSet_Iic
    have hmap : (volume : Measure I).map (fun x => x ≤ p) = ambientCoordLaw p := by
      have : IsProbabilityMeasure ((volume : Measure I).map (fun x => x ≤ p)) :=
        (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
      apply probability_prop_eq_of_false
      simp_all [Measure.map_apply hm (MeasurableSet.singleton False),
        show (fun x : I => x ≤ p) ⁻¹' {False} = Set.Ioi p by ext; simp,
        volume_Ioi, ambientCoordLaw_false, ← ENNReal.ofReal_coe_nnreal]
    simp_rw [finiteFieldLaw, ← hmap]
    rw [← pi_map_pi (fun _ => hm.aemeasurable)]
    exact Measure.map_apply (by fun_prop) .of_discrete
  rw [h a, h c]
  exact measure_mono fun ω hω => hE (fun j hj => le_trans hj hac) hω

end HordijkSteelThreshold
