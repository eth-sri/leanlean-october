module
public import Mathlib

/-! Bernoulli coordinates: restrictions, independent rows and finite all-open tests. -/

@[expose] public section

namespace HordijkSteelThreshold
open MeasureTheory ProbabilityTheory unitInterval

/-- Enumerate a finite space in order of any integer-valued statistic. -/
lemma enumerate_by {X : Type*} [Fintype X] (rank : X → ℕ) :
    ∃ e : Fin (Fintype.card X) ≃ X, Monotone (rank ∘ e) :=
  let e := (Fintype.equivFin X).symm
  ⟨(Tuple.sort (rank ∘ e)).trans e,Tuple.monotone_sort (rank ∘ e)⟩

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

end HordijkSteelThreshold

namespace RAFEmergenceApprox.Generic
open MeasureTheory HordijkSteelThreshold unitInterval
variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable def colLaw (X : Type*) [Fintype X] (p : I) : Measure (X → Prop) :=
  Measure.pi (fun _ : X => ambientCoordLaw p)

instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance

noncomputable def law (p : R → I) : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))

instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

noncomputable abbrev iid (X R : Type*) [Fintype X] [Fintype R] (p : I) := law (X := X) (fun _ : R => p)

end RAFEmergenceApprox.Generic

namespace HordijkSteelThreshold
open MeasureTheory ProbabilityTheory unitInterval RAFEmergenceApprox.Generic
variable (a : I)

noncomputable abbrev missRate (k : ℕ) := 1-(toNNReal a : ENNReal)^k

lemma openWeight_le_one : (toNNReal a : ENNReal) ≤ 1 := by exact_mod_cast a.2.2
@[simp] lemma miss_toReal (k : ℕ) : (missRate a k).toReal = 1-(a:ℝ)^k := by
  simp [missRate,ENNReal.toReal_sub_of_le (pow_le_one₀ bot_le (openWeight_le_one a))]

lemma miss_mono : Monotone (missRate a) := fun _ _ h =>
  tsub_le_tsub_left (pow_le_pow_of_le_one bot_le (openWeight_le_one a) h) _

/-- All channels in a finite support open simultaneously. -/
lemma all_open {J : Type*} [Fintype J] (T : Finset J) :
    (colLaw J a) {ω | ∀ j ∈ T, ω j} = (toNNReal a : ENNReal)^T.card := by
  rw [show {ω : J → Prop | ∀ j ∈ T, ω j} = (T : Set J).pi (fun _ => {True}) by grind,colLaw,Measure.pi_pi_finset]
  simp [ambientCoordLaw]

@[simp] lemma fail_open (J : Type*) [Fintype J] :
    (colLaw J a) {v | ∀ j, v j}ᶜ = missRate a (Fintype.card J) := by
  rw [measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),measure_univ]
  congr 1; simpa using all_open a (Finset.univ : Finset J)

noncomputable abbrev fieldLaw (C : Type*) (p : I) := Measure.infinitePi fun _ : C => ambientCoordLaw p

/-- Reading distinct indices in an iid field yields the finite product law. -/
lemma iid_read {C J : Type*} [Fintype J] (f : J → C) (hf : Function.Injective f) :
    MeasurePreserving (fun (ω : C → Prop) j => ω (f j)) (fieldLaw C a) (colLaw J a) := by
  refine ⟨by fun_prop,?_⟩
  exact (Measure.map_infinitePi_infinitePi_of_inj hf).trans (Measure.infinitePi_eq_pi _)

/-- Reading a rectangular array of distinct marks gives a product of iid rows. -/
lemma iid_rows {C J D : Type*} [Fintype J] [Fintype D] (f : J × D → C) (hf : Function.Injective f) :
    MeasurePreserving (fun (ω : C → Prop) j d => ω (f (j,d))) (fieldLaw C a) (iid D J a) := by
  apply MeasurePreserving.comp (g := MeasurableEquiv.curry J D Prop) _ (iid_read a f hf)
  refine ⟨(MeasurableEquiv.curry ..).measurable,?_⟩
  simpa [iid,law,colLaw,Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry (fun (_ : J) (_ : D) => ambientCoordLaw a)

@[simp] theorem ambientCoordLaw_false :
    ambientCoordLaw a {False} = toNNReal (σ a) := by
  simp [ambientCoordLaw]

open Classical
/-- The two set samples are simply the two summands of one iid function. -/
lemma split_sets {S D : Type*} [Fintype S] [Fintype D] :
    MeasurePreserving (fun (ω : S ⊕ D → Prop) => ({s | ω (.inl s)}, {d | ω (.inr d)}))
      (fieldLaw (S ⊕ D) a) ((setBernoulli Set.univ a).prod (setBernoulli Set.univ a)) := by
  rw [fieldLaw,Measure.infinitePi_eq_pi]
  apply (MeasurePreserving.prod ?_ ?_).comp (measurePreserving_sumPiEquivProdPi fun _ => ambientCoordLaw a)
  all_goals exact ⟨measurable_of_finite _, by rw [setBernoulli_eq_map,Measure.infinitePi_eq_pi]; rfl⟩

end HordijkSteelThreshold

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAFEmergenceApprox.Generic

theorem measure_alternatives {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E A B : Set Ω}
    (h : ∀ ω ∈ E, ω ∉ A → ω ∈ B) : μ E ≤ μ A + μ B :=
  (measure_mono fun ω he => Classical.or_iff_not_imp_left.mpr (h ω he)).trans (measure_union_le A B)

/-- Union bound for a finite cover with a uniform bound on each piece. -/
lemma finite_cover {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] (μ : Measure Ω) {E : Set Ω}
    (S : J → Set Ω) (h : ∀ ω ∈ E, ∃ j, ω ∈ S j) {b : ENNReal} (hb : ∀ j, μ (S j) ≤ b) :
    μ E ≤ Fintype.card J * b :=
  (measure_mono fun ω he => Set.mem_iUnion.mpr (h ω he)).trans <| (measure_iUnion_fintype_le μ S).trans
    ((Finset.sum_le_sum (fun j _ => hb j)).trans_eq (by simp))

/-- Finite events can be pulled back under a law without measurability side conditions. -/
lemma _root_.MeasureTheory.MeasurePreserving.finite_event {Ω J : Type*} [MeasurableSpace Ω] [MeasurableSpace J]
    [Finite J] [MeasurableSingletonClass J] {f : Ω → J} {μ ν} (hf : MeasurePreserving f μ ν) (s : Set J) :
    μ (f ⁻¹' s) = ν s := hf.measure_preimage (Set.toFinite s).measurableSet.nullMeasurableSet

theorem finite_many_open_probability (J : Type*) [Fintype J] (a : I) (r : ℕ) :
    colLaw J a {ω | r ≤ (Finset.univ.filter ω).card} ≤
      ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let P := (Finset.univ : Finset J).powersetCard r
  refine (finite_cover (b := (toNNReal a : ENNReal)^r) _ (fun T : P => {ω | ∀ j ∈ T.val, ω j}) ?_ ?_).trans_eq ?_
  · intro ω h
    obtain ⟨T,hs,hc⟩ := Finset.exists_subset_card_eq h
    exact ⟨⟨T,by simp [P,hc]⟩,by grind⟩
  · intro T; rw [all_open,(Finset.mem_powersetCard.mp T.property).2]
  · simp [P]

end RAFCriticalWindowQuantitative
