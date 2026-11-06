module

public import proofs.RAFCriticalWindowQuantitative.RecordIteration
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

theorem explicit_truncation_idx (idx : List Bool × ℕ → List Bool × ℕ)
    (hprod : ∀ z, (idx z).1 = z.1)
    (hpref : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (hmf : Measurable (idxField idx)) (a : I) (S : ENNReal) (m L r : ℕ)
    (hi : (infiniteSplitPi a).map (idxField idx)
      {field | ∀ w ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field w} ≤ S + (m : ENNReal)⁻¹) :
    infiniteSplitPi a {ω | ∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (idxField idx ω) w} ≤
      S + (m : ENNReal)⁻¹ + ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  let K := recordCap L r
  let E : Set SplitField := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (idxField idx ω) w}
  let H : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (idxField idx ω) v}
  have hbad : infiniteSplitPi a (E ∩ Hᶜ) ≤
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
    finite_seed_failure_idx idx hprod hpref a (actualBinaryWords L) L
      (fun v hv => let hh := (mem_actualBinaryWords v L).mp hv; ⟨List.length_pos_iff.mpr hh.1, hh.2⟩) r
  have hmeas : MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} := by
    rw [show {field : InfiniteSplitEnvironment | ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} =
      ⋂ v ∈ actualBinaryWords L, {field | InfiniteReversibleGenerated 2 field v} by ext; simp]
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun v _ => measurableSet_infiniteReversibleGenerated 2 v
  rw [Measure.map_apply hmf hmeas] at hi
  have hgood : infiniteSplitPi a H ≤ S + (m : ENNReal)⁻¹ :=
    (measure_mono (show H ⊆ _ from fun ω hω v hv => finiteReversibleGenerated_to_infinite (hω v hv))).trans hi
  have hs : E ⊆ (E ∩ Hᶜ) ∪ H := fun ω hω => by by_cases hh : ω ∈ H; exact Or.inr hh; exact Or.inl ⟨hω, hh⟩
  exact (measure_mono hs).trans ((measure_union_le _ _).trans (by simpa [add_comm] using add_le_add hbad hgood))

theorem explicit_split_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let L := 10*seedIndex q hq hq1 m
    splitEscapeProbability a (recordCap L r) ≤ staticSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
  explicit_truncation_idx id (fun _ => rfl) (fun h => h) measurable_currySplitField a (staticSurvival a) m _ r
    (effective_seed_probability_le_survival q hq hq1 m hm a ha)

end RAFCriticalWindowQuantitative
