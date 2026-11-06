module

public import proofs.RAFCriticalWindowQuantitative.RecordIteration
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeedSurvival

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

noncomputable def escapeProbabilityWith (field : SplitField → InfiniteSplitEnvironment)
    (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (field ω) w}

/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

theorem explicit_truncation_with (field : SplitField → InfiniteSplitEnvironment)
    (hf : Measurable field) (survival : I → ENNReal) (L m : ℕ) (a : I) (r : ℕ)
    (hgood₀ : (infiniteSplitPi a).map field {f | ∀ v ∈ actualBinaryWords L,
      InfiniteReversibleGenerated 2 f v} ≤ survival a + (m : ENNReal)⁻¹)
    (hcontract : ∀ v, 0 < v.length → ∀ B, 2 ≤ B →
      infiniteSplitPi a (escapedMissingWith field (2*B+v.length) v) ≤
        infiniteSplitPi a (escapedMissingWith field B v) *
          (1-(toNNReal a : ENNReal)^(v.length+1))) :
    escapeProbabilityWith field a (recordCap L r) ≤ survival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  let K := recordCap L r
  let E : Set SplitField := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (field ω) w}
  let H : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (field ω) v}
  let G : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 (field ω) v}
  have hseed : ∀ v ∈ actualBinaryWords L, 0 < v.length ∧ v.length ≤ L := by
    intro v hv
    have hh := (mem_actualBinaryWords v L).mp hv
    exact ⟨List.length_pos_iff.mpr hh.1,hh.2⟩
  have hbad : infiniteSplitPi a (E ∩ Hᶜ) ≤
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
    have anti (v : List Bool) : Antitone (fun B => escapedMissingWith field B v) := by
      intro B N hBN ω hω
      obtain ⟨w,hw,hg⟩ := hω.1
      exact ⟨⟨w,by omega,hg⟩, fun hv => hω.2 (finiteReversibleGenerated_mono_cap hBN hv)⟩
    have repeated (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
        infiniteSplitPi a (escapedMissingWith field (recordCap v.length r) v) ≤
          (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
      induction r with
      | zero => simpa only [pow_zero] using
        (prob_le_one : infiniteSplitPi a (escapedMissingWith field (recordCap v.length 0) v) ≤ 1)
      | succ r ih =>
        calc
          _ ≤ infiniteSplitPi a (escapedMissingWith field (recordCap v.length r) v) *
              (1-(toNNReal a : ENNReal)^(v.length+1)) :=
            hcontract v hv _ (recordCap_ge_two _ _)
          _ ≤ (1-(toNNReal a : ENNReal)^(v.length+1))^r *
              (1-(toNNReal a : ENNReal)^(v.length+1)) := mul_le_mul' ih le_rfl
          _ = _ := (pow_succ _ _).symm
    have common (v : List Bool) (hv : 0 < v.length) (hvL : v.length ≤ L) :
        infiniteSplitPi a (escapedMissingWith field (recordCap L r) v) ≤
          (1-(toNNReal a : ENNReal)^(L+1))^r := by
      have hp : (toNNReal a : ENNReal)^(L+1) ≤ (toNNReal a : ENNReal)^(v.length+1) := by
        apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
        · exact_mod_cast a.property.2
        · omega
      exact ((measure_mono (anti v (recordCap_mono_length hvL r))).trans (repeated v hv r)).trans
        (pow_le_pow_left' (tsub_le_tsub_left hp 1) r)
    have hsub : {ω : SplitField |
        (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (field ω) w) ∧
        ¬ ∀ v ∈ actualBinaryWords L,
          FiniteReversibleGenerated (recordCap L r) 2 (field ω) v} ⊆
        ⋃ v ∈ actualBinaryWords L, escapedMissingWith field (recordCap L r) v := by
      intro ω hω
      push Not at hω
      obtain ⟨v,hv,hmissing⟩ := hω.2
      exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hω.1,hmissing⟩⟩
    calc
      _ ≤ infiniteSplitPi a (⋃ v ∈ actualBinaryWords L,
          escapedMissingWith field (recordCap L r) v) := measure_mono hsub
      _ ≤ ∑ v ∈ actualBinaryWords L, infiniteSplitPi a
          (escapedMissingWith field (recordCap L r) v) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _v ∈ actualBinaryWords L, (1-(toNNReal a : ENNReal)^(L+1))^r := by
        apply Finset.sum_le_sum
        intro v hv
        exact common v (hseed v hv).1 (hseed v hv).2
      _ = _ := by simp
  have hgood : infiniteSplitPi a H ≤ survival a + (m : ENNReal)⁻¹ := by
    have hmeas : MeasurableSet {f : InfiniteSplitEnvironment |
        ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 f v} := by
      have he : {f : InfiniteSplitEnvironment |
          ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 f v} =
          ⋂ v ∈ actualBinaryWords L, {f | InfiniteReversibleGenerated 2 f v} := by
        ext f
        simp
      rw [he]
      exact MeasurableSet.biInter (Finset.countable_toSet _) (fun v _ =>
        measurableSet_infiniteReversibleGenerated 2 v)
    rw [Measure.map_apply hf hmeas] at hgood₀
    apply (measure_mono (show H ⊆ G from ?_)).trans hgood₀
    intro ω hω v hv
    exact finiteReversibleGenerated_to_infinite (hω v hv)
  have hs : E ⊆ (E ∩ Hᶜ) ∪ H := by
    intro ω hω
    by_cases hh : ω ∈ H
    · exact Or.inr hh
    · exact Or.inl ⟨hω,hh⟩
  calc
    escapeProbabilityWith field a K ≤ infiniteSplitPi a ((E ∩ Hᶜ) ∪ H) := measure_mono hs
    _ ≤ infiniteSplitPi a (E ∩ Hᶜ) + infiniteSplitPi a H := measure_union_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hbad hgood

theorem explicit_split_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let L := 10*seedIndex q hq hq1 m
    splitEscapeProbability a (recordCap L r) ≤ staticSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  let L := 10*seedIndex q hq hq1 m
  exact explicit_truncation_with currySplitField measurable_currySplitField staticSurvival L m a r
    (effective_seed_probability_le_survival q hq hq1 m hm a ha)
    (fun v hv B hB => escaped_missing_contraction a v hv B hB)

end RAFCriticalWindowQuantitative
