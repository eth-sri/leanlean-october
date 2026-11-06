import proofs.RAFCriticalWindowQuantitative.RecordIteration
import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
import proofs.HordijkSteelThreshold.StaticSeedMassBound
import proofs.HordijkSteelThreshold.AmbientEscapeBound
import proofs.HordijkSteelThreshold.SourceTerminalRAF
import proofs.RAFCriticalWindowQuantitative.RecordContraction
import proofs.RAFReactionQuotient.InfiniteSource
import proofs.HordijkSteelThreshold.RecordCylinderDeficit
import proofs.HordijkSteelThreshold.RecordTargetTrial
import proofs.HordijkSteelThreshold.SplitPrefixIndependence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import proofs.RAFCriticalWindowQuantitative.FiniteRepair
import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
import proofs.RAFReactionQuotient.SeedApproximation
import proofs.HordijkSteelThreshold.StaticSurvivalContinuity


namespace RAFCriticalWindowQuantitative




open HordijkSteelThreshold unitInterval

open Filter MeasureTheory RAF.Polymer RAF.Concrete in
theorem seed_survival_bound (μ : Measure InfiniteSplitEnvironment) [IsFiniteMeasure μ]
    (L m : ℕ) (hm : 2 ≤ m)
    (hbad : ∀ N, 0 < N → μ {field |
      MassDeficit m (temporaryReactionClosure L (restrictedSplitReactions N field))} ≤ (m : ENNReal)⁻¹) :
    μ {field | ∀ w ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field w} ≤
      μ {field | ReversibleUnbounded 2 field} + (m : ENNReal)⁻¹ := by
  refine ge_of_tendsto' ((reversible_escape_probability_tendsto μ 2).add_const (m : ENNReal)⁻¹)
    fun K => ?_
  simp only [finite_seed_common_cap, ← Set.iUnion_ofPred]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := μ) ?_) ?_
  · intro N M h field hg w hw
    exact finiteReversibleGenerated_mono_cap h (hg w hw)
  · filter_upwards [tendsto_atTop.mp card_molecule_tendsto_atTop
      (m*Fintype.card (Molecule (K+2))+1), eventually_ge_atTop 1] with N hlarge hN
    refine (measure_mono ?_).trans
      ((food_seed_mass_bound N L m μ (restrictedSplitReactions N)).trans
        (add_le_add ?_ (hbad N (by omega))))
    · intro field hseed x hx
      obtain ⟨y, hy, he⟩ := finiteReversible_to_literalClosure (hseed _
        ((mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x,
          by simpa [moleculeWord_length] using (Finset.mem_filter.mp hx).2⟩))
      exact moleculeWord_injective he ▸ hy
    · apply measure_mono
      intro field hg
      let S := temporaryReactionClosure 2 (restrictedSplitReactions N field)
      change NearFull m S at hg
      have hc : Fintype.card (Molecule (K+2)) < S.card := by
        have hm' : _ ≤ (m-1)*Fintype.card (Molecule N) := Nat.le_mul_of_pos_left _ (by omega)
        nlinarith
      obtain ⟨x,hx,hl⟩ : ∃ x ∈ S, K+2 < molLength x := by
        simpa [binaryFood] using
          Finset.exists_mem_notMem_of_card_lt_card ((binaryFood_card_le_cutoff N (K+2)).trans_lt hc)
      apply (reversibleEscapeEvent_iff 2 K field).mpr
      exact ⟨moleculeWord x, by simpa [moleculeWord_length] using hl,
        finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible field x hx)⟩

/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def splitEscapeProbability (a : I) (K : ℕ)  :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}


open RAFReactionQuotient

def quotientPrefixIndex : PrefixIndex :=
  ⟨canonicalIndex,canonicalIndex_product,canonicalIndex_prefix⟩







/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def quotientEscapeProbability (a : I) (K : ℕ)  :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}


open MeasureTheory

variable (a : I) (K : ℕ)

theorem split_escape_finite  (hK : 2 ≤ K) :
    splitEscapeProbability a K =
      staticReactionMeasure _ a (staticEscapeEvent 2 (K-2)) := by
  unfold splitEscapeProbability
  rw [finite_static_escape_measure_eq, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  simp only [Set.mem_preimage, reversibleEscapeEvent_iff, Nat.sub_add_cancel hK, Set.mem_ofPred_eq]



theorem quotient_escape_finite  (hK : 2 ≤ K) :
    quotientEscapeProbability a K =
      quotientStaticMeasure _ a (quotientEscapeEvent 2 (K-2)) := by
  unfold quotientEscapeProbability
  rw [quotient_escape_measure_eq, quotientInfiniteMeasure,
    Measure.map_apply quotientField_measurable (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  simp only [Set.mem_preimage, reversibleEscapeEvent_iff, Nat.sub_add_cancel hK, Set.mem_ofPred_eq]



end RAFCriticalWindowQuantitative
