module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CentralHaarInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorFiniteOrbitIntegral

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

include ζ hζ in

theorem card_cubic_center : Nat.card (rootsOfUnity 3 F) = 3 := by
  exact (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ
    (by norm_num : 12 = 4 * 3)).card_rootsOfUnity


private lemma measurable_iff_comp_q (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞) :
    Measurable a ↔ Measurable (a ∘ q F ζ hζ U) := by
  have hmap := Continuous.map_borel_eq
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U)
  rw [show KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU F ζ hζ U =
        borel (KPFiniteCuspAtlas.rawXU F ζ hζ U) from rfl,
      show instMeasurableSpaceCoveredSpherical F ζ hζ U =
        borel (CoveredSpherical F ζ hζ U) from rfl]
  rw [measurable_iff_le_map, measurable_iff_le_map, ← hmap, MeasurableSpace.map_comp]

def centralAverage (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) :
    CoveredSpherical F ζ hζ U → ℝ≥0∞ :=
  fun v => (3 : ℝ≥0∞)⁻¹ * ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)


theorem centralAverage_invariant (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U) :
    centralAverage F ζ hζ U ψ (z F ζ hζ U ε v) =
      centralAverage F ζ hζ U ψ v := by
  simp only [centralAverage]
  congr 1
  have h1 : (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U δ (z F ζ hζ U ε v))) =
      ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v) := by
    apply Finset.sum_congr rfl
    intro δ _
    congr 1
    exact (mul_smul δ ε v).symm
  have h2 : (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v)) =
      ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U δ v) := by
    rw [show (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v)) =
        ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U ((Equiv.mulRight ε) δ) v) from rfl]
    rw [Equiv.sum_comp (Equiv.mulRight ε) (fun δ => ψ (z F ζ hζ U δ v))]
  rw [h1, h2]

theorem centralAverage_measurable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    Measurable (centralAverage F ζ hζ U ψ) := by
  show Measurable (fun v => (3 : ℝ≥0∞)⁻¹ *
    ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro ε _
  exact hψ.comp (z F ζ hζ U ε).continuous.measurable

theorem existsUnique_borel_descent (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    ∃! a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞,
      Measurable a ∧ ∀ v, a (q F ζ hζ U v) = centralAverage F ζ hζ U ψ v := by
  have hf : Measurable (centralAverage F ζ hζ U ψ) := centralAverage_measurable F ζ hζ U ψ hψ
  have hfiber : ∀ v w, q F ζ hζ U v = q F ζ hζ U w →
      centralAverage F ζ hζ U ψ v = centralAverage F ζ hζ U ψ w := by
    intro v w hvw
    obtain ⟨ε, rfl⟩ :=
      (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U v w).mp hvw
    exact (centralAverage_invariant F ζ hζ U ψ ε v).symm
  obtain ⟨g, hg⟩ :=
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U).hasRightInverse
  have hgq : ∀ v, q F ζ hζ U (g (q F ζ hζ U v)) = q F ζ hζ U v :=
    fun v => hg (q F ζ hζ U v)
  refine ⟨fun b => centralAverage F ζ hζ U ψ (g b), ⟨?_, ?_⟩, ?_⟩
  · rw [measurable_iff_comp_q F ζ hζ U]
    have hcomp : (fun b => centralAverage F ζ hζ U ψ (g b)) ∘ q F ζ hζ U =
        centralAverage F ζ hζ U ψ := by
      funext v
      exact hfiber (g (q F ζ hζ U v)) v (hgq v)
    rw [hcomp]
    exact hf
  · intro v
    exact hfiber (g (q F ζ hζ U v)) v (hgq v)
  · intro a ha
    funext b
    obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U b
    exact (ha.2 v).trans (hfiber (g (q F ζ hζ U v)) v (hgq v)).symm

def borelDescent (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  Classical.choose (existsUnique_borel_descent F ζ hζ U ψ hψ).exists

theorem borelDescent_measurable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    Measurable (borelDescent F ζ hζ U ψ hψ) :=
  (Classical.choose_spec (existsUnique_borel_descent F ζ hζ U ψ hψ).exists).1

theorem borelDescent_q (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ)
    (v : CoveredSpherical F ζ hζ U) :
    borelDescent F ζ hζ U ψ hψ (q F ζ hζ U v) =
      centralAverage F ζ hζ U ψ v :=
  (Classical.choose_spec (existsUnique_borel_descent F ζ hζ U ψ hψ).exists).2 v

private lemma lintegral_centralAverage
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
  have hcard : Nat.card (rootsOfUnity 3 F) = 3 :=
    (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ
      (by norm_num : 12 = 4 * 3)).card_rootsOfUnity
  have hzmeas : ∀ ε : rootsOfUnity 3 F, Measurable (z F ζ hζ U ε) :=
    fun ε => (z F ζ hζ U ε).continuous.measurable
  have hmp : ∀ ε : rootsOfUnity 3 F,
      (∫⁻ v, ψ (z F ζ hζ U ε v) ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U :=
    fun ε =>
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).lintegral_comp hψ
  have hmeas : Measurable (fun v => ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)) :=
    Finset.measurable_sum _ (fun ε _ => hψ.comp (hzmeas ε))
  calc
    (∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U)
        = ∫⁻ v, (3 : ℝ≥0∞)⁻¹ * (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
            ∂coveredMeasure F ζ hζ R U := rfl
    _ = (3 : ℝ≥0∞)⁻¹ * ∫⁻ v, (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
            ∂coveredMeasure F ζ hζ R U := lintegral_const_mul _ hmeas
    _ = (3 : ℝ≥0∞)⁻¹ * ∑ ε : rootsOfUnity 3 F,
            ∫⁻ v, ψ (z F ζ hζ U ε v) ∂coveredMeasure F ζ hζ R U := by
          rw [lintegral_finsetSum (f := fun ε v => ψ (z F ζ hζ U ε v)) Finset.univ
            (fun ε _ => hψ.comp (hzmeas ε))]
    _ = (3 : ℝ≥0∞)⁻¹ * ∑ _ε : rootsOfUnity 3 F,
            ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
          congr 1
          exact Finset.sum_congr rfl (fun ε _ => hmp ε)
    _ = (3 : ℝ≥0∞)⁻¹ * ((Nat.card (rootsOfUnity 3 F) : ℝ≥0∞) *
            ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) := by
          congr 1
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    _ = ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
          rw [hcard, show (↑(3 : ℕ) : ℝ≥0∞) = 3 from by norm_num, ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem lintegral_borelDescent
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ b, borelDescent F ζ hζ U ψ hψ b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  rw [← map_q_coveredMeasure F ζ hζ R P U]
  rw [lintegral_map (borelDescent_measurable F ζ hζ U ψ hψ)
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable]
  rw [show (∫⁻ v, borelDescent F ζ hζ U ψ hψ (q F ζ hζ U v)
        ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U from
    lintegral_congr (fun v => borelDescent_q F ζ hζ U ψ hψ v)]
  exact (lintegral_centralAverage F ζ hζ R U ψ hψ).symm




theorem centralAverage_indicator
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) :
    centralAverage F ζ hζ U ((q F ζ hζ U ⁻¹' E).indicator ψ) =
      (q F ζ hζ U ⁻¹' E).indicator (centralAverage F ζ hζ U ψ) := by
  funext v
  by_cases hv : q F ζ hζ U v ∈ E
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hv), centralAverage, centralAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    rw [Set.indicator_of_mem]
    show q F ζ hζ U (z F ζ hζ U ε v) ∈ E
    rw [KPContSectorCoveredQuotientVocabulary.q_z F ζ hζ U ε v]
    exact hv
  · rw [Set.indicator_of_notMem (by simpa using hv), centralAverage]
    have hzero : (∑ ε : rootsOfUnity 3 F,
        ((q F ζ hζ U ⁻¹' E).indicator ψ) (z F ζ hζ U ε v)) = 0 := by
      apply Finset.sum_eq_zero
      intro ε _
      rw [Set.indicator_of_notMem]
      show q F ζ hζ U (z F ζ hζ U ε v) ∉ E
      rw [KPContSectorCoveredQuotientVocabulary.q_z F ζ hζ U ε v]
      exact hv
    rw [hzero, mul_zero]

theorem lintegral_indicator_borelDescent
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
    (∫⁻ v, (q F ζ hζ U ⁻¹' E).indicator ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ b, E.indicator (borelDescent F ζ hζ U ψ hψ) b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  have hqm : Measurable (q F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hφ : Measurable ((q F ζ hζ U ⁻¹' E).indicator ψ) := hψ.indicator (hqm hE)
  rw [lintegral_borelDescent F ζ hζ R P U ((q F ζ hζ U ⁻¹' E).indicator ψ) hφ]
  refine lintegral_congr (fun b => ?_)
  obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U b
  rw [borelDescent_q F ζ hζ U ((q F ζ hζ U ⁻¹' E).indicator ψ) hφ v,
    centralAverage_indicator F ζ hζ U ψ E]
  by_cases hv : q F ζ hζ U v ∈ E
  · rw [Set.indicator_of_mem (s := q F ζ hζ U ⁻¹' E) (a := v) (by simpa using hv)
        (centralAverage F ζ hζ U ψ),
      Set.indicator_of_mem (s := E) (a := q F ζ hζ U v) hv (borelDescent F ζ hζ U ψ hψ),
      borelDescent_q F ζ hζ U ψ hψ v]
  · rw [Set.indicator_of_notMem (s := q F ζ hζ U ⁻¹' E) (a := v) (by simpa using hv)
        (centralAverage F ζ hζ U ψ),
      Set.indicator_of_notMem (s := E) (a := q F ζ hζ U v) hv (borelDescent F ζ hζ U ψ hψ)]

end DedekindZetaZeroFree.KPContSectorFiniteOrbitIntegral

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport
open KPContSectorFiniteOrbitIntegral

end DedekindZetaZeroFree

end
