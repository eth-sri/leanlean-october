module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Elapsed-time Lebesgue measure for finite and infinite horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal

/-- Positive elapsed times strictly below a finite or infinite horizon. -/
abbrev ElapsedTime (S : ℝ≥0∞) := {τ : ℝ // 0 < τ ∧ ENNReal.ofReal τ < S}

/-- Elapsed-time Lebesgue measure on its literal interval subtype. -/
def elapsedVolume (S : ℝ≥0∞) : Measure (ElapsedTime S) :=
  Measure.comap Subtype.val volume

/-- The literal ordered query at a positive elapsed time. -/
def elapsedQuery {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀) {S : ℝ≥0∞} (τ : ElapsedTime S) :
    EvolutionQuery Ω γ :=
  ⟨(σ₀, (σ₀ + τ.1, p.1)), le_add_of_nonneg_right τ.2.1.le, p.2⟩

variable (S : ℝ≥0∞)

/-- The elapsed-time carrier is a Borel subset, even at an infinite horizon. -/
theorem measurableSet_elapsedTime  :
    MeasurableSet {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} :=
  measurableSet_Ioi.inter (ENNReal.measurable_ofReal measurableSet_Iio)

/-- Comap on this subtype is ordinary Lebesgue measure of its image. -/
theorem elapsedVolume_apply  (s : Set (ElapsedTime S))
    (hs : MeasurableSet s) : elapsedVolume S s = volume (Subtype.val '' s) := (MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime S)).comap_apply volume s

/-- Elapsed Lebesgue measure is sigma finite for every horizon, including infinity. -/
instance elapsedVolume_sigmaFinite (S : ℝ≥0∞) : SigmaFinite (elapsedVolume S) := by
  apply SigmaFinite.of_map (elapsedVolume S)
    (f := Subtype.val) measurable_subtype_coe.aemeasurable
  have heq : (elapsedVolume S).map Subtype.val =
      volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} := map_comap_subtype_coe (measurableSet_elapsedTime S) volume
  rw [heq]
  infer_instance

/-- The Green construction has an s-finite elapsed measure for every horizon. -/
instance elapsedVolume_sFinite (S : ℝ≥0∞) : SFinite (elapsedVolume S) := inferInstance

/-- The literal inclusion of a shorter elapsed-time carrier. -/
def elapsedInclusion {T S : ℝ≥0∞} (hTS : T ≤ S) : ElapsedTime T → ElapsedTime S :=
  fun τ => ⟨τ.1, τ.2.1, τ.2.2.trans_le hTS⟩


variable {T S : ℝ≥0∞} (hTS : T ≤ S)

/-- The shorter-horizon inclusion is measurable. -/
theorem measurable_elapsedInclusion  :
    Measurable (elapsedInclusion hTS) := measurable_subtype_coe.subtype_mk

/-- Horizon inclusion pushes Lebesgue measure to its exact time restriction. -/
theorem elapsedInclusion_map  :
    (elapsedVolume T).map (elapsedInclusion hTS) =
      (elapsedVolume S).restrict {τ | ENNReal.ofReal τ.1 < T} := by
  have ht : MeasurableSet {τ : ElapsedTime S | ENNReal.ofReal τ.1 < T} :=
    (ENNReal.measurable_ofReal.comp measurable_subtype_coe) measurableSet_Iio
  ext A hA
  rw [Measure.map_apply (measurable_elapsedInclusion hTS) hA,
    elapsedVolume_apply T _ ((measurable_elapsedInclusion hTS) hA),
    Measure.restrict_apply hA, elapsedVolume_apply S _ (hA.inter ht)]
  congr 1
  ext t
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨elapsedInclusion hTS τ, ⟨hτ, τ.2.2⟩, rfl⟩
  aesop

/-- Finite elapsed-time volume is exactly the unnormalized horizon length. -/
theorem elapsedVolume_univ (S : ℝ) (hS : 0 < S) :
    elapsedVolume (ENNReal.ofReal S) univ = ENNReal.ofReal S := by
  rw [elapsedVolume_apply _ _ MeasurableSet.univ]
  have himage : (Subtype.val : ElapsedTime (ENNReal.ofReal S) → ℝ) '' univ =
      {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal S} := by
    simp
  rw [himage]
  have he : {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal S} = Ioo 0 S := by
    aesop
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
