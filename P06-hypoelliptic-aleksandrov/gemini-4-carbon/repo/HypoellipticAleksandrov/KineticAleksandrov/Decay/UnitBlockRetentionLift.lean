module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import Mathlib.MeasureTheory.Measure.Filter

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory




/-- Comap lifts an ambient retained ball measure to the larger valid source fiber,
preserving its measure, mass and smaller-ball support. -/
theorem retained_ball_comap_properties {d : ℕ} (v : PDE.Vec d) (η r s : ℝ)
    (hη : 0 ≤ η) (hηr : η ≤ r)
    (μ : Measure (EvolutionAmbientState d)) [IsFiniteMeasure μ]
    (hsupport : μ (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0) :
    let R := μ.comap (Subtype.val :
      EvolutionState (PDE.euclideanBall v r) stationary s → EvolutionAmbientState d)
    R.map Subtype.val = μ ∧ R.real univ = μ.real univ ∧
      (∀ᵐ p ∂R, p.1.1 ∈ PDE.euclideanBall v η)   := by
  intro R
  have map_comap_evolutionState_eq {D : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (s : ℝ) (μ : Measure (EvolutionAmbientState d)) (hsupport : μ (evolutionStateSet D γ s)ᶜ = 0) :
      Measure.map (Subtype.val : EvolutionState D γ s → EvolutionAmbientState d)
      (μ.comap Subtype.val) = μ := by
    have he := MeasurableEmbedding.subtype_coe (measurableSet_evolutionStateSet (γ := γ) hD s)
    rw [he.map_comap, Subtype.range_coe]
    apply Measure.restrict_eq_self_of_ae_mem
    exact ae_iff.mpr hsupport
  have comap_evolutionState_real_univ {D : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (s : ℝ) (μ : Measure (EvolutionAmbientState d)) [IsFiniteMeasure μ] (hsupport : μ (evolutionStateSet D γ s)ᶜ = 0) :
      (μ.comap (Subtype.val : EvolutionState D γ s → EvolutionAmbientState d)).real univ =
      μ.real univ := by
    simpa only [map_measureReal_apply_of_aemeasurable
      measurable_subtype_coe.aemeasurable MeasurableSet.univ,
      preimage_univ] using (congrArg (fun ν : Measure (EvolutionAmbientState d) => ν.real univ) (map_comap_evolutionState_eq hD s μ hsupport))
  have hsub : PDE.euclideanBall v η ×ˢ (univ : Set (PDE.Vec d)) ⊆
      evolutionStateSet (PDE.euclideanBall v r) stationary s := by
    intro x hx
    exact ⟨by rw [movingDomain_stationary]; exact PDE.euclideanBall_mono hη hηr hx.1,
      mem_univ _⟩
  have hs :=
    measure_mono_null (compl_subset_compl.mpr hsub) hsupport
  have hm := map_comap_evolutionState_eq (PDE.isOpen_euclideanBall v r).measurableSet s μ hs
  refine ⟨hm, comap_evolutionState_real_univ
    (PDE.isOpen_euclideanBall v r).measurableSet s μ hs, ?_⟩
  have hae :=
    ae_iff.mpr hsupport
  rw [← hm] at hae
  exact (ae_of_ae_map measurable_subtype_coe.aemeasurable hae).mono (fun p hp => hp.1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

