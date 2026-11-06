module
public import Mathlib

public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity.FK


noncomputable section

/-- A measurable equivariant factor of the product of two mixing lattice
actions is translation ergodic. -/
theorem mixingProduct_factor_translationErgodic {C : Type*} [MeasurableSpace C]
    {μ : Measure LatticeConfiguration} {ν : Measure (Vertex → C)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Vertex → LatticeConfiguration → LatticeConfiguration)
    (S : Vertex → (Vertex → C) →  Vertex → C )
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩  T a  ⁻¹' B)) cofinite
        (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set (Vertex → C), MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩  S a  ⁻¹' B)) cofinite
        (𝓝 (ν.real A * ν.real B)))
    (F : LatticeConfiguration × (Vertex → C) → Vertex → C)
    (hF : Measurable F)
    (hFshift : ∀ a z x, F (productShift T S a z) x = F z (x - a)) :
    PottsDiscontinuity.IsTranslationErgodic
      ((μ.prod ν).map F) := by
  
  let Q  := productShift T S
  have hQmeas (a : Vertex) : Measurable (Q a) := Measurable.prodMk (Measurable.comp (hTpres a).measurable measurable_fst)
                                                   (Measurable.comp (hSpres a).measurable measurable_snd)
  have hQpres (a : Vertex) : MeasurePreserving (Q a) (μ.prod ν) (μ.prod ν) := by
                                                                                solve_by_elim [_root_.MeasureTheory.MeasurePreserving.prod]
  have hτmeas (a : Vertex) : Measurable  fun σ : Vertex → C => fun x => σ (x + a)  :=
    by
      fun_prop
  constructor
  · intro a
    rw [Measure.map_map (hτmeas a) hF]
    have hcomp : (fun σ  => fun x => σ (x + a)) ∘ F = F ∘ Q (-a) := by
      funext z x
      simpa  using (hFshift (-a) z x).symm
    rw [hcomp, ← Measure.map_map hF (hQmeas (-a)), (hQpres (-a)).map_eq]
  · intro A hA hAinv
    let E  := F ⁻¹' A
    
    have hEinv : ∀ a,  Q a  ⁻¹' E = E := by
      intro a
      ext z
      change F (Q a z) ∈ A ↔ F z ∈ A
      
      rw [ funext (hFshift a z) ]
      
      
      
      exact  Set.ext_iff.mp (hAinv (-a)) (F z) 
    rcases mixingProduct_invariant_event μ ν T S hTpres hSpres hTmix hSmix (hF hA) hEinv with h | h
    · left
      rw [Measure.map_apply hF hA]
      exact h
    · simp_all

end
end PottsDiscontinuity.PottsThm
