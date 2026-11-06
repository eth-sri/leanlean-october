module

public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite

noncomputable section

/-- A measurable equivariant factor of the product of two mixing lattice
actions is translation ergodic. -/
theorem mixingProduct_factor_translationErgodic {C : Type*} [MeasurableSpace C]
    {μ : Measure LatticeConfiguration} {ν : Measure (Vertex → C)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Vertex → LatticeConfiguration → LatticeConfiguration)
    (S : Vertex → (Vertex → C) → (Vertex → C))
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩ (T a) ⁻¹' B)) cofinite
        (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set (Vertex → C), MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩ (S a) ⁻¹' B)) cofinite
        (𝓝 (ν.real A * ν.real B)))
    (F : LatticeConfiguration × (Vertex → C) → Vertex → C)
    (hF : Measurable F)
    (hFshift : ∀ a z x, F (productShift T S a z) x = F z (x - a)) :
    PottsDiscontinuity.IsTranslationErgodic
      ((μ.prod ν).map F) := by
  classical
  let Q : Vertex → LatticeConfiguration × (Vertex → C) →
      LatticeConfiguration × (Vertex → C) := productShift T S
  have hQpres (a : Vertex) : MeasurePreserving (Q a) (μ.prod ν) (μ.prod ν) :=
    (hTpres a).prod (hSpres a)
  refine ⟨fun a => ?_, fun A hA hAinv => ?_⟩
  · rw [Measure.map_map (measurable_pi_iff.mpr fun x => measurable_pi_apply (x + a)) hF,
      show (fun σ : Vertex → C => fun x => σ (x + a)) ∘ F = F ∘ Q (-a) by
        funext z x; simpa [Function.comp_apply, sub_neg_eq_add] using (hFshift (-a) z x).symm,
      ← Measure.map_map hF (hQpres (-a)).measurable, (hQpres (-a)).map_eq]
  · have hEinv (a : Vertex) : Q a ⁻¹' (F ⁻¹' A) = F ⁻¹' A := by
      ext z
      change F (Q a z) ∈ A ↔ F z ∈ A
      rw [show F (Q a z) = fun x => F z (x + -a) by
        funext x; simpa [sub_eq_add_neg] using hFshift a z x]
      exact Set.ext_iff.mp (hAinv (-a)) (F z)
    simpa [Measure.map_apply hF hA, Measure.map_apply hF hA.compl] using
      mixingProduct_invariant_event μ ν T S hTpres hSpres hTmix hSmix (hF hA) hEinv

end
end PottsDiscontinuity.PottsThm
