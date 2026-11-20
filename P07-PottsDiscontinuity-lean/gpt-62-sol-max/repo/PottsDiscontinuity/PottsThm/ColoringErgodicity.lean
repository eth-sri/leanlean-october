module

public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite

noncomputable section

def spinShift {C : Type*} (a : Vertex) (σ : Vertex → C) (x : Vertex) : C := σ (x - a)

def IsTranslationMixing {C : Type*} [MeasurableSpace C] (μ : Measure (Vertex → C)) : Prop :=
  (∀ a, MeasurePreserving (spinShift a) μ μ) ∧
    ∀ A B, MeasurableSet A → MeasurableSet B → MixingLimit μ spinShift cofinite A B

theorem IsTranslationMixing.ergodic {C : Type*} [MeasurableSpace C] {μ : Measure (Vertex → C)}
    [IsProbabilityMeasure μ] (hm : IsTranslationMixing μ) :
    PottsDiscontinuity.IsTranslationErgodic μ := by
  have hs (a : Vertex) : spinShift (-a) = (fun σ : Vertex → C => fun x => σ (x + a)) := by
    funext σ x
    change σ (x - -a) = σ (x + a)
    simp
  refine ⟨fun a => hs a ▸ (hm.1 (-a)).map_eq, ?_⟩
  intro A hA hInv
  refine zero_or_compl_zero_of_mixing μ hA (hm.2 A A hA hA) fun a => ?_
  rw [← neg_neg a, hs]
  exact hInv (-a)

/-- A measurable equivariant factor of the product of two mixing lattice
actions inherits mixing. -/
theorem mixingProduct_factor {C : Type*} [MeasurableSpace C]
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
    IsTranslationMixing ((μ.prod ν).map F) := by
  classical
  let Q := productShift T S
  have hQpres (a : Vertex) : MeasurePreserving (Q a) (μ.prod ν) (μ.prod ν) :=
    (hTpres a).prod (hSpres a)
  have hs (a : Vertex) : Measurable (spinShift a : (Vertex → C) → Vertex → C) :=
    measurable_pi_iff.mpr fun x => measurable_pi_apply (x - a)
  have hc (a : Vertex) : spinShift a ∘ F = F ∘ Q a := by
    funext z x
    exact (hFshift a z x).symm
  constructor
  · intro a
    refine ⟨hs a, ?_⟩
    rw [Measure.map_map (hs a) hF, hc, ← Measure.map_map hF (hQpres a).measurable, (hQpres a).map_eq]
  · intro A B hA hB
    have hp (a : Vertex) : F ⁻¹' (A ∩ spinShift a ⁻¹' B) = F ⁻¹' A ∩ Q a ⁻¹' (F ⁻¹' B) := by
      simp [Set.preimage_inter, ← Set.preimage_comp, hc]
    have hr (D : Set (Vertex → C)) (hD : MeasurableSet D) :
        ((μ.prod ν).map F).real D = (μ.prod ν).real (F ⁻¹' D) := by
      simp [Measure.real_def, Measure.map_apply hF hD]
    unfold MixingLimit
    simp_rw [hr A hA, hr B hB, fun a => hr _ (hA.inter ((hs a) hB)), hp]
    exact mixingProduct μ ν T S hTpres hSpres hTmix hSmix (hF hA) (hF hB)

end
end PottsDiscontinuity.PottsThm
