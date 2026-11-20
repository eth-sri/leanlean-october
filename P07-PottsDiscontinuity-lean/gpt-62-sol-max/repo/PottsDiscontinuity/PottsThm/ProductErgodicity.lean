module

public import PottsDiscontinuity.Infra.MeasureMixing

@[expose] public section

open MeasureTheory Filter Topology Set MeasurableSpace

namespace PottsDiscontinuity.PottsThm

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

/-- A product of mixing probability systems is mixing. -/
theorem mixingProduct {Γ X Y : Type*} [Infinite Γ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Γ → X → X) (S : Γ → Y → Y)
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩ (T a) ⁻¹' B)) cofinite (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩ (S a) ⁻¹' B)) cofinite (𝓝 (ν.real A * ν.real B)))
    {E F : Set (X × Y)} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MixingLimit (μ.prod ν) (productShift T S) cofinite E F := by
  let ρ := μ.prod ν
  have hPres (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ :=
    (hTpres a).prod (hSpres a)
  refine mixing_of_generators generateFrom_prod.symm isPiSystem_prod ρ hPres ?_ hE hF
  rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
  have he (a : Γ) : (A ×ˢ B) ∩ (productShift T S a) ⁻¹' (C ×ˢ D) =
      (A ∩ T a ⁻¹' C) ×ˢ (B ∩ S a ⁻¹' D) := by
    ext z
    simp <;> tauto
  simpa [MixingLimit, he, ρ, mul_mul_mul_comm] using (hTmix A C hA hC).mul (hSmix B D hB hD)

end PottsDiscontinuity.PottsThm
