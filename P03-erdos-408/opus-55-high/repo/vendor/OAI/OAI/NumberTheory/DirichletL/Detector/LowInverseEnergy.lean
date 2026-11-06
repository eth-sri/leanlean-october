module

public import OAI.NumberTheory.DirichletL.Detector.LowPrimeFamily

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "Id" => Ideal ActualEisensteinCubic.O

def lowCorrectionEnergy : ℝ := ∑χ : RayCharacter,‖ProbeCompleted.correctionCoeff χ‖^2

lemma lowCorrectionEnergy_nonneg : 0≤lowCorrectionEnergy :=
  Finset.sum_nonneg (by simp)

lemma fixed_correction_energy {ι κ : Type*} [Fintype ι] (R : Finset κ) (c : ι→ℂ) (F : ι→κ→ℂ) :
    (∑m∈R,‖∑χ : ι,c χ*F χ m‖^2)≤
      (∑χ : ι,‖c χ‖^2)*∑χ : ι,∑m∈R,‖F χ m‖^2 := by
  calc
    _≤∑m∈R,(∑χ : ι,‖c χ‖^2)*(∑χ : ι,‖F χ m‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _≤(∑χ : ι,‖c χ‖*‖F χ m‖)^2 := by
          apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
          simpa using norm_sum_le Finset.univ (fun χ=>c χ*F χ m)
        _≤_ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

end SevenEighths.ProbePhysical
end

end OAI
