module

public import OAI.NumberTheory.DirichletL.Detector.LowRowMellin

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "Id" => Ideal ActualEisensteinCubic.O

def lowRayAmplitude (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (m : ActualEisensteinCubic.O) (v : ℝ) : ℂ :=
  ∑'s : {I : Id // Supported I},if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0

lemma lowAdditiveCoefficient_common_support (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀m : ActualEisensteinCubic.O,∀v : ℝ,∀s∉F,
      lowAdditiveCoefficient C W1 Y s m v=0 := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  refine ⟨ho.toFinset,?_⟩
  intro m v s hs
  apply lowAdditiveCoefficient_outer_zero
  simp_all

lemma lowRayAmplitude_group (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : ActualEisensteinCubic.O) (v : ℝ)
    (B : RayRing→ℂ) :
    (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  have hleft : (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑s∈F,lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s) := by
    apply tsum_eq_sum
    intro s hs
    rw [hF m v s hs,zero_mul]
  have hr (σ : RayRing) : lowRayAmplitude C W1 Y σ m v=
      ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
    apply tsum_eq_sum
    intro s hs
    simp only [hF m v s hs,ite_self]
  rw [hleft]
  simp_rw [hr,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

end SevenEighths.ProbePhysical
end

end OAI
