module
public import OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude
public import OAI.NumberTheory.DirichletL.Moments.ReflectedChild

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumn (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then
    (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)
  else 0

lemma lowGaussColumn_row (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) (m : O) :
    (if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0)=
      lowGaussColumn C W1 Y σ v s*
        gaussRow (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) (-m) := by
  have he := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
  unfold lowGaussColumn gaussRow
  rw [congrArg Ideal.absNorm he]
  split_ifs
  · rw [lowAdditiveCoefficient_eq]
    simp only [div_eq_mul_inv]
    ring
  · simp

end SevenEighths.ProbePhysical
end

end OAI
