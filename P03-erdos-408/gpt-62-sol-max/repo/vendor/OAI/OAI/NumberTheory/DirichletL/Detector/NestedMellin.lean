module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Detector.PhysicalRadial
public import OAI.NumberTheory.DirichletL.Detector.OuterMellin
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def nestedMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

lemma verticalIntegral_mul_const (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun s=>F s*c)=verticalIntegral σ F*c := by
  unfold verticalIntegral
  rw [integral_mul_const,mul_assoc]

theorem markedPhysicalProbe_eq_nested_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (mw : MellinWindows)
    (X Y Z ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hξ : 1<ξ) :
    markedPhysicalProbe η (calibrationForSet S hS) D mw.left mw.right X Y Z=
      nestedMellinPhysicalProbe η (calibrationForSet S hS) D mw.left mw.right X Y Z ξ υ := by
  rw [markedPhysicalProbe_eq_radial_mellin η S hS hSne D mw.left mw.right mw.leftLo mw.leftHi mw.left_pos mw.left_support X Y Z ξ hX hZ hξ]
  unfold radialMellinPhysicalProbe nestedMellinPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    rw [verticalIntegral_mul_const,verticalIntegral_mul_const,
      ←outer_source_scaled_inverse mw.right mw.rightLo mw.rightHi mw.right_pos mw.right_support υ (Ideal.absNorm s.val:ℝ) Y
        (by exact_mod_cast Ideal.absNorm_pos_of_ne_bot (s.property.1)) hY]
    ring
  · simp only [mul_zero]

end SevenEighths.ProbePhysical
end

end OAI
