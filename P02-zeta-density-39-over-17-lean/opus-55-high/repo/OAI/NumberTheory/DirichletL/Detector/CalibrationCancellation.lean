module
public import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
public import OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma Xi_apply (C : CalibrationData) (a : O) :
    C.Xi a = C.residueMonoid a * idealRowHom C.generator (Ideal.span {a}) := rfl

theorem calibration_coefficient_cancel (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid H)) *
      (C.Xi A)⁻¹ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcA : IsCoprime C.generator A := hcop.of_mul_right_left
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  pm_8152 hXA A hA hcA
  pm_8152 hXs s hs hcs
  rw [Xi_apply] at hXA hXs
  have hηA := left_ne_zero_of_mul hXA
  have hκA := right_ne_zero_of_mul hXA
  have hηs := left_ne_zero_of_mul hXs
  have hκs := right_ne_zero_of_mul hXs
  have hηH : C.residueMonoid H≠0 :=
    C.residue.apply_ne_zero_iff.mpr ((isUnit_quotient_span_iff C.generator H).mpr hH)
  have hηHstar : star (C.residueMonoid H)≠0 := star_ne_zero.mpr hηH
  have hτ : C.tau≠0 := calibrationForSet_tau_ne_zero S hS
  have hq : 0<elementNorm C.generator := by
    pm_4905 elementNorm Nat.pos_of_ne_zero C.generator_ne_zero
  have hroot : (Real.sqrt (elementNorm C.generator):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have he := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop H
  dsimp only at he
  rw [he, Xi_apply, map_mul]
  change _ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H
  dsimp only [C] at hηA hκA hηs hκs hηHstar hτ hroot
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
