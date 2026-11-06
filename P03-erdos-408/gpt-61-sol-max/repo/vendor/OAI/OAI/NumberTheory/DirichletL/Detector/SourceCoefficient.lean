module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.CompletedCoefficient
public import OAI.NumberTheory.DirichletL.Detector.CalibrationCancellation

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow ConcretePrimeRowBridge


def sourceHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I ) (hI : primaryGenerator I≠0) (A s : ActualEisensteinCubic.O) (hA : A≠0) (u a : ActualEisensteinCubic.O)  :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : HeckeFamily.Character) (I )
    (hI : primaryGenerator I≠0) (A s : ActualEisensteinCubic.O) (hA : A≠0) (H : ActualEisensteinCubic.O)  :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

theorem sourceHighCoefficient_eq_bare  S   hS 
     η   I   hI 
     A s   hA  (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))  u a 
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  grind

theorem bareSourceCoefficient_product (η : HeckeFamily.Character) (I J : Ideal ActualEisensteinCubic.O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
     n m s r 
     hc   hd 
     hn   hm 
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r))  H  :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      bareSourceCoefficient η I hI.2 A s hA H * bareSourceCoefficient η J hJ.2 B r hB H := by
  have he := correctedFiniteCoefficient_product I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop H
  dsimp only at he ⊢
  unfold bareSourceCoefficient
  rw [he,map_mul,angularFactor_mul,star_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
