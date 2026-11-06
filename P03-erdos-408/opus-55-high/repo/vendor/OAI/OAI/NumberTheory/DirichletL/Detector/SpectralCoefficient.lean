module

public import OAI.NumberTheory.DirichletL.Detector.CoefficientDirect
public import OAI.NumberTheory.DirichletL.Detector.SpectralSeparation

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase CubicEisenstein

lemma rayMask_supported (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) : RayFourExpansion.rayMask a=1 := by
  let : (Ideal.span {(2:ActualEisensteinCubic.O)}).IsMaximal := by
    simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {(2:ActualEisensteinCubic.O)}) := Ideal.Quotient.field _
  have h2 : IsCoprime (2:ActualEisensteinCubic.O) a := by
    apply (isUnit_quotient_span_iff _ _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ((supported_span_iff a).mp ha).2
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h4 : IsCoprime (4:ActualEisensteinCubic.O) a := by
    simpa only [show (2:ActualEisensteinCubic.O)^2=4 by norm_num] using (h2.pow_left : IsCoprime ((2:ActualEisensteinCubic.O)^2) a)
  exact ite_eq_left ((isUnit_quotient_span_iff (4:ActualEisensteinCubic.O) a).mpr h4)

lemma completedCorrection_supported (I J : Ideal ActualEisensteinCubic.O) (hI : Supported I) (hJ : Supported J) :
    completedCorrection I J=star (G (completedIndex I J)) := by
  rw [completedCorrection_eq_phase,rayMask_supported]
  · simp
  · exact supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
      ((supported_span_primaryGenerator_iff J).mpr hJ)

lemma baseRowCoefficient_unit_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s})) (A : ActualEisensteinCubic.O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  exact congrArg (fun n : ℤ=>(n:ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem spectralSummand_source_coefficient (S : Finset (Ideal ActualEisensteinCubic.O)) (D I J : Ideal ActualEisensteinCubic.O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
          star (FiniteGaussPhase.angularFactor (completedIndex I J)*G (completedIndex I J))*
          targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : FiniteGaussPhase.angularFactor (completedIndex I J)=
      FiniteGaussPhase.angularFactor (primaryGenerator I)*FiniteGaussPhase.angularFactor (primaryGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryGenerator J^3=(primaryGenerator J*primaryGenerator J)*primaryGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3=
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryGenerator_ne_zero I hI)]
  change _*(star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  grind

end SevenEighths.ProbePhysical
end

end OAI
