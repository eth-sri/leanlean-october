module

public import OAI.NumberTheory.DirichletL.Detector.HighRowsMultiplicative

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT

local notation "Id" => Ideal ActualEisensteinCubic.O

@[simp] theorem bareIdealHighCoefficient_row_one  η   u  :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal ActualEisensteinCubic.O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:ActualEisensteinCubic.O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:ActualEisensteinCubic.O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one  η   u   x w z  :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal ActualEisensteinCubic.O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

end SevenEighths.ProbePhysical


end OAI
