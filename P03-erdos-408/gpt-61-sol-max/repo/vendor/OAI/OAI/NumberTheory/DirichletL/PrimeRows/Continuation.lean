module

public import OAI.NumberTheory.DirichletL.PrimeRows.Product
public import OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss


lemma actualACube_norm_le  η   p  : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

def ramifiedProduct (S ) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)  :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S ) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)  :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
