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
local notation "O" => HeckeFamily.O

lemma actualACube_norm_le (η : Character) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
