module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical


section
variable {K : ℕ} (S : Finset (Ideal HeckeFamily.O))

theorem tupleOutside     (P : Fin K→PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  simp_all

def calibratedTupleValue {K } (S ) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)  :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor      hS 
     hmax   η   u 
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)  x w z  :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end

end SevenEighths.ProbeHighRowFamily
end

end OAI
