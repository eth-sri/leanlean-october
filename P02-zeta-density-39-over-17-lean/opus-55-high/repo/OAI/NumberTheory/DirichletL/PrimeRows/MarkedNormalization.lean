module
public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

section
variable (S : Finset (Ideal O))
include S
lemma lift_outside_hasProd (f : PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>f P.val) a) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal | P.val∉S}) (f:=f)).mp h
  pm_8272 hh

theorem localNormalization_hasProd (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  pm_745 hz hw hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
