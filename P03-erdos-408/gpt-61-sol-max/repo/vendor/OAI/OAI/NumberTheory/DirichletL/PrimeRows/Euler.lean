module

public import OAI.NumberTheory.DirichletL.PrimeRows.Character

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion


def targetRow (η : Character) (u : FreeRow)  := η.product (rawRow u).inverse

theorem rowCharacter_hasProd  S   hS 
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)  u 
     s  (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealRowHom u.val P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (rowCharacter S hS u) s) := by
  apply LFunction_hasProd_outside (rowCharacter S hS u) S (idealRowHom u.val) _ s hs
  intro P
  rw [rowCharacter_coeff S hS hbad,highExclusion_prime]
  split_ifs <;> simp only [zero_mul,one_mul]

theorem targetRow_hasProd  S   hS 
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)  η   u 
     s  (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealCoeff η P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => idealCoeff η P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

def localCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ)  :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal HeckeFamily.O)) (η : Character) (u : FreeRow) (x w z : ℂ)  :=
  ∏' P : {P : PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd  S   hS 
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)  η   u 
     x w z  (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz1).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW := (rowCharacter_hasProd S hS hbad u w hw1).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

end SevenEighths.ProbeHighRowFamily

end

end OAI
