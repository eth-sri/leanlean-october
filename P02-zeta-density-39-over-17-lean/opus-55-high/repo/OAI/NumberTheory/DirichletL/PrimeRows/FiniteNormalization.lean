module
public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedNormalization
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

section
variable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
include S hS hbad T hT η u x w z
theorem globalNormalization_finite_split
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    globalNormalization S hS η u x w z=
      globalNormalization (markExclusions S T) (markExclusions_prime S hS T) η u x w z*
        ∏P∈T,localNormalization η u P x w z := by
  have hleft := localNormalization_hasProd S hS hbad η u x w z hx hw hz
  have hbase := localNormalization_hasProd (markExclusions S T) (markExclusions_prime S hS T)
    (hbad.trans Finset.subset_union_left) η u x w z hx hw hz
  let R := fun P : PrimeIdeal=>if P∈T then localNormalization η u P x w z else 1
  have hR : HasProd R (∏P∈T,localNormalization η u P x w z) := by
    pm_5581 T R
  apply hleft.unique
  convert hbase.mul hR using 1
  · funext P
    by_cases hP : P∈T
    · simp only [ite_eq_right (hT P hP),mem_markExclusions,hP,or_true,ite_true,R,ite_eq_left hP,one_mul]
    · simp only [mem_markExclusions,hP,or_false,R,ite_eq_right hP,mul_one]
  · rfl

theorem finite_replacement_normalized
    (g : PrimeIdeal→ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (markedIdealHighSeries (markExclusions S T) 1 η u.val x w z*∏P∈T,g P)*
      globalNormalization S hS η u x w z=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,g P*localNormalization η u P x w z := by
  pm_6062
  rw [globalNormalization_finite_split S hS hbad T hT η u x w z (by linarith) (by linarith) hz1,
    globalCorrection,(localCorrection_hasProd (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).tprod_eq,
    Finset.prod_mul_distrib,globalNormalization]
  ring
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
