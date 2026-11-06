module

public import OAI.NumberTheory.DirichletL.Detector.TuplePrincipal

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve HeckeInverseAmplification

local notation "Id" => Ideal ActualEisensteinCubic.O

def compensatedRowSeries {K } (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→ActualEisensteinCubic.O) (x w z : ℂ)  :=
  (∏i,(elementNorm (p i):ℂ)^(z-1))*
    ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      indexedCompensatedHigh η S p u.val x w z

def compensatedRowTripleIntegral {K } (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→ActualEisensteinCubic.O) (X Y Z : ℝ)  :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    compensatedRowSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

section
variable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1) (p : Fin K→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) (X Y Z : ℝ)

include hp in
lemma tupleSourceTripleIntegral_eq_rows      
         
        :
    tupleSourceTripleIntegral η S C W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S C W0 W1 p X Y Z := by
  unfold tupleSourceTripleIntegral compensatedRowTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact tupleSourceSeries_eq_rows η S C p hp
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

include hpS hbad hSne ha0 ha1 hW0 hW1 hp in
theorem compensatedTuple_eq_row_triple    
         
         
         
       
       
      (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  rw [compensatedTuple_eq_source_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    p hp X Y Z hX hY hZ,tupleSourceTripleIntegral_eq_rows η S _ W0 W1 p hp]

end

end SevenEighths.ProbePhysical
end

end OAI
