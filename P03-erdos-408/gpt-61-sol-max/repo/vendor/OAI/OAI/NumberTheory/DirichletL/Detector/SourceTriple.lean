module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.RawSourceIntegral
public import OAI.NumberTheory.DirichletL.Detector.SixthSeries

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve


def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal ActualEisensteinCubic.O))
    (C : CalibrationData) (D : Ideal ActualEisensteinCubic.O) (x w z : ℂ)  :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z

def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)  :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

section
variable (η : HeckeFamily.Character) (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
include η S hS hpS hbad

lemma rawSourceTripleIntegral_eq_source  
         
       D   W0 W1   X Y Z  :
    rawSourceTripleIntegral η S hS D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  unfold rawSourceTripleIntegral sourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  congr 1
  unfold sourceRowSeries
  exact rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem markedPhysicalProbe_eq_source_triple  
         
      (hSne : S.Nonempty) (D : Ideal ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
     X Y Z  (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_triple η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  solve_by_elim [rawSourceTripleIntegral_eq_source]

end

end SevenEighths.ProbePhysical
end

end OAI
