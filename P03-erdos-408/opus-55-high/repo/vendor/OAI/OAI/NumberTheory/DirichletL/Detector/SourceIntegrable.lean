module

public import OAI.NumberTheory.DirichletL.Detector.SourceTriple

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance (S : Finset (Ideal ActualEisensteinCubic.O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal ActualEisensteinCubic.O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

lemma sourceRows_initial_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal ActualEisensteinCubic.O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>
      sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
      sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  apply hi.integral_prod_right.congr
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp]
  have he := rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by simp)
    (by norm_num)
    (by simp)
  change rawArithmeticSeries S D η (calibrationForSet S hS) _ _ _=
    sourceRowSeries η S (calibrationForSet S hS) D _ _ _ at he
  rw [←he,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

end SevenEighths.ProbePhysical
end

end OAI
