module

public import OAI.NumberTheory.DirichletL.Detector.PhysicalRawIntegral
public import OAI.NumberTheory.DirichletL.Detector.RawArithmetic
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

def rawSourceOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  initialHighOnLines S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val))
    3 3 2 (sourceRawEmbedding S i) p *sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

lemma originalRawOnLines_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (i : SourceRawIndex S) (p : HeightSpace) :
    originalRawOnLines η S hS D W0 W1 X Y Z i p=
      rawSourceOnLines η S hS D W0 W1 X Y Z i (sourceHeightShear.symm p) := by
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ i.property.1
    i.property.2 W0 W1 X Y Z hX i.val.1]
  have he : (4:ℂ)+p.1.1*Complex.I+1-((2:ℂ)+p.1.2*Complex.I)=
      3+((p.1.1-p.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hs : sourceHeightShear.symm p=((p.1.1-p.1.2,p.1.2),p.2) := rfl
  simp only [rawSourceOnLines,initialHighOnLines,he,hs,sourceRawEmbedding,Complex.ofReal_ofNat]
  ring

lemma rawSourceOnLines_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>rawSourceOnLines η S hS D mw.left mw.right X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  have hm (H : NonzeroFrequency) : ‖star ((calibrationForSet S hS).residueMonoid H.val)‖≤1 := by
    simpa only [norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  unfold rawSourceOnLines
  apply initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) hm 3 3 2
    (by norm_num) (by norm_num) (by norm_num)
    (fun p : HeightSpace=>sourceMellinWeight mw.left mw.right X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I))
  · exact sourceMellinWeight_initial_integrable mw
      X Y Z hX hY hZ 3 2 3 (by norm_num)
  · exact sourceMellinWeight_initial_continuous mw.left mw.right mw.rightLo mw.rightHi mw.right_pos mw.right_support
      X Y Z hX hY hZ 3 2 3 (by norm_num)

lemma rawPhysicalTotalIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : SourceRawIndex S×HeightSpace,rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2
          ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  unfold rawPhysicalTotalIntegral
  congr 1
  let e  :=
    (MeasurableEquiv.refl (SourceRawIndex S)).prodCongr sourceHeightShear.symm
  have hp : MeasurePreserving e ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) :=
    (MeasurePreserving.id _).prod (sourceHeightShear_preserving.symm sourceHeightShear)
  have he := hp.integral_comp' (fun p : SourceRawIndex S×HeightSpace=>
    rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
  refine Eq.trans ?_ he
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact originalRawOnLines_eq_source η S hS hpS hbad D W0 W1 X Y Z hX p.1 p.2

def rawSourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    rawArithmeticSeries S D η (calibrationForSet S hS) ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawPhysicalTotalIntegral_eq_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawPhysicalTotalIntegral η S hS D mw.left mw.right X Y Z=
      rawSourceTripleIntegral η S hS D mw.left mw.right X Y Z := by
  rw [rawPhysicalTotalIntegral_eq_source η S hS hpS hbad D mw.left mw.right X Y Z hX]
  unfold rawSourceTripleIntegral
  congr 1
  have hi := rawSourceOnLines_integrable η S hS D mw
    X Y Z hX hY hZ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

theorem markedPhysicalProbe_eq_raw_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D mw.left mw.right X Y Z=
      rawSourceTripleIntegral η S hS D mw.left mw.right X Y Z := by
  rw [markedPhysicalProbe_eq_raw_integral η S hS hpS hbad hSne D mw
    X Y Z hX hY hZ]
  exact rawPhysicalTotalIntegral_eq_triple η S hS hpS hbad D mw
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI
