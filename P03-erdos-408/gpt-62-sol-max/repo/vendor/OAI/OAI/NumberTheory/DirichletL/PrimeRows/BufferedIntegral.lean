module

public import OAI.NumberTheory.DirichletL.PrimeRows.CoarseAmplitude
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u mw.left mw.right X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C0,hC0,hbound0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  let C := C0 * contourArithmeticCost η u P * (3+|H|)^2
  have hC : 0≤C := by dsimp [C]; positivity [contourArithmeticCost_nonneg η u P]
  have hbound := hbound0 η u hu P hPS ψ a B H i ha haTop hB hH hbin σ ⟨hσ,hσ2⟩ r ⟨hr,hr1⟩
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound mw
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    refine le_mul_of_one_le_right hC ?_
    nlinarith [abs_nonneg t.1.1]
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous mw.left mw.right mw.rightLo mw.rightHi mw.right_pos mw.right_support X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight mw.left mw.right X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u mw.left mw.right X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily

end

end OAI
