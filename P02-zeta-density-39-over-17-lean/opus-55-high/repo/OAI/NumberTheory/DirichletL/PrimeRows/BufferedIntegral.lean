module
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedGrowth
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  pm_3482
  intro t ht
  pm_3475
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simp) (by simpa using hr)
  pm_3476
  unfold rowAmplitudeOnLines
  pm_3477 hA

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  pm_3483
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    pm_3478
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily


end OAI
