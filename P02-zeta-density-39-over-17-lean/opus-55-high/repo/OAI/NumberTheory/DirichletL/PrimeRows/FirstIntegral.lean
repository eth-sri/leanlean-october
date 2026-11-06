module
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstJoint
public import OAI.NumberTheory.DirichletL.PrimeRows.WZTransport
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowAmplitudeOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1))*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u
        ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I))

section
variable {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
include K S hS hmax P hPS η u
lemma continuedRowOnLines_eq_amplitude
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0<elementNorm (CompletedGauss.primaryGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  pm_6883 hN
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  fun_prop
end

lemma rowAmplitudeOnLines_first_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (υ r : ℝ)
    (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  pm_3171 B C mul_nonneg hB hC
  intro t
  pm_3475
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  pm_3476
  unfold rowAmplitudeOnLines
  pm_3477 hB

theorem continuedPhysicalRowKernel_first_integrable {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_first_bound S hS hmax hfirst P hPS η u hu υ r hυ hr
  have hm := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hbound t).trans
    pm_3478
  have hi := (hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC _ hm.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ 2 r υ (by linarith)
  have hk : AEStronglyMeasurable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
    have heq : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun t=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
          rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t) := by funext t;exact continuedRowOnLines_eq_amplitude ..
    rw [heq]
    exact hs.aestronglyMeasurable.mul hm.aestronglyMeasurable
  exact hi.mono' hk (Filter.Eventually.of_forall fun t=>by rw [continuedRowOnLines_eq_amplitude,norm_mul])

end SevenEighths.ProbeHighRowFamily

end

end OAI
