module

public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorFrequency CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentHeckeColumnWindow


section
variable (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset ActualEisensteinCubic.O) (hrows : ∀z∈rows,z≠0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)

include hCD in
theorem normalizedBlock_zero_of_common        
         
       
             
    (hz:∀z∈rows,idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)=0) :
    normalizedBlock η t S β C D hC hD U R rows W K n=0 := by
  unfold normalizedBlock
  apply Finset.sum_eq_zero
  intro z hzr
  let F:ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) (hz z hzr)
  simpa only [sectorFrequency,F,mul_zero] using congrArg (fun x:ℂ=>retainedScalar C D U R z*x) he

include hCD in
theorem normalizedBlock_nonzero_common        
         
       
             
    (hne:normalizedBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  by_contra hn
  push Not at hn
  apply hne
  exact normalizedBlock_zero_of_common η t S β C D hC hD hCD U R rows W K n
    (fun z hz=>by simpa only [mul_assoc] using hn z hz)

include hCD hrows hK in
theorem physicalBlock_nonzero_common        
         
       
         
           
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  exact normalizedBlock_nonzero_common η t S β C D hC hD hCD U R rows W K n
    (right_ne_zero_of_mul hne)

end

end SevenEighths.CenteredMomentSecondBlockSupport



end OAI
