module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.ActiveSource

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth


 section
variable (C D : Ideal HeckeFamily.O) (hC : C≠0) (hD : D≠0) (η : Character) (t : ℝ) (S : Finset (Ideal HeckeFamily.O)) (β f : Ideal HeckeFamily.O→ℂ)

theorem sectorPool_active     :
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active     
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  simp_all

 theorem sector_pair_sum_active    
      (f:Ideal HeckeFamily.O→Ideal HeckeFamily.O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_all [sector_sum_active]

 theorem sectorFrequency_active     
     C D  hC  hD  F  z :
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal HeckeFamily.O→Ideal HeckeFamily.O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal HeckeFamily.O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dite_eq_left hc,dite_eq_left hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active     
     C D  hC  hD  U 
     R  rows  W  K  n :
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

end

end SevenEighths.CenteredMomentSecondActivePhysicalDictionary



end OAI
