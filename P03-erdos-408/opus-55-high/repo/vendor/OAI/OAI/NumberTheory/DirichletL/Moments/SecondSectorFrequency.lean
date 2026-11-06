module

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
public import OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondSectorFrequency
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst

def sectorFrequency (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ)
    (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (j : ActualEisensteinCubic.O) : ℂ :=
  ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
    (if IsCoprime (I:Ideal ActualEisensteinCubic.O) (J:Ideal ActualEisensteinCubic.O) then
      idealCorrelation (C*I) (D*J)
        ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
        ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) j
      else 0)*((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F j I J

theorem sectorFrequency_zero_of_common (η : Character) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (j : ActualEisensteinCubic.O) (hj : idealCorrelation C D hC hD j=0) :
    sectorFrequency η t S β C D hC hD F j=0 := by
  have he := sector_correlation_children η t S β C D hC hD hCD 1 {j} (fun _=>1) F
  simpa only [Finset.sum_singleton,one_mul,hj,zero_mul,mul_zero,Finset.sum_const_zero,
    sectorFrequency] using he

theorem sectorFrequency_common_support (η : Character) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) (j : ActualEisensteinCubic.O)
    (hj : sectorFrequency η t S β C D hC hD F j≠0) : commonFrequencyGenerator C D∣j := by
  by_contra hn
  exact hj (sectorFrequency_zero_of_common η t S β C D hC hD hCD F j
    (idealCorrelation_zero_outside_common C D hC hD hCD j hn))

theorem sectorFrequency_tsum_common (η : Character) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) :
    (∑' j : ActualEisensteinCubic.O,sectorFrequency η t S β C D hC hD F j)=
      ∑' w : ActualEisensteinCubic.O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq
    (f := sectorFrequency η t S β C D hC hD F) ?_
  intro j hj
  obtain ⟨w,hw⟩ := sectorFrequency_common_support η t S β C D hC hD hCD F j hj
  simp_all

theorem sectorFrequency_tsum_partition (η : Character) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ)
    (hs : Summable (fun w : ActualEisensteinCubic.O=>sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))) :
    (∑' w : ActualEisensteinCubic.O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))=
      ∑ U : Finset (CommonIndex C D),∑' w : ActualEisensteinCubic.O,if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
  have he (w : ActualEisensteinCubic.O) : sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w)=
      ∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
    simp [canonicalPartition,eq_comm]
  calc
    _ = ∑' w : ActualEisensteinCubic.O,∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun U _=>hs.indicator {w | canonicalPartition C D U w})

theorem sectorFrequency_partition_nonunit (η : Character) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) :
    (∑' w : ActualEisensteinCubic.O,if canonicalPartition C D U w then
      sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0)=
      ∑' h : ActualEisensteinCubic.O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD F
          ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  let f : ActualEisensteinCubic.O→ℂ := fun w=>if canonicalPartition C D U w then
    sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by grind)
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact by grind
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end SevenEighths.CenteredMomentSecondSectorFrequency

end

end OAI
