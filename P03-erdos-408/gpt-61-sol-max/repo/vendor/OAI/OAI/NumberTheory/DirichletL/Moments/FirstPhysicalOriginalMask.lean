module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
public import OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalOriginalMask
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstMaskedFamily CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonSupport
open CenteredMomentFirstRetainedNorm CenteredMomentFirstSourceReduction
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
lemma original_coefficient (s : Input ι)  R seed C I 
    (hI : Supported I)  t  :
    CenteredMomentFirstPhysicalSource.coefficient s.η (fixedBadMask*idealGenerator R) 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I =
    CenteredMomentFirstPhysicalSource.coefficient s.η fixedBadMask 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I := by
  unfold CenteredMomentFirstPhysicalSource.coefficient
  by_cases h : CenteredMomentOriginalCommonHarmonic.coefficient s R seed (C*I)=0
  · simp [h]
  · have hc : IsCoprime I R :=
      (beta_coprime (original s R seed) (C*I) h).of_mul_left_right
    have hw := rowWeight_mask_factor s.η (idealGenerator R) I hI t
    change CenteredMomentHeckeExpansion.rowWeight s.η (fixedBadMask*idealGenerator R) 1 1 t I =
      idealMask (idealGenerator R) I * CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 t I at hw
    rw [hw]
    simp only [idealMask, span_idealGenerator, hc, ite_true, one_mul]

omit [DecidableEq ι] in
theorem original_block (s : Input ι)  R seed   t 
     S   C D   hC   hD 
     E   rows   W 
     V   K K₀ H₀ A₀ B₀  :
    block s.η (fixedBadMask*idealGenerator R) 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ =
    block s.η fixedBadMask 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  unfold block
  apply congrArg (fun z : ℂ => inactiveWeight C D E * z)
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [original_coefficient s R seed C a (column_supported C C hC.1 S a) t,
    original_coefficient s R seed D b (column_supported C D hD.1 S b) t]

omit [DecidableEq ι] in
lemma original_sectorMass (s : Input ι)  R seed   t 
     S   C D   hC   hD 
     W   K X Z ξ  :
    sectorMass s R seed (fixedBadMask*idealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sectorMass s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  simp_rw [original_block]

omit [DecidableEq ι] in
theorem original_physicalMass (s : Input ι)  R seed 
     W   K Z ξ  :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
    physicalMass s R seed fixedBadMask 1 W K Z ξ := by
  unfold physicalMass
  simp_rw [original_sectorMass]

end SevenEighths.CenteredMomentFirstPhysicalOriginalMask

end

end OAI
