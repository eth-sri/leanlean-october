module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBlock

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBlock CenteredMomentHeckeColumnWindow


def outerScalar (C D : Ideal ActualEisensteinCubic.O) (K : ℝ) (n : Fin 4→ℤ)  :=
  K/(Real.sqrt (Ideal.absNorm C:ℝ)*Real.sqrt (Ideal.absNorm D:ℝ)*
    Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3)))

def physicalBlock (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ)
    (C D ) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)  :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) then
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal ActualEisensteinCubic.O) (J:Ideal ActualEisensteinCubic.O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      (physicalKernel C D W K R (A*z) I J*
        ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue z)*
          dyadicWeight (n 2) (Ideal.absNorm (I:Ideal ActualEisensteinCubic.O):ℝ)*
          dyadicWeight (n 3) (Ideal.absNorm (J:Ideal ActualEisensteinCubic.O):ℝ):ℝ):ℂ)) else 0

def normalizedBlock (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ)
    (C D ) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)  :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,retainedScalar C D U R z*
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal ActualEisensteinCubic.O) (J:Ideal ActualEisensteinCubic.O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue z/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm (I:Ideal ActualEisensteinCubic.O):ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm (J:Ideal ActualEisensteinCubic.O):ℝ)/dyadicScale (n 3)))

private lemma physicalBlock_scalar (a b c d e f : ℂ) (hb : b ≠ 0) :
    c * d * (a * e * f) = a * b * (b⁻¹ * e * (c * d * f)) := by
  field_simp <;> ring

theorem physicalBlock_eq  η   t   S   β 
     C D   hC   hD   U 
     R   rows  (hrows : ∀z∈rows,z≠0)
     W   K  (hK : 0<K)  n  :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        normalizedBlock η t S β C D hC hD U R rows W K n := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock normalizedBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [physical_kernel_dyadic C D _ _ hC hD
    (sectorPool_supported C hC.1 S _) (sectorPool_supported D hD.1 S _)
    _ z hA (hrows z hz) W K R hK n]
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  simp only [outerScalar,Complex.ofReal_div,Complex.ofReal_mul,retainedScalar,canonicalPartitionScalar]
  simp only [normalizer] at hn ⊢
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*z)
  · simp only [hp,ite_true]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    solve_by_elim [physicalBlock_scalar]
  · simp only [hp,ite_false,mul_zero,zero_mul,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI
