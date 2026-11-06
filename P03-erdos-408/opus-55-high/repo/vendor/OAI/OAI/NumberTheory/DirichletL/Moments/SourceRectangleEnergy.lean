module

public import OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
public import OAI.NumberTheory.DirichletL.Moments.RestrictedSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O→ℂ) (z : ActualEisensteinCubic.O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

theorem source_restricted_energy_eq_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (t : ℝ) (keep : ActualEisensteinCubic.O→Prop)
    (slots : ι→Finset (Ideal ActualEisensteinCubic.O)) (S₁ S₂ : Finset (Ideal ActualEisensteinCubic.O))
    (R L : Ideal ActualEisensteinCubic.O) (ν : ι→Ideal ActualEisensteinCubic.O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal ActualEisensteinCubic.O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (tuplePool slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff η t) W K=
      ∑' z : ActualEisensteinCubic.O,if keep z then
        ‖maskedRectangle η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2*
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂]

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI
