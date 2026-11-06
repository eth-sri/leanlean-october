module

public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
public import OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

end SevenEighths.CenteredMomentSecondFamilyTransport

end

end OAI
