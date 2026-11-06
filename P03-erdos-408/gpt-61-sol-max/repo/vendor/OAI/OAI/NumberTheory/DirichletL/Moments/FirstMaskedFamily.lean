module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
public import OAI.NumberTheory.DirichletL.Moments.FixedRowMask
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily CenteredMomentSourceAllocationEnergy
open CenteredMomentAmplificationFamilyEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows

local notation "fixedBadMask" => (goodLambda*(2:HeckeFamily.O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

def idealMask (u : HeckeFamily.O) (I : Ideal HeckeFamily.O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : HeckeFamily.O) (β : Ideal HeckeFamily.O → ℂ) (I : Ideal HeckeFamily.O)  := β I * idealMask u I

lemma idealMask_span  u n  : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary  u   I  (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma rowWeight_mask_factor  η   u   I 
    (hI : Supported I)  t  :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_canonical_masked_pair  η   C D 
     hC   E   ξ₁ ξ₂  :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:HeckeFamily.O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal HeckeFamily.O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal HeckeFamily.O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : HeckeFamily.O, ∀ I : Ideal HeckeFamily.O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : HeckeFamily.O, ∀ I : Ideal HeckeFamily.O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:HeckeFamily.O)) (dvd_mul_left (2:HeckeFamily.O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : Character) (F : HeckeFamily.O → ℂ)  ξ 
    (hτ : ∀ I : Ideal HeckeFamily.O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
     u   L I  (hI : Supported I)  β   t  :
    divisorCoefficient L (fun J : Ideal HeckeFamily.O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma maskedSource_eq_of_live  u   β 
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  grind [maskedSource, idealMask]

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI
