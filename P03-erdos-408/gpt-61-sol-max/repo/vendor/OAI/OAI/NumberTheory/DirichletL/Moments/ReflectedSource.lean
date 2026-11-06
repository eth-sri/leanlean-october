module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection
public import OAI.NumberTheory.DirichletL.Hecke.UnitRows
public import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentReflectedSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow



def reflected (η:Character):=η.product (HeckeUnitRows.character (-1:HeckeFamily.Oˣ))

theorem unit_ideal  I (hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:HeckeFamily.Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,ite_eq_left hI]
  rfl

theorem reflected_height  η  t  I (hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,idealCoeff_product,unit_ideal I hI,heightCoeff]
  ring

theorem reflected_row  η  m A z n 
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:HeckeFamily.O)∣m):
    rowTwist (HeckeRowClosure.elementHom η) m 1 (A*(-z)) n=
      rowTwist (HeckeRowClosure.elementHom (reflected η)) m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change elementCoeff η n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      elementCoeff (reflected η) n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,elementCoeff_product,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:HeckeFamily.Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [ite_eq_left hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing  η  Q  m A z 
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:HeckeFamily.O)∣m):
    CenteredExceptionalProfile.FixedInducingRow η Q m A (-z) ↔
      CenteredExceptionalProfile.FixedInducingRow (reflected η) Q m A z:=by
  unfold CenteredExceptionalProfile.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]

end SevenEighths.CenteredMomentReflectedSource

end

end OAI
