module

public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeRowClosure

abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement

structure RowData where
  η : Character
  m : O
  f : O
  m_ne_zero : m≠0
  f_ne_zero : f≠0
  lambda_dvd : ConcretePrimeRowBridge.goodLambda∣m
  two_dvd : (2 : O)∣m

def RowData.character (data : RowData) (u : NonzeroElement)  :=
  Classical.choose (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)

section
variable (data : RowData) (u : NonzeroElement)

theorem RowData.character_spec      n  :
    elementCoeff (data.character u) n=
      CanonicalRowCompletion.rowTwist (elementHom data.η) data.m data.f u.val n :=
  Classical.choose_spec (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd) n

def amplifiedElement (u : NonzeroElement) (A : NonzeroIdeal) : NonzeroElement :=
  ⟨u.val*(ConcretePrimeRowBridge.idealGenerator A.val)^6,
    mul_ne_zero u.property (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero A.val A.property))⟩

theorem RowData.amplified_prime_mask    
     P  :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

theorem RowData.prime_energy    
    (P : SmoothMobiusCorrection.PrimeIdeal)  W  (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
     D σ freq  (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

end

end SevenEighths.HeckeInverseAmplification

end

end OAI
