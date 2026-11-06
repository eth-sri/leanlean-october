module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
public import OAI.NumberTheory.DirichletL.Moments.RowNorm

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss


section
variable (η : Character) (m A z : ActualEisensteinCubic.O) (t : ℝ)

theorem rowWeight_split        I  :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported      
    (hmLam : goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)  I  (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

def supportedColumns (S : Finset (Ideal ActualEisensteinCubic.O))  := S.filter Supported

theorem primary_span_supported  I  (hI : Supported I) : Ideal.span {primaryGenerator I}=I := by
  have hn : primaryGenerator I ≠ 0 := by
    have hs : Supported (Ideal.span {idealGenerator I}) := by rw [span_idealGenerator]; exact hI
    have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff (idealGenerator I)).mpr
      ((supported_span_iff _).mp hs).1
    simpa only [span_idealGenerator] using hg
  exact (primaryGenerator_spec I hn).1

def sourceGenerator (S ) (I : supportedColumns S)  := primaryGenerator I

theorem sourceGenerator_supported  S   I  :
    Supported (Ideal.span {sourceGenerator S I}) := by
  have hI := (Finset.mem_filter.mp I.property).2
  rw [sourceGenerator,primary_span_supported I hI]
  exact hI

theorem finite_hecke_sum_eq_rowPolynomial      
    (hmLam : goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (c : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    grind [rowWeight_zero_of_not_supported]
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

end

def finiteHeckeEnergy (η : Character) (m A : ActualEisensteinCubic.O) (t : ℝ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (c : Ideal ActualEisensteinCubic.O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ)  :=
  ∑' z : ActualEisensteinCubic.O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)

theorem finiteHeckeEnergy_eq  η   m A   t 
    (hmLam : goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
     S   c   W   K  :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

end SevenEighths.CenteredMomentSourceRow

end

end OAI
