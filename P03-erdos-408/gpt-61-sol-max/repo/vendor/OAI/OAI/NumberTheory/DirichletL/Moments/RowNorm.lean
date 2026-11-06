module

public import OAI.NumberTheory.DirichletL.Moments.Initial
public import OAI.NumberTheory.DirichletL.Moments.Cauchy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport


def pairResidue (a b ) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b))  :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

section
variable (a b : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
include a b ha hb

@[simp] theorem pairResidue_mk    
       z  :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b ) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : ActualEisensteinCubic.O)  :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

theorem row_pair_summable    
      (W : 𝓢(ℝ, ℂ))  K  (hK : 0 < K) :
    Summable (fun z : ActualEisensteinCubic.O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

end

def rowPolynomial {α } (S : Finset α) (a : α → ActualEisensteinCubic.O) (c : α → ℂ) (z : ActualEisensteinCubic.O)  :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α } (S : Finset α) (a : α → ActualEisensteinCubic.O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ)  :=
  ∑' z : ActualEisensteinCubic.O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

section
variable {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O) (c : α → ℂ)
include α S a c

theorem rowPolynomial_norm_sq      
       z  :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rowEnergy_expand        
    (ha : ∀ i, Supported (Ideal.span {a i}))
     W   K  (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : ActualEisensteinCubic.O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

end

end SevenEighths.CenteredMomentRowNorm

end

end OAI
