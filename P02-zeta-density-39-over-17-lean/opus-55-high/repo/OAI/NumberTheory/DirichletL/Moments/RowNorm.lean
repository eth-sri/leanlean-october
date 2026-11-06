module
public import OAI.NumberTheory.DirichletL.Moments.Initial
public import OAI.NumberTheory.DirichletL.Moments.Cauchy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  pm_2978
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simp_all

def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  pm_3622
  ring

theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by pm_2979 row_pair_summable rowEnergy rowPolynomial_norm_sq

end SevenEighths.CenteredMomentRowNorm

end

end OAI
