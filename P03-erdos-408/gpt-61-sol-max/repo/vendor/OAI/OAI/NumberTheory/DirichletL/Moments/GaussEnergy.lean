module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.RowNorm

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation


def gaussRow (a ) (ha : Supported (Ideal.span {a})) (z : ActualEisensteinCubic.O)  :=
  ProbePhysical.sexticGauss a (supported_element_ne_zero a ha) z /
    (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)

theorem gaussRow_pair_summable (a b : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ))  K  (hK : 0 < K) :
    Summable (fun z : ActualEisensteinCubic.O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

def gaussPolynomial {α } (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : ActualEisensteinCubic.O)  :=
  ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

def gaussEnergy {α } (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ)  :=
  ∑' z : ActualEisensteinCubic.O, ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

section
variable {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
include α S a ha c

theorem gaussPolynomial_norm_sq      
         z  :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

section
variable (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
include W K hK

theorem gaussEnergy_expand      
       
          :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : ActualEisensteinCubic.O, (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) *
          W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussEnergy, gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem gaussEnergy_summable      
       
          :
    Summable (fun z : ActualEisensteinCubic.O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_gaussEnergy      
       
           rows 
    (hW : ∀ z : ActualEisensteinCubic.O, 0 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖eisEmbedding z‖ ^ 2 / K)).re := by
      bound
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem gaussEnergy_poisson      
       
          :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ))) *
          ∑' h : ActualEisensteinCubic.O, actualCorrelation (a i) (a j) (ha i) (ha j) (-h) *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [gaussEnergy_expand S a ha c W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gaussRow]
  rw [sextic_gauss_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end

end

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
