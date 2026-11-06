module
public import OAI.NumberTheory.DirichletL.Moments.RowNorm
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def gaussRow (a : O) (ha : Supported (Ideal.span {a})) (z : O) : ℂ :=
  ProbePhysical.sexticGauss a (supported_element_ne_zero a ha) z /
    (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  pm_2978
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

def gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

def gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

section
variable {α : Type*} (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
include α S a ha c
theorem gaussPolynomial_norm_sq (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  pm_3622
  ring

theorem gaussEnergy_expand
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) *
          W (‖eisEmbedding z‖ ^ 2 / K) := by pm_2979 gaussRow_pair_summable gaussEnergy gaussPolynomial_norm_sq
end

section
variable {α : Type*} (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
include α S a ha c W K hK
theorem gaussEnergy_summable :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by pm_2878 gaussRow_pair_summable gaussPolynomial_norm_sq

theorem finite_energy_le_gaussEnergy (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  pm_5933 gaussEnergy_summable W
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖eisEmbedding z‖ ^ 2 / K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem gaussEnergy_poisson :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ))) *
          ∑' h : O, actualCorrelation (a i) (a j) (ha i) (ha j) (-h) *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [gaussEnergy_expand S a ha c W K hK]
  pm_3622
  simp only [gaussRow]
  rw [sextic_gauss_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]
end

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
