module
public import OAI.NumberTheory.DirichletL.CubicSieve.DualCoefficients
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  pm_5832
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖eisEmbedding z‖ ^ 2 / M) else 0

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryGenerator_norm_sq I hI.2, primaryGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  pm_3817
  · simp only [ite_eq_left hcop]
    pm_3802
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    convert hs using 1
    pm_3801
    grind
  simp_all

section
variable {n : Type*} [Fintype n] (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M)
include n cols hc a W M hM
lemma cubicDualRow_tsum :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    pm_3802
    convert cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    pm_3801
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    pm_3803
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    pm_3803
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  pm_3170 j hj Finset.mul_sum k hk
  pm_3817
  · rw [ite_eq_left hcop, ite_eq_left hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero]
end

end
end SevenEighths.CubicSieve

end OAI
