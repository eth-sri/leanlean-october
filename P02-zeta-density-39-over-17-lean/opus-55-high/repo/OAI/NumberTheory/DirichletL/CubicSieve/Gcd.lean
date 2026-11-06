module
public import OAI.NumberTheory.DirichletL.CubicSieve.Dyadic
public import OAI.NumberTheory.DirichletL.Descent.IdealMasks
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I z)

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

section
variable (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O)
include D hD z
lemma cubicRow_common_mask :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact SevenEighths.InverseMoment.ideal_coprime_mobius D _ (primaryGenerator_ne_zero_ideal D hD)
end

section
variable {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I)
include I D hI hD
lemma cubic_admissible_of_dvd :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  grind

lemma cubic_admissible_quotient :
    Admissible (idealQuotient D I) :=
  cubic_admissible_of_dvd hI (CanonicalQuadraticSieve.idealQuotient_dvd hD)
end

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact cubicRow_mul _ _ _

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      pm_1351 CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime
      · rw [ite_eq_left hg, ite_eq_left hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        pm_666 hk gcd_dvd_right
      simp only [cubicGcdTerm, ite_eq_right hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      pm_666 hj gcd_dvd_left
    simp only [cubicGcdTerm, ite_eq_right hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    pm_3005 cubicGcdTerm CanonicalQuadraticSieve.mem_gcdPool
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => cubicRow (cols j) z * a j)

end
end SevenEighths.CubicSieve

end OAI
