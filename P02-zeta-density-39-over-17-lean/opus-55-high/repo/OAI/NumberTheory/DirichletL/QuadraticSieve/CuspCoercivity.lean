module
public import OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

section
variable {n : Type} [Fintype n]
include n
theorem unrestrictedPrincipalDensity_twisted_squarefree [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q))
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  pm_3782
  pm_2996
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),
      normalizedIdealPair,unrestrictedPairCharacter,Complex.ofReal_div]
    ring
  grind

theorem densityPairSum_weighted_sum
    (cols : n → Ideal O) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : Ideal O → Ideal O → ℂ) (Q : ι → Ideal O → Ideal O → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  pm_3815
  pm_2996
  grind
  simp_all

theorem summed_dual_density [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM hcols]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
      pm_4886 q hq
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl

theorem actual_source_dual_density_cancellation [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (hG : G ≠ 0)
    (M K : ℝ) (hM : 0 ≤ M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) -
      maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K := by
  rw [summed_dual_density cols a G M K hM hcols,
    maskedSourceDensity_coprime_squarefree G hG K M hM cols a hcols hray hGc hbad,
    actualPrincipalDifference_densityColumn cols a G K
      (fun j => (hcols j).1) (fun j => (hGc j).symm)]
  change _ = (Real.sqrt M:ℂ)*(densityPairSum cols a
    (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) -
    primePoolDensity G*densityPairSum cols a (fun I J => normalizedPairCoprimePartial I J G K))
  ring
end

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped Classical Topology InnerProductSpace

namespace CubicEisenstein

section

open Filter MeasureTheory
open scoped Classical Topology InnerProductSpace ENNReal

end

section
open Filter MeasureTheory
open scoped Classical Topology ENNReal

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  ring

end

open Filter MeasureTheory
open scoped Classical Topology InnerProductSpace ENNReal ContDiff

end CubicEisenstein

open scoped Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    pm_6261
  have hf : UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
    simpa [commonMaskIdeal] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  rw [IdealMobiusDivisorSum.primeSupport,hf,Finset.val_toFinset]

theorem commonMask_subset_sum_eq_divisors (D : Ideal O) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ q ∈ idealDivisors (commonMaskIdeal D), f q := by
  rw [sum_subtype_powerset_products,← commonMaskIdeal_primeSupport D]
  exact (squarefree_divisor_sum_eq_support _ (commonMaskIdeal_squarefree D) f).symm

theorem primaryProduct_norm (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖ =
      Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hs : ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2 =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
    rw [map_mul,norm_mul,mul_pow,
      primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I (admissible_supported hI)),
      primaryGenerator_norm_sq J (supported_primaryGenerator_ne_zero J (admissible_supported hJ))]
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

def maskedPairIdealDualKernel (G I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))

section
variable (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hDI : D ∣ I) (hDJ : D ∣ J)
include D I J hI hJ hDI hDJ
theorem originalPairIdealDualKernel_eq_divisors (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  pm_6263
  have hn := primaryProduct_norm Q T hQ hT
  have hnonneg : 0 ≤ (Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ) := by positivity
  unfold originalPairIdealDualKernel maskedPairIdealDualKernel
  change ((M:ℂ)/(‖eisEmbedding (primaryGenerator Q*primaryGenerator T)‖:ℂ))*_ =
    ((M:ℂ)/(Real.sqrt ((Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ)):ℂ))*_
  rw [hn]
  congr 1
  rw [← commonMask_subset_sum_eq_divisors D]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Real.sq_sqrt hnonneg,primeSubsetGenerator,unrestrictedPairCharacter,
    idealGenerator_norm_sq,Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro B
  congr 2
  ring

theorem originalPairDualKernel_eq_divisors (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M
end

end CanonicalQuadraticSieve

end

end OAI
