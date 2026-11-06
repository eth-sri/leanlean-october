module

public import OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open Set
open scoped Classical
open scoped Classical

open scoped Classical
namespace CanonicalQuadraticSieve
open ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem unrestrictedPrincipalDensity_twisted_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q))
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),
      normalizedIdealPair,unrestrictedPairCharacter,Complex.ofReal_div]
    ring
  simp_all

theorem densityPairSum_weighted_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : Ideal O → Ideal O → ℂ) (Q : ι → Ideal O → Ideal O → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · grind
  simp_all

theorem summed_dual_density {n : Type} [Fintype n] [DecidableEq n]
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
      rw [Finset.mul_sum]
      grind
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl

theorem actual_source_dual_density_cancellation {n : Type} [Fintype n] [DecidableEq n]
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

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped Classical

namespace CubicEisenstein

section

open Filter MeasureTheory
open scoped Classical

def cuspBaseArea : Measure (ℝ×ℝ) := volume.restrict cuspRectangle
instance cuspBaseArea_sFinite : SFinite cuspBaseArea := by unfold cuspBaseArea; infer_instance

end

section
open Filter MeasureTheory
open scoped Classical

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (by grind) 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num
  ring

end

open Filter MeasureTheory
open scoped Classical

end CubicEisenstein

open scoped Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
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

theorem originalPairIdealDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
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
  grind

theorem originalPairDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M

end CanonicalQuadraticSieve

end

end OAI
