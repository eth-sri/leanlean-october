module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion
public import OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics
open scoped ContDiff FourierTransform SchwartzMap BigOperators Classical
open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem supported_mul_iff (A B : Ideal O) : Supported (A * B) ↔ Supported A ∧ Supported B := by
  constructor
  · intro h
    have hA : A ≠ 0 := left_ne_zero_of_mul h.1
    have hB : B ≠ 0 := right_ne_zero_of_mul h.1
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inl hP)
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inr hP)
  · rintro ⟨hA, hB⟩
    refine ⟨mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hA.1 hB.1] at hP
    rcases Multiset.mem_add.mp hP with hP | hP
    · exact hA.2 P hP
    · exact hB.2 P hP

theorem supported_sq_iff (A : Ideal O) : Supported (A ^ 2) ↔ Supported A := by
  rw [pow_two, supported_mul_iff, and_self]

theorem supported_square_parts (lengthScale : Ideal O) :
    Supported lengthScale ↔ Supported (squarePart lengthScale) ∧ Admissible (squarefreePart lengthScale) := by
  have he := supported_mul_iff (squarePart lengthScale ^ 2) (squarefreePart lengthScale)
  rw [squarePart_sq_mul_squarefreePart, supported_sq_iff] at he
  rw [he]
  have hsf := squarefree_squarefreePart lengthScale
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hsf, hB.2⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hB.2.2⟩

def supportedSquarefreeEquiv : {lengthScale : Ideal O // Supported lengthScale} ≃
    ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) where
  toFun lengthScale := (⟨squarePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).1⟩,
    ⟨squarefreePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).2⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val,
    (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩⟩
  left_inv lengthScale := Subtype.ext (squarePart_sq_mul_squarefreePart lengthScale.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2

theorem canonical_quadraticRow_argument_mul (D : Ideal O) (hD : Admissible D) (a b : O) :
    quadraticRow D (a * b) = quadraticRow D a * quadraticRow D b := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  simp only [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ a b

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

theorem supported_generator_injective :
    Function.Injective (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => primaryGenerator lengthScale.val) := by
  intro I J h
  change primaryGenerator I.val = primaryGenerator J.val at h
  have hi := primaryGenerator_ne_zero_of_good_factors I.val I.property.1 (fun P hP => (I.property.2 P hP).1)
  have hj := primaryGenerator_ne_zero_of_good_factors J.val J.property.1 (fun P hP => (J.property.2 P hP).1)
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.val hi).1, ← (primaryGenerator_spec J.val hj).1, h]

theorem supported_radial_norm_summable (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun lengthScale : Ideal O => if Supported lengthScale then ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ else 0) := by
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  have hp := hs.comp_injective supported_generator_injective
  have hi : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => ‖W ((Ideal.absNorm lengthScale.val : ℝ) / M)‖) := by
    apply hp.congr
    intro lengthScale
    dsimp only [Function.comp_def]
    rw [primaryGenerator_norm_sq lengthScale.val (primaryGenerator_ne_zero_of_good_factors lengthScale.val
      lengthScale.property.1 (fun P hP => (lengthScale.property.2 P hP).1))]
  have ht : Summable (({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator
      (fun lengthScale => ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖)) := (summable_subtype_iff_indicator).mp hi
  exact ht

def originalPairSource (I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) (lengthScale : Ideal O) : ℂ :=
  if Supported lengthScale then (star (quadraticRow I (primaryGenerator lengthScale)) *
    quadraticRow J (primaryGenerator lengthScale)) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0

def originalPairLow (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K then originalPairSource I J W M lengthScale else 0

def originalPairHigh (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then originalPairSource I J W M lengthScale else 0

theorem originalPairSource_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun lengthScale => norm_nonneg _) _ (supported_radial_norm_summable W M hM)
  intro lengthScale
  by_cases hL : Supported lengthScale
  · simp only [originalPairSource, ite_eq_left hL, norm_mul, norm_star]
    calc
      _ ≤ (1 * 1) * ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ := by
        gcongr
        · exact quadraticRow_norm_le_one I _
        · exact quadraticRow_norm_le_one J _
      _ = _ := by ring
  · simp only [originalPairSource, ite_eq_right hL, norm_zero, le_refl]

theorem originalPairLow_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_eq_source_sub_low (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairHigh I J W M K lengthScale) =
      (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) -
        ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
  calc
    _ = ∑' lengthScale : Ideal O, (originalPairSource I J W M lengthScale - originalPairLow I J W M K lengthScale) := by
      apply tsum_congr
      intro lengthScale
      by_cases hK : (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K
      · simp [originalPairHigh, originalPairLow, hK, not_lt.mpr hK]
      · simp [originalPairHigh, originalPairLow, hK, lt_of_not_ge hK]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss EisensteinSchwartzPoisson GaussGeneratorTransport

theorem canonical_gcd_masked_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
      χ (primaryGenerator lengthScale) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let R := fun P : gcdMaskPrimes D => P.val
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask R Finset.univ z = 0 := by
    rw [gcdMaskPrimes_mask, badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => (supported_span_iff z).mp h |>.1 hz
    simp only [ite_eq_right hns, zero_mul]
  have hlat := canonical_same_ray_pair_poisson R Subtype.val_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_mask_lattice_eq_six_all_ideals R Finset.univ hm I J hI hJ hray W M hM
  have he : (∑' lengthScale : Ideal O, rowCoprimeMask R Finset.univ (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M)) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
        (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
    apply tsum_congr
    intro lengthScale
    rw [gcdMaskPrimes_mask, badPrime_mask_primaryGenerator]
    by_cases hL : Supported lengthScale <;> simp [hL]
  rw [he] at hid
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

theorem canonical_pair_divisor_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (z : O) :
    star (quadraticRow I z) * quadraticRow J z =
      idealZeroMask D z *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by
  rw [canonical_quadraticRow_star I hI, quadraticRow_divisor_factor I D hI hDI,
    quadraticRow_divisor_factor J D hJ hDJ]
  calc
    _ = (quadraticRow D z * quadraticRow D z) *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared D (admissible_of_dvd hI hDI)]

theorem canonical_original_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let I' := idealQuotient D I
    let J' := idealQuotient D J
    let n := primaryGenerator I' * primaryGenerator J'
    let χ := fun z => quadraticRow I' z * quadraticRow J' z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then
      (star (quadraticRow I (primaryGenerator lengthScale)) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hDI : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hDJ : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hcop := (gcd_eq_iff_quotient_coprime D I J hD.1 hDI hDJ).mp hgcd
  have hqray := columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray
  have h := canonical_gcd_masked_pair_poisson D (idealQuotient D I) (idealQuotient D J)
    hIq hJq hcop hqray W M hM
  simpa only [canonical_pair_divisor_mask D I J hI hJ hDI hDJ] using h

theorem residual_pair_nontrivial (D I J : Ideal O) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hIJ : I ≠ J) : idealQuotient D I ≠ 1 ∨ idealQuotient D J ≠ 1 := by
  by_contra hn
  push Not at hn
  apply hIJ
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hDI).symm
    _ = D := by rw [hn.1, mul_one]
    _ = D * idealQuotient D J := by rw [hn.2, mul_one]
    _ = J := idealQuotient_mul hDJ

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

def rayPairCoefficient (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I J : idealRange N) : ℂ :=
  if gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c then star (a I) * a J else 0

theorem annularRayGcdBlock_eq_pair_high
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ∑' lengthScale : Ideal O, originalPairHigh I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale := by
  let W := QuadraticInitialBound.annularSieveCutoff
  let f := fun (I J : idealRange N) (lengthScale : Ideal O) =>
    rayPairCoefficient N D c a I J * originalPairHigh I.val J.val W M K lengthScale
  have hf (I J : idealRange N) : Summable (f I J) :=
    (originalPairHigh_summable I.val J.val W M K hM).mul_left _
  have hterm (lengthScale : Ideal O) :
      (if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
        W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) =
      ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := by
    rw [rayPairValue_eq]
    by_cases hs : Supported lengthScale
    · by_cases hk : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)
      · have hsk : Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) := ⟨hs, hk⟩
        rw [ite_eq_left hsk]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [f, rayPairCoefficient, originalPairHigh, originalPairSource]
        rw [ite_eq_left hk, ite_eq_left hs]
        by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
        · rw [ite_eq_left hc, ite_eq_left hc]
          simp only [star_mul]
          ring
        · rw [ite_eq_right hc, ite_eq_right hc, zero_mul, mul_zero]
      · simp [f, originalPairHigh, hk]
    · simp [f, originalPairHigh, originalPairSource, hs]
  rw [annularRayGcdBlock_eq_tsum M N K hM D c a]
  change (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) = _
  calc
    _ = ∑' lengthScale : Ideal O, ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := tsum_congr hterm
    _ = ∑ I : idealRange N, ∑' lengthScale : Ideal O, ∑ J : idealRange N, f I J lengthScale :=
      Summable.tsum_finsetSum (fun I _ => summable_sum (fun J _ => hf I J))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Summable.tsum_finsetSum (fun J _ => hf I J)]
      apply Finset.sum_congr rfl
      intro J _
      exact tsum_mul_left

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss EisensteinSchwartzPoisson GaussGeneratorTransport

def originalPairDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, χ h * paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairSource_poisson (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) = originalPairDualKernel D I J W M :=
  canonical_original_pair_poisson D I J hI hJ hgcd hray W M hM

end CanonicalQuadraticSieve

namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels JointLogSeparation

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
