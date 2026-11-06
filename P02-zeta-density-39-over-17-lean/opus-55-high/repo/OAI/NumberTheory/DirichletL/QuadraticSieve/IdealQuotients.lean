module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound
public import OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
public import OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

set_option hygiene false in
macro "pf_239" x1:term:max x2:term:max : tactic => `(tactic| (
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I $x1:term).1.symm
    _ = Ideal.span {primaryGenerator J} := by grind
    _ = J := (primaryGenerator_spec J $x2:term).1))
theorem primaryGenerator_inj_on_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J) (heq : primaryGenerator I = primaryGenerator J) : I = J := by pf_239 (primaryGenerator_admissible I hI) (primaryGenerator_admissible J hJ)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  pm_7214
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => (hF I hI).1
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (hF I hI).2.2 P hP |>.1
  have hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2 := by
    intro i
    obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp i.property
    exact (hF I hI).2.2 i.val hP |>.2
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    pm_136 z hz I hI Finset.mem_image.mp
    rw [primaryGenerator_norm_sq I (primaryGenerator_admissible I (mem_idealRange.mp hI).1)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N)
  pm_3070
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3) =
        ∑ J : F, quadraticRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [quadraticRow_eq F hF J.val J.property z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 3 =
      (idealSexticRow F hFp hFg J.val z) ^ 3 * a J
    exact mul_comm _ _
  have he := QuadraticInitialBound.ideal_initial_quadratic_sieve F hFp hFg
    (fun I hI => (hF I hI).2.1) hchar ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2 := by
    pm_3072
  pm_3071

end

open ActualEisensteinCubic CompletedGauss

def idealQuotient (D I : Ideal O) : Ideal O := if h : D ∣ I then h.choose else 0

section
variable {D I : Ideal O} (h : D ∣ I)
include D I h
theorem idealQuotient_mul : D * idealQuotient D I = I := by
  rw [idealQuotient, dite_eq_left h]
  exact h.choose_spec.symm

theorem idealQuotient_dvd : idealQuotient D I ∣ I := by
  refine ⟨D, ?_⟩
  rw [mul_comm, idealQuotient_mul h]
end

theorem idealQuotient_injective_on (D : Ideal O) :
    Set.InjOn (idealQuotient D) {I | D ∣ I} := by
  intro I hI J hJ heq
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hI).symm
    _ = D * idealQuotient D J := by rw [heq]
    _ = J := idealQuotient_mul hJ

theorem admissible_of_dvd {I J : Ideal O} (hI : Admissible I) (hJI : J ∣ I) : Admissible J := by
  have hJ : J ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hJI
  refine ⟨hJ, hI.2.1.squarefree_of_dvd hJI, ?_⟩
  intro P hP
  have hfac := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI.1).mp hJI
  exact hI.2.2 P (Multiset.mem_of_le hfac hP)

theorem admissible_idealQuotient {D I : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) := admissible_of_dvd hI (idealQuotient_dvd hD)

theorem idealQuotient_norm_le {D I : Ideal O} (hD0 : D ≠ 0) (hD : D ∣ I)
    (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hp : (0 : ℝ) < Ideal.absNorm D := by
    pm_3073 Nat.pos_of_ne_zero h hD0
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (Ideal.absNorm (D * idealQuotient D I) : ℝ) := by
      rw [map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm I : ℝ) := by rw [idealQuotient_mul hD]
    _ ≤ N := hN

theorem quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  pm_7986 family_squared_norm_le
  pm_3074

def quotientMatrix {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) :
    Matrix m n ℂ := fun i j => if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0

theorem quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  pm_3076
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
    pm_681 quotient_family_squared_norm_le
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (sieveNorm_nonneg _ _)
  pm_3075
  calc
    _ ≤ sieveNorm M (N / (Ideal.absNorm D : ℝ)) * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sieveNorm_nonneg _ _)
      pm_3077

end CanonicalQuadraticSieve

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge

def fourierSeminormBound (k : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ k * (k + 1) *
    (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C

def fourierPointBound (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ k * (fourierSeminormBound 0 C + fourierSeminormBound k C)

theorem fourierPointBound_nonneg (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierPointBound k C := by unfold fourierPointBound fourierSeminormBound; positivity

theorem uniform_fourier_pointwise (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C)
    (t : ℝ) :
    S * (1 + ‖t‖) ^ k * ‖(𝓕 g) t‖ ≤ fourierPointBound k C := by
  have h0 : S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) ≤ fourierSeminormBound 0 C :=
    uniform_fourier_seminorm_transfer g 0 S C hS hC
      (fun i hi => hsource i (hi.trans (Nat.zero_le k)))
  have hk : S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤ fourierSeminormBound k C :=
    uniform_fourier_seminorm_transfer g k S C hS hC hsource
  have hpow : (1 + ‖t‖) ^ k ≤ (2 : ℝ) ^ k * (1 + ‖t‖ ^ k) := by
    pm_7360 h k
    pm_5401 he k
    simp only [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hn0 := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) t
  have hnk := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 g) k t
  calc
    _ ≤ S * ((2 : ℝ) ^ k * (1 + ‖t‖ ^ k)) * ‖(𝓕 g) t‖ := by gcongr
    _ = (2 : ℝ) ^ k * (S * ‖(𝓕 g) t‖ + S * (‖t‖ ^ k * ‖(𝓕 g) t‖)) := by ring
    _ ≤ (2 : ℝ) ^ k * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g)) := by gcongr
    _ ≤ fourierPointBound k C := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 hk) (by positivity)

end FourierBridge

namespace LocalLogFourier

set_option hygiene false in
macro "pb_585" : tactic => `(tactic| (
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J))
theorem coupled_positive_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  pm_3079
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  let C : ℝ := (B + Bpoint) / m ^ A
  pm_5893 hP P Lwin hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hBpoint : 0 ≤ Bpoint := FourierBridge.fourierPointBound_nonneg J P hP
  pm_3442
  refine ⟨C, hC, ?_⟩
  pb_585
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      pm_6049
    pm_3080
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hBpoint) (by positivity))
  · intro t
    pm_3078
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hB) (by positivity))

end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_envelope V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

def rayIdealRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  conjugateIdealRowSum (supportIdealFamily P (F \ D))
    (supportIdealFamily_pos P (F \ D)) (supportIdealFamily_good P hg (F \ D))
    (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
      else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C (D ∪ recoveredSupport P (F \ D) I)) h

def cubeLogCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C V y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C V y t) d

end FirstPassCubeLabels

end

end OAI
