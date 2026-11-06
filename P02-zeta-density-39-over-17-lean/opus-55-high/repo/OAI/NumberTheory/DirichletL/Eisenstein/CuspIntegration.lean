module
public import OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical Topology

end CubicEisenstein

open scoped Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp_all
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  simp_all
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

section
variable (G : Ideal O)
include G
theorem primePool_singleton_eq_primeSupport :
    primePool {G} = primeSupport G := by
  simp [primePool, primeSupport]

theorem primePool_subset_sum_eq_divisors (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primePool {G})).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products, primePool_singleton_eq_primeSupport]
  exact (squarefree_divisor_sum_eq_support G hG f).symm

theorem middleTruncation_eq_ideal_divisors (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primePool_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  pm_6624 hc
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2 =
        X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  pm_2997 hc ite_false mul_zero Finset.sum_const_zero

theorem principalTruncation_eq_ideal_divisors (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primePool {G}, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primePool_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primePool_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]
end

end

open ActualEisensteinCubic

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  pm_3719 h hh
  pm_3619
  pm_3719 d hd
  pm_3010 hμ d

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  pm_7026 a b f b.val
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem original_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
        else 0 else 0))]
  pm_3717
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    rw [middleTruncation_eq_ideal_frequencies _ hsq, Finset.mul_sum]
    pm_3620
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, originalPrincipalKernel]
        ring
      pm_3429 hdv hp ite_true ite_false mul_zero
    pm_2997 hdv ite_false ite_self mul_zero
  pm_3621

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
      else 0 else 0
  have he : originalTruncatedMiddle W rows left right a b M Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold originalTruncatedMiddle
    pm_3622
    apply Finset.sum_congr rfl
    intro k hk
    exact original_truncated_pair_expansion W K rows left right a b M Y Z lengthScale hleft hright hK i j k
  pm_3624
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d.val i
      else 0 else 0‖)]
  pm_8260 originalProductDivisorMiddleAt
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
      else 0 else 0‖)]
  pm_3623

theorem HasSieveExponent.original_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  pm_3625
  have hb := hexp.original_product_divisor_middle deltaLoss hδ ε hε K B N M U hB hN hM hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  pm_3626
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M P h :=
      originalTruncatedMiddle_le_product_divisors W K rows left right a b M Y Z lengthScale
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, originalProductDivisorMiddleAt W K rows left right a b M P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => originalProductDivisorMiddleAt_nonneg W K rows left right a b M P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

end

end OAI
