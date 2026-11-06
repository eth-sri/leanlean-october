module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped SchwartzMap
open Finset
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation
open Filter
open scoped LSeries.notation
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

open scoped Classical SchwartzMap
namespace CanonicalQuadraticSieve
open EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_all

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    grind
  grind

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 := fun j => (hleft j).1.1
  have hr0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (by grind))
    (columnDivisorPool_norm_bounds right hr0 N (by grind))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (by grind)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

end SecondPassArithmetic

namespace DescentFiberCost
open ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

end DescentFiberCost

namespace SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm columnLog)

end SecondPassIntegration

namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates

end ShortDraftLatticeCount
namespace SecondPassArithmetic

end SecondPassArithmetic

open Filter MeasureTheory
open scoped Classical

namespace CubicEisenstein

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical

namespace CubicEisenstein

def cuspRectangle : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 (3*Real.sqrt 3)

end CubicEisenstein

end

end OAI
