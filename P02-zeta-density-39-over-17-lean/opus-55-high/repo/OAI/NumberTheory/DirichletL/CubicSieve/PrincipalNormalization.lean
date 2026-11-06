module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds
public import OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
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

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open ConcretePrimeRowBridge (idealGenerator)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (newLabel newRow)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem rowCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a = rowCoprimeMask (fun i => Ideal.span {p i}) S b := by
  have hm (i : ι) : a ∈ Ideal.span {p i} ↔ b ∈ Ideal.span {p i} := by
    rw [← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [rowCoprimeMask,hm]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg F Ψ a H f y = fixedChildRow p hp hcop hg F Ψ b H f y := by
  simp only [fixedChildRow,secondChildColumn,rowCoprimeMask_congr_span p _ h]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      pm_5490 m hm
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      pm_5490 f hf
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

end SecondPassArithmetic

open scoped Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def signedProductDivisorSum (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ)*H d i j k else 0

def correctionRectangleMajorant (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * H (D*E) i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  pm_1423
  pm_1195 hpair hleft hright hK
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    pm_3782
    pm_3778
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    pm_3777
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    pm_1044
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  pm_8098
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

section
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
include α hexp deltaLoss hδ ε hε
theorem HasSieveExponent.small_principal_window (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      pm_387 Finset.sum_le_sum D E i
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => ⟨(hrows i).1,(hrows i).2.2⟩) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      pm_201 Finset.sum_eq_zero D hD E hE
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).2.1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    pm_3602
    positivity

theorem HasSieveExponent.small_principal_divisor_sum
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  pm_5141
  pm_3095
  have hS := columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2)
  have hT := columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)).trans
  pm_814
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)
end

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

lemma source_large_cut_lower (M B b N T d : ℝ)
    (hM : 0 < M) (_hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) (hN : 0 ≤ N) (hT : 0 < T)
    (hd : T*Real.sqrt (M/b) ≤ d) :
    Real.sqrt (M/B)*N ≤ ((4*N/T)/4)*d := by
  have hs : Real.sqrt (M/B) ≤ Real.sqrt (M/b) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hb hbB)
  have hsd : Real.sqrt (M/B) ≤ d/T := (le_div_iff₀ hT).mpr (by nlinarith)
  calc
    _ ≤ (d/T)*N := mul_le_mul_of_nonneg_right hsd hN
    _ = _ := by ring

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

section
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
include α hexp deltaLoss hδ ε hε
theorem HasSieveExponent.source_large_principal_sum
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b M (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N M (4*N/T) hB hN hM (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact source_large_cut_lower M B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

theorem HasSieveExponent.dual_large_principal_sum
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)
end

end CanonicalQuadraticSieve

end

end OAI
