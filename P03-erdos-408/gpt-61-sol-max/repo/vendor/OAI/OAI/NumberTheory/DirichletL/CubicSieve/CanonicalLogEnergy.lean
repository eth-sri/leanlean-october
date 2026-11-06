module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 
 

namespace SecondPassIntegration
open   SecondPassArithmetic  

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassIntegration

namespace CanonicalRowCompletion

section

 
 

section
 
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
     pool   Ψ   m f z   H  :
    fixedChildRow p hp hcop hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring

end

 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem cube_coefficient_restore  H₀   Ψ   I 
    (hI : I ≠ 0) :
    reopenedCubeCoefficient H₀ Ψ I * (Ideal.absNorm I : ℂ)⁻¹ =
      largeCubeCoefficient H₀ I * cubeWeight Ψ I := by
  have hN : (Ideal.absNorm I : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)))
  unfold reopenedCubeCoefficient cubePhase
  field_simp

theorem cubeIdeal_row  F   hF 
     v   z  :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (fun i => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]

def outsideCanonicalBin (S ) (D ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X H₀ : ℝ)  :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ∑ v ∈ Q,
    (largeCubeCoefficient H₀ (cubeIdeal F v) *
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3) : ℂ)⁻¹) *
      idealRowHom z (cubeIdeal F v)^3 *
      outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3)

end

section
 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

def activeCubeExponents (S ) (D ) (b X : ℝ)  :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3 ≤ b*X)

theorem activeCubeExponents_norm_bound
     S   D   b X 
     v 
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (InitialMeanSquare.outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
  
  have hnn : n ≤ n^3 := by
    bound
  exact (hnn.trans hcube).trans (le_max_right _ _)

end

 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def cubeLogIndex (S ) (D )
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)  :=
  normLogBin (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ)  :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S ) (D ) (b X : ℝ) (j : ℕ)  :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

theorem activeCubeLogIndex_mem  S   D   b X 
     v 
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem activeCubeLogBin_norms  S   D  (b X : ℝ)  j 
     v 
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

theorem cubeLogRange_card  b X  :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := Finset.card_range _

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (activeCubeLogIndex_mem S D b X) a

end CanonicalRowCompletion

 
namespace SecondPassArithmetic
 
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

theorem nonzeroRowMajorantSum_exact_disk  P   K  (hK : 0<K) :
    nonzeroRowMajorantSum P K=
      ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ) := by
  unfold nonzeroRowMajorantSum
  have hz (z : ActualEisensteinCubic.O) (hz : z∉(firstFrequencyDisk (2*K)).erase 0) :
      (if z=0 then 0 else rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ))=0 := by
    by_cases hzero : z=0
    · simp [hzero]
    have hn : z∉firstFrequencyDisk (2*K) := by
      simp_all
    have hlarge : 2<‖eisEmbedding z‖^2/K :=
      (lt_div_iff₀ hK).mpr (outside_firstFrequencyDisk (2*K) z hn)
    rw [ite_eq_right hzero,rowMajorant_zero _ hlarge,zero_mul]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ite_eq_right (Finset.mem_erase.mp hz).1]

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
