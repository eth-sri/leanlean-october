module

public import OAI.NumberTheory.DirichletL.Eisenstein.FundamentalDomain

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
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
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Set
open scoped Classical
open scoped Classical

namespace CompletedGauss

theorem largeCubeCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (H₀ : ℝ) (B : Ideal O),B≠⊥ →
      ‖largeCubeCoefficient H₀ B‖ ≤ C*(Ideal.absNorm B : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  exact ⟨C,hC,fun H₀ B hB => (largeCubeCoefficient_norm_le H₀ B).trans (by grind)⟩

end CompletedGauss

open scoped Classical
namespace SecondPassArithmetic

section
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

section

open scoped Classical
open SecondPassFiber (newLabel newRow)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

open scoped Classical

end SecondPassArithmetic

section

open scoped Classical
namespace SecondPassArithmetic
open FirstPassCubeLabels (columnLog primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

namespace SecondPassIntegration

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end SecondPassIntegration
end

namespace SecondPassArithmetic

open scoped Classical

end SecondPassArithmetic

open scoped Classical
namespace CanonicalQuadraticSieve
open CompletedGauss
open QuadraticSquarefreeKernel

def liftingPrimeElement : O := ActualEisensteinCoordinates.eval 1 3
def liftingPrime : Ideal O := Ideal.span {liftingPrimeElement}

theorem liftingPrimeElement_norm : ShortDraftLatticeCount.qNat liftingPrimeElement=7 := by
  unfold ShortDraftLatticeCount.qNat liftingPrimeElement
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem liftingPrime_norm : Ideal.absNorm liftingPrime=7 := by
  rw [liftingPrime,←qNat_eq_absNorm_span,liftingPrimeElement_norm]

theorem liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hh := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hh
    omega
  · exact Ideal.isPrime_of_irreducible_absNorm (by
      rw [liftingPrime_norm,Nat.irreducible_iff_nat_prime]
      exact (by decide : Nat.Prime 7))

theorem liftingPrime_supported : Supported liftingPrime := by
  apply (supported_span_iff liftingPrimeElement).mpr
  have hlam : ShortDraftLatticeCount.qNat lambda=3 := by
    have he := theta_counter_lambda_eq
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  have htwo : ShortDraftLatticeCount.qNat (2:O)=4 := by
    have he : (2:O)=ActualEisensteinCoordinates.eval 2 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,hlam] at h
    omega
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,htwo] at h
    omega

theorem supported_pow {I : Ideal O} (hI : Supported I) (k : ℕ) : Supported (I^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    change P∈UniqueFactorizationMonoid.normalizedFactors (1:Ideal O) at hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    simp_all
  | succ k hk =>
    rw [pow_succ]
    exact (supported_mul_iff _ _).mpr (by grind)

theorem exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I≠0)
    (hIM : (Ideal.absNorm I:ℝ)≤M) :
    ∃k : ℕ, M<(49:ℝ)^k*(Ideal.absNorm I:ℝ) ∧
      (49:ℝ)^k*(Ideal.absNorm I:ℝ)≤49*M := by
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by linarith))
    (by norm_num : (1:ℝ)<49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : Ideal O :=
  (liftingPrime^liftingExponent M I hI hIM)^2*I

theorem liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    (Ideal.absNorm (liftedRow M I hI hIM):ℝ)=(49:ℝ)^liftingExponent M I hI hIM*(Ideal.absNorm I:ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    M<(Ideal.absNorm (liftedRow M I hI hIM):ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM):ℝ)≤49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

theorem liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : squarefreePart (liftedRow M I hI.1 hIM)=I :=
  (squarePart_mul_squarefree (pow_ne_zero _ liftingPrime_prime.ne_zero) hI.2.1).2

theorem liftedRow_supported (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : Supported (liftedRow M I hI.1 hIM) :=
  (supported_mul_iff _ _).mpr
    ⟨supported_pow (supported_pow liftingPrime_supported _) _,admissible_supported hI⟩

theorem liftedRow_character (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) (J : Ideal O) (hJ : Admissible J)
    (hPJ : IsCoprime liftingPrime J) :
    quadraticRow J (primaryGenerator (liftedRow M I hI.1 hIM)) =
      quadraticRow J (primaryGenerator I) := by
  rw [liftedRow,canonical_quadraticRow_primary_squarefree J hJ,
    idealZeroMask_primary_eq_indicator J _ hJ.1 (supported_pow liftingPrime_supported _),
    ite_eq_left hPJ.pow_left,one_mul]

end CanonicalQuadraticSieve

end

end OAI
