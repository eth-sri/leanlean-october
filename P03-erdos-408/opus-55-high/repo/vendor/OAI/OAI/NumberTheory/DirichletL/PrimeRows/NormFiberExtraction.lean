module

public import OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction

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
open Filter
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped ArithmeticFunction.Moebius
open Filter
open scoped ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory

namespace ConcretePrimeRowBridge

section

open ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I

theorem span_idealGenerator (I : Ideal O) :
    Ideal.span {idealGenerator I} = I :=
  Submodule.IsPrincipal.span_singleton_generator I

theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by simp_all
    _ = J := span_idealGenerator J

def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo]

def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))


def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

theorem primePool_maximal (F : Finset (Ideal O))
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  grind

def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]


def idealSexticRow
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I) u

private theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · simp_all
  simp_all

theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)





open scoped Classical

def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)

theorem mem_rowNormDisk {H : ℕ} {u : O} :
    u ∈ rowNormDisk H ↔
      0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H u h.2, h⟩



end

open ShortDraftHeckeBridge

def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
    Finset (Ideal O) := by
  classical
  exact (idealsUpTo D).filter (fun I => ∀ P ∈ S, ¬ P ∣ I)

theorem mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ}
    {I : Ideal O} :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]

theorem outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  simp_all


theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'






open ShortDraftHeckeBridge FiniteSFactor Filter

end ConcretePrimeRowBridge

end

end OAI
