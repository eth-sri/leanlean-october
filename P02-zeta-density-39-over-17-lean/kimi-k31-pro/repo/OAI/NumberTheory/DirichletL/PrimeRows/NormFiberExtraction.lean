module
public import OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

noncomputable def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I

theorem span_idealGenerator (I : Ideal O) :
    Ideal.span {idealGenerator I} = I := by
  exact Submodule.IsPrincipal.span_singleton_generator I

theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by rw [h]
    _ = J := span_idealGenerator J

noncomputable def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]

noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

noncomputable def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))

theorem columnWeight_idealGenerator {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (I : Ideal O) :
    columnWeight χ W (idealGenerator I) =
      baseChangeWeight χ I * W (Ideal.absNorm I) := by
  simp [columnWeight, span_idealGenerator]

noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
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
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  exact hFgood I hIF i.1 hfac

noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]

theorem idealGenerator_mem_prime_of_support
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (hIF : I ∈ F) (i : primePool F)
    (hi : i ∈ idealSupport F I) : idealGenerator I ∈ i.1 := by
  have hfac := (mem_idealSupport_iff F I i).mp hi
  have hle := ((Ideal.mem_normalizedFactors_iff (hFpos I hIF)).mp hfac).2
  have hmem : idealGenerator I ∈ Ideal.span {idealGenerator I} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [span_idealGenerator I] at hmem
  exact hle hmem

noncomputable def idealSexticRow
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
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

theorem columnWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (hW : ∀ n, ‖W n‖ ≤ 1) (x : O) :
    ‖columnWeight χ W x‖ ≤ 1 := by
  rw [columnWeight, norm_mul]
  have hμ := baseChangeWeight_norm_le_one χ (Ideal.span {x})
  have hW' := hW (Ideal.absNorm (Ideal.span {x}))
  exact (mul_le_mul hμ hW' (norm_nonneg _) (by positivity)).trans (by norm_num)

noncomputable def elementRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ := by
  classical
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ∑ x ∈ F.image idealGenerator,
    columnWeight χ W x *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood)
        (idealSupport F (Ideal.span {x})) u

noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    baseChangeWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u

theorem elementRow_eq_idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) :
    elementRow F hFpos hFgood χ W u =
      idealRowSum F hFpos hFgood χ W u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  unfold elementRow idealRowSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [columnWeight_idealGenerator, span_idealGenerator]
    rfl
  · intro I hI J hJ h
    exact idealGenerator_injective h

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical

noncomputable def rowNormDisk (H : ℕ) : Finset O := by
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

open ShortDraftHeckeBridge FiniteSFactor

noncomputable def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
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
  subst I
  simp at hn

theorem outsideIdealsUpTo_norm_le (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) :
    Ideal.absNorm I ≤ D :=
  (mem_outsideIdealsUpTo.mp hI).2.1

theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem outsideIdealsUpTo_good
    (S : Finset (Ideal O)) (D : ℕ)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D)
    (Q : Ideal O) (hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    goodLambda ∉ Q := by
  intro hmemLam
  have hne : I ≠ ⊥ := outsideIdealsUpTo_ne_bot S D I hI
  have hp : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
  have hmax : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hQS : Q ∈ S := hSbad Q hmax hmemLam
  have hdiv : Q ∣ I := (Ideal.dvd_iff_le).mpr
    ((Ideal.mem_normalizedFactors_iff hne).mp hQ).2
  exact (mem_outsideIdealsUpTo.mp hI).2.2 Q hQS hdiv

theorem idealsUpTo_eq_biUnion_fibers (D : ℕ) :
    idealsUpTo D =
      (Finset.Icc 1 D).biUnion FiniteSFactor.fiber := by
  rfl

private theorem normFibers_pairwiseDisjoint (D : ℕ) :
    ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint
      FiniteSFactor.fiber := by
  intro n hn m hm hnm
  apply Finset.disjoint_left.mpr
  intro I hIn hIm
  exact hnm ((FiniteSFactor.mem_fiber.mp hIn).symm.trans
    (FiniteSFactor.mem_fiber.mp hIm))

open ShortDraftHeckeBridge FiniteSFactor Filter

end ConcretePrimeRowBridge

end

end OAI
