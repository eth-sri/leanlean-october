module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction

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
 
 
 
 
 
 

namespace ConcretePrimeRowBridge

section

open   ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

noncomputable def idealGenerator (I : Ideal O)  :=
  Submodule.IsPrincipal.generator I

theorem span_idealGenerator  I  :
    Ideal.span {idealGenerator I} = I := Submodule.IsPrincipal.span_singleton_generator I

theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by rw [h]
    _ = J := span_idealGenerator J

noncomputable def idealsUpTo (D : ℕ)  :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

theorem mem_idealsUpTo  {D}   {I}  :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]

noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

noncomputable def columnWeight {q }
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O)  :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))



noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

noncomputable def primePool (F : Finset (Ideal O))  :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

theorem mem_primePool_iff  {F}   {P}  :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

section
variable (F : Finset (Ideal O))

theorem primePool_maximal  
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primePool_good  
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  grind [I, OAI.ConcretePrimeRowBridge.mem_primePool_iff]

noncomputable def idealSupport (F ) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff    I 
     i  :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]



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
    (χ : DirichletCharacter ℂ q)  I  :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)









end

 
 

noncomputable def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)

theorem mem_rowNormDisk  {H}   {u}  :
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

theorem mem_outsideIdealsUpTo  {S}   {D} 
     {I}  :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]

section
variable (S : Finset (Ideal O)) (D : ℕ)

theorem outsideIdealsUpTo_ne_bot    
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  subst I
  simp at hn



theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'









end



 

end ConcretePrimeRowBridge

end

end OAI
