module
public import OAI.NumberTheory.DirichletL.Moments.ChildRows
public import OAI.NumberTheory.DirichletL.Moments.PartitionNorm
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ forcingSet c d V, P i

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (hI i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))]

theorem valuation_prime (P Q : Ideal O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro R hR; simpa only [Multiset.mem_singleton.mp hR] using hP))
  simp only [valuation,hf,Multiset.count_singleton]
  simp only [eq_comm]

section
variable (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
include P hp hinj
omit [Fintype ι] in
theorem valuation_prime_product (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp
end

section
variable (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
include P hp
omit [DecidableEq ι] in
theorem movingIdeal_ne_zero
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  rw [movingIdeal_valuation P hp hinj c d V i,hc,hd,ite_eq_left hiV]
  norm_num
end

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    pm_6848 i
    pm_6848 j
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  pm_8346

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    pm_67 R hR i hi Multiset.mem_map.mp
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  exact ⟨i,hi,hPi.symm⟩

def movingElement (p : ι → O) (c d : ι → ℕ) (V : Finset ι) : O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  pm_352 movingElement movingIdeal Ideal.span_singleton_pow Ideal.prod_span_singleton Ideal.span_singleton_mul_span_singleton

end SevenEighths.CenteredMomentForcing

end

end OAI
