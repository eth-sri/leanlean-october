module

public import OAI.NumberTheory.DirichletL.Moments.ChildRows
public import OAI.NumberTheory.DirichletL.Moments.PartitionNorm

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal ActualEisensteinCubic.O) (c d : ι → ℕ) (V : Finset ι) : Ideal ActualEisensteinCubic.O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal ActualEisensteinCubic.O) (c d : ι → ℕ) (V : Finset ι) : Ideal ActualEisensteinCubic.O :=
  ∏ i ∈ forcingSet c d V, P i

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal ActualEisensteinCubic.O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal ActualEisensteinCubic.O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (by grind)
        (Finset.prod_ne_zero_iff.mpr (by grind)),
      ih (by grind)]

theorem valuation_prime (P Q : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal ActualEisensteinCubic.O)))
      (by simp_all))
  simp only [valuation,hf,Multiset.count_singleton]
  grind

omit [Fintype ι] in
theorem valuation_prime_product (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp

omit [DecidableEq ι] in
theorem movingIdeal_ne_zero (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  simp [movingIdeal_valuation P hp hinj c d V i,hc,hd,ite_eq_left hiV]

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    let : (P i).IsMaximal := (Ideal.isPrime_of_prime (hp i)).isMaximal (hp i).ne_zero
    let : (P j).IsMaximal := (Ideal.isPrime_of_prime (hp j)).isMaximal (hp j).ne_zero
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  simp_all

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal ActualEisensteinCubic.O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal ActualEisensteinCubic.O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    intro R hR
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hR
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  grind

def movingElement (p : ι → ActualEisensteinCubic.O) (c d : ι → ℕ) (V : Finset ι) : ActualEisensteinCubic.O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → ActualEisensteinCubic.O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  simp only [movingElement,movingIdeal,Ideal.span_singleton_pow,
    Ideal.prod_span_singleton,Ideal.span_singleton_mul_span_singleton]

end SevenEighths.CenteredMomentForcing

end

end OAI
