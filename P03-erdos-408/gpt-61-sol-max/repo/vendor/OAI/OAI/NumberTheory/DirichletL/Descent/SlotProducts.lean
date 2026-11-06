module

public import OAI.NumberTheory.DirichletL.Descent.HybridBound

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal ActualEisensteinCubic.O)  := ∏ i, p i

theorem slotTupleProduct_injective_on
    (L : ι → Finset (Ideal ActualEisensteinCubic.O)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) :
    Set.InjOn (slotTupleProduct (ι := ι)) {p | ∀ i, p i ∈ L i} := by
  intro p hpL q hqL he
  funext i
  change (∏ i, p i) = ∏ i, q i at he
  have hdiv : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, hj, hd⟩ := ((hp i (p i) (hpL i)).dvd_finsetProd_iff q).mp hdiv
  have hpq : p i = q j := associated_iff_eq.mp
    ((hp i (p i) (hpL i)).associated_of_dvd (hp j (q j) (hqL j)) hd)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hL hne) (hpL i) (hpq.symm ▸ hqL j)
  simpa only [← hij] using hpq

omit [DecidableEq ι] in
theorem slotTupleProduct_admissible
    (L : ι → Finset (Ideal ActualEisensteinCubic.O)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hgen : ∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0)
    (p : ι → Ideal ActualEisensteinCubic.O) (hpL : ∀ i, p i ∈ L i) :
    CubicSieve.Admissible (slotTupleProduct p) := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      have hpi := hp i (p i) (hpL i)
      have hpj := hp j (p j) (hpL j)
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime hpi).isMaximal hpi.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime hpj).isMaximal hpj.ne_zero
      apply (Ideal.isCoprime_of_isMaximal ?_).isRelPrime
      intro he
      exact Finset.disjoint_left.mp (hL hij) (hpL i) (he.symm ▸ hpL j)
    · intro i hi
      exact (hp i (p i) (hpL i)).squarefree
  · change primaryGeneratorHom (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hgen i (p i) (hpL i))

def slotProductCoefficient (tuples : Finset (ι → Ideal ActualEisensteinCubic.O))
    (a : (ι → Ideal ActualEisensteinCubic.O) → ℂ) (P : Ideal ActualEisensteinCubic.O)  :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal ActualEisensteinCubic.O))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal ActualEisensteinCubic.O)))
     a   p  (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact ite_eq_right (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

end
end SevenEighths.InverseMoment

end OAI
