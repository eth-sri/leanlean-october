module

public import Erdos821.S34.Probability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Factorization.Defs

@[expose] public section


open scoped BigOperators Classical

namespace Erdos821.S34Core

noncomputable section

theorem count_nat_ofFn (j : ℕ) (f : Fin j → ℕ) (p : ℕ) :
    List.count p (List.ofFn f) = ∑ i, if f i = p then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, ih]
    by_cases h : f 0 = p
    · simp [h, Nat.add_comm]
    · simp [h]

theorem tuple_factorization (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z : S34.Core.Tuple G k) :
    (S34.Core.product G k z).factorization =
      ∑ g, ∑ i, Finsupp.single (z g i).val 1 := by
  have hrow (g : Fin G.size) : (∏ i, (z g i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (G.prime g _ (z g i).property).ne_zero
  unfold S34.Core.product
  rw [Nat.factorization_prod (fun g _ => hrow g)]
  apply Finset.sum_congr rfl
  intro g _
  rw [Nat.factorization_prod (fun i _ => (G.prime g _ (z g i).property).ne_zero)]
  apply Finset.sum_congr rfl
  intro i _
  exact (G.prime g _ (z g i).property).factorization

theorem group_count_factorization (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z : S34.Core.Tuple G k) (g : Fin G.size) (p : ℕ) (hp : p ∈ G.primes g) :
    (S34.Core.product G k z).factorization p =
      List.count p (List.ofFn (fun i => (z g i).val)) := by
  rw [tuple_factorization, count_nat_ofFn]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_single g
  · intro h _ hne
    apply Finset.sum_eq_zero
    intro i _
    have hneq : (z h i).val ≠ p := by
      intro heq
      have hmem : p ∈ G.primes h := heq ▸ (z h i).property
      exact Finset.disjoint_left.mp (G.disjoint h g hne) hmem hp
    simp [hneq]
  · intro hcontra
    exact False.elim (hcontra (Finset.mem_univ g))

theorem group_row_perm (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ)
    (z w : S34.Core.Tuple G k) (g : Fin G.size)
    (hprod : S34.Core.product G k z = S34.Core.product G k w) :
    (List.ofFn (fun i => (z g i).val)).Perm (List.ofFn (fun i => (w g i).val)) := by
  apply List.perm_iff_count.mpr
  intro p
  by_cases hp : p ∈ G.primes g
  · rw [← group_count_factorization G k z g p hp,
      ← group_count_factorization G k w g p hp, hprod]
  · have hmem (v : S34.Core.Tuple G k) : p ∉ List.ofFn (fun i => (v g i).val) := by
      intro h
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      apply hp
      rw [← hi]
      exact (v g i).property
    rw [List.count_eq_zero.mpr (hmem z), List.count_eq_zero.mpr (hmem w)]

def tupleFiber (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) :
    Finset (S34.Core.Tuple G k) := Finset.univ.filter fun z => S34.Core.product G k z = n

/-- Unique factorization and disjoint prime groups keep the representation
cost multiplicative in the individual slot counts. -/
theorem tupleFiber_card_le (G : S34.Core.PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) :
    (tupleFiber G k n).card ≤ ∏ g, Nat.factorial (k g) := by
  by_cases hne : (tupleFiber G k n).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    let target : Type := ∀ g : Fin G.size,
      ↥((List.ofFn (fun i => (z₀ g i).val)).permutations.toFinset)
    let encode : ↥(tupleFiber G k n) → target := fun z g =>
      ⟨List.ofFn (fun i => (z.val g i).val), by
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply group_row_perm G k z.val z₀ g
        exact (Finset.mem_filter.mp z.property).2.trans (Finset.mem_filter.mp hz₀).2.symm⟩
    have hinj : Function.Injective encode := by
      intro z w h
      apply Subtype.ext
      funext g i
      apply Subtype.ext
      have hg := congrArg Subtype.val (congrFun h g)
      exact congrFun (List.ofFn_injective hg) i
    have hc := Fintype.card_le_of_injective encode hinj
    calc
      _ = Fintype.card ↥(tupleFiber G k n) := by simp
      _ ≤ Fintype.card target := hc
      _ = ∏ g, (List.ofFn (fun i => (z₀ g i).val)).permutations.toFinset.card := by simp [target]
      _ ≤ ∏ g, Nat.factorial (k g) := by
        gcongr with g
        calc
          _ ≤ (List.ofFn (fun i => (z₀ g i).val)).permutations.length := List.toFinset_card_le _
          _ = _ := by rw [List.length_permutations]; simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end
end Erdos821.S34Core
