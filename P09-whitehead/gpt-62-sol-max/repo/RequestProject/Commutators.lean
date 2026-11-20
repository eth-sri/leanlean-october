module

public import RequestProject.Fox

@[expose] public section

/-!
# Words with vanishing exponent sums are products of commutators

Rule 3 of Section 3.4 factors a word `r⁰` with zero exponent sums in every
generator as a product `∏_{h=1}^q [u_h, v_h]`, padding with `[1,1]` until
`q ≥ 2`.  The paper gives an explicit sorting algorithm; what the construction
actually uses is the existence of such a factorization, i.e. that the kernel of
the exponent-sum homomorphism on a free group is its commutator subgroup.
-/

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

namespace FiniteChains

variable {α : Type*}

/-- The total exponent-sum homomorphism of a free group. -/
noncomputable def expSumTotal : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  (AddMonoidHom.toMultiplicativeRight FreeAbelianGroup.toFinsupp).comp Abelianization.of

@[simp] theorem expSumTotal_of (i : α) :
    (expSumTotal (FreeGroup.of i)).toAdd = Finsupp.single i (1 : ℤ) :=
  FreeAbelianGroup.toFinsupp_of i

theorem expSumTotal_apply [DecidableEq α] (w : FreeGroup α) (i : α) :
    (expSumTotal w).toAdd i = (expSum i w).toAdd := by
  have h : (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom i : (α →₀ ℤ) →+ ℤ)).comp
      expSumTotal = expSum i := by
    apply FreeGroup.ext_hom
    intro k
    change (expSumTotal (FreeGroup.of k)).toAdd i = (expSum i (FreeGroup.of k)).toAdd
    simp [expSum, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun h w

/-- A word with vanishing exponent sums lies in the commutator subgroup. -/
theorem mem_commutator_of_expSum_eq_zero [DecidableEq α] (w : FreeGroup α)
    (h : ∀ i : α, (expSum i w).toAdd = 0) : w ∈ commutator (FreeGroup α) := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  apply (FreeAbelianGroup.equivFinsupp (X := α)).injective
  change (expSumTotal w).toAdd = 0
  ext i
  simp [expSumTotal_apply, h]

/-- **Rule 3 of Section 3.4.**  A word with vanishing exponent sums in every generator is a
product of `q ≥ 2` commutators, as required before substituting a block `B_q`. -/
theorem exists_commutator_factorization [DecidableEq α] (w : FreeGroup α)
    (h : ∀ i : α, Multiplicative.toAdd (expSum i w) = 0) :
    ∃ (q : ℕ) (u v : Fin q → FreeGroup α), 2 ≤ q ∧
      w = (List.ofFn fun j : Fin q => ⁅u j, v j⁆).prod := by
  classical
  have hw := mem_commutator_of_expSum_eq_zero w h
  rw [commutator_eq_closure] at hw
  have hsub : w ∈ Submonoid.closure (commutatorSet (FreeGroup α)) := by
    have hi : (commutatorSet (FreeGroup α))⁻¹ ⊆ commutatorSet (FreeGroup α) := by
      intro x hx
      obtain ⟨a, b, hab⟩ := Set.mem_inv.mp hx
      exact ⟨b, a, by rw [← commutatorElement_inv, hab, inv_inv]⟩
    simpa only [Set.union_eq_left.mpr hi, Subgroup.closure_toSubmonoid] using
      show w ∈ (Subgroup.closure (commutatorSet (FreeGroup α))).toSubmonoid from hw
  obtain ⟨l, hl, hlp⟩ := Submonoid.exists_list_of_mem_closure hsub
  let l' := l ++ [1, 1]
  have hmem (x : FreeGroup α) (hx : x ∈ l') : x ∈ commutatorSet (FreeGroup α) := by
    simp only [l', List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    rcases hx with hx | rfl
    · exact hl x hx
    · exact one_mem_commutatorSet _
  choose a b h using hmem
  refine ⟨l'.length, fun i => a _ (List.getElem_mem i.2), fun i => b _ (List.getElem_mem i.2), by simp [l'], ?_⟩
  rw [funext (fun i : Fin l'.length => h _ (List.getElem_mem i.2)), List.ofFn_getElem]
  simp [l', hlp]

end FiniteChains
