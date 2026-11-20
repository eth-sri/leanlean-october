module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

open Set Filter

noncomputable section

namespace DedekindZetaZeroFree.RestrictedProductDensity

variable {ι : Type*} [DecidableEq ι] {R : ι → Type*} [∀ i, Group (R i)]
  [∀ i, TopologicalSpace (R i)]

variable (A S : ∀ i, Subgroup (R i))

def singleSet :
    Set (RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite) :=
  {x | ∃ i, ∃ h : R i, h ∈ S i ∧ RestrictedProduct.mulSingle A i h = x}

theorem closure_closure_singleSet_eq_forall_mem
    (hSclosed : ∀ i, IsClosed (S i : Set (R i))) :
    closure (Subgroup.closure (singleSet A S)) =
      {x : RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite |
        ∀ i, x i ∈ S i} := by
  let closure₀ := Subgroup.closure (singleSet A S)
  classical
  let P : Set (RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite) :=
    {x | ∀ i, x i ∈ S i}
  let hPsub : Subgroup (RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite) :=
    { carrier := P
      one_mem' := fun i => (S i).one_mem
      mul_mem' := fun {_ _} hx hy i => by
        exact (S i).mul_mem (hx i) (hy i)
      inv_mem' := fun {_} hx i => by
        exact (S i).inv_mem (hx i)}
  have hPclosed : IsClosed P := by
    have heq : P = ⋂ i, {x | x i ∈ S i} := by
      ext x; simp [P]
    rw [heq]
    exact isClosed_iInter fun i =>
      (hSclosed i).preimage (RestrictedProduct.continuous_eval i)
  have hTsub : singleSet A S ⊆ (hPsub : Set (RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite)) := by
    rintro x ⟨i, h, hh, rfl⟩ j
    rcases eq_or_ne j i with rfl | hj
    · simpa using hh
    · simp_all
  have hclosure_le : closure (closure₀) ⊆ (hPsub : Set (RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite)) := by
    have h2 : closure₀ ≤ hPsub :=
      (Subgroup.closure_le hPsub).mpr hTsub
    exact closure_minimal h2 hPclosed
  apply Set.Subset.antisymm hclosure_le
  intro x hx
  rw [mem_closure_iff]
  intro V hVopen hxV

  have hsfin : ({i | x i ∉ A i} : Set ι).Finite := by
    have h : ({i | x i ∈ A i}ᶜ : Set ι).Finite := Filter.mem_cofinite.mp x.2
    simpa only [Set.compl_setOf] using h
  let s := hsfin.toFinset
  let principal₀ := Filter.principal ((s : Set ι)ᶜ)
  have hsc : Filter.cofinite ≤ principal₀ := by
    rw [Filter.le_principal_iff]
    exact s.finite_toSet.compl_mem_cofinite
  let inc := RestrictedProduct.inclusion R (fun i => (A i : Set (R i))) hsc
  let x' : RestrictedProduct R (fun i => (A i : Set (R i)))
      (principal₀) :=
    ⟨x.1, by
      intro i hi
      change x i ∈ A i
      simp_all [Set.mem_compl_iff, Finset.mem_coe, s]⟩
  have hx' : x' ∈ inc ⁻¹' V := by
    change inc x' ∈ V
    have hinc : inc x' = x := by ext i; rfl
    rw [hinc]; exact hxV
  have hopen :=
    hVopen.preimage (RestrictedProduct.continuous_inclusion hsc)
  obtain ⟨W, hW, hWV⟩ :=
    RestrictedProduct.isEmbedding_coe_of_principal.toIsInducing.isOpen_iff.mp hopen
  have hx'W : x.1 ∈ W := by
    have h : x' ∈ (DFunLike.coe : RestrictedProduct R (fun i => (A i : Set (R i)))
        (principal₀) → Π i, R i) ⁻¹' W := by
      rw [hWV]; exact hx'
    exact h
  obtain ⟨t, u, hu, huW⟩ := isOpen_pi_iff.mp hW x.1 hx'W

  have hgfun : ∀ t : Finset ι, ∀ᶠ i in Filter.cofinite,
      (fun i => if i ∈ t then x i else 1) i ∈ A i := by
    intro t
    refine Filter.mem_of_superset ((t ∪ s).finite_toSet.compl_mem_cofinite) ?_
    intro i hi
    simp only [Finset.mem_coe, Set.mem_compl_iff, Finset.mem_union, not_or] at hi
    change (if i ∈ t then x i else 1) ∈ A i
    rw [if_neg hi.1]
    exact (A i).one_mem
  let G : Finset ι → RestrictedProduct R (fun i => (A i : Set (R i))) Filter.cofinite :=
    fun t => ⟨fun i => if i ∈ t then x i else 1, hgfun t⟩
  have hGmem : ∀ t : Finset ι, G t ∈ closure₀ := by
    intro t
    induction t using Finset.induction with
    | empty =>
      exact (closure₀).one_mem
    | insert a t ha ih =>
      have hstep : G (insert a t) =
          G t * RestrictedProduct.mulSingle A a (x a) := by
        apply Subtype.ext
        funext i
        show (if i ∈ insert a t then x i else 1) =
          (if i ∈ t then x i else 1) * Pi.mulSingle a (x a) i
        by_cases hia : i = a
        · rw [hia, if_pos (Finset.mem_insert_self a t), if_neg ha,
            Pi.mulSingle_eq_same, one_mul]
        · simp_all
      rw [hstep]
      exact (closure₀).mul_mem ih
        (Subgroup.subset_closure ⟨a, x a, hx a, rfl⟩)
  have hgcoord : ∀ i ∈ t, G t i = x i := by
    intro i hi
    show (if i ∈ t then x i else 1) = x i
    exact if_pos hi
  have hgone : ∀ i ∉ t, G t i = 1 := by
    intro i hi
    show (if i ∈ t then x i else 1) = 1
    exact if_neg hi
  have hgH := hGmem t
  have hgV : G t ∈ V := by
    let g' : RestrictedProduct R (fun i => (A i : Set (R i)))
        (Filter.principal (sᶜ)) :=
      ⟨fun i => if i ∈ t then x i else 1, by
        intro i hi
        change (if i ∈ t then x i else 1) ∈ A i
        by_cases hit : i ∈ t
        · simp_all [Set.mem_compl_iff, Finset.mem_coe, s]
        · rw [if_neg hit]; apply one_mem⟩
    have hg'W : g'.1 ∈ W := by
      apply huW
      intro i hi
      show (if i ∈ t then x i else 1) ∈ u i
      rw [if_pos (by simpa using hi)]
      exact (hu i hi).2
    have hg'V : g' ∈ inc ⁻¹' V := by
      rw [← hWV]
      exact hg'W
    have hinc : inc g' = G t := by ext i; rfl
    rw [← hinc]
    exact hg'V
  exact ⟨G t, hgV, hgH⟩

end DedekindZetaZeroFree.RestrictedProductDensity

end
