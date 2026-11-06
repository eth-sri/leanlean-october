module

public import ADR11.Trees.Hierarchy

/-!
# Section 1: counting rooted and unrooted gene trees

"For `n` species, there are `(2n-5)!!` unrooted gene trees, and each unrooted gene tree can be
realized by `2n-3` rooted gene trees, corresponding to choices of an edge on which to place the
root" (Section 1, with the count `(2n-3)!!` of rooted binary topologies cited from
[Felsenstein 2004]).

* `IsBinaryHierarchy G`: `G` is a rooted binary tree on the leaves `L`, given by its clusters.
* `section1_card_rooted`: there are `(2n-3)!!` rooted binary trees on `n ≥ 1` labelled leaves.
* `section1_card_rootings`: each unrooted binary tree on `n ≥ 2` leaves has `2n-3` rooted versions.
* `section1_card_unrooted`: there are `(2n-5)!!` unrooted binary trees on `n ≥ 3` leaves.

## Proof

* `counts_card_eq`: a binary hierarchy on `n ≥ 1` leaves has `2n - 1` clusters. Its two clusters
  below the root (`counts_rootChildren`) form the only complementary pair of clusters, so its
  unrooted tree has `2(2n - 3)` sides of splits (`counts_card_unroot`).
* `counts_reroot T A`: the rooting of the unrooted tree `T` on the edge of the split `A | Aᶜ`, the
  root together with the sides of splits contained in `A` or in `Aᶜ`. It is a rooted binary tree
  with unrooted tree `T` (`counts_reroot_spec`, using `counts_unroot_split`), and it is the only
  one in which `A` and `Aᶜ` are clusters (`counts_reroot_unroot`). Counting the pairs of a rooting
  and a cluster below its root in two ways gives `counts_card_rootings`.
* `counts_ext G`: adding the leaf `Fin.last n` as a child of the root; `counts_res`: removing it.
  Rooting on the pendant edge of the leaf `n + 1`, the unrooted binary trees on `n + 1` leaves
  correspond to the rooted binary trees on `n` leaves (`counts_card_unrooted_succ`).
* Hence the number of rooted binary trees on `n + 1` leaves is `2n - 1` times the number of
  unrooted ones (`counts_card_rooted_eq_mul`), that is, `2n - 1` times the number of rooted
  binary trees on `n` leaves.
-/

@[expose] public section

namespace ADR11

open Finset

section General

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of a hierarchy are nonempty proper subsets. -/
theorem counts_nonempty_of_mem_unroot {G : Fam L} (hG : IsHierarchy G)
    {A : Finset L} (hA : A ∈ unroot G) : A.Nonempty ∧ A ≠ univ := by
  rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hG.2.2.1 A h1, h2⟩
  · refine ⟨(compl_ne_univ_iff_nonempty A).1 h2, ?_⟩
    rintro rfl
    rw [compl_univ] at h1
    exact not_nonempty_empty (hG.2.2.1 _ h1)

/-- The rooting of an unrooted tree `T` on the edge of the split `A | Aᶜ`: the root, together
with the sides of splits contained in `A` or in `Aᶜ`. -/
def counts_reroot (T : Fam L) (A : Finset L) : Fam L :=
  insert univ (T.filter fun C => C ⊆ A ∨ C ⊆ Aᶜ)

theorem counts_mem_reroot {T : Fam L} {A C : Finset L} :
    C ∈ counts_reroot T A ↔ C = univ ∨ (C ∈ T ∧ (C ⊆ A ∨ C ⊆ Aᶜ)) := by
  rw [counts_reroot, mem_insert, mem_filter]

/-- In a hierarchy, a side of a split contained in a cluster `A ≠ univ` is a cluster. -/
theorem counts_mem_of_mem_unroot_of_subset {G : Fam L} (hG : IsHierarchy G)
    {A C : Finset L} (hA : A ∈ G) (hAu : A ≠ univ) (hC : C ∈ unroot G) (hCA : C ⊆ A) :
    C ∈ G := by
  rcases mem_unroot.1 hC with ⟨h, -⟩ | ⟨h, hu⟩
  · exact h
  · rcases hG.2.2.2 _ h A hA with h' | h' | h'
    · exfalso
      refine hAu (eq_univ_iff_forall.2 fun x => ?_)
      by_contra hx
      exact hx (h' (compl_subset_compl.2 hCA (mem_compl.2 hx)))
    · exfalso
      refine hu (eq_univ_iff_forall.2 fun x => ?_)
      rw [mem_compl]
      intro hx
      exact mem_compl.1 (h' (hCA hx)) hx
    · have : Cᶜ = Aᶜ := Subset.antisymm (subset_compl_iff_disjoint_right.2 h')
        (compl_subset_compl.2 hCA)
      rw [compl_inj_iff.1 this]
      exact hA

/-- A hierarchy with two complementary clusters `A`, `Aᶜ` is the rooting of its unrooted tree on
the edge of the split `A | Aᶜ`. -/
theorem counts_reroot_unroot {G : Fam L} (hG : IsHierarchy G) {A : Finset L}
    (hA : A ∈ G) (hAu : A ≠ univ) (hAc : Aᶜ ∈ G) : counts_reroot (unroot G) A = G := by
  have hAne := hG.2.2.1 A hA
  have hAcu : Aᶜ ≠ univ := (compl_ne_univ_iff_nonempty A).2 hAne
  ext C
  rw [counts_mem_reroot]
  constructor
  · rintro (rfl | ⟨hC, hCA | hCA⟩)
    · exact hG.1
    · exact counts_mem_of_mem_unroot_of_subset hG hA hAu hC hCA
    · exact counts_mem_of_mem_unroot_of_subset hG hAc hAcu hC hCA
  · intro hC
    by_cases hCu : C = univ
    · exact Or.inl hCu
    refine Or.inr ⟨mem_unroot.2 (Or.inl ⟨hC, hCu⟩), ?_⟩
    rcases hG.2.2.2 C hC A hA with h | h | h
    · exact Or.inl h
    · rcases hG.2.2.2 C hC _ hAc with h' | h' | h'
      · exfalso
        obtain ⟨a, ha⟩ := hAne
        exact mem_compl.1 (h' (h ha)) ha
      · exfalso
        refine hCu (eq_univ_iff_forall.2 fun x => ?_)
        by_cases hx : x ∈ A
        · exact h hx
        · exact h' (mem_compl.2 hx)
      · exact Or.inl (disjoint_compl_right_iff.1 h')
    · exact Or.inr (subset_compl_iff_disjoint_right.2 h)

end General

section Fin

variable {n : ℕ}

end Fin

/-! ### Counting -/

end ADR11
