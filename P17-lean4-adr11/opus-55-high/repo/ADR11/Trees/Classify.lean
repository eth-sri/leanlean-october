module

public import ADR11.MSC.Relabel
public import ADR11.SmallTrees

/-!
# Unrooted trees on four and five taxa, and their rootings

Every species tree on four or five taxa is, after relabelling, a rooting of one of a few standard
unrooted trees, and the rootings of each standard unrooted tree are listed explicitly.

* Four taxa: `U4 1 = AB|CD` and the star `U4 0`; `rootings4 k` lists the hierarchies on `Fin 4`
  with unrooted tree `U4 k` (7 for `AB|CD`: four caterpillars, the balanced tree, and the two
  trees with one cherry and a trifurcating root; 5 for the star).
* Five taxa: `U5 2 = {AB|CDE, ABC|DE}`, `U5 1 = AB|CDE`, the star `U5 0`; `rootings5 k` lists the
  hierarchies on `Fin 5` with unrooted tree `U5 k` (10, 8 and 6 of them), and
  `binaryRootings5` the 7 binary ones with unrooted tree `U5 2`.

## Main results

* `exists_equiv_unroot_eq_U4`, `exists_equiv_unroot_eq_U5`: normal forms up to relabelling.
* `exists_equiv_unroot_eq_U5_two_of_isBinary`: a binary 5-taxon tree has unrooted shape `U5 2`.
* `mem_rootings4`, `mem_rootings5`, `mem_binaryRootings5`: the lists are complete.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted trees on `Fin 4`: `U4 1` has the split `AB|CD`, `U4 0` is the star. -/
def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The unrooted trees on `Fin 5`: `U5 2` has the splits `AB|CDE` and `ABC|DE`, `U5 1` the split
`AB|CDE`, and `U5 0` is the star. -/
def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

/-- The hierarchies on `Fin 4` with unrooted tree `U4 k`. -/
def rootings4 : ℕ → Finset (Finset (Finset (Fin 4)))
  | 1 => {hierarchyOf {{0, 1}, {0, 1, 2}}, hierarchyOf {{0, 1}, {0, 1, 3}},
          hierarchyOf {{2, 3}, {0, 2, 3}}, hierarchyOf {{2, 3}, {1, 2, 3}},
          hierarchyOf {{0, 1}, {2, 3}}, hierarchyOf {{0, 1}}, hierarchyOf {{2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{0, 1, 2}}, hierarchyOf {{0, 1, 3}},
          hierarchyOf {{0, 2, 3}}, hierarchyOf {{1, 2, 3}}}

/-- The seven binary rootings of `U5 2` (roots on the pendant edges of `e`, `d`, `a`, `b`, `c`,
and on the internal edges `ABC|DE` and `AB|CDE`). -/
def binaryRootings5 : Finset (Finset (Finset (Fin 5))) :=
  {hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}, hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}},
   hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}},
   hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}}

/-- The hierarchies on `Fin 5` with unrooted tree `U5 k`. -/
def rootings5 : ℕ → Finset (Finset (Finset (Fin 5)))
  | 2 => insert (hierarchyOf {{0, 1}, {3, 4}}) (insert (hierarchyOf {{0, 1}, {0, 1, 2}})
          (insert (hierarchyOf {{3, 4}, {2, 3, 4}}) binaryRootings5))
  | 1 => {hierarchyOf {{0, 1}}, hierarchyOf {{2, 3, 4}}, hierarchyOf {{0, 1}, {2, 3, 4}},
          hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}, hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}},
          hierarchyOf {{0, 1}, {0, 1, 3, 4}}, hierarchyOf {{0, 1}, {0, 1, 2, 4}},
          hierarchyOf {{0, 1}, {0, 1, 2, 3}}}
  | _ => {hierarchyOf ∅, hierarchyOf {{1, 2, 3, 4}}, hierarchyOf {{0, 2, 3, 4}},
          hierarchyOf {{0, 1, 3, 4}}, hierarchyOf {{0, 1, 2, 4}}, hierarchyOf {{0, 1, 2, 3}}}

/-! ### Unrooting and relabelling -/

theorem classify_relabelFamily_trans {Y Z : Type*} [DecidableEq Y] [DecidableEq Z] (e : X ≃ Y)
    (f : Y ≃ Z) (F : Finset (Finset X)) :
    relabelFamily f (relabelFamily e F) = relabelFamily (e.trans f) F := by
  simp [relabelFamily, image_image, Function.comp_def, map_map]

/-! ### The splits of a species tree on four or five taxa -/

/-- On four or five taxa, the splits of a species tree are the trivial ones and those with a side
of two taxa. -/
theorem mem_unroot_iff (hX : Fintype.card X = 4 ∨ Fintype.card X = 5)
    (σ : SpeciesTree X) (A : Finset X) :
    A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = Fintype.card X - 1 ∨
      A ∈ (unroot σ.clusters).filter (fun B => #B = 2) ∨
      Aᶜ ∈ (unroot σ.clusters).filter (fun B => #B = 2) := by
  have hc := card_compl A
  have h1 : ∀ B : Finset X, #B = 1 → B ∈ unroot σ.clusters := fun B hB => by
    obtain ⟨x, rfl⟩ := card_eq_one.1 hB
    exact mem_unroot.2 (.inl ⟨σ.singleton_mem x, fun h => by
      rw [← card_univ, ← h, card_singleton] at hX; omega⟩)
  constructor
  · intro h
    simp [mem_filter, h, compl_mem_unroot.2 h, true_and]
    rcases mem_unroot.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> have := (σ.nonempty_of_mem _ h1).card_pos <;>
      have := (card_lt_iff_ne_univ _).2 h2 <;> omega
  · simp
    rintro (h | h | ⟨h, -⟩ | ⟨h, -⟩)
    exacts [h1 A h, compl_mem_unroot.1 (h1 _ (by omega)), h, compl_mem_unroot.1 h]

/-- Normal form of the unrooted tree of a species tree, from a finite check on `Fin n`. -/
theorem classify_exists_equiv {n : ℕ} (hX : Fintype.card X = n) (hn : n = 4 ∨ n = 5)
    (σ : SpeciesTree X) (U : ℕ → Finset (Finset (Fin n))) (K : Finset ℕ)
    (hdec : ∀ P ∈ (powersetCard 2 (univ : Finset (Fin n))).powerset,
      (∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ Aᶜ ⊆ B) →
      (∀ A ∈ P, #Aᶜ = 2 → Aᶜ ∈ P) → ∃ π ∈ (univ : Finset (Equiv.Perm (Fin n))), ∃ k ∈ K,
        ∀ A ∈ (univ : Finset (Finset (Fin n))), A ∈ U k ↔ #A = 1 ∨ #A = n - 1 ∨
          A ∈ relabelFamily π P ∨ Aᶜ ∈ relabelFamily π P) :
    ∃ e : Fin n ≃ X, ∃ k ∈ K, unroot (σ.relabel e.symm).clusters = U k := by
  let τ := σ.relabel (Fintype.equivFinOfCardEq hX)
  obtain ⟨π, -, k, hk, h⟩ := hdec ((unroot τ.clusters).filter fun B => #B = 2)
    (mem_powerset.2 fun A hA => mem_powersetCard.2 ⟨subset_univ A, (mem_filter.1 hA).2⟩)
    (fun A hA B hB => unroot_compat τ (mem_filter.1 hA).1 (mem_filter.1 hB).1)
    fun A hA h2 => mem_filter.2 ⟨compl_mem_unroot.2 (mem_filter.1 hA).1, h2⟩
  refine ⟨((Fintype.equivFinOfCardEq hX).trans π).symm, k, hk, ?_⟩
  rw [Equiv.symm_symm, SpeciesTree.relabel_clusters, ← classify_relabelFamily_trans,
    ← SpeciesTree.relabel_clusters, unroot_relabelFamily]
  ext A
  rw [mem_relabelFamily, mem_unroot_iff (by rw [Fintype.card_fin]; exact hn) τ,
    h A (mem_univ A), mem_relabelFamily, mem_relabelFamily, card_map, msc_map_compl,
    Fintype.card_fin]

/-! ### Hierarchies with prescribed splits -/

/-- A hierarchy consists of the root, the singletons and its other clusters. -/
theorem classify_eq_hierarchyOf (σ : SpeciesTree X) :
    σ.clusters = hierarchyOf (σ.clusters.filter fun A => 2 ≤ #A ∧ A ≠ univ) := by
  ext A
  have := card_eq_one (s := A)
  have := σ.nonempty_of_mem A
  have := σ.univ_mem
  have := σ.singleton_mem
  simp [hierarchyOf, mem_insert, mem_union, mem_image, mem_univ, true_and, mem_filter]
  grind

/-- Reduction of the classification of the rootings of an unrooted tree `U` to a finite check
over the subfamilies of the nontrivial splits of `U`. -/
theorem classify_mem_of_forall {τ : SpeciesTree X} {U : Finset (Finset X)}
    {R : Finset (Finset (Finset X))}
    (hdec : ∀ N ∈ (U.filter fun A => 2 ≤ #A).powerset,
      (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      (∀ A ∈ U, 2 ≤ #A → 2 ≤ #Aᶜ → A ∈ N ∨ Aᶜ ∈ N) → hierarchyOf N ∈ R)
    (h : unroot τ.clusters = U) : τ.clusters ∈ R := by
  subst h
  rw [classify_eq_hierarchyOf τ]
  refine hdec _ (mem_powerset.2 fun A hA => ?_) (fun A hA B hB => τ.laminar A (mem_filter.1 hA).1
    B (mem_filter.1 hB).1) fun A hA h2 h2c => ?_ <;> simp only [mem_filter] at *
  · exact ⟨mem_unroot.2 (.inl ⟨hA.1, hA.2.2⟩), hA.2.1⟩
  · rcases mem_unroot.1 hA with h | h <;> simp [h, h2, h2c]

/-! ### Finite checks on the standard trees

The `Fintype` instances deciding unbounded quantifiers are switched off, so that the bounded
quantifiers below are decided by running through the given finsets (otherwise instance search
may decide `∀ N ∈ s, p N` by enumerating all of `Finset (Finset (Fin 5))`, which happens
silently when the instance through `Finset.decidableDforallFinset` exceeds
`synthInstance.maxSize`; this size limit is raised locally for the larger checks). -/

section Decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option synthInstance.maxSize 4000 in
theorem classify_perm5 : ∀ P ∈ (powersetCard 2 (univ : Finset (Fin 5))).powerset,
    (∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ Aᶜ ⊆ B) → (∀ A ∈ P, #Aᶜ = 2 → Aᶜ ∈ P) →
    ∃ π ∈ (univ : Finset (Equiv.Perm (Fin 5))), ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      ∀ A ∈ (univ : Finset (Finset (Fin 5))), A ∈ U5 k ↔ #A = 1 ∨ #A = 5 - 1 ∨
        A ∈ relabelFamily π P ∨ Aᶜ ∈ relabelFamily π P := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem classify_perm4 : ∀ P ∈ (powersetCard 2 (univ : Finset (Fin 4))).powerset,
    (∀ A ∈ P, ∀ B ∈ P, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ Aᶜ ⊆ B) → (∀ A ∈ P, #Aᶜ = 2 → Aᶜ ∈ P) →
    ∃ π ∈ (univ : Finset (Equiv.Perm (Fin 4))), ∃ k ∈ ({0, 1} : Finset ℕ),
      ∀ A ∈ (univ : Finset (Finset (Fin 4))), A ∈ U4 k ↔ #A = 1 ∨ #A = 4 - 1 ∨
        A ∈ relabelFamily π P ∨ Aᶜ ∈ relabelFamily π P := by decide

set_option synthInstance.maxSize 4000 in
theorem classify_rootings5 : ∀ k ∈ ({0, 1, 2} : Finset ℕ),
    ∀ N ∈ ((U5 k).filter fun A => 2 ≤ #A).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ U5 k, 2 ≤ #A → 2 ≤ #Aᶜ → A ∈ N ∨ Aᶜ ∈ N) → hierarchyOf N ∈ rootings5 k := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
theorem classify_rootings4 : ∀ k ∈ ({0, 1} : Finset ℕ),
    ∀ N ∈ ((U4 k).filter fun A => 2 ≤ #A).powerset,
    (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
    (∀ A ∈ U4 k, 2 ≤ #A → 2 ≤ #Aᶜ → A ∈ N ∨ Aᶜ ∈ N) → hierarchyOf N ∈ rootings4 k := by decide

set_option synthInstance.maxSize 1000 in
theorem classify_binary5 : ∀ k ∈ ({0, 1, 2} : Finset ℕ), ∀ H ∈ rootings5 k,
    (∀ A ∈ H, 2 ≤ #A → ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A) →
      k = 2 ∧ H ∈ binaryRootings5 := by decide

end Decide

/-! ### Main results -/

/-- Normal form on four taxa. -/
theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k :=
  classify_exists_equiv hX (.inl rfl) σ U4 _ classify_perm4

/-- Normal form on five taxa. -/
theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      unroot (σ.relabel e.symm).clusters = U5 k :=
  classify_exists_equiv hX (.inr rfl) σ U5 _ classify_perm5

theorem classify_mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ)
    (hk : k ∈ ({0, 1, 2} : Finset ℕ)) (h : unroot τ.clusters = U5 k) :
    τ.clusters ∈ rootings5 k :=
  classify_mem_of_forall (classify_rootings5 k hk) h

/-- A binary 5-taxon species tree has unrooted shape `U5 2`. -/
theorem exists_equiv_unroot_eq_U5_two_of_isBinary (hX : Fintype.card X = 5) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) :
    ∃ e : Fin 5 ≃ X, unroot (σ.relabel e.symm).clusters = U5 2 := by
  obtain ⟨e, k, hk, h⟩ := exists_equiv_unroot_eq_U5 hX σ
  exact ⟨e, (classify_binary5 k hk _ (classify_mem_rootings5 _ k hk h)
    ((σ.isBinary_relabel_iff e.symm).2 hσ)).1 ▸ h⟩

theorem mem_rootings4 (τ : SpeciesTree (Fin 4)) (k : ℕ) (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) : τ.clusters ∈ rootings4 k :=
  classify_mem_of_forall (classify_rootings4 k hk) h

theorem mem_binaryRootings5 (τ : SpeciesTree (Fin 5)) (hτ : τ.IsBinary)
    (h : unroot τ.clusters = U5 2) : τ.clusters ∈ binaryRootings5 :=
  (classify_binary5 2 (by simp) _ (classify_mem_rootings5 τ 2 (by simp) h) hτ).2

end ADR11
