module

public import ADR11.Identifiability.Corollary10
public import ADR11.Identifiability.Proposition8
public import ADR11.Trees.RootLocation

/-!
# Theorem 9 and Corollary 10 for nonbinary species trees

Helpers for Proposition 11, from the end of its proof (Appendix C): "Theorem 9 also extends,
noting that if the root of the species tree has degree greater than 2, then its location will be
identified by some 5-taxon subtree with the same property. The proof of Corollary 10 did not use
the assumption that `σ⁺` is binary, so it applies to nonbinary species trees as well."

The five-taxon case (Proposition 8 for nonbinary species trees) is a hypothesis of these results.

The location of the root `ρ` on `σ⁻` is an edge (a root of degree two) or a vertex (a root of
degree at least three); in both cases it is given by the children of the root, the sides of the
splits of `σ⁻` at `ρ` away from `ρ`.

## Main results

* `rl_nb_childClusters_univ_eq`: the unrooted tree and the induced five-taxon trees determine the
  children of the root: if `A` is a child of the root of one tree but not of the other, some set
  `S` of five taxa meeting `A` and `Aᶜ` has `A ∩ S` a child of the root of one induced tree but
  not of the other.
* `rl_nb_theorem9`: Theorem 9 for nonbinary species trees, given the five-taxon case.
* `c10_nb_corollary10`: Corollary 10 for nonbinary species trees, given the five-taxon case.
-/

@[expose] public section

namespace ADR11

open Finset

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The location of the root is determined (proof of Proposition 11): two species trees on at least
five taxa with the same unrooted tree and the same induced trees on all sets of five taxa have
the same children of the root. If `A` is a child of the root of `τ` but not of the root `ρ` of
`σ`, a set `S` of five taxa separates them: `S` contains `a ∈ A`, `b ∉ A`, a taxon `r` outside the
child `R ∋ a` of `ρ`, and a taxon on which `A` and `R` differ. The most recent common ancestor of
`S` is the root in both trees, so the children of the roots of `τ(S)` and `σ(S)` are the traces of
the children of the roots of `τ` and `σ`, and `A ∩ S` is a child of the first but not the
second. -/
theorem rl_nb_childClusters_univ_eq (hX : 5 ≤ Fintype.card X) {σ σ' : SpeciesTree X}
    (hU : unroot σ.clusters = unroot σ'.clusters)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).clusters = (σ'.restrict S hS).clusters) :
    childClusters σ.clusters univ = childClusters σ'.clusters univ := by
  have key : ∀ τ σ : SpeciesTree X, unroot τ.clusters = unroot σ.clusters →
      (∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
        (τ.restrict S hS).clusters = (σ.restrict S hS).clusters) →
      ∀ A ∈ childClusters τ.clusters univ, A ∈ childClusters σ.clusters univ := by
    intro τ σ hU h5 A hA₀
    by_contra hAR
    have hH := σ.isHierarchy
    obtain ⟨⟨a, ha⟩, hAu⟩ := nonempty_of_mem_unroot hH
      (hU ▸ mem_unroot.2 (.inl ⟨(mem_childClusters.1 hA₀).1, rl_ne_univ_of_mem_childClusters hA₀⟩))
    obtain ⟨b, hb⟩ := rl_compl_nonempty hAu
    obtain ⟨R, hR, haR⟩ := rl_exists_mem_childClusters_univ hH (by omega) a
    obtain ⟨r, hr⟩ := rl_compl_nonempty (rl_ne_univ_of_mem_childClusters hR)
    -- a taxon `w` on which `A` and the child `R ∋ a` of the root differ
    obtain ⟨w, hw⟩ : ∃ w, ¬(w ∈ A ↔ w ∈ R) := by
      by_contra h
      push Not at h
      exact hAR (ext h ▸ hR)
    obtain ⟨S, hTS, hS5⟩ := rl_exists_five hX (T := {a, b, r, w}) (card_le_four.trans (by norm_num))
    have hS : S.Nonempty := ⟨a, hTS (by simp)⟩
    have hC := h5 S hS hS5 ▸ (rl_mem_childClusters_restrict_iff τ hS hA₀
      ⟨a, mem_inter.2 ⟨ha, hTS (by simp)⟩⟩ ⟨b, mem_inter.2 ⟨hb, hTS (by simp)⟩⟩).2
        ⟨A, hA₀, ⟨a, mem_inter.2 ⟨ha, hTS (by simp)⟩⟩, rfl⟩
    -- `A ∩ S` is the trace `R' ∩ S` of a child `R' ∋ a` of the root, so `R' = R`
    obtain ⟨R', hR', -, hR'eq⟩ := (rl_mem_childClusters_restrict_iff σ hS hR
      ⟨a, mem_inter.2 ⟨haR, hTS (by simp)⟩⟩ ⟨r, mem_inter.2 ⟨hr, hTS (by simp)⟩⟩).1 hC
    obtain rfl := rl_eq_of_mem_childClusters hH hR hR' haR
      ((mem_iff_of_subtype_eq hR'eq (hTS (by simp))).2 ha)
    exact hw (mem_iff_of_subtype_eq hR'eq (hTS (by simp))).symm
  ext A
  grind

/-- Theorem 9 for species trees that need not be binary (proof of Proposition 11: "Theorem 9 also
extends, noting that if the root of the species tree has degree greater than 2, then its location
will be identified by some 5-taxon subtree with the same property"), given the five-taxon case
`five` (Proposition 8 for nonbinary species trees, for the induced five-taxon trees). For
`|X| ≥ 5`, the unrooted gene tree distribution determines the metric species tree.

The proof of Theorem 9: `σ⁻` is determined (Corollary 6 for nonbinary species trees,
`sameUnrootedMetricTree_of_unrootedDist_eq`), and by Lemma 5 and `five` so is every induced
five-taxon tree; they determine the location of the root (`rl_nb_childClusters_univ_eq`), hence
`ψ⁺` (`rl_eq_of_unroot_eq`), and the edge lengths (`rl_sameRootedMetricTree_of_clusters_eq`).

-/
theorem rl_nb_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id)
    (five : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).unrootedDist id = (σ'.restrict S hS).unrootedDist id →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  have h5 S hS hS5 := five S hS hS5 (unrootedDist_restrict_eq h S hS)
  exact rl_sameRootedMetricTree_of_clusters_eq hX (rl_eq_of_unroot_eq σ.isHierarchy σ'.isHierarchy
    hU.1 (rl_nb_childClusters_univ_eq hX hU.1 fun S hS hS5 => (h5 S hS hS5).1)) hU h5

/-- Corollary 10 for species trees that need not be binary (proof of Proposition 11: "The proof of
Corollary 10 did not use the assumption that `σ⁺` is binary, so it applies to nonbinary species
trees as well"), given the five-taxon case `five` (Proposition 8 for nonbinary species trees): the
proof of Corollary 10 (`c10_of_theorem9`) with Theorem 9 for nonbinary species trees
(`rl_nb_theorem9`). -/
theorem c10_nb_corollary10
    (five : ∀ {Y : Type u} [Fintype Y] [DecidableEq Y], Fintype.card Y = 5 →
      ∀ τ τ' : SpeciesTree Y, τ.unrootedDist id = τ'.unrootedDist id →
        τ.SameRootedMetricTree τ')
    (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  c10_of_theorem9 (P := fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun hY τ τ' _ _ hd => rl_nb_theorem9 hY τ τ' hd fun _ _ hS5 hdS =>
      five (by simpa using hS5) _ _ hdS)
    ℓ hℓ hcond σ σ' trivial trivial h

end ADR11
