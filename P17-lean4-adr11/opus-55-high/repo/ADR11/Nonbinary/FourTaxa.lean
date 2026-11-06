module

public import ADR11.Rootings.Proofs
public meta import ADR11.Rootings.Proofs
public import ADR11.Trees.Classify
public import ADR11.Trees.Hierarchy

/-!
# Four taxa, binary or not (Section 4.1, Section 5)

On four taxa, the unrooted gene tree distribution of a species tree, binary or not, determines
exactly its unrooted metric tree (Proposition 3, Theorem 9 for `|X| = 4`, and Section 5,
l.709–711). After relabelling, a species tree is a rooting of `U4 1` (one internal edge, of length
`t`) or of the star `U4 0`, and by the formulas of Section 4.1 and their limits of Section 5
(computed by `msc`), the gene tree with the split of the species tree has probability
`1 - (2/3) e^{-t}` and the two others `(1/3) e^{-t}` (with `t = 0` for the star).

## Main results

* `unrootedDist_eq_iff_four`: on four taxa the distribution of a species tree, binary or not,
  determines, and is determined by, its unrooted metric tree `σ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Relabelling quartet trees -/

/-- Relabelling the taxa of the unrooted tree with the nontrivial splits `A | Aᶜ`, `A ∈ C`. -/
lemma four_relabelFamily_treeOfClusters {Y : Type*} [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (C : Finset (Finset X)) :
    relabelFamily e (treeOfClusters C) = treeOfClusters (relabelFamily e C) := by
  unfold treeOfClusters
  rw [← unroot_relabelFamily]
  congr 1
  unfold relabelFamily
  rw [image_insert, image_union, image_image, Finset.map_univ_equiv]
  congr 2
  ext D
  simp
  constructor
  · grind
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp⟩

/-! ### Finite computations on `Fin 4` -/

/-- Two distributions on four taxa with the quartet probabilities `1 - (2/3)E`, `E/3`, `E/3` are
equal: these sum to `1`, so the other gene trees have probability `0`. -/
theorem four_ext {σ τ : SpeciesTree (Fin 4)} {E : ℝ}
    (hσ : σ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * E ∧
      σ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * E ∧
      σ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * E)
    (hτ : τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * E ∧
      τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * E ∧
      τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * E) :
    σ.unrootedDist id = τ.unrootedDist id := by
  have key (ρ : SpeciesTree (Fin 4)) (h : ρ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * E ∧
      ρ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * E ∧
      ρ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * E) U
      (hU : U ∉ ({treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}} : Finset _)) :
      ρ.unrootedDist id U = 0 := by
    have hn : ∀ T, 0 ≤ ρ.unrootedDist id T :=
      unrootedDistOf_nonneg ρ.isHierarchy (fun A hA hAu => (ρ.length_pos A hA hAu).le) id
    have hs : ∑ T, ρ.unrootedDist id T = 1 := unrootedDistOf_sum ρ.isHierarchy ρ.length id
    have := sum_le_univ_sum_of_nonneg (s := insert U {treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}},
      treeOfClusters {{0, 3}}}) hn
    rw [sum_insert hU, sum_insert (by decide), sum_pair (by decide), hs, h.1, h.2.1, h.2.2] at this
    linarith [hn U]
  funext U
  by_cases hU : U ∈ ({treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}} : Finset _) <;> grind

/-- The unrooted length of `{0, 1}` as the sum of the lengths of the clusters among `{0, 1}`,
`{2, 3}`. -/
lemma four_unrootedLength_eq_sum (τ : SpeciesTree (Fin 4)) {S : Finset (Finset (Fin 4))}
    (hS : τ.clusters.filter (fun C => C ≠ univ ∧ (C = {0, 1} ∨ C = {0, 1}ᶜ)) = S) :
    τ.unrootedLength {0, 1} = ∑ C ∈ S, τ.length C := by aesop

/-- Section 4.1's formulas for the rootings of `U4 1 = AB|CD` and their limits of Section 5, with
internal edge length `t = τ.unrootedLength {0, 1}`; for the rootings of the star `U4 0`, `t = 0`
and the three quartet trees have probability `1/3`. -/
lemma four_unrootedDist_U4 (τ : SpeciesTree (Fin 4)) {k : ℕ} (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = 1 - 2 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = 1 / 3 * exp (-τ.unrootedLength {0, 1}) := by
  have hm := mem_rootings4 τ k hk h
  simp at hk
  rcases hk with rfl | rfl <;> simp [rootings4, mem_insert, mem_singleton] at hm
  · rcases hm with hc | hc | hc | hc | hc <;>
      rw [four_unrootedLength_eq_sum τ (S := ∅) (by rw [hc]; decide), sum_empty] <;>
      msc hc with neg_zero, exp_zero
  rcases hm with hc | hc | hc | hc | hc | hc | hc <;>
    first
    | rw [four_unrootedLength_eq_sum τ (S := {{0, 1}}) (by rw [hc]; decide), sum_singleton]
    | rw [four_unrootedLength_eq_sum τ (S := {{2, 3}}) (by rw [hc]; decide), sum_singleton]
    | rw [four_unrootedLength_eq_sum τ (S := {{0, 1}, {2, 3}}) (by rw [hc]; decide),
        sum_pair (by decide)]
  all_goals msc hc

/-- The quartet trees on `Fin 4` with the split of `U4 k`, and the others. -/
lemma four_cases : ∀ k ∈ ({0, 1} : Finset ℕ), ∀ B : Finset (Fin 4), #B = 2 →
    B ∈ U4 k ∧ k = 1 ∧ (B = {0, 1} ∨ B = {2, 3}) ∧ treeOfClusters {B} = treeOfClusters {{0, 1}} ∨
    B ∉ U4 k ∧ (k = 0 ∧ treeOfClusters {B} = treeOfClusters {{0, 1}} ∨
      treeOfClusters {B} = treeOfClusters {{0, 2}} ∨
      treeOfClusters {B} = treeOfClusters {{0, 3}}) := by
  decide

/-! ### The gene tree distribution on four taxa -/

/-- The unrooted length of a split of a species tree is positive. -/
theorem four_unrootedLength_pos (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A := by
  refine Finset.sum_pos (fun C hC => ?_) ?_
  · rw [mem_filter] at hC
    exact σ.length_pos C hC.1 hC.2.1
  · rcases mem_unroot.1 hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨A, mem_filter.2 ⟨h1, h2, Or.inl rfl⟩⟩
    · exact ⟨Aᶜ, mem_filter.2 ⟨h1, h2, Or.inr rfl⟩⟩

/-- The unrooted length of a set of taxa which is not a split vanishes. -/
theorem four_unrootedLength_eq_zero {σ : SpeciesTree X} {A : Finset X}
    (hA : A ∉ unroot σ.clusters) : σ.unrootedLength A = 0 :=
  sum_eq_zero fun C hC => by grind [mem_unroot]

/-- On four taxa, a quartet tree `B | Bᶜ` has probability `> 1/3` exactly when `B` is a split of
the species tree, and then its probability is `1 - (2/3) e^{-t}`, where `t` is the length of the
internal edge (Section 4.1, Section 5). -/
theorem four_unrootedDist_split (hX : Fintype.card X = 4) (σ : SpeciesTree X) {B : Finset X}
    (hB : #B = 2) : (B ∈ unroot σ.clusters ↔ 1 / 3 < σ.unrootedDist id (treeOfClusters {B})) ∧
      (B ∈ unroot σ.clusters →
        σ.unrootedDist id (treeOfClusters {B}) = 1 - 2 / 3 * exp (-σ.unrootedLength B)) := by
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
  rw [← SpeciesTree.unrootedDist_relabel σ e.symm, four_relabelFamily_treeOfClusters,
    relabelFamily, image_singleton, ← SpeciesTree.unrootedLength_relabel σ e.symm B,
    ← map_mem_relabelFamily (e := e.symm), ← unroot_relabelFamily, ← SpeciesTree.relabel_clusters,
    he]
  obtain ⟨h1, h2, h3⟩ := four_unrootedDist_U4 _ hk he
  have h23 := (σ.relabel e.symm).unrootedLength_compl {0, 1}
  rw [show ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} by decide] at h23
  have hpos := four_unrootedLength_pos (σ.relabel e.symm) (A := {0, 1})
  have hzero := four_unrootedLength_eq_zero (σ := σ.relabel e.symm) (A := {0, 1})
  rw [he] at hpos hzero
  have := exp_le_one_iff.2 (neg_nonpos.2 (by
    by_cases h : ({0, 1} : Finset (Fin 4)) ∈ U4 k; exacts [(hpos h).le, (hzero h).ge]))
  have hB' : #(B.map e.symm.toEmbedding) = 2 := by simpa
  generalize B.map e.symm.toEmbedding = B' at hB' ⊢
  rcases four_cases k hk _ hB' with ⟨hm, rfl, rfl | rfl, ht⟩ | ⟨hm, ⟨rfl, ht⟩ | ht | ht⟩
  all_goals simp only [hm, ht, h1, h2, h3, true_iff, false_iff, true_imp_iff, false_imp_iff,
    and_true, not_lt, h23]
  all_goals first
    | linarith
    | rw [hzero (by decide)]; norm_num
    | linarith [exp_lt_one_iff.2 (neg_lt_zero.2 (hpos (by decide)))]

/-! ### The distribution determines `σ⁻`, and conversely -/

/-- On four taxa, two species trees have the same unrooted gene tree distribution exactly when
they have the same unrooted metric tree.

This holds for binary and nonbinary species trees alike (Section 5, l.709–711): the quartet
probabilities are those of Section 4.1 for a binary tree and their limits of Section 5 for a
nonbinary one. -/
theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  have hU (h : σ.unrootedDist id = σ'.unrootedDist id) : unroot σ.clusters = unroot σ'.clusters := by
    have hs B (hB : #B = 2) : B ∈ unroot σ.clusters ↔ B ∈ unroot σ'.clusters := by
      rw [(four_unrootedDist_split hX σ hB).1, (four_unrootedDist_split hX σ' hB).1, h]
    ext A
    rw [mem_unroot_iff (.inl hX) σ, mem_unroot_iff (.inl hX) σ']
    grind
  refine ⟨fun h => ⟨hU h, fun A hA h2 h2' => ?_⟩, fun hσ => ?_⟩
  · have hA2 : #A = 2 := by have := card_compl A; have := card_le_univ A; omega
    have h1 := (four_unrootedDist_split hX σ hA2).2 hA
    rw [h, (four_unrootedDist_split hX σ' hA2).2 (hU h ▸ hA)] at h1
    simpa using h1.symm
  · obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U4 hX σ
    obtain ⟨hU, hL⟩ := (SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e.symm).2 hσ
    have hx : (σ.relabel e.symm).unrootedLength {0, 1} =
        (σ'.relabel e.symm).unrootedLength {0, 1} := by
      by_cases h01 : ({0, 1} : Finset (Fin 4)) ∈ unroot (σ.relabel e.symm).clusters
      · aesop
      · rw [four_unrootedLength_eq_zero h01, four_unrootedLength_eq_zero (hU ▸ h01)]
    rw [← SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm]
    exact four_ext (four_unrootedDist_U4 _ hk he) (hx ▸ four_unrootedDist_U4 _ hk (hU ▸ he))

end ADR11
