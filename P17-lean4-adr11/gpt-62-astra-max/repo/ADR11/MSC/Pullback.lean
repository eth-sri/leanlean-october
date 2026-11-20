module
public import ADR11.MSC.Basic

/-! Sampling along an arbitrary map pulls a species tree back to the sampled
lineages. Keep the nonempty preimages, add any missing leaves, and sum time
along each chain with the same preimage. This covers both pruning to a
subset and expanding taxa to stars over their samples. -/
@[expose] public section
namespace ADR11
open Finset
variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]

variable {σ : SpeciesTree X} {s : L → X} {A B C : Finset X} {nonempty : (univ : Finset L).Nonempty}
local notation "τ" => σ.pull s nonempty
local notation "tr" => pre s
local notation "kids" => σ.kids
local notation "buds" => childClusters (σ.traces s)

private theorem cut_fiber (ha : A ∈ σ.clusters) (hb : B ∈ kids A) (hn : (tr B).Nonempty) (hc : C ∈ σ.fiber s (tr B)) :
    C ⊆ B ∨ (A ⊆ C ∧ tr A = tr B) := by
  obtain ⟨x,hx⟩ := hn; obtain ⟨hc,e⟩ := mem_filter.mp hc
  have := σ.cut ha hb hc (mem_pre.mp hx) (mem_pre.mp (e ▸ hx))
  have sub := pre_mono s (child_lt hb).subset; grind [mem_pre]

private abbrev Bottom (σ : SpeciesTree X) (s : L → X) (A : Finset X) := ∀ C ∈ σ.clusters, C ⊂ A → pre s C ≠ pre s A

private theorem bottom (bot : ∀ B ∈ kids A, tr B ≠ tr A) : Bottom σ s A := by
  intro C hc lt e; obtain ⟨B,hb,sub⟩ := subset_child hc lt
  exact bot B hb (subset_antisymm (pre_mono s (child_lt hb).subset) (e ▸ pre_mono s sub))

/-- Above the bottom of a trace chain, the branching children are exactly
    the images of the branching children in the original tree. -/
private theorem branching (ha : A ∈ σ.clusters) (bot : Bottom σ s A) :
    ((buds (tr A)).filter fun D => 2 ≤ #D) = ((kids A).filter fun B => 2 ≤ #(tr B)).image tr := by
  let big (D : Finset L) := 2 ≤ #D
  have mono (D E : Finset L) (sub : D ⊆ E) (h : big D) : big E := h.trans (card_le_card sub)
  have e : ((σ.traces s).filter (· ⊂ tr A)).filter big = (project s (σ.clusters.filter (· ⊂ A))).filter big := by
    ext D; simp only [mem_filter,and_congr_left_iff,mem_project]; intro h
    have hn : D.Nonempty := card_pos.mp (by change 2 ≤ #D at h; omega)
    have order (C) (hc : C ∈ σ.clusters) (e : tr C = D) : D ⊂ tr A ↔ C ⊂ A := by
      subst D; exact ⟨σ.forest.reflect_lt hc ha hn,fun lt => ((pre_mono s) lt.subset).ssubset_of_ne (bot C hc lt)⟩
    grind [σ.source,σ.traced]
  rw [kids_roots, ← roots_filter _ mono, e, roots_filter _ mono, roots_project (σ.forest.filter _), SpeciesTree.kids,kids_roots]
  ext D; grind [mem_project,Finset.card_pos]

private noncomputable abbrev lower (σ : SpeciesTree X) (s : L → X) (A : Finset X) := (σ.fiber s (pre s A)).filter (· ⊆ A)
private noncomputable abbrev timesBelow (σ : SpeciesTree X) (s : L → X) (A : Finset X) := ∑ C ∈ lower σ s A, σ.length C

private theorem top_time (ha : A ∈ σ.clusters) (hb : B ∈ kids A) (hn : (tr B).Nonempty) (ne : tr B ≠ tr A) : (τ).length (tr B) = timesBelow σ s B := by
  rw [σ.pull_time (child_mem hb) nonempty]; congr 1; symm; apply filter_eq_self.mpr
  grind [cut_fiber ha hb hn]

private theorem chain_time (ha : A ∈ σ.clusters) (hb : B ∈ kids A) (hn : (tr A).Nonempty) (he : tr B = tr A) :
    timesBelow σ s A = timesBelow σ s B + σ.length A := by
  have lt := child_lt hb
  have hnB : (tr B).Nonempty := he ▸ hn
  have eqn : lower σ s A = insert A (lower σ s B) := by ext C; grind [cut_fiber ha hb hnB,SpeciesTree.fiber]
  rw [timesBelow,eqn,sum_insert (by grind),add_comm]

private theorem bottom_time (ha : A ∈ σ.clusters) (bot : Bottom σ s A) : timesBelow σ s A = σ.length A := by
  apply sum_eq_single_of_mem A <;> grind [SpeciesTree.fiber]

private theorem child_ne_top {H : Clusters X} (hb : B ∈ childClusters H A) : B ≠ univ := ((child_lt hb).trans_le (subset_univ _)).ne

/-- A population with at most one sampled lineage contributes only its seed. -/
private theorem small_cdf (ha : A ∈ σ.clusters) {K : Clusters L} (h : #(tr A) ≤ 1) (hs : sampledForest s A ⊆ K) :
    Law.cdf (σ.leave s A) K = 1 := by
  have v := σ.valid_leave s ha
  refine Eq.trans (Law.expect_congr (g := 1) ?_) v.mass; intro F hz
  obtain ⟨hf,_,hl⟩ := v.support hz
  have sub : F ⊆ K := fun C hc => by
    have le : C ⊆ tr A := (subset_lineages hc).trans hl
    obtain ⟨x,rfl⟩ := card_eq_one.mp (show #C = 1 by have := (hf.1 C hc).card_pos; have := card_le_card le; omega)
    exact hs (singleton_mem_sampledForest.mpr (mem_pre.mp (singleton_subset_iff.mp le)))
  simp [sub]

@[simp] private theorem pre_id (D : Finset L) : pre id D = D := by ext; simp
@[simp] private theorem sampled_trace (D : Finset X) : sampledForest id (tr D) = sampledForest s D := by ext; simp [sampledForest]

private theorem seed_sub {K : Clusters L} (hb : B ∈ kids A) (h : sampledForest s A ⊆ K) : sampledForest s B ⊆ K :=
  (image_subset_image (f := fun l : L => ({l} : Finset L)) (pre_mono s (child_lt hb).subset)).trans h

private theorem chain_entry (hb : B ∈ kids A) (he : tr B = tr A) :
    σ.enter s A = σ.leave s B := by
  have seeds : sampledForest s A = sampledForest s B := by change (tr A).image _ = (tr B).image _; rw [he]
  apply Law.cdf_inj; intro K; rw [SpeciesTree.enter,Law.cdf_combine,seeds]; split_ifs with hs
  · apply prod_eq_single_of_mem B hb
    intro D hd ne; apply small_cdf (child_mem hd)
    · have dis := pre_disjoint s (σ.siblings hd hb ne)
      have := pre_mono s (child_lt hd).subset
      grind [Finset.disjoint_left,Finset.card_le_one]
    · exact seed_sub hd (seeds ▸ hs)
  · exact (Law.cdf_zero (fun _ h => ((σ.valid_leave s (child_mem hb)).support h).2.1) hs).symm

private theorem cdf_enter (K : Clusters L) : Law.cdf (σ.enter s A) K = if sampledForest s A ⊆ K then
    ∏ B ∈ kids A with 2 ≤ #(tr B), Law.cdf (σ.leave s B) K else 0 := by
  rw [SpeciesTree.enter,Law.cdf_combine]; split_ifs with hs <;> try rfl
  symm; apply prod_filter_of_ne; intro B hb hz; by_contra! hn
  exact hz (small_cdf (child_mem hb) (by omega) (seed_sub hb hs))

private noncomputable abbrev entry (ρ : SpeciesTree L) (s : L → X) (A : Finset X) := ρ.enter id (pre s A)

private theorem bottom_entry (ha : A ∈ σ.clusters) (bot : Bottom σ s A)
    (ih : ∀ B ∈ kids A, (tr B).Nonempty → σ.leave s B = Law.bind (entry τ s B) (populationKernel (timesBelow σ s) B)) :
    σ.enter s A = entry τ s A := by
  apply Law.cdf_inj; intro K; simp only [entry,cdf_enter,pre_id,sampled_trace]; split_ifs <;> try rfl
  change _ = ∏ D ∈ (buds (tr A)).filter _, _
  rw [branching ha bot,prod_image fun B hb C hc e => eq_of_trace (σ.siblings (mem_filter.mp hb).1 (mem_filter.mp hc).1) (card_pos.mp (by have := (mem_filter.mp hb).2; omega)) e.le]
  apply prod_congr rfl; intro B hb; obtain ⟨hb,h2⟩ := mem_filter.mp hb
  have hn := card_pos.mp (by omega : 0 < #(tr B))
  have lt := ((pre_mono s) (child_lt hb).subset).ssubset_of_ne (bot B (child_mem hb) (child_lt hb))
  rw [ih B hb hn,SpeciesTree.leave_eq]; simp [entry,populationKernel,child_ne_top hb,(lt.trans_le (subset_univ _)).ne,top_time (nonempty := nonempty) ha hb hn lt.ne]

private theorem continue_time {len len' : Finset X → ℝ} {t : ℝ} (he : len' A = t + len A)
    (p : Law (Clusters L)) (hp : ∀ F, p F ≠ 0 → IsForest F) :
    Law.bind (Law.bind p (kingmanTransition t)) (populationKernel len A) = Law.bind p (populationKernel len' A) := by
  funext G; change dotProduct _ _ = dotProduct p _; rw [Law.expect_bind p (kingmanTransition t) (fun F => populationKernel len A F G)]
  apply Law.expect_congr; intro F hz; by_cases hu : A = univ <;> simp [populationKernel,hu,dotProduct,he,kingmanTransition_add,Matrix.mul_apply,kingmanTransition_mul_kingmanAbsorption (hp _ hz)]

private theorem prune (ha : A ∈ σ.clusters) (hn : (tr A).Nonempty) : σ.leave s A = Law.bind (entry τ s A) (populationKernel (timesBelow σ s) A) := by
  induction A using σ.cladeInduction with | step A ih =>
  have step (B) (hb : B ∈ kids A) := ih B hb (child_mem hb)
  rw [SpeciesTree.leave_eq]; by_cases same : ∃ B ∈ kids A, tr B = tr A
  · obtain ⟨B,hb,e⟩ := same
    rw [chain_entry hb e,step B hb (e ▸ hn),populationKernel,ite_eq_right (child_ne_top hb),show entry τ s B = entry τ s A by simp only [entry,e]]
    exact continue_time (chain_time ha hb hn e) _ fun F hf => (((τ).valid_enter id _).support hf).1
  · push Not at same; rw [bottom_entry ha (bottom same) step]; simp [populationKernel,bottom_time ha (bottom same)]

theorem SpeciesTree.unrootedDist_pull (σ : SpeciesTree X) (s : L → X) (nonempty : (univ : Finset L).Nonempty) : (σ.pull s nonempty).unrootedDist id = σ.unrootedDist s := by
  funext U
  have hn : (pre s univ).Nonempty := by simpa
  change Law.push unroot ((σ.pull s nonempty).leave id univ) U = Law.push unroot (σ.leave s univ) U
  rw [prune (nonempty := nonempty) σ.univ_mem hn,SpeciesTree.leave_eq]; simp [entry,populationKernel]

end ADR11
