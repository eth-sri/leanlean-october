module

public import ADR11.MSC.Basic
public import ADR11.Clusters
public import ADR11.MSC.Law

/-! Consistency under sampling of lineages. Generator increments commute
with projection: pairs with an invisible endpoint give zero, and visible
pairs project bijectively. Pass to the exponential and its limit, then
compose over the species tree. -/

@[expose] public section

namespace ADR11

open Finset Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

private theorem project_merge {F : Clusters L} (s : L' → L) {A B : Finset L} (ha : A ∈ F) (hb : B ∈ F) :
    project s (insert (A ∪ B) F) = if (pre s A).Nonempty ∧ (pre s B).Nonempty then
      insert (pre s A ∪ pre s B) (project s F) else project s F := by
  have ins (C) : project s (insert C F) = if (pre s C).Nonempty then insert (pre s C) (project s F) else project s F := by
    unfold project; rw [filter_insert]; split <;> simp
  simp only [ins,pre_union,union_nonempty]
  by_cases a : (pre s A).Nonempty <;> by_cases b : (pre s B).Nonempty <;>
    simp_all [nonempty_iff_ne_empty, project_mem ha,project_mem hb]

/-- Bijections lift to sets of a prescribed cardinality. -/
private theorem sum_pairs_image {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (R : Finset α)
    (inj : Set.InjOn f R) (k : ℕ) (u : Finset β → ℝ) :
    ∑ P ∈ (R.image f).powersetCard k, u P = ∑ P ∈ R.powersetCard k, u (P.image f) := by
  simp only [powersetCard_eq_filter,sum_filter,powerset_image,sum_image (image_injOn_powerset_of_injOn inj)]
  exact sum_congr rfl fun P hp => by rw [card_image_of_injOn (inj.mono (mem_powerset.mp hp))]

/-- Restricting annihilates the generator increments of pairs of roots
without two visible endpoints. The remaining pairs project bijectively. -/
private theorem generator_project {F : Clusters L} (hf : IsForest F) (s : L' → L) (w : Clusters L' → ℝ) :
    (kingmanGenerator *ᵥ (w ∘ project s)) F = (kingmanGenerator *ᵥ w) (project s F) := by
  let R := (roots F).filter fun A => (pre s A).Nonempty
  have inj : Set.InjOn (pre s) R := fun _ ha _ hb e => eq_of_trace
    (hf.disjoint_of_mem_roots (mem_filter.mp ha).1 (mem_filter.mp hb).1) (mem_filter.mp ha).2 e.le
  change ∑ G, _ * w (project s G) = ∑ G, _ * w G
  rw [hf.generator_pairs (fun G => w (project s G)),(hf.project s).generator_pairs,roots_project hf]
  change _ = ∑ P ∈ (R.image (pre s)).powersetCard 2, _
  have part : R.powersetCard 2 = ((roots F).powersetCard 2).filter (· ⊆ R) := by
    ext; have := filter_subset (fun A => (pre s A).Nonempty) (roots F); grind
  rw [sum_pairs_image _ _ inj,part,sum_filter]
  apply sum_congr rfl; intro P hp; obtain ⟨a,ha,b,hb,ne,rfl⟩ := mem_pairs.mp hp
  simp [project_merge s (roots_subset _ ha) (roots_subset _ hb),R,ha,hb,insert_subset_iff,apply_ite,ite_sub]; grind

private theorem pow_project (s : L' → L) (n : ℕ) {F : Clusters L} (hf : IsForest F) (w : Clusters L' → ℝ) :
    ((kingmanGenerator ^ n) *ᵥ (w ∘ project s)) F = ((kingmanGenerator ^ n) *ᵥ w) (project s F) := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ',← Matrix.mulVec_mulVec,← generator_project hf]
    change ∑ G, _ * _ = ∑ G, _ * _
    rw [hf.sum_kingmanGenerator_mul,hf.sum_kingmanGenerator_mul,ih hf]; congr 1
    exact sum_congr rfl fun G hg => ih (hf.of_mem_merges hg).1

private theorem transition_project {F : Clusters L} (hf : IsForest F) (s : L' → L) (t : ℝ) :
    Law.push (project s) (kingmanTransition t F) = kingmanTransition t (project s F) := by
  apply dotProduct_eq; intro w; rw [Law.expect_push]
  change (kingmanTransition t *ᵥ (w ∘ project s)) F = (kingmanTransition t *ᵥ w) (project s F)
  refine (hasSum_exp_vec _ t _ F).unique ?_
  simp_rw [pow_project s _ hf]; exact hasSum_exp_vec _ t w _

private theorem population_project (len : Finset X → ℝ) (A : Finset X) {F : Clusters L} (hf : IsForest F) (s : L' → L) :
    Law.push (project s) (populationKernel len A F) = populationKernel len A (project s F) := by
  unfold populationKernel; split
  · funext G
    have h : Filter.Tendsto (fun t => Law.push (project s) (kingmanTransition t F) G) Filter.atTop (nhds (Law.push (project s) (kingmanAbsorption F) G)) := by
      apply tendsto_finsetSum; intro H _; split <;> first | exact tendsto_const_nhds | exact tendsto_kingmanTransition hf H
    simp only [transition_project hf] at h
    exact tendsto_nhds_unique h (tendsto_kingmanTransition (hf.project _) G)
  · apply transition_project hf

private theorem project_union (s : L' → L) (F G : Clusters L) : project s (F ∪ G) = project s F ∪ project s G := by simp [project,filter_union,image_union]
private theorem project_sampled (e : L' ↪ L) (s : L → X) (A : Finset X) :
    project e (sampledForest s A) = sampledForest (s ∘ e) A := by
  ext D; rw [mem_project,mem_sampledForest]; constructor
  · rintro ⟨hn,C,hc,rfl⟩; obtain ⟨l,hl,rfl⟩ := mem_sampledForest.mp hc; obtain ⟨i,hi⟩ := hn
    obtain rfl := mem_singleton.mp (mem_pre.mp hi)
    exact ⟨i,hl,(pre_atom e.injective i).symm⟩
  · rintro ⟨i,hi,rfl⟩; exact ⟨singleton_nonempty _,{e i},singleton_mem_sampledForest.mpr hi,pre_atom e.injective _⟩

/-- Projection commutes first with independent union, then with evolution in
one population. -/
private theorem forest_push (σ : SpeciesTree X) (s : L → X) (e : L' ↪ L) {A : Finset X} :
    Law.push (project e) (σ.leave s A) = σ.leave (s ∘ e) A := by
  induction A using σ.cladeInduction with | step A ih =>
  have enter : Law.push (project e) (σ.enter s A) = σ.enter (s ∘ e) A := by
    apply Law.cdf_inj; intro K; unfold SpeciesTree.enter
    rw [Law.cdf_push_combine _ _ _ _ (project_union e) (by simp [project]),Law.cdf_combine,project_sampled]
    congr 1; exact prod_congr rfl fun B hb => congrArg (Law.cdf · K) (ih B hb)
  rw [σ.leave_eq,σ.leave_eq,Law.push_bind (r := project e) _ (fun F hf => population_project σ.length A ((σ.valid_enter s A).support hf).1 e),enter]

private theorem unroot_project (s : L' → L) (G : Clusters L) : unroot (project s G) = (project s (unroot G)).erase univ := by
  ext D
  have flip : (∃ C, (Cᶜ ∈ G ∧ Cᶜ ≠ univ) ∧ pre s C = D) ↔ ∃ C, (C ∈ G ∧ C ≠ univ) ∧ pre s C = Dᶜ := by
    constructor <;> rintro ⟨C,h,e⟩ <;> exact ⟨Cᶜ,by simp_all⟩
  simp only [mem_unroot,mem_erase,mem_project,nonempty_iff_ne_empty,or_and_right,exists_or,ne_eq,compl_eq_univ_iff,compl_eq_empty_iff]
  have := pre_univ (X := L) s; grind [compl_eq_univ_iff,compl_eq_empty_iff]

theorem sample_eq {σ τ : SpeciesTree X} {s : L → X} (h : σ.unrootedDist s = τ.unrootedDist s) (e : L' ↪ L) :
    σ.unrootedDist (s ∘ e) = τ.unrootedDist (s ∘ e) := by
  have eqn (μ : SpeciesTree X) : μ.unrootedDist (s ∘ e) = Law.push (fun T => (project e T).erase univ) (μ.unrootedDist s) := by
    change Law.push unroot (μ.leave _ univ) = Law.push _ (Law.push unroot (μ.leave _ univ))
    rw [← forest_push μ s e,Law.push_push,Law.push_push]; exact congrArg (Law.push · _) (funext (unroot_project e))
  rw [eqn,eqn,h]

end ADR11
