module
public import ADR11.Trees.Hierarchy

@[expose] public section
namespace ADR11.SpeciesTree
open Finset Real
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Metric coordinates, padding a missing edge with length zero. -/
noncomputable def edge (σ : SpeciesTree X) (C : Finset X) := if C ∈ σ.clusters.erase univ then σ.length C else 0

@[simp] theorem edge_pos_iff {σ : SpeciesTree X} {C : Finset X} : 0 < σ.edge C ↔ C ∈ σ.clusters.erase univ := by
  unfold edge; split_ifs with h <;> simp_all [σ.length_pos,mem_erase]

theorem edge_nonneg (σ : SpeciesTree X) (C : Finset X) : 0 ≤ σ.edge C := by
  unfold edge; split_ifs with h; exact (σ.length_pos _ (mem_erase.mp h).2 (mem_erase.mp h).1).le; rfl

theorem same_of_edge {σ τ : SpeciesTree X}
    (h : ∀ C, 2 ≤ #C → C ≠ univ → σ.edge C = τ.edge C) : σ.SameRootedMetricTree τ := by
  have hi : σ.internal = τ.internal := by
    ext C; by_cases ok : 2 ≤ #C ∧ C ≠ univ
    · simpa [internal,ok.1,ok.2] using (show 0 < σ.edge C ↔ 0 < τ.edge C by rw [h C ok.1 ok.2])
    · simp [internal,ok]
  have hc := σ.complete_internal.trans ((congrArg hierarchyOf hi).trans τ.complete_internal.symm)
  exact ⟨hc, fun C hm h2 hu => by simpa [edge, hu, hm, hc ▸ hm] using h C h2 hu⟩

theorem edge_eq {σ τ : SpeciesTree X} (h : σ.SameRootedMetricTree τ) {A : Finset X} (ha : 2 ≤ #A) : σ.edge A = τ.edge A := by
  simp only [edge,mem_erase,← h.1]; split <;> grind [h.2]

/-- Restriction adds the padded coordinates in each trace fibre. -/
theorem pull_edge {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X) (s : L → X) (hn) {D : Finset L}
    (h2 : 2 ≤ #D) (hu : D ≠ univ) : (σ.pull s hn).edge D = ∑ C ∈ univ.filter (pre s · = D), σ.edge C := by
  have nz := card_pos.mp (by omega : 0 < #D)
  have fam : ((univ.filter (pre s · = D)).filter (· ∈ σ.clusters.erase univ)) = σ.fiber s D := by
    ext C; grind [fiber,pre_univ]
  simp only [edge,← sum_filter,fam]; split_ifs with hm
  · obtain ⟨C,hc,rfl⟩ := σ.source (mem_erase.mp hm).2 h2
    exact σ.pull_time hc _
  · symm; apply sum_eq_zero; intro C hC; obtain ⟨hc,e⟩ := mem_filter.mp hC
    exact (hm (mem_erase.mpr ⟨hu,e ▸ σ.traced hc (e ▸ nz)⟩)).elim

theorem edge_add_compl (σ : SpeciesTree X) (A : Finset X) : σ.edge A + σ.edge Aᶜ = σ.unrootedLength A := by
  obtain ⟨x,_⟩ := σ.nonempty_of_mem _ σ.univ_mem
  have ne : A ≠ Aᶜ := fun e => by have h := Finset.ext_iff.mp e x; simp at h
  unfold unrootedLength
  have he : σ.clusters.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) =
      ({A, Aᶜ} : Finset _).filter (· ∈ σ.clusters.erase univ) := by ext; simp; grind
  rw [he,sum_filter,sum_pair ne]; rfl

theorem split_pos (σ : SpeciesTree X) (A : Finset X) : A ∈ unroot σ.clusters ↔ 0 < σ.unrootedLength A := by
  have e : A ∈ unroot σ.clusters ↔ 0 < σ.edge A ∨ 0 < σ.edge Aᶜ := by simp [mem_unroot,and_comm]
  rw [e,← edge_add_compl]; have := σ.edge_nonneg A; have := σ.edge_nonneg Aᶜ; grind

theorem split_zero {σ : SpeciesTree X} {A : Finset X} (h : A ∉ unroot σ.clusters) : σ.unrootedLength A = 0 := by
  rw [split_pos,← edge_add_compl] at h; rw [← edge_add_compl]; linarith [σ.edge_nonneg A,σ.edge_nonneg Aᶜ]

theorem split_eq {σ τ : SpeciesTree X} (h : σ.SameUnrootedMetricTree τ) {A : Finset X}
    (ha : 2 ≤ #A) (hb : 2 ≤ #Aᶜ) : σ.unrootedLength A = τ.unrootedLength A := by
  by_cases hm : A ∈ unroot σ.clusters; · exact h.2 A hm ha hb
  rw [split_zero hm,split_zero (h.1 ▸ hm)]

end ADR11.SpeciesTree
