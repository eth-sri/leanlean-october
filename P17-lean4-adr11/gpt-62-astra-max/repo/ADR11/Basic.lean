module
public import ADR11.Clusters

/-! The induced species tree for any sampling map. Take nonempty inverse
images, complete the family by adding singleton leaves, and sum time over
all clades with the same trace. New leaves can be given any positive time. -/
@[expose] public section
namespace ADR11.SpeciesTree
open Finset
variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L] (σ : SpeciesTree X)

def traces (s : L → X) := project s σ.clusters ∪ univ.image fun l : L => {l}
def fiber (s : L → X) (D : Finset L) := σ.clusters.filter fun C => pre s C = D

theorem traced {s : L → X} {C : Finset X} (hc : C ∈ σ.clusters) (hn : (pre s C).Nonempty) : pre s C ∈ σ.traces s := mem_union_left _ (project_mem hc hn)

theorem source {s : L → X} {D : Finset L} (hd : D ∈ σ.traces s) (h2 : 2 ≤ #D) : ∃ C ∈ σ.clusters, pre s C = D := by
  rcases mem_union.mp hd with h | h; exact (mem_project.mp h).2
  obtain ⟨l,_,rfl⟩ := mem_image.mp h; simp at h2

noncomputable def pull (s : L → X) (hn : (univ : Finset L).Nonempty) : SpeciesTree L where
  clusters := σ.traces s
  univ_mem := pre_univ s ▸ σ.traced σ.univ_mem (by simpa)
  singleton_mem l := mem_union_right _ (mem_image_of_mem _ (mem_univ l))
  nonempty_of_mem := ((σ.forest.project s).with_atoms univ).1
  laminar := ((σ.forest.project s).with_atoms univ).2
  length D := if (σ.fiber s D).Nonempty then ∑ C ∈ σ.fiber s D, σ.length C else 1
  length_pos D _ hu := by
    split_ifs with h
    · exact sum_pos (fun C hc => σ.length_pos C (mem_filter.mp hc).1 (by rintro rfl; exact hu ((mem_filter.mp hc).2.symm.trans (pre_univ _)))) h
    · exact one_pos

theorem pull_time {s : L → X} {C : Finset X} (hc : C ∈ σ.clusters) (hn) :
    (σ.pull s hn).length (pre s C) = ∑ B ∈ σ.fiber s (pre s C), σ.length B := ite_eq_left ⟨C,mem_filter.mpr ⟨hc,rfl⟩⟩

theorem traces_of_injective (s : L → X) (hs : Function.Injective s) : σ.traces s = project s σ.clusters := by
  apply union_eq_left.mpr; intro D h; obtain ⟨l,_,rfl⟩ := mem_image.mp h
  rw [← pre_atom hs]; exact project_mem (σ.singleton_mem _) ⟨l,by simp⟩

noncomputable abbrev restrict (S : Finset X) (h : S.Nonempty) := σ.pull (Subtype.val : S → X) (by simpa using h)

end ADR11.SpeciesTree
