module
public import ADR11.Types
@[expose] public section
namespace ADR11
open Finset
theorem Compatible.flip {X : Type*} {A B : Finset X} (h : Compatible A B) : Compatible B A := by grind

theorem compatible_singleton {X : Type*} (x : X) (A : Finset X) : Compatible {x} A := by simp [Compatible]; grind

/-- A forest: nonempty clusters, any two of which are nested or disjoint. -/
def IsForest {L : Type*} (F : Clusters L) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ Laminar F

theorem IsForest.filter {L : Type*} {F : Clusters L} (hf : IsForest F) (p : Finset L → Prop) [DecidablePred p] : IsForest (F.filter p) := by grind [IsForest]

theorem SpeciesTree.forest {X : Type*} [Fintype X] [DecidableEq X] (σ : SpeciesTree X) : IsForest σ.clusters := ⟨σ.nonempty_of_mem,σ.laminar⟩

/-- Adding sampled singletons never introduces an incompatibility. -/
theorem IsForest.with_atoms {L : Type*} [DecidableEq L] {F : Clusters L} (h : IsForest F) (S : Finset L) : IsForest (F ∪ S.image fun l => {l}) := by
  grind [IsForest,compatible_singleton,Compatible.flip]

variable {L X : Type*} [Fintype L] [DecidableEq X]

/-- The lineages sampled in a set of taxa. -/
def pre (s : L → X) (A : Finset X) := univ.filter fun l => s l ∈ A
@[simp] theorem mem_pre {s : L → X} {A : Finset X} {l : L} : l ∈ pre s A ↔ s l ∈ A := by simp [pre]
@[simp] theorem pre_univ [Fintype X] (s : L → X) : pre s univ = univ := by aesop

theorem pre_mono (s : L → X) : Monotone (pre s) := by grind [Monotone,mem_pre]
theorem pre_disjoint [DecidableEq L] (s : L → X) {A B : Finset X} (h : Disjoint A B) :
    Disjoint (pre s A) (pre s B) := by grind [Finset.disjoint_left,mem_pre]

/-- A visible trace distinguishes members of a disjoint family. -/
theorem eq_of_trace {s : L → X} {A B : Finset X} (hd : A ≠ B → Disjoint A B)
    (hn : (pre s A).Nonempty) (le : pre s A ⊆ pre s B) : A = B := by
  obtain ⟨l,hl⟩ := hn; by_contra ne; exact disjoint_left.mp (hd ne) (mem_pre.mp hl) (mem_pre.mp (le hl))

theorem Compatible.preimage [DecidableEq L] {A B : Finset X} (h : Compatible A B) (s : L → X) :
    Compatible (pre s A) (pre s B) := by
  grind [mem_pre,Finset.disjoint_left]

@[simp] theorem pre_union [DecidableEq L] (s : L → X) (A B : Finset X) : pre s (A ∪ B) = pre s A ∪ pre s B := by aesop
@[simp] theorem pre_compl [Fintype X] [DecidableEq L] (s : L → X) (A : Finset X) : pre s Aᶜ = (pre s A)ᶜ := by aesop

theorem pre_atom {s : L → X} (h : Function.Injective s) (l : L) : pre s {s l} = {l} := by aesop
/-- Trace on an induced subtree. -/
abbrev traceOn (S A : Finset X) := pre (Subtype.val : S → X) A


/-- Pull a family back along a sampling map and discard empty traces. -/
def project [DecidableEq L] (s : L → X) (F : Clusters X) := (F.filter fun A => (pre s A).Nonempty).image (pre s)

theorem mem_project [DecidableEq L] {s : L → X} {F : Clusters X} {C : Finset L} :
    C ∈ project s F ↔ C.Nonempty ∧ ∃ A ∈ F, pre s A = C := by grind [project]

theorem project_mem [DecidableEq L] {s : L → X} {F : Clusters X} {A : Finset X} (ha : A ∈ F) (h : (pre s A).Nonempty) :
    pre s A ∈ project s F := mem_project.mpr ⟨h,A,ha,rfl⟩

theorem IsForest.project [DecidableEq L] {F : Clusters X} (h : IsForest F) (s : L → X) : IsForest (ADR11.project s F) := by
  grind [IsForest,mem_project,Compatible.preimage]

variable {s : L → X} (hs : Function.Surjective s)
include hs
@[simp] theorem image_pre (A : Finset X) : (pre s A).image s = A := by
  ext x; obtain ⟨l,rfl⟩ := hs x; aesop

theorem pre_injective : Function.Injective (pre s) := fun A B e => by grind [image_pre]

end ADR11
