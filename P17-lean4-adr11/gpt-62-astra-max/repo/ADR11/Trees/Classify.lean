module
public import ADR11.Computation.Certificate
public import ADR11.MSC.Relabel

@[expose] public section
namespace ADR11.Skeleton
open Finset _root_.ADR11.Computation
variable {n : ℕ}

private theorem member (C : List ℕ) (T : Family n) (h : Laminar T) : C.filter (fun c => decC n c ∈ T) ∈ admissible n C := by
  induction C with
  | nil => simp [admissible]
  | cons c C ih => by_cases hc : decC n c ∈ T <;> simp [admissible,hc,ih] <;> grind

/-- The checked catalogue covers every tree whose internal clades are among `C`. -/
theorem covered {σ : SpeciesTree (Fin n)} {C : List ℕ}
    (cand : ∀ A ∈ σ.clusters, 2 ≤ #A → A ≠ univ → A ∈ decF n C) : σ.clusters ∈ catalogue n C := by
  let s := C.filter (fun c => decC n c ∈ σ.internal)
  have e : decF n s = σ.internal := by
    ext A; simp only [s,decF,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq] at *
    grind [SpeciesTree.internal]
  exact List.mem_map.mpr ⟨s,member C σ.internal (by grind [SpeciesTree.internal,σ.laminar]),(congrArg hierarchyOf e).trans σ.complete_internal.symm⟩

theorem full_mem (σ : SpeciesTree (Fin n)) : σ.clusters ∈ full n := by
  apply covered; intro A _ h2 hu; simp [decF,inner,Function.comp_def,h2,hu]

end ADR11.Skeleton
