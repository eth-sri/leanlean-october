module
public import ADR11.Nonbinary.FourTaxa

@[expose] public section
namespace ADR11
open Finset Quartet Skeleton _root_.ADR11.Computation
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Two caterpillars sharing the same positive-length split. -/
private noncomputable def witness (k : Fin 2) : Quartet.Tree where
  clusters := hierarchy 4 [3,if k = 0 then 7 else 11]
  length _ := 1
  length_pos _ _ _ := one_pos
  univ_mem := by fin_cases k <;> decide
  singleton_mem := by fin_cases k <;> decide
  nonempty_of_mem := by fin_cases k <;> decide
  laminar := by fin_cases k <;> decide

private theorem binary (k : Fin 2) : (witness k).IsBinary := by
  unfold SpeciesTree.IsBinary; fin_cases k <;> decide

theorem Challenge.proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ τ _ _ => (Challenge.proposition11_theorem9_four hX σ τ).mp, ?_⟩
  have hd : (witness 0).unrootedDist id = (witness 1).unrootedDist id := by
    apply (Quartet.weight_eq_iff ..).mpr
    funext i
    fin_cases i <;> norm_num [sides,Sparse.branch,SpeciesTree.edge,witness,side] <;> congr 2 <;> decide
  have hn : ¬ (witness 0).SameRootedMetricTree (witness 1) := fun h =>
    (by decide : (witness 0).clusters ≠ (witness 1).clusters) h.1
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨(witness 0).relabel e, (witness 1).relabel e, SpeciesTree.binary_relabel (binary 0) e,
      SpeciesTree.binary_relabel (binary 1) e, (SpeciesTree.unrootedDist_relabel_eq_iff _ _ e).2 hd,
      fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff _ _ e).1 hs)⟩

end ADR11
