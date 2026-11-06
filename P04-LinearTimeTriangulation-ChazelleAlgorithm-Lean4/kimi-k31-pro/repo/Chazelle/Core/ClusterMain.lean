module

public import Chazelle.Core.ClusterCost

/-!
# WP-I, part 72: the cluster decomposition — `clusters : ClusterSpec`

`clusterProg = phase1; phase2a; labS; outS; bumpS`. Outputs: the flags of `D* = D ∪ H` in slot
48 (register `130004`), the labels in slot 2 (register `130005`).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- **The cluster decomposition.** -/
def clusterProg : Stmt := .seq phase1 (.seq phase2a (.seq labS (.seq outS bumpS)))

/-- A filter over `Fin n` counts like the filter over `range n`. -/
theorem card_fin_filter {n : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun v : Fin n => p v)).card = ((Finset.range n).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v.2, hv⟩
  · rintro ⟨hx, hp⟩; exact ⟨⟨x, hx⟩, hp, rfl⟩

end

end Chazelle.Core.Cluster
