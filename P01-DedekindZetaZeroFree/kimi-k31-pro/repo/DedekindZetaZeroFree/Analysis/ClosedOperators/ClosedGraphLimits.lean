module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

noncomputable section
open Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

theorem closed_graph_limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Δ : H →ₗ.[ℂ] H) (hclosed : Δ.IsClosed)
    (z : ℕ → H × H) (hz : ∀ n, ∃ hn : (z n).1 ∈ Δ.domain,
      Δ ⟨(z n).1, hn⟩ = (z n).2)
    (u v : H) (hlim : Tendsto z atTop (nhds (u,v))) :
    ∃ hu : u ∈ Δ.domain, Δ ⟨u,hu⟩ = v := by
  have hgclosed : IsClosed (Δ.graph : Set (H × H)) := hclosed
  have hmem : (u, v) ∈ Δ.graph := by
    refine hgclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    obtain ⟨hn, hval⟩ := hz n
    show z n ∈ Δ.graph
    grind
  grind

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
