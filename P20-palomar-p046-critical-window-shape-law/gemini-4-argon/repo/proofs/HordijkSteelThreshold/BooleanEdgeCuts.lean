module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

/-- A cut in a finite graph with separately indexed edges, including parallel
edges. Its definition never identifies edges with equal endpoints. -/
def booleanEdgeCut {V E : Type*} (edges : Finset E) (a b : E → V)
    (label : V → Bool) : Finset E := edges.filter (fun e => label (a e) ≠ label (b e))

theorem minimal_separating_cut_is_bond {V E : Type*} [DecidableEq E]
    (edges : Finset E) (a b : E → V) (closed : Finset E)
    (x y : V) (f : V → Bool) (hf : f x ≠ f y)
    (hfclosed : booleanEdgeCut edges a b f ⊆ closed)
    (hmin : ∀ g : V → Bool, g x ≠ g y → booleanEdgeCut edges a b g ⊆ closed →
      (booleanEdgeCut edges a b f).card ≤ (booleanEdgeCut edges a b g).card)
    (g : V → Bool) (hgne : (booleanEdgeCut edges a b g).Nonempty)
    (hgsub : booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f) :
    booleanEdgeCut edges a b g = booleanEdgeCut edges a b f := by
  by_cases hsep : g x ≠ g y
  · exact Finset.eq_of_subset_of_card_le hgsub (hmin g hsep (hgsub.trans hfclosed))
  · have hxor : (f x ^^ g x) ≠ (f y ^^ g y) := by
      rw [not_ne_iff.mp hsep]; cases hx : f x <;> cases hy : f y <;> cases hg : g y <;> simp_all
    have hc : booleanEdgeCut edges a b (fun v => f v ^^ g v) =
        booleanEdgeCut edges a b f \ booleanEdgeCut edges a b g := by
      ext e
      by_cases he : e ∈ edges
      · have := fun hg => (Finset.mem_filter.mp (hgsub (Finset.mem_filter.mpr ⟨he, hg⟩))).2
        cases hfa : f (a e) <;> cases hfb : f (b e) <;>
          cases hga : g (a e) <;> cases hgb : g (b e) <;> simp_all [booleanEdgeCut]
      · simp [booleanEdgeCut, he]
    have hsmall := Finset.card_lt_card (Finset.sdiff_ssubset hgsub hgne)
    have hm := hmin (fun v => f v ^^ g v) hxor (hc ▸ Finset.sdiff_subset.trans hfclosed)
    rw [hc] at hm; omega

end HordijkSteelThreshold
