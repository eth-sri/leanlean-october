module

public import RequestProject.PosetCoverUpTransform
public import RequestProject.StrictOrderComplex

@[expose] public section

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

variable (e : StrictOrdEdge Q) (v : P)

/-- The actual unique lift of a strict edge from a specified actual source vertex. -/
noncomputable def strictEdgeLiftFrom (hv : f v = e.1.1) :
    StrictOrdEdge P := by
  let h := hv.symm ▸ e.2.le
  exact ⟨(v, (Classical.choose _)), lt_of_le_of_ne (Classical.choose_spec (hf.up v e.1.2 h)).1.1 (by
    grind)⟩

theorem strictEdgeLiftFrom_projection (hv : f v = e.1.1) :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftFrom e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext hv
  exact (Classical.choose_spec (hf.up v _ (hv.symm ▸ e.2.le))).1.2

theorem strictEdgeLiftFrom_unique (hv : f v = e.1.1)
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (hs : r.1.1 = v) : r = hf.strictEdgeLiftFrom e v hv := by
  apply Subtype.ext
  apply Prod.ext hs
  have hp := congrArg (fun s : StrictOrdEdge Q => s.1.2)
    (hr.trans (hf.strictEdgeLiftFrom_projection e v hv).symm)
  exact hf.up_inj (hs ▸ r.2.le) (hf.strictEdgeLiftFrom e v hv).2.le hp

variable (hv : f v = e.1.2)

/-- The actual unique lift of a strict edge to a specified actual target vertex. -/
noncomputable def strictEdgeLiftTo :
    StrictOrdEdge P := by
  let h := hv.symm ▸ e.2.le
  exact ⟨((Classical.choose _), v), lt_of_le_of_ne (Classical.choose_spec (hf.down v e.1.1 h)).1.1 (by
    grind)⟩

theorem strictEdgeLiftTo_projection :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftTo e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Classical.choose_spec (hf.down v _ (hv.symm ▸ e.2.le))).1.2
  · exact hv

theorem strictEdgeLiftTo_unique
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (ht : r.1.2 = v) : r = hf.strictEdgeLiftTo e v hv := by
  apply Subtype.ext
  apply Prod.ext
  · have hp := congrArg (fun s : StrictOrdEdge Q => s.1.1)
      (hr.trans (hf.strictEdgeLiftTo_projection e v hv).symm)
    exact hf.down_inj (ht ▸ r.2.le) (hf.strictEdgeLiftTo e v hv).2.le hp
  · exact ht

end FiniteChains.Comb.IsPosetCover
