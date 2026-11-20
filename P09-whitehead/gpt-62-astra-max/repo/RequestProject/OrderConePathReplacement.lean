module

public import RequestProject.ConeAdjPoset

@[expose] public section

namespace FiniteChains.Comb
universe u

/-- A null loop obtained by closing a path with a reverse path proves the two paths homotopic. -/
theorem htpy_of_append_rev_null {X : Complex2.{u}} {a b : X.V}
    {p q : List _} (hp : IsPath X.src X.tgt p a b)
    (hq : IsPath X.src X.tgt q a b) (h : Htpy X a a (p ++ revPath q) []) :
    Htpy X a b p q := by
  have hh := h.congr_append (show IsPath X.src X.tgt [] a a from rfl) hq
  have hc' : Htpy X a b ((p ++ revPath q) ++ q) p := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using ((htpy_revPath_append hq).congr_append hp (show IsPath X.src X.tgt [] b b from rfl))
  apply hc'.symm.trans <;> assumption

/-- Every actual path below a fixed apex is homotopic to the two-edge path through that apex. -/
theorem htpy_path_through_upper_bound {P : Type u} [Preorder P]
    (d : P) {a b : P} (ha : a ≤ d) (hb : b ≤ d)
    {p : List _}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hs : PathIn (fun x => x ≤ d) p) :
    Htpy _ a b p [ordPos ha, ordNeg hb] := by
  have hq : IsPath (orderCx P).src (orderCx P).tgt [ordPos ha, ordNeg hb] a b :=
    ⟨rfl, rfl, rfl⟩
  apply htpy_of_append_rev_null hp hq
  exact htpy_nil_of_pathIn_le d ha (hp.append (isPath_revPath hq))
    (pathIn_append hs (pathIn_revPath (pathIn_cons ⟨ha, le_refl d⟩ (pathIn_cons ⟨hb, le_refl d⟩ (pathIn_nil _)))))

end FiniteChains.Comb
