import RequestProject.ConeAdjPoset


namespace FiniteChains.Comb
universe u

/-- A null loop obtained by closing a path with a reverse path proves the two paths homotopic. -/
theorem htpy_of_append_rev_null {a b}
    {p q} (hp : IsPathX X p a b)
    (hq : IsPathX X q a b) (h : Htpy X a a (p ++ revPath q) []) :
    Htpy X a b p q := by
  have hc := (htpy_revPath_append hq).congr_append hp (show IsPathX X [] b b from rfl)
  have hh := h.congr_append (show IsPathX X [] a a from rfl) hq
  have hc' : Htpy X a b ((p ++ revPath q) ++ q) p := by
    simp_all
  have hh' : Htpy X a b ((p ++ revPath q) ++ q) q := by
    simp_all
  exact hc'.symm.trans hh'

/-- Every actual path below a fixed apex is homotopic to the two-edge path through that apex. -/
theorem htpy_path_through_upper_bound {P} [Preorder P]
    d {a b : P} (ha : a ≤ d) (hb : b ≤ d)
    {p}
    (hp : IsPathX (orderCx P) p a b)
    (hs : PathIn (· ≤ d) p) :
    Htpy (orderCx P) a b p [ordPos ha, ordNeg hb] := by
  have hq : IsPathX (orderCx P) [ordPos ha, ordNeg hb] a b :=
    by tauto
  have hqs : PathIn (· ≤ d) [ordPos ha, ordNeg hb] :=
    pathIn_cons ⟨ha, le_refl d⟩ (pathIn_cons ⟨hb, le_refl d⟩ (pathIn_nil _))
  apply htpy_of_append_rev_null hp hq
  exact htpy_nil_of_pathIn_le d ha (hp.append (isPath_revPath hq))
    (pathIn_append hs (pathIn_revPath hqs))
