module

public import RequestProject.ConeAdjPoset

@[expose] public section

namespace FiniteChains.Comb
universe u

/-- Every actual path below a fixed apex is homotopic to the two-edge path through that apex. -/
theorem htpy_path_through_upper_bound {P : Type u} [Preorder P]
    (d : P) {a b : P} (ha : a ≤ d) (hb : b ≤ d)
    {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b)
    (hs : PathIn (fun x => x ≤ d) p) :
    Htpy (orderCx P) a b p [ordPos ha, ordNeg hb] := by
  have hq : IsPath (orderCx P).src (orderCx P).tgt [ordPos ha, ordNeg hb] a b :=
    ⟨rfl, rfl, rfl⟩
  have hqs : PathIn (fun x => x ≤ d) [ordPos ha, ordNeg hb] :=
    pathIn_cons ⟨ha, le_refl d⟩ (pathIn_cons ⟨hb, le_refl d⟩ (pathIn_nil _))
  apply htpy_of_append_rev_null hp hq
  exact htpy_nil_of_pathIn_le d ha (hp.append (isPath_revPath hq))
    (pathIn_append hs (pathIn_revPath hqs))

end FiniteChains.Comb
