import Mathlib.Tactic
import RequestProject.CmpNerve

import RequestProject.ConeAdjPoset

namespace FiniteChains.Comb

/-- A null loop obtained by closing a path with a reverse path proves the two paths homotopic. -/
theorem htpy_of_append_rev_null {X : Complex2.{u}} {a b : X.V}
    {p q : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a b)
    (hq : IsPath X.src X.tgt q a b) (h : Htpy X a a (p ++ revPath q) []) :
    Htpy X a b p q := FiniteChains.Davis.htpy_of_loop_nil hp hq h

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
