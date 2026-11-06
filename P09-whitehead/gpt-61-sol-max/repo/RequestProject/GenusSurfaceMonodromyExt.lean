import Mathlib.Tactic

import RequestProject.GenusSurfaceMonodromy
import RequestProject.OrderCocycleComparisonAction

/-! Agreement on the genuine genus markings determines all surface monodromy. -/

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  (c d : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

local instance genusSurfacePi1Group : Group
    (Pi1 (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)) :=
  @Pi1.instGroup (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)

/-- The marked equalities give the actual vertex gauge needed to glue the old
and base cocycles along the surface in the geometric mapping cylinder. -/
theorem genus_cocycle_gauge_of_marked
    (hm : ∀ x : Fin q × Bool,
      c.readPath (gSig q (x.1.val, x.2)) = d.readPath (gSig q (x.1.val, x.2))) :
    ∃ k : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) → G,
      k (gBase q) = 1 ∧ ∀ {a b}, a ≤ b → c.val a b * k b = k a * d.val a b := by
  have hf : ∀ x : Fin q × Bool, (OrdCocycle.product c d).readPath (gSig q (x.1.val, x.2)) •
      (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) = OrdCocycle.comparisonOne := by
    intro x
    rw [OrdCocycle.product_readPath, OrdCocycle.comparisonOne_fixed_iff]
    exact hm x
  obtain ⟨s, hs, hb⟩ := genus_exists_flat_section q
    (OrdCocycle.comparisonOne : OrdCocycle.ComparisonPoint G) (OrdCocycle.product c d) hf
  refine ⟨fun a => (s a).val, congrArg OrdCocycle.ComparisonPoint.val hb, ?_⟩
  intro a b hab
  have h := congrArg OrdCocycle.ComparisonPoint.val (hs hab)
  
  exact (mul_inv_eq_iff_eq_mul).mp h

end FiniteChains.Davis.Genus
