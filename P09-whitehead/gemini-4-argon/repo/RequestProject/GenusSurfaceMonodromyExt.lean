module

public import RequestProject.GenusSurfaceMonodromy
public import RequestProject.OrderCocycleComparisonAction

@[expose] public section

/-! Agreement on the genuine genus markings determines all surface monodromy. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
universe v
variable (q : ℕ) [NeZero q] {G : Type v} [Group G]
  (c d : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)


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
  change c.val a b * (s b).val * (d.val a b)⁻¹ = (s a).val at h
  exact (mul_inv_eq_iff_eq_mul).mp h
