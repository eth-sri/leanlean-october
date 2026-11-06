import RequestProject.OrderNerveAffineCoordinates
import Mathlib.Order.WellFounded
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- At a simplex point with positive barycentric coordinates, a vertex indicator
has positive value precisely on the vertices of that simplex. -/
theorem orderNerveAffineSimplex_indicator_pos_iff {P} [PartialOrder P]
    {n} s
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (p : P) :
    0 < orderNerveAffineSimplex (if · = p then 1 else 0) s z ↔
      p ∈ Set.range s.obj := by
  classical
  constructor
  · intro h
    by_contra hp
    have hn : ∀ i, s.obj i ≠ p := by simp_all
    simp [orderNerveAffineSimplex, hn] at h
  · rintro ⟨i, rfl⟩
    change 0 < ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0)
    have hsum := Finset.single_le_sum
      (f := fun j => z.down.weights j * (if s.obj j = s.obj i then 1 else 0))
      (by aesop)
      (Finset.mem_univ i)
    grind

/-- Two actual simplex interiors meeting in the realization have the same vertex set. -/
theorem orderNerveRealizationSimplex_interior_range_eq {P} [PartialOrder P]
    {n m} s
    t
    (z : SimplexCategory.toTop.obj n) (w : SimplexCategory.toTop.obj m)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s z = orderNerveRealizationSimplex P t w) :
    Set.range s.obj = Set.range t.obj := by
  ext p
  let v : P → ℝ := fun q => if q = p then 1 else 0
  have hc := congrArg (· z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (· w) (orderNerveAffineRealization_simplex v t)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P t w) =
    orderNerveAffineSimplex v t w at hd
  rw [← orderNerveAffineSimplex_indicator_pos_iff s z hz p,
    ← orderNerveAffineSimplex_indicator_pos_iff t w hw p]
  grind

/-- Nondegenerate simplices in the same dimension with meeting interiors are equal. -/
theorem orderNerveRealization_nonDegenerate_interior_eq {P} [PartialOrder P]
    {n} (s t : (nerve P).nonDegenerate n)
    z w
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    s = t := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property
  have he := (hs.range_inj ht).mp hrange
  apply Subtype.ext
  exact CategoryTheory.Functor.ext (congrFun he)

/-- Nondegenerate simplex interiors in different dimensions cannot meet. -/
theorem orderNerveRealization_nonDegenerate_interior_dimension_eq {P}
    [PartialOrder P] {n m} (s : (nerve P).nonDegenerate n)
    (t : (nerve P).nonDegenerate m)
    z
    w
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    n = m := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_injective t.val).mp t.property
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj hs).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective t.val.obj ht).symm))
  simp_all
