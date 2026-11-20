module

public import RequestProject.OrderNerveAffineCoordinates
public import Mathlib.Order.WellFounded

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

variable {P : Type} [PartialOrder P]

/-- At a simplex point with positive barycentric coordinates, a vertex indicator
has positive value precisely on the vertices of that simplex. -/
theorem orderNerveAffineSimplex_indicator_pos_iff
    {n : SimplexCategory} (s : (nerve P).obj _)
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (p : P) :
    0 < orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z ↔
      p ∈ Set.range s.obj := by
  classical
  constructor
  · intro h
    by_contra hp
    simp_all [orderNerveAffineSimplex, (fun i hi => hp _)]
  · rintro ⟨i, rfl⟩
    change 0 < ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0)
    have hsum := Finset.single_le_sum
      (f := fun j => z.down.weights j * (if s.obj j = s.obj i then 1 else 0))
      (fun j _ => mul_nonneg (le_of_lt (hz j)) (by split_ifs <;> norm_num))
      (Finset.mem_univ i)
    grind

/-- Two actual simplex interiors meeting in the realization have the same vertex set. -/
theorem orderNerveRealizationSimplex_interior_range_eq
    {n m : SimplexCategory} (s : (nerve P).obj _)
    (t : (nerve P).obj _)
    (z : SimplexCategory.toTop.obj n) (w : SimplexCategory.toTop.obj m)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s z = orderNerveRealizationSimplex P t w) :
    Set.range s.obj = Set.range t.obj := by
  ext p
  let v : P → ℝ := fun q => if q = p then 1 else 0
  have hf := congrArg (orderNerveAffineRealization v) h
  have hc := congrArg (fun k => k z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (fun k => k w) (orderNerveAffineRealization_simplex v t)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P t w) =
    orderNerveAffineSimplex v t w at hd
  rw [← orderNerveAffineSimplex_indicator_pos_iff s z hz p,
    ← orderNerveAffineSimplex_indicator_pos_iff t w hw p] <;> grind

/-- Nondegenerate simplices in the same dimension with meeting interiors are equal. -/
theorem orderNerveRealization_nonDegenerate_interior_eq
    {n : ℕ} (s t : (nerve P).nonDegenerate n)
    (z w : SimplexCategory.toTop.obj _)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    s = t := by
  have he := (((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property).range_inj ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property)).mp (orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h)
  ext <;> simp_all

/-- Nondegenerate simplex interiors in different dimensions cannot meet. -/
theorem orderNerveRealization_nonDegenerate_interior_dimension_eq {n m : ℕ} (s : (nerve P).nonDegenerate n)
    (t : (nerve P).nonDegenerate m)
    (z : SimplexCategory.toTop.obj _)
    (w : SimplexCategory.toTop.obj _)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    n = m := by
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property)).trans
    ((Set.equivOfEq (orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h)).trans (Equiv.ofInjective t.val.obj ((PartialOrder.mem_nerve_nonDegenerate_iff_injective t.val).mp t.property)).symm))
  simp_all

end FiniteChains.Comb
