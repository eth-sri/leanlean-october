module

public import RequestProject.OrderNerveAffineCoordinates
public import Mathlib.Order.WellFounded

@[expose] public section


namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- At a simplex point with positive barycentric coordinates, a vertex indicator
has positive value precisely on the vertices of that simplex. -/
theorem orderNerveAffineSimplex_indicator_pos_iff {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (p : P) :
    0 < orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z ↔
      p ∈ Set.range s.obj := by
  classical
  constructor
  · intro h
    by_contra hp
    have hn : ∀ i, s.obj i ≠ p := fun i hi => hp ⟨i, hi⟩
    simp [orderNerveAffineSimplex, hn] at h
  · rintro ⟨i, rfl⟩
    change 0 < ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0)
    have hsum := Finset.single_le_sum
      (f := fun j => z.down.weights j * (if s.obj j = s.obj i then 1 else 0))
      (fun j _ => mul_nonneg (le_of_lt (hz j)) (by split_ifs <;> norm_num))
      (Finset.mem_univ i)
    grind

/-- Two actual simplex interiors meeting in the realization have the same vertex set. -/
theorem orderNerveRealizationSimplex_interior_range_eq {P : Type} [PartialOrder P]
    {n m : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : (nerve P).obj (Opposite.op m))
    (z : SimplexCategory.toTop.obj n) (w : SimplexCategory.toTop.obj m)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s z = orderNerveRealizationSimplex P t w) :
    Set.range s.obj = Set.range t.obj := by
  ext p
  rw [← orderNerveAffineSimplex_indicator_pos_iff s z hz p,
    ← orderNerveAffineSimplex_indicator_pos_iff t w hw p,
    ← orderNerveAffineRealization_simplex, ← orderNerveAffineRealization_simplex, h]

/-- An increasing nondegenerate simplex is determined by its vertex set. -/
theorem orderNerveNondegenerate_eq_of_range {P : Type} [PartialOrder P]
    {n m : ℕ} (s : (nerve P).nonDegenerate n) (t : (nerve P).nonDegenerate m)
    (h : Set.range s.val.obj = Set.range t.val.obj) : ∃ e : n = m, e ▸ s = t := by
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj hs.injective).trans
    ((Set.equivOfEq h).trans (Equiv.ofInjective t.val.obj ht.injective).symm))
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  have e : n = m := by omega
  subst m
  exact ⟨rfl, Subtype.ext (CategoryTheory.Functor.ext (congrFun ((hs.range_inj ht).mp h)))⟩

end FiniteChains.Comb
