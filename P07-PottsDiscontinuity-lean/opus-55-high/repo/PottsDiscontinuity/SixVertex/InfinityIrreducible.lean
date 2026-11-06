module

public import PottsDiscontinuity.SixVertex.InfinityDescent

/-!
# Irreducibility on independent row states

A connected component has a minimum of the sum of occupied positions. Such a
minimum contains zero and is closed under subtracting two. It is consequently an
even initial segment. Equal particle counts make all component minima identical.
-/

public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

abbrev Reach (x y : IndependentState N n) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < infinityRestriction N n a b) x y

theorem reach_symm {x y : IndependentState N n} (h : Reach x y) : Reach y x :=
  reflTransGen_symm_of_symm (fun a b h => by rwa [infinityRestriction_symm]) h

section
variable (hn : 0 < n) (p : IndependentState N n) (hmin : ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1)
include hn p hmin
theorem minimum_contains_zero  :
    ∀ z : Fin N, z.val = 0 → z ∈ p.1.1 := by
  by_contra hnot
  have h0 : ∀ i ∈ p.1.1, 0 < i.val := by
    grind
  have hne : p.1.1.Nonempty := by grind
  exact (not_lt_of_ge (hmin (unrotateIndependent p) (unrotateIndependent_reachable hn p))) (positionSum_rotateDown_lt p.1.1 hne h0)

theorem minimum_closed_two  :
    ∀ i ∈ p.1.1, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ p.1.1 := by
  intro i hi j hi2 hji2
  by_contra hj
  let k : Fin N := ⟨i.val - 1, by omega⟩
  have hki : nxt k = i := by
    apply Fin.ext
    rw [nxt_val_of_lt k (by grind)]
    grind
  have hkj : prv k = j := by
    apply Fin.ext
    rw [prv_val_of_pos k (by grind)]
    grind
  have hk := fun h => p.2 k h (hki ▸ hi)
  obtain ⟨q, hq, hpq⟩ := infinityRestriction_slide_left_reachable hn p hi hk
    (by grind) hki
  have hlt := positionSum_jump_lt hi hk (show k.val < i.val by grind)
  grind
end

theorem minimum_unique (hn : 0 < n) (p q : IndependentState N n)
    (hp : ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1)
    (hq : ∀ y, Reach q y → positionSum q.1.1 ≤ positionSum y.1.1) : p = q := by
  have hpc := minimum_closed_two hn p hp
  have hqc := minimum_closed_two hn q hq
  have hpe := even_of_closed_two p.2 (minimum_contains_zero hn p hp) hpc
  have hqe := even_of_closed_two q.2 (minimum_contains_zero hn q hq) hqc
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_even_prefix (p.1.2.trans q.1.2.symm) hpe hqe
    (even_prefix_of_closed_two hpe hpc) (even_prefix_of_closed_two hqe hqc)

theorem exists_component_minimum (x : IndependentState N n) :
    ∃ p, Reach x p ∧ ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1 := by
  let s := {p | Reach x p}
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image s (fun p => positionSum p.1.1)
    (Set.toFinite s) ⟨x, Relation.ReflTransGen.refl⟩
  exact ⟨p, hp, fun y hy => hmin y (hp.trans hy)⟩

section
variable (hn : 0 < n) (x y : IndependentState N n)
include hn
/-- Any two independent states communicate through positive entries of the limiting matrix. -/
theorem infinityRestriction_reachable  :
    Relation.ReflTransGen (fun a b : IndependentState N n =>
      0 < infinityRestriction N n a b) x y := by
  obtain ⟨p, hxp, hp⟩ := exists_component_minimum x
  obtain ⟨q, hyq, hq⟩ := exists_component_minimum y
  have he := minimum_unique hn p q hp hq
  simp_all
  exact hxp.trans (reach_symm hyq)

/-- A positive power (with strictly positive exponent) connects every independent pair. -/
theorem infinityRestriction_exists_pow_pos  :
    ∃ k > 0, 0 < (infinityRestriction N n ^ k) x y := by
  obtain ⟨k, hk⟩ := exists_pow_pos_of_reflTransGen infinityRestriction_nonneg
    (infinityRestriction_reachable hn x y)
  by_cases hk0 : k = 0
  · have hxy : x = y := by
      by_contra h
      simp_all
    subst y
    exact ⟨2, by norm_num, infinityRestriction_square_self_pos hn x⟩
  grind
end

/-- The restriction to configurations without consecutive up arrows is irreducible. -/
theorem infinityRestriction_isIrreducible (hn : 0 < n) :
    (infinityRestriction N n).IsIrreducible :=
  (Matrix.isIrreducible_iff_exists_pow_pos infinityRestriction_nonneg).mpr
    (infinityRestriction_exists_pow_pos hn)

end PottsDiscontinuity.SixVertex
