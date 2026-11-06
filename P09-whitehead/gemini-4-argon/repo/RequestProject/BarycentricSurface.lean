module

public import RequestProject.FlagComplex

@[expose] public section

/-!
# The barycentric subdivision of a closed surface is again a closed surface

The block construction of Section 3.3 uses, for `L_q`, the barycentric subdivision of a
triangulation of the closed surface `Σ_q`, and it needs two properties of `L_q`:

* `L_q` is flag (proved in `RequestProject/FlagComplex.lean`);
* every edge of `L_q` lies in exactly two triangles — this is the incidence count behind
  "every square meets exactly two three-cubes, because every edge of `L` meets two
  triangles", the hypothesis of the collapse and of the fundamental-cycle computation
  (`RequestProject/MomentAngle.lean`, `RequestProject/SpineCollapse.lean`).

This file proves the second property: if every face of `K` has at most three vertices and
every edge of `K` lies in exactly two triangles, then the same holds for the barycentric
subdivision of `K`.  The subdivision is the order complex of the poset of nonempty faces,
so its triangles are the flags `v ⊂ e ⊂ t` of `K`, and the proof is the usual case
distinction on the type of an edge of the subdivision:

* an edge `v ⊂ e` extends by the two triangles of `K` containing `e`;
* an edge `v ⊂ t` extends by the two edges of `t` through `v`;
* an edge `e ⊂ t` extends by the two vertices of `e`.

Together with `RequestProject/FlagComplex.lean` this verifies, for the subdivision, both
combinatorial hypotheses that the cube complex `C(L_q)` of the paper requires.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ASC

universe u

variable {V : Type u} [DecidableEq V]

/-- "The predicate `P` has exactly two witnesses." -/
def ExactlyTwo {α : Sort*} (P : α → Prop) : Prop :=
  ∃ x y, x ≠ y ∧ P x ∧ P y ∧ ∀ z, P z → z = x ∨ z = y

/-- Every edge of `K` lies in exactly two triangles: for every edge `e` there are exactly
two vertices outside `e` spanning a triangle with it. -/
def EdgeInTwoTriangles (K : ASC V) : Prop :=
  ∀ e ∈ K.faces, e.card = 2 → ExactlyTwo (fun v => v ∉ e ∧ insert v e ∈ K.faces)


variable {P : Type u} [Preorder P]

theorem isChain_triple {x y z : P} (hxy : x ≤ y ∨ y ≤ x) (hxz : x ≤ z ∨ z ≤ x)
    (hyz : y ≤ z ∨ z ≤ y) : IsChain (· ≤ ·) ({x, y, z} : Set P) := by
  rintro p (rfl | rfl | rfl) q (rfl | rfl | rfl) hpq <;> first
    | exact absurd rfl hpq
    | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm

theorem le_or_le_of_isChain {s : Set P} (hs : IsChain (· ≤ ·) s) {x y : P} (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y ∨ y ≤ x := by
  by_cases hxy : x = y
  · exact Or.inl (le_of_eq hxy)
  · exact hs hx hy hxy
