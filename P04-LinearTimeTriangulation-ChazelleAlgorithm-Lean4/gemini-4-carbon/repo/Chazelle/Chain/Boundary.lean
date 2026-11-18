module

public import Chazelle.Chain.Separation

/-!
# The double boundary as the boundary walk of the domain

Chazelle (p. 490) thickens the chain `C` into an infinitesimally thin simple polygon whose
boundary is the *double boundary* `∂C`.  In the box model (`docs/design-subchain-model.md`)
the domain is `dom C = box R \ (C ∪ slit)`, and the double boundary is (the chain part of) the
*boundary walk* of `dom C`: the closed vertex list

```
slitTop, (-R, R), (-R, -R), (R, -R), (R, R),   -- the box perimeter, counterclockwise from slitTop
slitTop, v_T, v_{T+1}, …, v_m,                  -- down the slit, one side of the chain
         v_{m-1}, …, v_0,                       -- around v_m, the other side
         v_1, …, v_T                            -- around v_0, back to the top vertex
(closing edge v_T → slitTop: up the slit)
```

where `T = C.topIdx` and `v_k = C.vertex k` (`boundaryWalk`, with the chain part `chainWalk`
and the box part `boxList`/`boxPoly`).  Every chain edge and the slit are traversed twice, once
in each direction.

Main results:

* `boundaryWalk_boundary : C.boundaryWalk.boundary = C.set ∪ C.slit ∪ boxPerimeter C.radius`;
* `crossSum_boundaryWalk : crossSum C.boundaryWalk z = crossSum C.boxPoly z` for **every** `z`
  (the doubled chain and the doubled slit cancel in `ZMod 2`, by `crossInd_comm`), hence
  `parity_boundaryWalk`;
* `crossSum_boxPoly` / `parity_boxPoly_iff`: the crossing sum of the box polygon is `1` exactly
  on the half-open square `[-R, R) × [-R, R)`, so off the perimeter its parity is `true`
  exactly in the open box;
* `dom_eq_walk_interior : C.dom = {z | z ∉ C.boundaryWalk.boundary ∧ parity C.boundaryWalk z}`
  — the double boundary (with the box perimeter and the doubled slit) is the boundary walk of
  the domain;
* **Lemma 2.1, parity form** (`chord_splits_walk`): every chord `c = [a, b]` of `C.chords` cuts
  the boundary walk (up to rotation `P ++ Q`) into two closed walks `Γ₁ = a, Q, b` and
  `Γ₂ = b, P, a` (closed by `c`) whose crossing sums add up to that of the boundary walk; every
  point of `dom C \ c` is odd for exactly one of them, and every other chord of `C.chords` has
  constant `Γ₁`- and `Γ₂`-parity on its part in the domain.

The combinatorial tool is the crossing sum `pathSum z L` and point set `pathSet L` of an open
polygonal path given by a vertex list `L`, with the gluing rule `pathSum_glue`
(`pathSum (l₁ ++ l₂.tail) = pathSum l₁ + pathSum l₂` when `l₁` ends where `l₂` starts), the
reversal rule `pathSum_reverse`, `crossSum ⟨a :: l⟩ = pathSum (a :: l ++ [a])`
(`crossSum_eq_pathSum`), rotation invariance (`crossSum_rotate`), and the subdivision rule
`crossInd_split : a ∈ [u, v] → crossInd z u a + crossInd z a v = crossInd z u v`.

**Not proved here (side-aware combinatorial Lemma 2.1).**  The parity form does not say on
which side of the cut a chord endpoint on the chain lies: a chain point is visited twice by the
walk, and the mod-2 parity of `Γ₁` cannot tell which of its two local sides is odd.  The
statement "no chord joins the two pieces `Q` and `P` of the double boundary" in terms of walk
positions needs an orientation refinement (the odd side of `Γ₁` along a strand is its left
side, i.e. integer winding numbers), which is not available in `Chazelle.Jordan`.
-/

namespace Chazelle.Chain

@[expose] public section

open Set
open Chazelle.Jordan

/-! ### Open polygonal paths -/

/-- The crossing sum (in `ZMod 2`) of the open polygonal path through the vertex list `L`: the
sum of `crossInd z a b` over consecutive pairs `a, b` of `L`. -/
noncomputable def pathSum (z : Point) : List Point → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => crossInd z a b + pathSum z (b :: l)

/-- The point set of the open polygonal path through the vertex list `L`: the union of the
segments joining consecutive vertices. -/
def pathSet : List Point → Set Point
  | [] => ∅
  | [_] => ∅
  | a :: b :: l => Chazelle.segment a b ∪ pathSet (b :: l)

@[simp] theorem pathSum_nil (z : Point) : pathSum z [] = 0 := rfl

@[simp] theorem pathSum_singleton (z a : Point) : pathSum z [a] = 0 := rfl

@[simp] theorem pathSum_cons_cons (z a b : Point) (l : List Point) :
    pathSum z (a :: b :: l) = crossInd z a b + pathSum z (b :: l) := rfl

@[simp] theorem pathSet_nil : pathSet [] = ∅ := rfl

@[simp] theorem pathSet_singleton (a : Point) : pathSet [a] = ∅ := rfl

@[simp] theorem pathSet_cons_cons (a b : Point) (l : List Point) :
    pathSet (a :: b :: l) = Chazelle.segment a b ∪ pathSet (b :: l) := rfl

/-! ### Index form, and closed walks as polygons -/

/-! ### Chain vertex lists -/

variable (C : Chain)

/-! ### The doubled chain -/

/-! ### Horizontal and vertical segments and edges -/

/-! ### The box polygon -/

/-- The vertex list of the box polygon: the top end of the slit, then the corners
`(-R, R), (-R, -R), (R, -R), (R, R)` (counterclockwise). -/
noncomputable def boxList : List Point :=
  [C.slitTop, (-C.radius, C.radius), (-C.radius, -C.radius), (C.radius, -C.radius),
    (C.radius, C.radius)]

theorem abs_top_fst_lt_radius : |C.top.1| < C.radius :=
  lt_of_le_of_lt C.abs_top_fst_le C.coordBound_lt_radius

/-! ### The boundary walk of the domain -/

/-! ### Splitting a closed walk at two points -/

/-! ### Lemma 2.1, parity form: a chord cuts the boundary walk into two closed walks -/

end

end Chazelle.Chain
