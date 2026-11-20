module

public import RequestProject.SquareComplexMonodromy
public import RequestProject.SquareComplexUniversalCover

@[expose] public section

/-!
# Existence of the universal cover of a square complex

`RequestProject/SquareComplexUniversalCover.lean` proves that a connected, simply connected
covering of a square complex is unique up to isomorphism over the base.  This file constructs
one, so that the universal cover exists for every square complex:

* `FiniteChains.SquareComplex.UnivVx` — the vertices are pairs (a vertex `y`, a homotopy class
  of walks from the base point to `y`);
* `FiniteChains.SquareComplex.univCover` — the square complex structure: an edge joins two
  classes when one is obtained from the other by appending an edge, and a square is a square of
  the base whose four corners are joined in this way;
* `FiniteChains.SquareComplex.isCovering_univProj` — the projection to the base is a covering;
* `FiniteChains.SquareComplex.univCover_walkConnected`,
  `FiniteChains.SquareComplex.univCover_simplyConnectedW` — it is connected and simply connected;
* `FiniteChains.SquareComplex.exists_universal_cover` — hence every square complex has a
  connected, simply connected covering, which by
  `FiniteChains.SquareComplex.exists_iso_of_universal` is unique over the base.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u}

/-- The vertex set of the universal cover: a vertex of the base together with a homotopy class,
through walks, of walks from the base point to it. -/
def UnivVx (S : SquareComplex Vx) (b₀ : Vx) : Type u := Σ y : Vx, Quotient (walkSetoid S b₀ y)

variable {S : SquareComplex Vx} {b₀ : Vx}

/-- Appending an edge to a homotopy class of walks. -/
def extendCls {y z : Vx} (h : S.adj y z) (c : Quotient (walkSetoid S b₀ y)) :
    Quotient (walkSetoid S b₀ z) :=
  Quotient.lift
    (fun w : (toSimpleGraph S).Walk b₀ y => Quotient.mk (walkSetoid S b₀ z)
      (w.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)))
    (fun _ _ hpq => Quotient.sound (walkHtpy_append_right hpq _)) c

@[simp] theorem extendCls_mk {y z : Vx} (h : S.adj y z) (w : (toSimpleGraph S).Walk b₀ y) :
    extendCls (b₀ := b₀) h (Quotient.mk (walkSetoid S b₀ y) w)
      = Quotient.mk (walkSetoid S b₀ z)
          (w.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)) := rfl

/-- The projection of the universal cover to the base. -/
def univProj (S : SquareComplex Vx) (b₀ : Vx) : UnivVx S b₀ → Vx := Sigma.fst

@[simp] theorem univProj_apply (P : UnivVx S b₀) : univProj S b₀ P = P.1 := rfl

/-! ### The universal cover is connected and simply connected -/

/-- The base point of the universal cover. -/
def univBase (S : SquareComplex Vx) (b₀ : Vx) : UnivVx S b₀ :=
  ⟨b₀, Quotient.mk (walkSetoid S b₀ b₀) SimpleGraph.Walk.nil⟩

@[simp] theorem univProj_univBase : univProj S b₀ (univBase S b₀) = b₀ := rfl

end SquareComplex

end FiniteChains
