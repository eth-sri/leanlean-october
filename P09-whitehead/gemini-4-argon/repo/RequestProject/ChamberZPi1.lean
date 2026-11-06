module

public import RequestProject.ChamberZPoset
public import RequestProject.OrderComplexGluing

@[expose] public section

/-!
# When a copy of the base splits off the fundamental group of `Z`

The attaching map `att` of `RequestProject/ChamberZPoset.lean` is defined on the **nonempty**
simplices only: no extension over the cone point of a chamber is assumed, because the cone point
of a modified chamber is exactly what is removed.

If, in addition, the attaching map does extend monotonically over the cone — that is, if there
is a monotone `attExt : Finset V →o X` agreeing with `att` on nonempty simplices — then the
whole of `Z` retracts monotonically onto the base poset, and every copy of the base is a
**split** subgroup of `π₁(Z)`:

* `FiniteChains.Davis.zRetrAll` — the retraction `Z → X` under that hypothesis;
* `FiniteChains.Davis.pi1Map_zNew_injective` — `π₁(X) → π₁(Z)` is then injective for every copy
  of the base.

The hypothesis is a genuine restriction: it says that the attaching map of the block dies in the
base.  Without it the injectivity of a copy of the base is **not** proved here; it is the
free-product argument along the simply connected attaching intersections `J_w`, and it remains
open (see `THEOREM-A-OBLIGATIONS.md`).
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  (attExt : Finset V →o X)
  (hext : ∀ (σ : Finset V) (h : σ.Nonempty ∧ IsSimplex A σ), attExt σ = att ⟨σ, h⟩)



/-- The inclusion of a copy of the base is monotone. -/
theorem zNew_monotone (w : {w : CayGroup A // M w}) :
    Monotone (zNew (A := A) (X := X) (M := M) (att := att) w) :=
  fun _ _ h => ⟨rfl, h⟩
