module

public import RequestProject.SurfaceRegular

@[expose] public section

/-!
# The links of the vertices of the surface are connected

The local conditions verified in `RequestProject/SurfaceRegular.lean` make every vertex link of
the subdivision a disjoint union of cycles.  A polygon with identified sides is a closed surface
exactly when each of these links is a *single* cycle, i.e. when the corners of the polygon lying
over one vertex of the surface are glued to one another in a single cycle.

* `FiniteChains.Davis.CornerAdj` — two positions of the boundary are corners at the same vertex
  of the surface which share a side of the polygon;
* `FiniteChains.Davis.CornersConnected` — the corners over each vertex form a single cycle;
* `FiniteChains.Davis.linkConnected_SCell` — **under this hypothesis every vertex link of the
  subdivision is connected**;
* `FiniteChains.Davis.closedSurfacePoset_SCell` — hence the polygon with identified sides is a
  closed surface, in the combinatorial sense of `FiniteChains.ASC.ClosedSurfacePoset`.

The proof is the expected walk.  Around the centre one goes from one radius to the next through
the triangle of the fan between them; around a collar vertex one goes once around the ten cells
through it; around a vertex of the identified boundary one first walks, inside one corner of the
polygon, from the outgoing side to the incoming side through the two triangles and the two
diagonals of that corner, and then passes to the next corner through the side which glues them.
-/

namespace FiniteChains
namespace Davis

open Cell ASC Relation

universe u

section Link

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}
variable (hc : Compat vc ec)

/-! ### Elementary steps of a link -/

/-! ### The link of the centre -/

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt]

variable (r : Fin M)

theorem ctr_lt_rad : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-! ### The link of a collar vertex -/

/-! ### The cells at a corner of the polygon -/

section

variable {w : κ} {i : Fin M} (hi : vc i = w)
include hi

end

/-! ### Going around one corner of the polygon -/

variable {w : κ}

section

variable {i : Fin M} (hi : vc i = w)
include hi

end

/-! ### Passing from one corner to the next -/

/-- **Two corners of the polygon at the same vertex sharing a side**: the positions `i` and `j`
carry the same vertex, and one of the two sides through `i` is identified with one of the two
sides through `j`. -/
def CornerAdj (vc : Fin M → κ) (ec : Fin M → ι) (i j : Fin M) :=
  vc i = vc j ∧ (ec i = ec j ∨ ec i = ec (fpred j) ∨ ec (fpred i) = ec j ∨
    ec (fpred i) = ec (fpred j))

variable {i j : Fin M}

/-- **The corners of the polygon over one vertex of the surface form a single cycle.** -/
def CornersConnected (vc : Fin M → κ) (ec : Fin M → ι) :=
  ∀ i j : Fin M, vc i = vc j → ReflTransGen (CornerAdj vc ec) i j

section

variable {w : κ} {i j : Fin M} (hi : vc i = w)
include hi

end

/-! ### The closed surface -/

variable (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec)
include hcorners

end Link

end Davis
end FiniteChains
