module

public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# The quarter-turn of an odd square exchanges primal and dual

For a square board of odd side the rotation by a quarter turn about its centre maps the odd cells
onto the primal cells and carries the dual graph isomorphically onto the primal graph, sending
the left and right columns to the top and bottom rows.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

section
variable (c : Cell) (m : Cell)

include c in
/-- Quarter turn of cells. -/
def rot : Cell := (R.x0 + (c.2 - R.y0), R.y0 + R.w - (c.1 - R.x0))

include c in
/-- Inverse quarter turn of cells. -/
def rotInv : Cell := (R.x0 + R.w - (c.2 - R.y0), R.y0 + (c.1 - R.x0))

include m in
/-- Quarter turn of medial vertices. -/
def rotMed : Cell := (R.x0 + (m.2 - R.y0), R.y0 + R.w + 1 - (m.1 - R.x0))

include m in
/-- Inverse quarter turn of medial vertices. -/
def rotMedInv : Cell := (R.x0 + R.w + 1 - (m.2 - R.y0), R.y0 + (m.1 - R.x0))

theorem rot_rotInv : R.rot (R.rotInv c) = c := by
  grind [rot, rotInv]

theorem rotInv_rot : R.rotInv (R.rot c) = c := by
  grind [rot, rotInv]

theorem rotMed_rotMedInv : R.rotMed (R.rotMedInv m) = m := by
  grind [rotMed, rotMedInv]

end

theorem rot_injective : Function.Injective R.rot := fun a b h => by
  rw [← R.rotInv_rot a, ← R.rotInv_rot b, h]

variable (hsq : R.w = R.h) (hodd : R.w % 2 = 1) {c d : Cell} {m : Cell} (hm : m ∈ R.inner)

include hodd in
/-- Local identity: the quarter turn carries the ends of the dual edge at `m` to the ends of the
primal edge at the turned vertex. -/
theorem rot_dualEnds (m : Cell) :
    (R.rot (dualEnds m).1 = (primalEnds (R.rotMed m)).1 ∧
        R.rot (dualEnds m).2 = (primalEnds (R.rotMed m)).2) ∨
      (R.rot (dualEnds m).1 = (primalEnds (R.rotMed m)).2 ∧
        R.rot (dualEnds m).2 = (primalEnds (R.rotMed m)).1) := by
  unfold rot rotMed dualEnds primalEnds
  grind

include hsq hm in
theorem rotMed_mem_inner :
    R.rotMed m ∈ R.inner := by
  grind [mem_inner, rotMed]

include hsq hm in
theorem rotMedInv_mem_inner :
    R.rotMedInv m ∈ R.inner := by
  grind [mem_inner, rotMedInv]

include hsq hodd in
theorem rot_mem_pcells {c : Cell} (hc : c ∈ R.dcells) :
    R.rot c ∈ R.pcells := by
  grind [mem_dcells, mem_cells, mem_pcells, rot, IsPrimal]

include hsq hodd in
theorem rotInv_mem_dcells {c : Cell} (hc : c ∈ R.pcells) :
    R.rotInv c ∈ R.dcells := by
  grind [mem_pcells, mem_cells, mem_dcells, rotInv, IsPrimal]

include hsq hodd in
/-- The quarter-turn bijection from odd cells to primal cells. -/
def rotEquiv : R.dcells ≃ R.pcells where
  toFun z := ⟨R.rot z.1, R.rot_mem_pcells hsq hodd z.2⟩
  invFun c := ⟨R.rotInv c.1, R.rotInv_mem_dcells hsq hodd c.2⟩
  left_inv z := Subtype.ext (R.rotInv_rot z.1)
  right_inv c := Subtype.ext (R.rot_rotInv c.1)

/-- Dual edge between two cells. -/
def DE (c d : Cell) : Prop := ∃ m ∈ R.inner, dualEnds m = (c, d)

/-- Primal edge between two cells. -/
def PE (c d : Cell) : Prop := ∃ m ∈ R.inner, primalEnds m = (c, d)

include hsq hodd in
theorem DE_push (h : R.DE c d) :
    R.PE (R.rot c) (R.rot d) ∨ R.PE (R.rot d) (R.rot c) := by
  obtain ⟨m, hm, hend⟩ := h
  have := R.rot_dualEnds hodd m
  rw [hend] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨R.rotMed m, R.rotMed_mem_inner hsq hm, Prod.ext h1.symm h2.symm⟩
  · right
    exact ⟨R.rotMed m, R.rotMed_mem_inner hsq hm, Prod.ext h2.symm h1.symm⟩

include hsq hodd in
theorem PE_pull
    (h : R.PE (R.rot c) (R.rot d)) : R.DE c d ∨ R.DE d c := by
  obtain ⟨m', hm', hend⟩ := h
  have := R.rot_dualEnds hodd (R.rotMedInv m')
  rw [R.rotMed_rotMedInv, hend] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨R.rotMedInv m', R.rotMedInv_mem_inner hsq hm',
      Prod.ext (R.rot_injective h1) (R.rot_injective h2)⟩
  · right
    exact ⟨R.rotMedInv m', R.rotMedInv_mem_inner hsq hm',
      Prod.ext (R.rot_injective h1) (R.rot_injective h2)⟩

include hsq hodd in
/-- The quarter turn carries the dual graph isomorphically onto the primal graph. -/
def rotIso : R.dG ≃g R.pG where
  toEquiv := R.rotEquiv hsq hodd
  map_rel_iff' := by
    intro a b
    show R.pG.Adj (R.rotEquiv hsq hodd a) (R.rotEquiv hsq hodd b) ↔ R.dG.Adj a b
    rw [endGraph_adj, endGraph_adj]
    have hne : R.rotEquiv hsq hodd a ≠ R.rotEquiv hsq hodd b ↔ a ≠ b :=
      (R.rotEquiv hsq hodd).injective.ne_iff
    refine and_congr hne ?_
    change (R.PE (R.rot a.1) (R.rot b.1) ∨ R.PE (R.rot b.1) (R.rot a.1)) ↔
      (R.DE a.1 b.1 ∨ R.DE b.1 a.1)
    constructor
    · rintro (h | h)
      · exact R.PE_pull hsq hodd h
      · exact (R.PE_pull hsq hodd h).symm
    · rintro (h | h)
      · exact R.DE_push hsq hodd h
      · exact (R.DE_push hsq hodd h).symm

end Rect

end PottsDiscontinuity.TorusCrossing
