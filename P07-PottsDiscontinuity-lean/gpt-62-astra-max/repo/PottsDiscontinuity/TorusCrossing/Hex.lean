module

public import PottsDiscontinuity.TorusCrossing.SelfDual

/-!
# Hex-type existence: no vertical primal crossing forces a horizontal dual crossing

The cut edges of the component of the bottom row, which contains no top cell, form a dual
subgraph in which every odd cell strictly between the side columns has even degree, while the
total degree over the left column is odd.  The handshake lemma then produces a dual path from
the left column to the right column.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

section
variable (j : ℤ)
include j

/-- The primal cell of row `j` among the two leftmost columns. -/
def wcell : Cell := if IsPrimal (R.x0, j) then (R.x0, j) else (R.x0 + 1, j)

theorem wcell_primal : IsPrimal (R.wcell j) := by
  grind [wcell, IsPrimal]

theorem wcell_row : (R.wcell j).2 = j := by
  grind [wcell]

theorem wcell_col : (R.wcell j).1 = R.x0 ∨ (R.wcell j).1 = R.x0 + 1 := by
  grind [wcell]

end

theorem primalEnds_leftcol (b : ℤ) : primalEnds (R.x0 + 1, b) = (R.wcell b, R.wcell (b - 1)) := by
  unfold wcell primalEnds
  simp only [IsPrimal]
  grind


/-- Odd cells of the left column. -/
noncomputable def leftFaces : Finset R.dcells := Finset.univ.filter (fun z => z.1.1 = R.x0)

/-- Odd cells of the right column. -/
noncomputable def rightFaces : Finset R.dcells :=
  Finset.univ.filter (fun z => z.1.1 = R.x0 + R.w)

theorem leftcol_filter (m : Cell) (hm : m ∈ R.inner) :
    (R.dcells.filter (fun c => c.1 = R.x0 ∧ m ∈ corners c)).card =
      if m.1 = R.x0 + 1 then 1 else 0 := by
  have hmi := mem_inner.1 hm
  by_cases h1 : m.1 = R.x0 + 1
  · rw [ite_eq_left h1, Finset.card_eq_one]
    by_cases hp : IsPrimal (R.x0, m.2)
    · refine ⟨(R.x0, m.2 - 1), ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff]
      grind [IsPrimal]
    · refine ⟨(R.x0, m.2), ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff]
      grind [IsPrimal]
  · rw [ite_eq_right h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    grind [corners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]

/-- Sum over the left column of the dual degrees = number of edges of the first column. -/
theorem leftSum_eq (E : Finset Cell) (hE : E ⊆ R.inner) :
    ∑ z ∈ R.leftFaces, (E.filter (fun m => m ∈ corners z.1)).card =
      (E.filter (fun m => m.1 = R.x0 + 1)).card := by
  unfold leftFaces
  rw [Finset.sum_filter, (fun g => Finset.sum_coe_sort R.dcells (fun c => if c.1 = R.x0 then g c else 0)) (fun c => (E.filter (fun m => m ∈ corners c)).card)]
  calc _
      = ∑ c ∈ R.dcells, ∑ m ∈ E, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.card_filter]
        split_ifs with h
        · grind
        · simp_all
    _ = ∑ m ∈ E, ∑ c ∈ R.dcells, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ E, (if m.1 = R.x0 + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← R.leftcol_filter m (hE hm), Finset.card_filter]
    _ = _ := by simp


variable (hh : 0 < R.h) (hw : 0 < R.w) (X : Cell → Prop) (C : FK.Configuration R.pG)

theorem isCut_leftcol (b : ℤ) :
    IsCut X (R.x0 + 1, b) ↔ ¬ (X (R.wcell b) ↔ X (R.wcell (b - 1))) := by
  simp [R.primalEnds_leftcol, IsCut]

/-- Parity of the number of cut edges in the first column of medial vertices. -/
theorem cnt_parity (k : ℕ) :
    Even ((Finset.Icc (R.y0 + 1) (R.y0 + k)).filter (fun b => IsCut X (R.x0 + 1, b))).card ↔
      (X (R.wcell R.y0) ↔ X (R.wcell (R.y0 + k))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hset : Finset.Icc (R.y0 + 1) (R.y0 + ↑(k + 1)) =
        insert (R.y0 + (k + 1)) (Finset.Icc (R.y0 + 1) (R.y0 + k)) := by
      grind
    rw [hset, Finset.filter_insert]
    grind [R.isCut_leftcol]


include hw in
theorem cutSet_col_card :
    ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card =
      ((Finset.Icc (R.y0 + 1) (R.y0 + R.h)).filter
        (fun b => IsCut X (R.x0 + 1, b))).card := by
  have : (R.cutSet X).filter (fun m => m.1 = R.x0 + 1) =
      ((Finset.Icc (R.y0 + 1) (R.y0 + R.h)).filter
        (fun b => IsCut X (R.x0 + 1, b))).image (fun b => (R.x0 + 1, b)) := by
    grind [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, mem_cutSet, mem_inner]
  rw [this, Finset.card_image_of_injective]
  intro a b hab
  grind

include hw in
/-- The first column of cut edges has odd cardinality when the bottom corner is inside `X`
and the top corner is outside. -/
theorem cutSet_col_odd (hbot : X (R.wcell R.y0))
    (htop : ¬ X (R.wcell (R.y0 + R.h))) :
    Odd ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card := by
  rw [R.cutSet_col_card hw X, ← Nat.not_even_iff_odd]
  intro hev
  have := (R.cnt_parity X R.h).1 hev
  grind


/-- Reachability in the dual graph of `E` gives actual open connectivity for a larger set. -/
theorem dualOf_actualConnected {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    FK.ActualConnected (cfgOf R.dData D) x y := by
  exact h.mono (by
    intro a b hab
    rw [dualOf, endGraph_adj] at hab
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact ⟨m, hED hm, Or.inl h⟩
    · exact ⟨m, hED hm, Or.inr h⟩)

include C in
/-- Cells connected to the bottom row by open paths. -/
def botComp (c : Cell) : Prop :=
  ∃ hc, ∃ b, b.1.2 = R.y0 ∧ FK.ActualConnected C b ⟨c, hc⟩

theorem botComp_of_adj {x y : R.pcells}
    (hxy : (FK.openGraph C).Adj x y) : R.botComp C x.1 ↔ R.botComp C y.1 := by
  constructor
  · rintro ⟨_, b, hb, h⟩
    exact ⟨y.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy)⟩
  · rintro ⟨_, b, hb, h⟩
    exact ⟨x.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy.symm)⟩

include hh hw in
theorem hex
    (hno : ¬ ∃ u v, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧
      FK.ActualConnected C u v) :
    ∃ z z', z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧
      FK.ActualConnected (R.dualEquiv C) z z' := by
  set A := openMedials R.pData C with hA
  set X := R.botComp C with hX
  set E := R.cutSet X with hE
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hEc : E ⊆ R.inner \ A := by
    intro m hm
    rw [Finset.mem_sdiff]
    refine ⟨hEsub hm, fun hmA => ?_⟩
    have hmem := R.pData.mem m ((openMedials_subset R.pData C) hmA)
    apply ((R.mem_cutSet.1 hm).2)
    have hadj : (FK.openGraph C).Adj ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩ := by
      rw [openGraph_adj_iff R.pData]
      exact ⟨m, hmA, Or.inl rfl⟩
    exact propext (R.botComp_of_adj C hadj)
  -- statuses of the bottom and top rows
  have hbotX : ∀ c : Cell, ∀ hc : c ∈ R.pcells, c.2 = R.y0 → X c := fun c hc hy =>
    ⟨hc, ⟨c, hc⟩, hy, SimpleGraph.Reachable.refl _⟩
  have htopX : ∀ c : Cell, c ∈ R.pcells → c.2 = R.y0 + R.h → ¬ X c := by
    rintro c hc hy ⟨_, b, hb, hconn⟩
    grind
  have hXbot := hbotX _ (by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal R.y0
    have h2 := R.wcell_row R.y0
    have h3 := R.wcell_col R.y0
    grind) (R.wcell_row _)
  have hXtop := htopX _ (by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal (R.y0 + R.h)
    grind [R.wcell_row, R.wcell_col]) (R.wcell_row _)
  -- handshake
  obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hEsub R.leftFaces R.rightFaces (by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp_all [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and])
    (by
      intro z hz1 hz2
      simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      have hzc := mem_cells.1 (mem_dcells.1 z.2).1
      have hx1 : R.x0 < z.1.1 := by omega
      have hx2 : z.1.1 < R.x0 + R.w := by omega
      obtain ⟨hW, hE'⟩ := R.outer_pcells z hx1 hx2
      rw [cutSet_filter_corners]
      refine cut_deg_even R hh X z.1 (mem_dcells.1 z.2).2 hx1 hx2 hzc.2.2.1 hzc.2.2.2 ?_ ?_
      · grind
      · grind)
    (by
      rw [R.leftSum_eq E hEsub]
      exact R.cutSet_col_odd hw X hXbot hXtop)
  exact ⟨b, t, (by simp_all [leftFaces, Finset.mem_filter, Finset.mem_univ, true_and]), (by simp_all [rightFaces, Finset.mem_filter, Finset.mem_univ, true_and]), R.dualOf_actualConnected hEc Finset.sdiff_subset hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
