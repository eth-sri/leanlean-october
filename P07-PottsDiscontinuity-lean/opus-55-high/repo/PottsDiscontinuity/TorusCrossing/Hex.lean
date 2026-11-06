module

public import PottsDiscontinuity.TorusCrossing.SelfDual

/-!
# Hex-type existence: no vertical primal crossing forces a horizontal dual crossing

The cut edges of the component of the bottom row, which contains no top cell, form a dual
subgraph in which every odd cell strictly between the side columns has even degree, while the
total degree over the left column is odd.  The handshake lemma then produces a dual path from
the left column to the right column.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

section
variable (j : ℤ)
/-- The primal cell of row `j` among the two leftmost columns. -/
def wcell  : Cell := if IsPrimal (R.x0, j) then (R.x0, j) else (R.x0 + 1, j)

theorem wcell_primal  : IsPrimal (R.wcell j) := by
  unfold wcell
  split_ifs with h
  · omega
  grind [IsPrimal]

theorem wcell_row  : (R.wcell j).2 = j := by
  unfold wcell; grind

theorem wcell_col  : (R.wcell j).1 = R.x0 ∨ (R.wcell j).1 = R.x0 + 1 := by
  grind [wcell]
end

theorem primalEnds_leftcol (b : ℤ) : primalEnds (R.x0 + 1, b) = (R.wcell b, R.wcell (b - 1)) := by
  unfold wcell primalEnds
  simp only [IsPrimal]
  grind


/-- Odd cells of the left column. -/
def leftFaces : Finset R.dcells := Finset.univ.filter (fun z => z.1.1 = R.x0)

/-- Odd cells of the right column. -/
def rightFaces : Finset R.dcells :=
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
    grind [corners]

/-- Sum over the left column of the dual degrees = number of edges of the first column. -/
theorem leftSum_eq (E : Finset Cell) (hE : E ⊆ R.inner) :
    ∑ z ∈ R.leftFaces, (E.filter (fun m => m ∈ corners z.1)).card =
      (E.filter (fun m => m.1 = R.x0 + 1)).card := by
  unfold leftFaces
  rw [Finset.sum_filter]
  have e1 : ∀ g : Cell → ℕ, ∑ z : R.dcells, (if z.1.1 = R.x0 then g z.1 else 0) =
      ∑ c ∈ R.dcells, (if c.1 = R.x0 then g c else 0) := fun g =>
    Finset.sum_coe_sort R.dcells (fun c => if c.1 = R.x0 then g c else 0)
  rw [e1 (fun c => (E.filter (fun m => m ∈ corners c)).card)]
  calc ∑ c ∈ R.dcells, (if c.1 = R.x0 then (E.filter (fun m => m ∈ corners c)).card else 0)
      = ∑ c ∈ R.dcells, ∑ m ∈ E, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.card_filter]
        split_ifs with h
        · grind
        simp [h]
    _ = ∑ m ∈ E, ∑ c ∈ R.dcells, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ E, (if m.1 = R.x0 + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← R.leftcol_filter m (hE hm), Finset.card_filter]
    _ = (E.filter (fun m => m.1 = R.x0 + 1)).card := by simp


section
variable (X : Cell → Prop)
theorem isCut_leftcol (b : ℤ) :
    IsCut X (R.x0 + 1, b) ↔ ¬ (X (R.wcell b) ↔ X (R.wcell (b - 1))) := by
  unfold IsCut
  rw [R.primalEnds_leftcol]
  simp

/-- Parity of the number of cut edges in the first column of medial vertices. -/
theorem cnt_parity (k : ℕ) :
    Even ((Finset.Icc (R.y0 + 1) (R.y0 + k)).filter (fun b => IsCut X (R.x0 + 1, b))).card ↔
      (X (R.wcell R.y0) ↔ X (R.wcell (R.y0 + k))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hset : Finset.Icc (R.y0 + 1) (R.y0 + ((k + 1 : ℕ) : ℤ)) =
        insert (R.y0 + ((k + 1 : ℕ) : ℤ)) (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))) := by
      grind
    rw [hset, Finset.filter_insert]
    have hlast := R.isCut_leftcol X (R.y0 + ((k + 1 : ℕ) : ℤ))
    grind
end


section
variable (hw : 0 < R.w) (X : Cell → Prop)
include hw
theorem cutSet_col_card  :
    ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).card := by
  have : (R.cutSet X).filter (fun m => m.1 = R.x0 + 1) =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).image (fun b => (R.x0 + 1, b)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, mem_cutSet, mem_inner]
    grind
  rw [this, Finset.card_image_of_injective]
  intro a b hab
  simp_all

/-- The first column of cut edges has odd cardinality when the bottom corner is inside `X`
and the top corner is outside. -/
theorem cutSet_col_odd (hbot : X (R.wcell R.y0))
    (htop : ¬ X (R.wcell (R.y0 + R.h))) :
    Odd ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card := by
  rw [R.cutSet_col_card hw X, ← Nat.not_even_iff_odd]
  intro hev
  have := (R.cnt_parity X R.h).1 hev
  simp_all
end


/-- Reachability in the dual graph of `E` gives actual open connectivity for a larger set. -/
theorem dualOf_actualConnected {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    FK.ActualConnected R.dG (cfgOf R.dData D) x y := by
  have hle : R.dualOf E ≤ FK.openGraph R.dG (cfgOf R.dData D) := by
    intro a b hab
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact ⟨m, hED hm, Or.inl h⟩
    · exact ⟨m, hED hm, Or.inr h⟩
  exact h.mono hle

section
variable (C : FK.Configuration R.pG)
/-- Cells connected to the bottom row by open paths. -/
def botComp (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, ∃ b : R.pcells, b.1.2 = R.y0 ∧ FK.ActualConnected R.pG C b ⟨c, hc⟩

theorem botComp_of_adj {x y : R.pcells}
    (hxy : (FK.openGraph R.pG C).Adj x y) : R.botComp C x.1 ↔ R.botComp C y.1 := by
  constructor
  · rintro ⟨_, b, hb, h⟩
    exact ⟨y.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy)⟩
  · rintro ⟨_, b, hb, h⟩
    exact ⟨x.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy.symm)⟩
end

theorem hex (hh : 0 < R.h) (hw : 0 < R.w) (C : FK.Configuration R.pG)
    (hno : ¬ ∃ u v : R.pcells, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧
      FK.ActualConnected R.pG C u v) :
    ∃ z z' : R.dcells, z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧
      FK.ActualConnected R.dG (R.dualEquiv C) z z' := by
  set A := openMedials R.pData C with hA
  set X := R.botComp C with hX
  set E := R.cutSet X with hE
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hEc : E ⊆ R.inner \ A := by
    intro m hm
    simp
    refine ⟨hEsub hm, fun hmA => ?_⟩
    have hmem := R.pData.mem m ((openMedials_subset R.pData C) hmA)
    apply ((R.mem_cutSet.1 hm).2)
    have hadj : (FK.openGraph R.pG C).Adj ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩ := by
      rw [openGraph_adj_iff R.pData]
      exact ⟨m, hmA, Or.inl rfl⟩
    exact propext (R.botComp_of_adj C hadj)
  -- statuses of the bottom and top rows
  have hbotX : ∀ c : Cell, ∀ hc : c ∈ R.pcells, c.2 = R.y0 → X c := fun c hc hy =>
    ⟨hc, ⟨c, hc⟩, hy, SimpleGraph.Reachable.refl _⟩
  have htopX : ∀ c : Cell, c ∈ R.pcells → c.2 = R.y0 + R.h → ¬ X c := by
    rintro c hc hy ⟨_, b, hb, hconn⟩
    grind
  have hwbot : R.wcell R.y0 ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal R.y0
    have h2 := R.wcell_row R.y0
    have h3 := R.wcell_col R.y0
    grind
  have hwtop : R.wcell (R.y0 + R.h) ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_primal (R.y0 + R.h)
    have h2 := R.wcell_row (R.y0 + R.h)
    have h3 := R.wcell_col (R.y0 + R.h)
    grind
  have hdisj : Disjoint R.leftFaces R.rightFaces := by
    rw [Finset.disjoint_left]
    grind [leftFaces, rightFaces]
  obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hEsub R.leftFaces R.rightFaces hdisj
    (by
      intro z hz1 hz2
      simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      have hzc := mem_cells.1 (mem_dcells.1 z.2).1
      have hz := mem_dcells.1 z.2
      have hx1 : R.x0 < z.1.1 := by omega
      have hx2 : z.1.1 < R.x0 + R.w := by omega
      obtain ⟨hW, hE'⟩ := R.outer_pcells z hx1 hx2
      rw [cutSet_filter_corners]
      refine cut_deg_even R hh X z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2 ?_ ?_
      · grind
      grind)
    (by
      rw [R.leftSum_eq E hEsub]
      exact R.cutSet_col_odd hw X (hbotX _ hwbot (R.wcell_row _)) (htopX _ hwtop (R.wcell_row _)))
  have hb' : b.1.1 = R.x0 := by
    grind [leftFaces]
  have ht' : t.1.1 = R.x0 + R.w := by
    grind [rightFaces]
  exact ⟨b, t, hb', ht', R.dualOf_actualConnected hEc Finset.sdiff_subset hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
