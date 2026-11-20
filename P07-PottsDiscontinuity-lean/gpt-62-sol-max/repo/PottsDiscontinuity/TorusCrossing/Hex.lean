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

/-- The primal cell of row `j` among the two leftmost columns. -/
def wcell : Cell := if IsPrimal (R.x0, j) then (R.x0, j) else (R.x0 + 1, j)

theorem wcell_primal : IsPrimal (R.wcell j) := by
  unfold wcell
  split_ifs with h
  · exact h
  · unfold IsPrimal at * <;> grind

theorem wcell_row : (R.wcell j).2 = j := by
  unfold wcell; grind

theorem wcell_col : (R.wcell j).1 = R.x0 ∨ (R.wcell j).1 = R.x0 + 1 := by
  unfold wcell; grind

end

theorem primalEnds_leftcol (b : ℤ) : primalEnds (R.x0 + 1, b) = (R.wcell b, R.wcell (b - 1)) := by
  unfold wcell primalEnds
  simp [IsPrimal]
  by_cases h : (R.x0 + b) % 2 = 0
  · grind [Prod.mk.injEq]
  grind [Prod.mk.injEq]


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
      unfold IsPrimal at *
      omega
    · refine ⟨(R.x0, m.2), ?_⟩
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff]
      unfold IsPrimal at *
      omega
  · rw [ite_eq_right h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    simp only [corners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hc
    omega

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
        · simp [h]
        · simp [h]
    _ = ∑ m ∈ E, ∑ c ∈ R.dcells, (if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ E, (if m.1 = R.x0 + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← R.leftcol_filter m (hE hm), Finset.card_filter]
    _ = (E.filter (fun m => m.1 = R.x0 + 1)).card := by simp


theorem isCut_leftcol (X : Cell → Prop) (b : ℤ) :
    IsCut X (R.x0 + 1, b) ↔ ¬ (X (R.wcell b) ↔ X (R.wcell (b - 1))) := by
  unfold IsCut
  rw [R.primalEnds_leftcol]
  dsimp only
  tauto

/-- Parity of the number of cut edges in the first column of medial vertices. -/
theorem cnt_parity (X : Cell → Prop) (k : ℕ) :
    Even ((Finset.Icc (R.y0 + 1) (R.y0 + k)).filter (fun b => IsCut X (R.x0 + 1, b))).card ↔
      (X (R.wcell R.y0) ↔ X (R.wcell (R.y0 + k))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hset : Finset.Icc (R.y0 + 1) (R.y0 + ((k + 1 : ℕ) : ℤ)) =
        insert (R.y0 + ((k + 1 : ℕ) : ℤ)) (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))) := by
      ext a; simp; omega
    rw [hset, Finset.filter_insert]
    have hnot : R.y0 + ((k + 1 : ℕ) : ℤ) ∉
        (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))).filter (fun b => IsCut X (R.x0 + 1, b)) := by
      simp
    have hlast := R.isCut_leftcol X (R.y0 + ((k + 1 : ℕ) : ℤ))
    rw [show R.y0 + ((k + 1 : ℕ) : ℤ) - 1 = R.y0 + (k : ℤ) by push_cast; ring] at hlast
    by_cases hc : IsCut X (R.x0 + 1, R.y0 + ((k + 1 : ℕ) : ℤ))
    · rw [ite_eq_left hc, Finset.card_insert_of_notMem hnot, Nat.even_add_one, ih]
      by_cases h1 : X (R.wcell R.y0) <;> by_cases h2 : X (R.wcell (R.y0 + (k : ℤ))) <;>
        by_cases h3 : X (R.wcell (R.y0 + ((k + 1 : ℕ) : ℤ))) <;> simp_all
    simp_all


theorem cutSet_col_card (hw : 0 < R.w) (X : Cell → Prop) :
    ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).card := by
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  have : (R.cutSet X).filter (fun m => m.1 = R.x0 + 1) =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).image (fun b => (R.x0 + 1, b)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, mem_cutSet, mem_inner]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3, h4⟩, hc⟩, h5⟩
      exact ⟨m.2, ⟨⟨h3, h4⟩, by rw [← h5]; exact hc⟩, by rw [← h5]⟩
    · rintro ⟨b, ⟨⟨h3, h4⟩, hc⟩, rfl⟩
      simp_all <;> omega
  rw [this, Finset.card_image_of_injective]
  intro x; grind

/-- The first column of cut edges has odd cardinality when the bottom corner is inside `X`
and the top corner is outside. -/
theorem cutSet_col_odd (hw : 0 < R.w) (X : Cell → Prop) (hbot : X (R.wcell R.y0))
    (htop : ¬ X (R.wcell (R.y0 + R.h))) :
    Odd ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card := by
  rw [R.cutSet_col_card hw X, ← Nat.not_even_iff_odd]
  intro hev
  have := (R.cnt_parity X R.h).1 hev
  simp_all


/-- Cells connected to the bottom row by open paths. -/
def botComp (C : FK.Configuration R.pG) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, ∃ b : R.pcells, b.1.2 = R.y0 ∧ FK.ActualConnected R.pG C b ⟨c, hc⟩

theorem botComp_of_adj (C : FK.Configuration R.pG) {x y : R.pcells}
    (hxy : (FK.openGraph R.pG C).Adj x y) : R.botComp C x.1 ↔ R.botComp C y.1 := by
  constructor
  · rintro ⟨_, b, hb, h⟩
    exact ⟨y.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy)⟩
  · rintro ⟨_, b, hb, h⟩
    exact ⟨x.2, b, hb, h.trans (SimpleGraph.Adj.reachable hxy.symm)⟩

theorem hex (hh : 0 < R.h) (hw : 0 < R.w) (C : FK.Configuration R.pG)
    (hno : ¬ ∃ u v : R.pcells, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧
      FK.ActualConnected R.pG C u v) :
    ∃ z z' : R.dcells, z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧
      FK.ActualConnected R.dG (R.dualEquiv C) z z' := by
  set A := openMedials R.pData C with hA
  have hAsub : A ⊆ R.inner := openMedials_subset R.pData C
  set X := R.botComp C with hX
  set E := R.cutSet X with hE
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hEc : E ⊆ R.inner \ A := by
    intro m hm
    rw [Finset.mem_sdiff]
    refine ⟨hEsub hm, fun hmA => ?_⟩
    have hcut := (R.mem_cutSet.1 hm).2
    have hmem := R.pData.mem m (hAsub hmA)
    apply hcut
    have hadj : (FK.openGraph R.pG C).Adj ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩ := by
      rw [openGraph_adj_iff R.pData]
      exact ⟨m, hmA, Or.inl rfl⟩
    exact propext (R.botComp_of_adj C hadj)
  -- statuses of the bottom and top rows
  have hbotX : ∀ c : Cell, ∀ hc : c ∈ R.pcells, c.2 = R.y0 → X c := fun c hc hy =>
    ⟨hc, ⟨c, hc⟩, hy, SimpleGraph.Reachable.refl _⟩
  have htopX : ∀ c : Cell, c ∈ R.pcells → c.2 = R.y0 + R.h → ¬ X c := by
    rintro c hc hy ⟨_, b, hb, hconn⟩
    exact hno ⟨b, ⟨c, hc⟩, hb, hy, hconn⟩
  have hwcell {y : ℤ} (hy₁ : R.y0 ≤ y) (hy₂ : y ≤ R.y0 + R.h) : R.wcell y ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_col y
    rw [R.wcell_row y]
    exact ⟨⟨by omega, by omega, hy₁, hy₂⟩, R.wcell_primal y⟩
  have hXbot := hbotX _ (hwcell le_rfl (by omega)) (R.wcell_row _)
  have hXtop := htopX _ (hwcell (by omega) le_rfl) (R.wcell_row _)
  -- handshake
  obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hEsub R.leftFaces R.rightFaces
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
      · intro hy
        have hW' := hbotX _ hW (by simp [hy])
        have hE'' := hbotX _ hE' (by simp [hy])
        tauto
      · intro hy
        have hW' := htopX _ hW (by simp [hy])
        have hE'' := htopX _ hE' (by simp [hy])
        tauto)
    (by
      rw [R.leftSum_eq E hEsub]
      exact R.cutSet_col_odd hw X hXbot hXtop)
  have hb' : b.1.1 = R.x0 := by
    simpa only [leftFaces, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have ht' : t.1.1 = R.x0 + R.w := by
    simpa only [rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  exact ⟨b, t, hb', ht', R.dualOf_actualConnected hEc Finset.sdiff_subset hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
