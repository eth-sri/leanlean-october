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

def wcell (j : ℤ) : Cell := if IsPrimal (R.x0, j) then (R.x0, j) else (R.x0 + 1, j)

theorem wcell_primal (j : ℤ) : IsPrimal (R.wcell j) := by
  unfold wcell; split_ifs with h <;> [exact h; (unfold IsPrimal at *; dsimp only at *; omega)]

theorem wcell_row (j : ℤ) : (R.wcell j).2 = j := by
  unfold wcell; split_ifs <;> rfl

theorem wcell_col (j : ℤ) : (R.wcell j).1 = R.x0 ∨ (R.wcell j).1 = R.x0 + 1 := by
  unfold wcell; split_ifs <;> simp

theorem primalEnds_leftcol (b : ℤ) : primalEnds (R.x0 + 1, b) = (R.wcell b, R.wcell (b - 1)) := by
  unfold wcell primalEnds; simp only [IsPrimal]
  by_cases h : (R.x0 + b) % 2 = 0
  · have h0 : ¬ ((R.x0 + 1 + b) % 2 = 0) := by omega
    have h2 : ¬ ((R.x0 + (b - 1)) % 2 = 0) := by omega
    simp only [h, h0, h2, ite_true, ite_false, Prod.mk.injEq, and_true]; omega
  · have h0 : ((R.x0 + 1 + b) % 2 = 0) := by omega
    have h2 : ((R.x0 + (b - 1)) % 2 = 0) := by omega
    simp only [h, h0, h2, ite_true, ite_false, Prod.mk.injEq, and_true, true_and]; omega

noncomputable def leftFaces : Finset R.dcells := Finset.univ.filter (fun z => z.1.1 = R.x0)

noncomputable def rightFaces : Finset R.dcells :=
  Finset.univ.filter (fun z => z.1.1 = R.x0 + R.w)

theorem leftcol_filter (m : Cell) (hm : m ∈ R.inner) :
    (R.dcells.filter (fun c => c.1 = R.x0 ∧ m ∈ corners c)).card =
      if m.1 = R.x0 + 1 then 1 else 0 := by
  have hmi := mem_inner.1 hm
  by_cases h1 : m.1 = R.x0 + 1
  · rw [ite_eq_left h1, Finset.card_eq_one]
    refine ⟨if IsPrimal (R.x0, m.2) then (R.x0, m.2 - 1) else (R.x0, m.2), ?_⟩
    split_ifs with hp <;> ext c <;>
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_dcells, mem_cells, corners,
        Finset.mem_insert, Prod.ext_iff] <;>
      unfold IsPrimal at * <;> dsimp only at * <;> omega
  · rw [ite_eq_right h1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    simp only [corners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hc; omega

theorem leftSum_eq (E : Finset Cell) (hE : E ⊆ R.inner) :
    ∑ z ∈ R.leftFaces, (E.filter (fun m => m ∈ corners z.1)).card =
      (E.filter (fun m => m.1 = R.x0 + 1)).card := by
  unfold leftFaces
  rw [Finset.sum_filter,
    Finset.sum_coe_sort R.dcells (fun c => if c.1 = R.x0 then (E.filter (fun m => m ∈ corners c)).card else 0),
    show (∑ c ∈ R.dcells, if c.1 = R.x0 then (E.filter (fun m => m ∈ corners c)).card else 0) =
      ∑ c ∈ R.dcells, ∑ m ∈ E, if c.1 = R.x0 ∧ m ∈ corners c then 1 else 0 from
      Finset.sum_congr rfl fun c _ => by rw [Finset.card_filter]; split_ifs with h <;> simp [h],
    Finset.sum_comm, Finset.card_filter]
  exact Finset.sum_congr rfl fun m hm => by rw [← R.leftcol_filter m (hE hm), Finset.card_filter]

theorem isCut_leftcol (X : Cell → Prop) (b : ℤ) :
    IsCut X (R.x0 + 1, b) ↔ ¬ (X (R.wcell b) ↔ X (R.wcell (b - 1))) := by
  unfold IsCut; rw [R.primalEnds_leftcol]; dsimp only; tauto

theorem cnt_parity (X : Cell → Prop) (k : ℕ) :
    Even ((Finset.Icc (R.y0 + 1) (R.y0 + k)).filter (fun b => IsCut X (R.x0 + 1, b))).card ↔
      (X (R.wcell R.y0) ↔ X (R.wcell (R.y0 + k))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show Finset.Icc (R.y0 + 1) (R.y0 + ((k + 1 : ℕ) : ℤ)) =
        insert (R.y0 + ((k + 1 : ℕ) : ℤ)) (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))) by
      ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega,
      Finset.filter_insert]
    have hnot : R.y0 + ((k + 1 : ℕ) : ℤ) ∉
        (Finset.Icc (R.y0 + 1) (R.y0 + (k : ℤ))).filter (fun b => IsCut X (R.x0 + 1, b)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]; push_cast; omega
    have hlast := R.isCut_leftcol X (R.y0 + ((k + 1 : ℕ) : ℤ))
    rw [show R.y0 + ((k + 1 : ℕ) : ℤ) - 1 = R.y0 + (k : ℤ) by push_cast; ring] at hlast
    by_cases hc : IsCut X (R.x0 + 1, R.y0 + ((k + 1 : ℕ) : ℤ))
    · rw [ite_eq_left hc, Finset.card_insert_of_notMem hnot, Nat.even_add_one, ih]
      have := hlast.1 hc; tauto
    · rw [ite_eq_right hc, ih]
      have : ¬ IsCut X (R.x0 + 1, R.y0 + ((k + 1 : ℕ) : ℤ)) := hc
      tauto

theorem cutSet_col_card (hw : 0 < R.w) (X : Cell → Prop) :
    ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).card := by
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  rw [show (R.cutSet X).filter (fun m => m.1 = R.x0 + 1) =
      ((Finset.Icc (R.y0 + 1) (R.y0 + (R.h : ℤ))).filter
        (fun b => IsCut X (R.x0 + 1, b))).image (fun b => (R.x0 + 1, b)) by
    ext m; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc, mem_cutSet, mem_inner]
    exact ⟨fun ⟨⟨⟨_, _, h3, h4⟩, hc⟩, h5⟩ => ⟨m.2, ⟨⟨h3, h4⟩, h5 ▸ hc⟩, Prod.ext h5.symm rfl⟩,
      by rintro ⟨b, ⟨⟨h3, h4⟩, hc⟩, rfl⟩; exact ⟨⟨⟨by omega, by omega, h3, h4⟩, hc⟩, rfl⟩⟩]
  exact Finset.card_image_of_injective _ fun _ _ hab => (Prod.ext_iff.1 hab).2

theorem cutSet_col_odd (hw : 0 < R.w) (X : Cell → Prop) (hbot : X (R.wcell R.y0))
    (htop : ¬ X (R.wcell (R.y0 + R.h))) :
    Odd ((R.cutSet X).filter (fun m => m.1 = R.x0 + 1)).card := by
  rw [R.cutSet_col_card hw X, ← Nat.not_even_iff_odd, R.cnt_parity]
  tauto

theorem dualOf_actualConnected {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    FK.ActualConnected R.dG (cfgOf R.dData D) x y :=
  h.mono fun a b hab => by
    rw [dualOf, endGraph_adj] at hab
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;>
      [exact ⟨m, hED hm, Or.inl h⟩; exact ⟨m, hED hm, Or.inr h⟩]

def botComp (C : FK.Configuration R.pG) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, ∃ b : R.pcells, b.1.2 = R.y0 ∧ FK.ActualConnected R.pG C b ⟨c, hc⟩

theorem botComp_of_adj (C : FK.Configuration R.pG) {x y : R.pcells}
    (hxy : (FK.openGraph R.pG C).Adj x y) : R.botComp C x.1 ↔ R.botComp C y.1 :=
  ⟨fun ⟨_, b, hb, h⟩ => ⟨y.2, b, hb, h.trans hxy.reachable⟩,
   fun ⟨_, b, hb, h⟩ => ⟨x.2, b, hb, h.trans hxy.symm.reachable⟩⟩

theorem hex (hh : 0 < R.h) (hw : 0 < R.w) (C : FK.Configuration R.pG)
    (hno : ¬ ∃ u v : R.pcells, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧
      FK.ActualConnected R.pG C u v) :
    ∃ z z' : R.dcells, z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧
      FK.ActualConnected R.dG (R.dualEquiv C) z z' := by
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  set A := openMedials R.pData C
  set X := R.botComp C
  set E := R.cutSet X
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hEc : E ⊆ R.inner \ A := fun m hm => Finset.mem_sdiff.2 ⟨hEsub hm, fun hmA => by
    have hmem := R.pData.mem m (openMedials_subset R.pData C hmA)
    exact (R.mem_cutSet.1 hm).2 (propext (R.botComp_of_adj C (by
      rw [openGraph_adj_iff R.pData C ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩]
      exact ⟨m, hmA, Or.inl rfl⟩)))⟩
  have hbotX (c : Cell) (hc : c ∈ R.pcells) (hy : c.2 = R.y0) : X c :=
    ⟨hc, ⟨c, hc⟩, hy, SimpleGraph.Reachable.refl _⟩
  have htopX (c : Cell) (hc : c ∈ R.pcells) (hy : c.2 = R.y0 + R.h) : ¬ X c :=
    fun ⟨_, b, hb, hconn⟩ => hno ⟨b, ⟨c, hc⟩, hb, hy, hconn⟩
  have hwmem (r : ℤ) (hr : R.y0 ≤ r ∧ r ≤ R.y0 + R.h) : R.wcell r ∈ R.pcells := by
    rw [mem_pcells, mem_cells]
    have := R.wcell_row r; have := R.wcell_col r
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, R.wcell_primal r⟩
  obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd hEsub R.leftFaces R.rightFaces
    (Finset.disjoint_left.2 fun z hz hz' => by
      simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'; omega)
    (fun z hz1 hz2 => by
      simp only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
      have hzc := mem_cells.1 (mem_dcells.1 z.2).1
      have hz := mem_dcells.1 z.2
      obtain ⟨hW, hE'⟩ := R.outer_pcells z (by omega) (by omega)
      rw [cutSet_filter_corners]
      exact cut_deg_even R hh X z.1 hz.2 (by omega) (by omega) hzc.2.2.1 hzc.2.2.2
        (fun hy => iff_of_true (hbotX _ hW hy) (hbotX _ hE' hy))
        (fun hy => iff_of_false (htopX _ hW hy) (htopX _ hE' hy)))
    (by
      rw [R.leftSum_eq E hEsub]
      exact R.cutSet_col_odd hw X (hbotX _ (hwmem R.y0 ⟨le_rfl, by omega⟩) (R.wcell_row _))
        (htopX _ (hwmem (R.y0 + R.h) ⟨by omega, le_rfl⟩) (R.wcell_row _)))
  exact ⟨b, t, (Finset.mem_filter.1 hb).2, (Finset.mem_filter.1 ht).2,
    R.dualOf_actualConnected hEc Finset.sdiff_subset hr⟩

end Rect

end PottsDiscontinuity.TorusCrossing
