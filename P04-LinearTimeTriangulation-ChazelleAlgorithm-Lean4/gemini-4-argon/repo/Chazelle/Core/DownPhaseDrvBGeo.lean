module

public import Chazelle.Core.FactsInterior
public import Chazelle.Core.BruteCorner

/-!
# Down-phase base (D9), geometry part 1: the corner test at a vertex of a polygon

The base case of the down phase shoots, inside the host polygon of every region, from every
host vertex that is a vertex of `Q`, in every horizontal direction entering the host.  Whether a
horizontal direction enters a simple polygon at a vertex is decided by the corner of the
polygon there, for a polygon with the interior on its left:

* `dirInterior_iff_corner`: for `orient W = 1`, direction `σ = ±1` at vertex `p` is locally
  interior iff it lies in the open left sector of the corner `prev → v → next`
  (`FactsInterior.vertex_local`);
* `emitG a v b σ`: the decision of the RAM, a Boolean combination of height and abscissa
  comparisons of the three corner points and one orientation test (`Brute.emitR` when no
  neighbour is at the height of `v`; a neighbour at the height of `v` is an edge along a chord);
* `sideLeftOf_iff_emitG`: the corner decision is the left sector, for a corner that is not a
  spike (`FactsInterior.corner_nonSpike`).
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (sideLeftOf sideCcw sideCross sideDot sideNonSpike)
open Chazelle.Visibility (DirInterior rayPt)
open Chazelle.Jordan (simple_three_le simple_vtx_ne simple_vtx_succ_ne)

/-! ## Directions in the left sector of a corner -/

/-- A horizontal ray from the apex of a corner lies in its left sector at every parameter or at
none (the sector is a cone). -/
theorem sideLeftOf_rayPt_scale {a v b : Point} {σ s : ℝ} (hs : 0 < s) :
    sideLeftOf a v b (rayPt v σ s) ↔ sideLeftOf a v b (rayPt v σ 1) := by
  unfold sideLeftOf
  rw [FuseMath.rayPt_sub, FuseMath.rayPt_sub, one_smul, Chazelle.Chain.sideCcw_smul hs]

/-- **The corner test.**  For a simple polygon with the interior on its left, the horizontal
direction `σ = ±1` at vertex `p` is locally interior iff it lies in the open left sector of the
corner at `p`. -/
theorem dirInterior_iff_corner {W : Polygon} (hW : W.Simple) (hL : Mountain.orient W = 1)
    {p : ℕ} (hp : p < W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    DirInterior W p σ ↔
      sideLeftOf (W.vtx (Chazelle.Jordan.prevIdx W p)) (W.vtx p) (W.vtx ((p + 1) % W.n))
        (rayPt (W.vtx p) σ 1) := by
  obtain ⟨r, hr, hloc⟩ := FactsInterior.vertex_local hW hL hp
  have hball : ∀ s, 0 ≤ s → s < r → rayPt (W.vtx p) σ s ∈ ball (W.vtx p) r := fun s hs0 hsr => by
    rwa [mem_ball, FuseMath.dist_rayPt _ hσ hs0]
  constructor
  · intro h
    obtain ⟨s, hs, ⟨hs0, hsr⟩⟩ := (h.and (Ioo_mem_nhdsGT hr)).exists
    have hx := hball s hs0.le hsr
    rcases (hloc _ hx).2.2 hs.2 with hl | hr'
    · exact (sideLeftOf_rayPt_scale hs0).1 hl
    · exact absurd hs.1 ((hloc _ hx).2.1 hr')
  · intro h
    unfold DirInterior
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact (hloc _ (hball s hs.1.le hs.2)).1 ((sideLeftOf_rayPt_scale hs.1).2 h)

/-! ## The decision of the corner test -/

/-- **The corner decision** for the corner `a → v → b` and the horizontal direction `σ`: by the
heights of the neighbours (and their abscissae when one is at the height of `v`) and one
orientation test. -/
def emitG (a v b : Point) (σ : ℝ) : Prop :=
  if a.2 = v.2 then
    (if b.2 = v.2 then False
     else if v.2 < b.2 then σ = -1 ∧ v.1 < a.1 else σ = 1 ∧ a.1 < v.1)
  else if b.2 = v.2 then
    (if v.2 < a.2 then σ = 1 ∧ b.1 < v.1 else σ = -1 ∧ v.1 < b.1)
  else Brute.emitR a v b σ

/-- The four cases of `sideCcw`, spelled out. -/
theorem sideCcw_iff_raw (B X A : Point) : sideCcw B X A ↔
    (0 < sideCross B A ∧ 0 < sideCross B X ∧ 0 < sideCross X A) ∨
    (sideCross B A < 0 ∧ (0 < sideCross B X ∨ 0 < sideCross X A)) ∨
    (sideCross B A = 0 ∧ sideDot B A < 0 ∧ 0 < sideCross B X) ∨
    (sideCross B A = 0 ∧ 0 < sideDot B A ∧ (sideCross B X ≠ 0 ∨ sideDot B X < 0)) := Iff.rfl

/-- **The corner decision is the left sector** (for a corner that is not a spike). -/
theorem sideLeftOf_iff_emitG {a v b : Point} (hav : a ≠ v) (hbv : b ≠ v)
    (hns : sideNonSpike (b - v) (a - v)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    sideLeftOf a v b (rayPt v σ 1) ↔ emitG a v b σ := by
  have eBX : sideCross (b - v) ((σ, 0) : Point) = -σ * (b.2 - v.2) := by
    unfold sideCross; simp only [Prod.snd_sub, Prod.fst_sub]; ring
  have eXA : sideCross ((σ, 0) : Point) (a - v) = σ * (a.2 - v.2) := by
    unfold sideCross; simp only [Prod.snd_sub, Prod.fst_sub]; ring
  have eBA : sideCross (b - v) (a - v) =
      (b.1 - v.1) * (a.2 - v.2) - (b.2 - v.2) * (a.1 - v.1) := by
    unfold sideCross; simp only [Prod.snd_sub, Prod.fst_sub]
  unfold sideLeftOf
  rw [FuseMath.rayPt_sub_one, sideCcw_iff_raw]
  unfold emitG
  by_cases ha : a.2 = v.2
  · rw [ite_eq_left ha]
    have ha' : a.2 - v.2 = 0 := by rw [ha, sub_self]
    have ha1 : a.1 - v.1 ≠ 0 := fun h => hav (Prod.ext (by linarith) ha)
    have cXA : sideCross ((σ, 0) : Point) (a - v) = 0 := by rw [eXA, ha', mul_zero]
    by_cases hb : b.2 = v.2
    · -- both neighbours at the height of `v`: only a spike contains a horizontal direction
      rw [ite_eq_left hb]
      have hb' : b.2 - v.2 = 0 := by rw [hb, sub_self]
      have cBX : sideCross (b - v) ((σ, 0) : Point) = 0 := by rw [eBX, hb', mul_zero]
      have cBA : sideCross (b - v) (a - v) = 0 := by rw [eBA, ha', hb']; ring
      rw [cBX, cBA]
      simp only [iff_false]
      rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, hd, -⟩)
      · exact lt_irrefl _ h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ h
      · exact hns ⟨cBA, hd⟩
    · rw [ite_eq_right hb]
      have hb0 : b.2 - v.2 ≠ 0 := sub_ne_zero.2 hb
      have cBA : sideCross (b - v) (a - v) = -((b.2 - v.2) * (a.1 - v.1)) := by
        rw [eBA, ha']; ring
      have hne : (b.2 - v.2) * (a.1 - v.1) ≠ 0 := mul_ne_zero hb0 ha1
      rw [cXA, cBA, eBX]
      by_cases hvb : v.2 < b.2
      · rw [ite_eq_left hvb]
        have hbp : 0 < b.2 - v.2 := by linarith
        constructor
        · rintro (⟨-, -, h⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
          · exact absurd h (lt_irrefl _)
          · refine ⟨?_, ?_⟩
            · rcases hσ with rfl | rfl
              · exfalso; linarith
              · rfl
            · by_contra hc; push Not at hc
              nlinarith
          · exact absurd h2 (lt_irrefl _)
          · exact absurd (neg_eq_zero.1 h1) hne
          · exact absurd (neg_eq_zero.1 h1) hne
        · rintro ⟨rfl, h2⟩
          right; left
          refine ⟨?_, Or.inl ?_⟩
          · have : 0 < (b.2 - v.2) * (a.1 - v.1) := mul_pos hbp (by linarith)
            linarith
          · linarith
      · rw [ite_eq_right hvb]
        have hbn : b.2 - v.2 < 0 := by
          rcases lt_or_gt_of_ne hb0 with h | h
          · exact h
          · exact absurd (by linarith) hvb
        constructor
        · rintro (⟨-, -, h⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
          · exact absurd h (lt_irrefl _)
          · refine ⟨?_, ?_⟩
            · rcases hσ with rfl | rfl
              · rfl
              · exfalso; linarith
            · by_contra hc; push Not at hc
              nlinarith
          · exact absurd h2 (lt_irrefl _)
          · exact absurd (neg_eq_zero.1 h1) hne
          · exact absurd (neg_eq_zero.1 h1) hne
        · rintro ⟨rfl, h2⟩
          right; left
          refine ⟨?_, Or.inl ?_⟩
          · have : 0 < (b.2 - v.2) * (a.1 - v.1) := mul_pos_of_neg_of_neg hbn (by linarith)
            linarith
          · linarith
  · rw [ite_eq_right ha]
    have ha0 : a.2 - v.2 ≠ 0 := sub_ne_zero.2 ha
    by_cases hb : b.2 = v.2
    · rw [ite_eq_left hb]
      have hb' : b.2 - v.2 = 0 := by rw [hb, sub_self]
      have hb1 : b.1 - v.1 ≠ 0 := fun h => hbv (Prod.ext (by linarith) hb)
      have cBX : sideCross (b - v) ((σ, 0) : Point) = 0 := by rw [eBX, hb', mul_zero]
      have cBA : sideCross (b - v) (a - v) = (b.1 - v.1) * (a.2 - v.2) := by
        rw [eBA, hb']; ring
      have hne : (b.1 - v.1) * (a.2 - v.2) ≠ 0 := mul_ne_zero hb1 ha0
      rw [cBX, cBA, eXA]
      by_cases hva : v.2 < a.2
      · rw [ite_eq_left hva]
        have hap : 0 < a.2 - v.2 := by linarith
        constructor
        · rintro (⟨-, h, -⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
          · exact absurd h (lt_irrefl _)
          · exact absurd h2 (lt_irrefl _)
          · refine ⟨?_, ?_⟩
            · rcases hσ with rfl | rfl
              · rfl
              · exfalso; linarith
            · by_contra hc; push Not at hc
              nlinarith
          · exact absurd h1 hne
          · exact absurd h1 hne
        · rintro ⟨rfl, h2⟩
          right; left
          refine ⟨?_, Or.inr ?_⟩
          · exact mul_neg_of_neg_of_pos (by linarith) hap
          · linarith
      · rw [ite_eq_right hva]
        have han : a.2 - v.2 < 0 := by
          rcases lt_or_gt_of_ne ha0 with h | h
          · exact h
          · exact absurd (by linarith) hva
        constructor
        · rintro (⟨-, h, -⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
          · exact absurd h (lt_irrefl _)
          · exact absurd h2 (lt_irrefl _)
          · refine ⟨?_, ?_⟩
            · rcases hσ with rfl | rfl
              · exfalso; linarith
              · rfl
            · by_contra hc; push Not at hc
              nlinarith
          · exact absurd h1 hne
          · exact absurd h1 hne
        · rintro ⟨rfl, h2⟩
          right; left
          refine ⟨?_, Or.inr ?_⟩
          · exact mul_neg_of_pos_of_neg (by linarith) han
          · linarith
    · rw [ite_eq_right hb]
      have h := Brute.sideLeftOf_horiz ha hb hσ
      unfold sideLeftOf at h
      rwa [FuseMath.rayPt_sub_one, sideCcw_iff_raw] at h

/-- **The corner test by the decision.**  For a simple polygon with the interior on its left,
direction `σ = ±1` at vertex `p` is locally interior iff the corner decision holds. -/
theorem dirInterior_iff_emitG {W : Polygon} (hW : W.Simple) (hL : Mountain.orient W = 1)
    {p : ℕ} (hp : p < W.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    DirInterior W p σ ↔
      emitG (W.vtx (Chazelle.Jordan.prevIdx W p)) (W.vtx p) (W.vtx ((p + 1) % W.n)) σ := by
  rw [dirInterior_iff_corner hW hL hp hσ]
  have hn := simple_three_le hW
  have hav : W.vtx (Chazelle.Jordan.prevIdx W p) ≠ W.vtx p :=
    simple_vtx_ne hW (Chazelle.Jordan.prevIdx_lt W hp) hp (Chazelle.Jordan.prevIdx_ne W hn hp)
  have hbv : W.vtx ((p + 1) % W.n) ≠ W.vtx p := (simple_vtx_succ_ne hW hp).symm
  exact sideLeftOf_iff_emitG hav hbv (FactsInterior.corner_nonSpike hW hp) hσ

end

end DrvB

end Chazelle.Core
