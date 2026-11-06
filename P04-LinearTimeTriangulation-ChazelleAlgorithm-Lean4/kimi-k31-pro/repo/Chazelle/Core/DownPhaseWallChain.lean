module

public import Chazelle.Core.DownPhaseDropDeg
public import Chazelle.Core.DownPhaseBoxFilter
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-M (B3′, part 11): the wall-to-wall chords of a chain model

For a valid chord list `L` of a chain `C` (model `chainModel C`):

* a horizontal line not meeting the chain lies below it when it is not above the top
  (`chain_above`);
* the cuts of an augmented chord lie on the side walls (with the parameter fixed by the
  height), or on the double boundary or the upward slit, at heights above any level below the
  chain (`cut_cases`);
* a wall-to-wall record is the full-width chord `hseg y (-R) R` (`wall_shape`), which lies below
  the chain;
* **dropping the wall-to-wall chords** keeps the degree bound and at most doubles the weights
  (`drop_ok`, design finding M6).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set List Chazelle.Chain Chazelle.Visibility BuildNF
open BuildRegions (famOf)

/-! ## The chain above a line -/

theorem mem_set_lerp (C : Chain) {z : Point} (hz : z ∈ C.set) :
    ∃ k, k < C.m ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.2 = (C.vertex k).2 + t * ((C.vertex (k + 1)).2 - (C.vertex k).2) := by
  obtain ⟨k, hk, hzk⟩ := hz
  rw [C.chainEdge_eq] at hzk
  obtain ⟨t, ht0, ht1, rfl⟩ := hzk
  exact ⟨k, hk, t, ht0, ht1, rfl⟩

/-- Every chain point is at least as high as some vertex. -/
theorem vertex_below (C : Chain) {z : Point} (hz : z ∈ C.set) :
    ∃ k, k ≤ C.m ∧ (C.vertex k).2 ≤ z.2 := by
  obtain ⟨k, hk, t, ht0, ht1, e⟩ := mem_set_lerp C hz
  rcases le_total (C.vertex k).2 (C.vertex (k + 1)).2 with h | h
  · exact ⟨k, hk.le, by rwnl [e]⟩
  · exact ⟨k + 1, hk, by rwnl [e]⟩

/-- **A line missing the chain, not above the top, lies below the chain.** -/
theorem chain_above (C : Chain) {y : ℝ} (hno : ∀ z ∈ C.set, z.2 ≠ y) (htop : y < C.top.2) :
    ∀ z ∈ C.set, y < z.2 := by
  have step : ∀ k, k < C.m → (y < (C.vertex k).2 ↔ y < (C.vertex (k + 1)).2) := by
    intro k hk
    have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (((C.vertex k).1 + t * ((C.vertex (k + 1)).1 - (C.vertex k).1),
          (C.vertex k).2 + t * ((C.vertex (k + 1)).2 - (C.vertex k).2)) : Point) ∈ C.set :=
      fun t h0 h1 => ⟨k, hk, by rw [C.chainEdge_eq]; exact ⟨t, h0, h1, rfl⟩⟩
    have ha : (C.vertex k).2 ≠ y := hno _ (C.vertex_mem_set hk.le)
    have hb : (C.vertex (k + 1)).2 ≠ y := hno _ (C.vertex_mem_set hk)
    set a := (C.vertex k).2
    set b := (C.vertex (k + 1)).2
    by_contra hne
    have hcross : (y < a ∧ b < y) ∨ (a < y ∧ y < b) := by
      rcases lt_or_gt_of_ne ha with h1 | h1 <;> rcases lt_or_gt_of_ne hb with h2 | h2
      · exact absurd (iff_of_false (not_lt.2 h1.le) (not_lt.2 h2.le)) hne
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact absurd (iff_of_true h1 h2) hne
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hpos : 0 < a - b := by linarith
      refine hno _ (hseg ((a - y) / (a - b)) (div_nonneg (by linarith) hpos.le)
        ((div_le_one hpos).2 (by linarith))) ?_
      fsr
    · have hpos : 0 < b - a := by linarith
      refine hno _ (hseg ((y - a) / (b - a)) (div_nonneg (by linarith) hpos.le)
        ((div_le_one hpos).2 (by linarith))) ?_
      fsr
  have hall : ∀ k, k ≤ C.m → (y < (C.vertex k).2 ↔ y < (C.vertex 0).2) := by
    intro k hk
    induction k with
    | zero => exact Iff.rfl
    | succ k ih => exact (step k (by omega)).symm.trans (ih (by omega))
  have h0 : y < (C.vertex 0).2 := (hall _ C.topIdx_le).1 htop
  have hv : ∀ k, k ≤ C.m → y < (C.vertex k).2 := fun k hk => (hall k hk).2 h0
  intro z hz
  obtain ⟨k, hk, t, ht0, ht1, e⟩ := mem_set_lerp C hz
  have h1 := hv k hk.le
  have h2 := hv (k + 1) hk
  rw [e]
  rcases le_total (C.vertex k).2 (C.vertex (k + 1)).2 with h | h
  · have := mul_nonneg ht0 (sub_nonneg.2 h); linarith
  · have := mul_le_mul_of_nonpos_right ht1 (sub_nonpos.2 h); linarith

/-! ## Cuts of augmented chords -/

theorem sidePt_small (C : Chain) {p : ℕ} (hp : p < 6) (t : ℝ) :
    sidePt (C.sideWalk C.sideBeta) p t =
      Geometry.lerp ((C.sideWalk C.sideBeta).vtx p) ((C.sideWalk C.sideBeta).vtx (p + 1)) t := by
  unfold sidePt
  rw [C.sideWalk_n, Nat.mod_eq_of_lt (by omega)]

/-- **The cuts of an augmented chord.** -/
theorem cut_cases (C : Chain) {e : Set Point} {y : ℝ} (hey : ∀ z ∈ e, z.2 = y)
    (hyR : |y| < C.radius) (hyt : y ≤ C.top.2) {p : ℕ} {t : ℝ}
    (hA : SideAttach (C.sideWalk C.sideBeta) e p t) :
    (p = 1 ∧ y = C.radius - 2 * C.radius * t) ∨ (p = 3 ∧ y = -C.radius + 2 * C.radius * t) ∨
      (6 ≤ p ∧ ∀ y', (∀ z ∈ C.set, y' < z.2) → y' < y) := by
  obtain ⟨hp, ht0, ht1, hmem, -⟩ := hA
  have hpy := hey _ hmem
  have hn : (C.sideWalk C.sideBeta).n = 2 * C.m + 7 := C.sideWalk_n _
  have htR := C.top_snd_lt_radius
  have hR := abs_lt.1 hyR
  rcases Nat.lt_or_ge p 6 with h6 | h6
  · rw [sidePt_small C h6, Geometry.lerp_snd] at hpy
    interval_cases p
    · rw [C.sideWalk_vtx_zero, C.sideWalk_vtx_one] at hpy
      sil only [Chain.slitTop] at hpy
    · rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hpy
      left; exact ⟨rfl, by sil only at hpy⟩
    · rw [C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hpy
      sil only at hpy
    · rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hpy
      right; left; exact ⟨rfl, by sil only at hpy⟩
    · rw [C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hpy
      sil only [Chain.slitTop] at hpy
    · rw [C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hpy
      sinl only [Chain.slitTop] at hpy
  · right; right
    refine ⟨h6, fun y' hy' => ?_⟩
    unfold sidePt at hpy
    rw [Geometry.lerp_snd] at hpy
    rcases Nat.lt_or_ge p (2 * C.m + 6) with h' | h'
    · rw [hn, Nat.mod_eq_of_lt (by omega)] at hpy
      have hu := hy' _ (tour_mem C h6 (by omega))
      have hv := hy' _ (tour_mem C (by omega : 6 ≤ p + 1) (by omega))
      rwnl [← hpy]
    · have hp' : p = 2 * C.m + 6 := by omega
      subst hp'
      rw [C.sideWalk_vtx_wrap, walk_last] at hpy
      simp [Chain.slitTop] at hpy
      have := hy' _ C.top_mem_set
      rwnl [← hpy]

/-! ## Records -/

variable {C : Chain} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- The equality of horizontal segments. -/
theorem hseg_eq {y u v y' a b : ℝ} (he : hseg y u v = hseg y' a b) (hab : a < b) :
    y = y' ∧ u = a ∧ v = b := by
  have ha : ((a, y') : Point) ∈ hseg y u v := by rw [he]; exact ⟨rfl, le_rfl, hab.le⟩
  have hb : ((b, y') : Point) ∈ hseg y u v := by rw [he]; exact ⟨rfl, hab.le, le_rfl⟩
  have hyy  := ha.1
  subst hyy
  have hu : ((u, y') : Point) ∈ hseg y' a b := by
    rw [← he]; exact ⟨rfl, le_rfl, le_trans ha.2.1 ha.2.2⟩
  have hv : ((v, y') : Point) ∈ hseg y' a b := by
    rw [← he]; exact ⟨rfl, le_trans ha.2.1 ha.2.2, le_rfl⟩
  exact ⟨rfl, le_antisymm ha.2.1 hu.2.1, le_antisymm hv.2.2 hb.2.2⟩

/-- The height facts of a chord of a valid list. -/
theorem rec_facts (hL : ChordTriplesOK (chainModel C) Q L) {x : ℕ × ℕ × ℕ} (hx : x ∈ L) :
    (∀ z ∈ (recOf x).toSet (chainModel C) Q, z.2 = (Q.vtx x.1).2) ∧
      |(Q.vtx x.1).2| < C.radius ∧ (Q.vtx x.1).2 ≤ C.top.2 ∧
      ∃ a b, IsHChordIn C.dom (Q.vtx x.1).2 a b ∧
        (recOf x).toSet (chainModel C) Q = hseg (Q.vtx x.1).2 a b := by
  obtain ⟨y', a, b, hh, hyt, e⟩ := hL.1.2.1 ⟨x, hx, rfl⟩
  have hmem := (hL.2.2.1 x hx).1.2.2.2.1
  have hmem' : sidePt (C.sideWalk C.sideBeta) (recOf x).lp
      ((chainModel C).param Q (recOf x).lpos) ∈ hseg y' a b := e ▸ hmem
  have hyy  := hmem.1.symm.trans hmem'.1
  rw [← hyy] at hh hyt e
  have hR : |(Q.vtx x.1).2| < C.radius := by
    have hm := hh.open_mem ((a + b) / 2) (by linarith [hh.lt]) (by linarith [hh.lt])
    exact (C.dom_subset_box hm).2
  exact ⟨fun z hz => hz.1, hR, hyt, a, b, hh, e⟩

theorem wall_x {p : ℕ} (hp : p = 1 ∨ p = 3) (t : ℝ) :
    (sidePt (C.sideWalk C.sideBeta) p t).1 = -C.radius ∨
      (sidePt (C.sideWalk C.sideBeta) p t).1 = C.radius := by
  rcases hp with rfl | rfl
  · left
    rw [sidePt_small C (by norm_num), Geometry.lerp_fst, C.sideWalk_vtx_one, C.sideWalk_vtx_two]
    ring
  · right
    rw [sidePt_small C (by norm_num), Geometry.lerp_fst, C.sideWalk_vtx_three,
      C.sideWalk_vtx_four]
    ring

/-- **A wall-to-wall record is the full-width chord.** -/
theorem wall_shape (hL : ChordTriplesOK (chainModel C) Q L) {x : ℕ × ℕ × ℕ} (hx : x ∈ L)
    (hw : WallRec x) :
    (recOf x).toSet (chainModel C) Q = hseg (Q.vtx x.1).2 (-C.radius) C.radius ∧
      IsHChordIn C.dom (Q.vtx x.1).2 (-C.radius) C.radius := by
  obtain ⟨-, -, -, a, b, hh, e⟩ := rec_facts hL hx
  have e' := e
  unfold CRec.toSet at e'
  obtain ⟨-, hu, hv⟩ := hseg_eq e' hh.lt
  have hR := C.radius_pos
  have h1 := wall_x (C := C) hw.1 ((chainModel C).param Q (recOf x).lpos)
  have h2 := wall_x (C := C) hw.2 ((chainModel C).param Q (recOf x).rpos)
  have hlt := hh.lt
  have hu' : ((chainModel C).pos Q (recOf x).lpos).1 = a := hu
  have hv' : ((chainModel C).pos Q (recOf x).rpos).1 = b := hv
  have hpl : (chainModel C).pos Q (recOf x).lpos =
      sidePt (C.sideWalk C.sideBeta) x.2.1 ((chainModel C).param Q (recOf x).lpos) := rfl
  have hpr : (chainModel C).pos Q (recOf x).rpos =
      sidePt (C.sideWalk C.sideBeta) x.2.2 ((chainModel C).param Q (recOf x).rpos) := rfl
  rw [hpl] at hu'
  rw [hpr] at hv'
  have ha : a = -C.radius := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  have hb : b = C.radius := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
  subst ha hb
  exact ⟨e, hh⟩

/-- A full-width chord lies below the chain. -/
theorem wall_below {y : ℝ} (hh : IsHChordIn C.dom y (-C.radius) C.radius) (hyt : y ≤ C.top.2) :
    ∀ z ∈ C.set, y < z.2 := by
  have hno : ∀ z ∈ C.set, z.2 ≠ y := by
    intro z hz hzy
    have hb := C.set_subset_box hz
    rw [mem_box_iff, abs_lt, abs_lt] at hb
    have hm := hh.open_mem z.1 hb.1.1 hb.1.2
    rw [← hzy] at hm
    exact C.not_mem_set_of_mem_dom hm hz
  exact chain_above C hno (lt_of_le_of_ne hyt (Ne.symm (hno _ C.top_mem_set)))

theorem famOf_mono {M : Model} {L₁ L₂ : List (ℕ × ℕ × ℕ)} (h : ∀ x ∈ L₁, x ∈ L₂) :
    famOf M Q L₁ ⊆ famOf M Q L₂ := by
  rintro c ⟨x, hx, rfl⟩; exact ⟨x, h x hx, rfl⟩

/-- **Dropping the wall-to-wall chords** (design finding M6): the chord family without its
wall-to-wall chords keeps the degree bound and is `2γ`-semigranular. -/
theorem drop_ok (hP : C.P.Simple) (hL : ChordTriplesOK (chainModel C) Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe (famOf (chainModel C) Q L) d)
    (hγ : (chainModel C).Semigranular (famOf (chainModel C) Q L) γ) :
    (chainModel C).DegLe (famOf (chainModel C) Q (dropWalls L)) d ∧
      (chainModel C).Semigranular (famOf (chainModel C) Q (dropWalls L)) (2 * γ) := by
  set M := chainModel C
  set F := famOf M Q L
  set F' := famOf M Q (dropWalls L)
  have hM  := walkAx_of_goodModel (Or.inl ⟨C, hP, rfl⟩)
  have hFA  := hL.1.2.1
  have hfin  := hL.1.1
  have hsub : F' ⊆ F := famOf_mono fun x hx => (mem_dropWalls.1 hx).1
  have hR := C.radius_pos
  by_cases hwall : ∃ x ∈ L, WallRec x
  swap
  · push Not at hwall
    have hLL : dropWalls L = L := by
      unfold dropWalls
      rw [filter_eq_self]
      intro x hx; simp [hwall x hx]
    have hFF : F' = F := by simp [F', F, hLL]
    rw [hFF]
    exact ⟨hd, fun U hU => (hγ U hU).trans (by omega)⟩
  -- the highest wall-to-wall chord
  obtain ⟨xs, ⟨hxsL, hxsw⟩, hxsmax⟩ := Set.exists_max_image {x | x ∈ L ∧ WallRec x}
    (fun x => (Q.vtx x.1).2) ((List.finite_toSet L).subset fun x hx => hx.1)
    (by obtain ⟨x, hx, hw⟩ := hwall; exact ⟨x, hx, hw⟩)
  set ys := (Q.vtx xs.1).2 with hysdef
  obtain ⟨-, hysR, hyst, -⟩ := rec_facts hL hxsL
  have hbelow  := wall_below (wall_shape hL hxsL hxsw).2 hyst
  -- heights of the kept chords
  have hkept : ∀ x ∈ dropWalls L, ys < (Q.vtx x.1).2 := by
    intro x hx
    obtain ⟨hxL, hxw⟩ := mem_dropWalls.1 hx
    obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL hxL
    obtain ⟨hl, hr⟩ := hL.2.2.1 x hxL
    have hthird : ∀ {p : ℕ} {t : ℝ}, SideAttach (C.sideWalk C.sideBeta)
        ((recOf x).toSet M Q) p t → p ≠ 1 → p ≠ 3 → ys < (Q.vtx x.1).2 := by
      intro p t hA h1 h3
      rcases cut_cases C hey hyR hyt hA with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h h1
      · exact absurd h h3
      · exact h ys hbelow
    unfold WallRec at hxw
    by_cases hlw : x.2.1 = 1 ∨ x.2.1 = 3
    · have hrw : ¬ (x.2.2 = 1 ∨ x.2.2 = 3) := fun h => hxw ⟨hlw, h⟩
      rw [not_or] at hrw
      exact hthird hr hrw.1 hrw.2
    · rw [not_or] at hlw
      exact hthird hl hlw.1 hlw.2
  -- the level `yp`
  set Hs : Finset ℝ := (Finset.range (C.m + 1)).image (fun k => (C.vertex k).2) ∪
    ((dropWalls L).map fun x => (Q.vtx x.1).2).toFinset with hHs
  have hHne : Hs.Nonempty := ⟨(C.vertex 0).2, Finset.mem_union_left _
    (Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩)⟩
  set yp := Hs.min' hHne with hyp
  have hyp_v : ∀ k, k ≤ C.m → yp ≤ (C.vertex k).2 := fun k hk =>
    Hs.min'_le _ (Finset.mem_union_left _ (Finset.mem_image.2
      ⟨k, Finset.mem_range.2 (by omega), rfl⟩))
  have hyp_k : ∀ x ∈ dropWalls L, yp ≤ (Q.vtx x.1).2 := fun x hx =>
    Hs.min'_le _ (Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hx)))
  have hlt : ys < yp := by
    obtain ⟨h, hmem, e⟩ : ∃ h ∈ Hs, h = yp := ⟨yp, Hs.min'_mem hHne, rfl⟩
    rw [← e]
    rcases Finset.mem_union.1 hmem with h1 | h1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h1
      exact hbelow _ (C.vertex_mem_set (by have := Finset.mem_range.1 hk; omega))
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 h1)
      exact hkept x hx
  have hypt : yp ≤ C.top.2 := hyp_v _ C.topIdx_le
  have htR := C.top_snd_lt_radius
  have hysR' := abs_lt.1 hysR
  refine ⟨?_, ?_⟩
  · -- degrees
    refine degLe_drop (hM.sys F hFA hfin) hfin hsub hR hysR'.1.le hlt
      (fun z hz => C.dom_subset_box hz) ?_ ?_ ?_ hd
    · intro z h1 h2 h3 h4
      refine (C.mem_dom_iff).2 ⟨⟨abs_lt.2 ⟨h1, h2⟩, abs_lt.2 ⟨h3, by linarith⟩⟩, fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨k, hk, hkz⟩ := vertex_below C hz
        linarith [hyp_v k hk]
      · have := (C.mem_slit_iff.1 hz).2.1
        linarith
    · rintro c ⟨x, hx, rfl⟩ z hz
      rw [(rec_facts hL (mem_dropWalls.1 hx).1).1 z hz]
      exact hyp_k x hx
    · rintro c ⟨x, hx, rfl⟩ hc' z hz
      rw [(rec_facts hL hx).1 z hz]
      by_cases hw : WallRec x
      · exact hxsmax x ⟨hx, hw⟩
      · exact absurd ⟨x, mem_dropWalls.2 ⟨hx, hw⟩, rfl⟩ hc'
  · -- weights
    set R := C.radius
    have h2R : 0 < 2 * R := by linarith
    refine semigranular_drop hM hFA hfin hsub (lo := 1 + (R - ys) / (2 * R))
      (hi := 3 + (ys + R) / (2 * R)) ?_ ?_ ?_ hγ
    · rintro k ⟨c, ⟨x, hx, rfl⟩, p, t, hA, rfl⟩
      by_cases hw : WallRec x
      · right
        obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL hx
        have hyx  := hxsmax x ⟨hx, hw⟩
        have ht1 := hA.2.2.1
        have hbx := wall_below (wall_shape hL hx hw).2 hyt
        rcases cut_cases C hey hyR hyt hA with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨-, h⟩
        · have : (R - ys) / (2 * R) ≤ t := by rwli [div_le_iff₀ h2R]
          have : (ys + R) / (2 * R) ≥ 0 := div_nonneg (by linarith) h2R.le
          push_cast; constructor <;> linarith
        · have : t ≤ (ys + R) / (2 * R) := by rwli [le_div_iff₀ h2R]
          have : (R - ys) / (2 * R) ≤ 1 := by rwli [div_le_iff₀ h2R]
          have := hA.2.1
          push_cast; constructor <;> linarith
        · exact absurd (h _ hbx) (lt_irrefl _)
      · left
        exact ⟨_, ⟨x, mem_dropWalls.2 ⟨hx, hw⟩, rfl⟩, p, t, hA, rfl⟩
    · rintro k ⟨c, ⟨x, hx, rfl⟩, p, t, hA, rfl⟩
      obtain ⟨hey, hyR, hyt, -⟩ := rec_facts hL (mem_dropWalls.1 hx).1
      have hyx  := hkept x hx
      have hkR : (ys + R) / (2 * R) < 1 := by rwli [div_lt_one h2R]
      have ht0 := hA.2.1
      rcases cut_cases C hey hyR hyt hA with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨h6, -⟩
      · left
        have : t < (R - ys) / (2 * R) := by rwli [lt_div_iff₀ h2R]
        pcl
      · right
        have : (ys + R) / (2 * R) < t := by rwli [div_lt_iff₀ h2R]
        pcl
      · right
        have : (6 : ℝ) ≤ p := by exact_mod_cast h6
        linarith
    · intro p hp
      have h6 : (6 : ℝ) ≤ p := by exact_mod_cast hp.1
      have hkR : (ys + R) / (2 * R) < 1 := by rwli [div_lt_one h2R]
      linarith

/-! ## Box transport (B3′) -/

/-- **Box transport of a chain chord list** (B3′ with the filter of finding M6).  For twin chains
of simple hosts and a valid chord list of `C` whose family has degree `≤ d` and is
`γ`-semigranular, the list without its wall-to-wall chords is valid for `C'`, and its family in
the model of `C'` has degree `≤ d` and is `2γ`-semigranular. -/
theorem boxTransport {C' : Chain} (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    (hL : ChordTriplesOK (chainModel C) Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe (famOf (chainModel C) Q L) d)
    (hγ : (chainModel C).Semigranular (famOf (chainModel C) Q L) γ) :
    ChordTriplesOK (chainModel C') Q (dropWalls L) ∧
      (chainModel C').DegLe (famOf (chainModel C') Q (dropWalls L)) d ∧
      (chainModel C').Semigranular (famOf (chainModel C') Q (dropWalls L)) (2 * γ) := by
  obtain ⟨hd', hγ'⟩ := drop_ok hP hL hd hγ
  exact transport h hP hP' (h.inBand_dropWalls hL) (chordTriplesOK_dropWalls hL) hd' hγ'

/-- The chord triples of a valid normal form are a valid chord list. -/
theorem chordTriplesOK_of_isNF {M : Model} {N : NF} (hN : IsNF M Q N) :
    ChordTriplesOK M Q (N.chords.map fun r => (r.h, r.lp, r.rp)) := by
  obtain ⟨hfam, hinj, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  have hF := F_eq_famOf (M := M) (Q := Q) (N := N) (L := N.chords.map fun r => (r.h, r.lp, r.rp))
    rfl
  have hget : ∀ i (hi : i < N.chords.length), N.chord i = N.chords[i] := fun i hi => by
    unfold NF.chord; rw [getD_eq_getElem _ _ hi]
  refine ⟨by have := hF ▸ hfam; exact this, ?_, ?_, ?_⟩
  · rw [map_map]
    rw [List.nodup_iff_injective_get]
    intro i j e
    simp [List.get_eq_getElem, getElem_map, Function.comp_apply] at e
    have hi := i.2; have hj := j.2
    simp [length_map] at hi hj
    have := hinj i j hi hj (by rw [hget i hi, hget j hj]; exact e)
    exact Fin.ext this
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have := hatt i hi
    rw [hget i hi] at this
    exact this
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have := hh i hi
    rw [hget i hi] at this
    exact this

/-- **Box transport of a normal form** (B3′, record form): the chord triples of a valid normal
form of `C` of degree `≤ d` that is `γ`-semigranular, without the wall-to-wall chords, are a
valid chord list of the twin chain `C'`, whose family has degree `≤ d` and is
`2γ`-semigranular. -/
theorem boxTransport_nf {C' : Chain} (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    {N : NF} (hN : IsNF (chainModel C) Q N) {d γ : ℕ}
    (hd : (chainModel C).DegLe (N.F (chainModel C) Q) d)
    (hγ : (chainModel C).Semigranular (N.F (chainModel C) Q) γ) :
    ChordTriplesOK (chainModel C') Q (dropWalls (N.chords.map fun r => (r.h, r.lp, r.rp))) ∧
      (chainModel C').DegLe
        (famOf (chainModel C') Q (dropWalls (N.chords.map fun r => (r.h, r.lp, r.rp)))) d ∧
      (chainModel C').Semigranular
        (famOf (chainModel C') Q (dropWalls (N.chords.map fun r => (r.h, r.lp, r.rp)))) (2 * γ) := by
  have hF := F_eq_famOf (M := chainModel C) (Q := Q) (N := N)
    (L := N.chords.map fun r => (r.h, r.lp, r.rp)) rfl
  rw [hF] at hd hγ
  exact boxTransport h hP hP' (chordTriplesOK_of_isNF hN) hd hγ

end

end BoxT

end Chazelle.Core
