module

public import Chazelle.Core.DownPhaseDegSeg

/-!
# Degree bound on host curves, part 2: the trapezoid with horizontal obstacles

For `GoodH` obstacles (horizontal segments and ties allowed) and a chord family containing the
vertex chords (`SegObs.FullAt`):

* `exists_trapH`: a domain point off the chords has trapezoid data (`SegObs.Trap`);
* `Trap.no_obsH`: no obstacle point lies strictly inside the corridor (a horizontal segment
  reaching into it would cross a wall inside the corridor, at a vertex);
* `Trap.top_sideH`: an obstacle point of the open top side is a vertex or lies on a horizontal
  segment (same at the bottom);
* `Trap.top_side_fullH`: a domain point of the open top side lies on a chord (it is seen from the
  first vertex towards the top vertex);
* `Trap.region_subsetH`: the region of the point lies in the open trapezoid.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace HSegObs

open SegObs

variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}

/-- **Every domain point off the chords has trapezoid data.** -/
theorem exists_trapH (hS : GoodH R S t) {G : Set (Set Point)} (hfull : FullAt R S G) {q : Point}
    (hq : q ∈ dom R S) (hqG : q ∉ ⋃₀ G) : ∃ sL sR y₁ y₂, Trap R S q sL sR y₁ y₂ := by
  obtain ⟨a, ha, hanot, hain⟩ := exists_hit_westH hS hq
  obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_eastH hS hq
  have hina : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rw [min_eq_left ha.le] at h1; rw [max_eq_right ha.le] at h2
    exact hain x h1 h2.le
  have hinb : ∀ x, min b q.1 < x → x < max b q.1 → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rw [min_eq_right hb.le] at h1; rw [max_eq_left hb.le] at h2
    exact hbin x h1.le h2
  obtain ⟨sL, hsL, hL1, hL2, hLx⟩ := hit_wall hS (hit_mem_obsH hS hq hanot hina)
    (hit_not_vert hfull hq hqG hina) ha.ne hina
  obtain ⟨sR, hsR, hR1, hR2, hRx⟩ := hit_wall hS (hit_mem_obsH hS hq hbnot hinb)
    (hit_not_vert hfull hq hqG hinb) hb.ne' hinb
  have hseg : ∀ x, a < x → x < b → ((x, q.2) : Point) ∈ dom R S := by
    intro x h1 h2
    rcases le_total x q.1 with h | h
    · exact hain x h1 h
    · exact hbin x h h2
  have hnoq : ∀ v, IsVert S v → v.2 = q.2 → a ≤ v.1 → v.1 ≤ b → False := by
    intro v hv hvq h1 h2
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · have := hseg v.1 h1 h2
        rw [show ((v.1, q.2) : Point) = v from point_ext rfl hvq.symm] at this
        exact this.2 (vert_mem_obs hv)
      · exact hit_not_vert hfull hq hqG hinb
          (by rwa [show ((b, q.2) : Point) = v from point_ext h2.symm hvq.symm])
    · exact hit_not_vert hfull hq hqG hina
        (by rwa [show ((a, q.2) : Point) = v from point_ext h1 hvq.symm])
  have hV := finite_vertsH hS
  have hup : sL.1.2 < sL.2.2 := hL1.trans hL2
  have hupR : sR.1.2 < sR.2.2 := hR1.trans hR2
  set C₂ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ q.2 < y ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.2.2, sR.2.2}
  have hC₂f : C₂.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine (hV.image fun v => v.2).subset ?_
    rintro y ⟨v, hv, rfl, -⟩
    exact ⟨v, hv, rfl⟩
  obtain ⟨y₂, hy₂C, hmin⟩ := Set.exists_min_image C₂ id hC₂f ⟨sL.2.2, Or.inr (Or.inl rfl)⟩
  have hall₂ : ∀ y ∈ C₂, q.2 < y := by
    rintro y (⟨v, -, rfl, h, -⟩ | h)
    · exact h
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact hL2
      · exact hR2
  set C₁ : Set ℝ := {y | ∃ v, IsVert S v ∧ v.2 = y ∧ y < q.2 ∧ xAt sL y ≤ v.1 ∧ v.1 ≤ xAt sR y} ∪
    {sL.1.2, sR.1.2}
  have hC₁f : C₁.Finite := by
    refine Set.Finite.union ?_ ((finite_singleton _).insert _)
    refine (hV.image fun v => v.2).subset ?_
    rintro y ⟨v, hv, rfl, -⟩
    exact ⟨v, hv, rfl⟩
  obtain ⟨y₁, hy₁C, hmax⟩ := Set.exists_max_image C₁ id hC₁f ⟨sL.1.2, Or.inr (Or.inl rfl)⟩
  have hall₁ : ∀ y ∈ C₁, y < q.2 := by
    rintro y (⟨v, -, rfl, h, -⟩ | h)
    · exact h
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact hL1
      · exact hR1
  refine ⟨sL, sR, y₁, y₂, ⟨hsL, hsR, by rwa [← hLx], by rwa [← hRx],
    by rwa [← hLx, ← hRx], hall₁ _ hy₁C, hall₂ _ hy₂C,
    hmax _ (Or.inr (Or.inl rfl)), hmax _ (Or.inr (Or.inr rfl)),
    hmin _ (Or.inr (Or.inl rfl)), hmin _ (Or.inr (Or.inr rfl)), ?_, ?_, ?_⟩⟩
  · intro v hv h1 h2 h3 h4
    rcases lt_trichotomy v.2 q.2 with hlt | heq | hgt
    · have := hmax _ (Or.inl ⟨v, hv, rfl, hlt, h3, h4⟩)
      simp only [id] at this
      linarith
    · rw [heq, ← hLx] at h3
      rw [heq, ← hRx] at h4
      exact hnoq v hv heq h3 h4
    · have := hmin _ (Or.inl ⟨v, hv, rfl, hgt, h3, h4⟩)
      simp only [id] at this
      linarith
  · rcases hy₂C with ⟨v, hv, hvy, -, h3, h4⟩ | h
    · exact ⟨v, hv, hvy, fun _ => ⟨hvy ▸ h3, hvy ▸ h4⟩⟩
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact ⟨sL.2, ⟨sL, hsL, Or.inr rfl⟩, rfl, fun hle => ⟨by rw [xAt_hi hup],
          by rwa [← xAt_hi hup]⟩⟩
      · exact ⟨sR.2, ⟨sR, hsR, Or.inr rfl⟩, rfl, fun hle => ⟨by rwa [← xAt_hi hupR],
          by rw [xAt_hi hupR]⟩⟩
  · rcases hy₁C with ⟨v, hv, hvy, -, h3, h4⟩ | h
    · exact ⟨v, hv, hvy, fun _ => ⟨hvy ▸ h3, hvy ▸ h4⟩⟩
    · simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact ⟨sL.1, ⟨sL, hsL, Or.inl rfl⟩, rfl, fun hle => ⟨by rw [xAt_lo],
          by rwa [← xAt_lo sL]⟩⟩
      · exact ⟨sR.1, ⟨sR, hsR, Or.inl rfl⟩, rfl, fun hle => ⟨by rwa [← xAt_lo sR],
          by rw [xAt_lo]⟩⟩

end HSegObs

namespace SegObs

namespace Trap

open HSegObs

variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}
variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

theorem upL (h : Trap R S q sL sR y₁ y₂) : sL.1.2 < sL.2.2 :=
  lt_of_le_of_lt h.botL (h.y₁_lt_y₂.trans_le h.topL)

theorem upR (h : Trap R S q sL sR y₁ y₂) : sR.1.2 < sR.2.2 :=
  lt_of_le_of_lt h.botR (h.y₁_lt_y₂.trans_le h.topR)

theorem memLH (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sL p.2) : p ∈ obs S :=
  seg_subset_obs h.hL ((mem_seg_iff h.upL).2 ⟨h.botL.trans h1, h2.trans h.topL, hx⟩)

theorem memRH (h : Trap R S q sL sR y₁ y₂) {p : Point} (h1 : y₁ ≤ p.2)
    (h2 : p.2 ≤ y₂) (hx : p.1 = xAt sR p.2) : p ∈ obs S :=
  seg_subset_obs h.hR ((mem_seg_iff h.upR).2 ⟨h.botR.trans h1, h2.trans h.topR, hx⟩)

/-- **The walls do not cross** strictly between the heights. -/
theorem walls_ltH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {y : ℝ} (h1 : y₁ < y)
    (h2 : y < y₂) : xAt sL y < xAt sR y := by
  by_contra hle
  push Not at hle
  have hne : sL ≠ sR := by
    intro e; rw [e] at h; exact lt_irrefl _ (h.lt_q.trans h.q_lt)
  obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt sL y)
    ((continuous_xAt sR).sub (continuous_xAt sL)) (a := q.2) (b := y)
    (show (0 : ℝ) < xAt sR q.2 - xAt sL q.2 by have := h.lt_q; have := h.q_lt; linarith)
    (show xAt sR y - xAt sL y ≤ 0 by linarith)
  have hc1' : y₁ < c := lt_of_lt_of_le (lt_min h.bot_lt h1) hc1
  have hc2' : c < y₂ := lt_of_le_of_lt hc2 (max_lt h.lt_top h2)
  have hmL : ((xAt sL c, c) : Point) ∈ seg sL :=
    pt_mem_seg h.upL (h.botL.trans hc1'.le) (hc2'.le.trans h.topL)
  have hmR : ((xAt sL c, c) : Point) ∈ seg sR := by
    rw [show xAt sL c = xAt sR c by linarith]
    exact pt_mem_seg h.upR (h.botR.trans hc1'.le) (hc2'.le.trans h.topR)
  exact h.no_vertex _ (hS.cross sL h.hL sR h.hR hne _ hmL hmR) hc1' hc2' le_rfl
    (show xAt sL c ≤ xAt sR c by linarith)

/-- **No obstacle point strictly inside the corridor.** -/
theorem no_obsH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {p : Point} (hp : p ∈ obs S)
    (h1 : y₁ < p.2) (h2 : p.2 < y₂) (h3 : xAt sL p.2 < p.1) (h4 : p.1 < xAt sR p.2) : False := by
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hp
  rcases (hS.le s hs).lt_or_eq with hsu | hf
  · obtain ⟨hp1, hp2, hpx⟩ := (mem_seg_iff hsu).1 hps
    obtain ⟨y', hy'1, hy'2, hb1, hb2, hcases⟩ := exists_clamp (q := q.2) hp1 hp2
    have hy'in1 : y₁ < y' := lt_of_lt_of_le (lt_min h1 h.bot_lt) hb1
    have hy'in2 : y' < y₂ := lt_of_le_of_lt hb2 (max_lt h2 h.lt_top)
    have hp' : ((xAt s y', y') : Point) ∈ seg s := pt_mem_seg hsu hy'1 hy'2
    by_cases hin : xAt sL y' < xAt s y' ∧ xAt s y' < xAt sR y'
    · rcases hcases with he | he | he
      · have := h.hseg (xAt s y') (he ▸ hin.1) (he ▸ hin.2)
        rw [← he] at this
        exact this.2 (seg_subset_obs hs hp')
      · exact h.no_vertex _ ⟨s, hs, Or.inl (eq_lo hsu hp' he)⟩ hy'in1 hy'in2 hin.1.le hin.2.le
      · exact h.no_vertex _ ⟨s, hs, Or.inr (eq_hi hsu hp' he)⟩ hy'in1 hy'in2 hin.1.le hin.2.le
    · rw [not_and_or, not_lt, not_lt] at hin
      rcases hin with hle | hge
      · have hne : s ≠ sL := by
          intro e; subst e; linarith
        obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt s y - xAt sL y)
          ((continuous_xAt s).sub (continuous_xAt sL)) (a := p.2) (b := y')
          (show (0 : ℝ) < xAt s p.2 - xAt sL p.2 by linarith)
          (show xAt s y' - xAt sL y' ≤ 0 by linarith)
        have hc1' : y₁ < c := lt_of_lt_of_le (lt_min h1 hy'in1) hc1
        have hc2' : c < y₂ := lt_of_le_of_lt hc2 (max_lt h2 hy'in2)
        have hcs1 : s.1.2 ≤ c := le_trans (le_min hp1 hy'1) hc1
        have hcs2 : c ≤ s.2.2 := le_trans hc2 (max_le hp2 hy'2)
        have hmS : ((xAt sL c, c) : Point) ∈ seg s := by
          rw [show xAt sL c = xAt s c by linarith]
          exact pt_mem_seg hsu hcs1 hcs2
        have hmL : ((xAt sL c, c) : Point) ∈ seg sL :=
          pt_mem_seg h.upL (h.botL.trans hc1'.le) (hc2'.le.trans h.topL)
        exact h.no_vertex _ (hS.cross s hs sL h.hL hne _ hmS hmL) hc1' hc2' le_rfl
          (h.walls_ltH hS hc1' hc2').le
      · have hne : s ≠ sR := by
          intro e; subst e; linarith
        obtain ⟨c, hc, hc1, hc2, -⟩ := exists_zero_between (f := fun y => xAt sR y - xAt s y)
          ((continuous_xAt sR).sub (continuous_xAt s)) (a := p.2) (b := y')
          (show (0 : ℝ) < xAt sR p.2 - xAt s p.2 by linarith)
          (show xAt sR y' - xAt s y' ≤ 0 by linarith)
        have hc1' : y₁ < c := lt_of_lt_of_le (lt_min h1 hy'in1) hc1
        have hc2' : c < y₂ := lt_of_le_of_lt hc2 (max_lt h2 hy'in2)
        have hcs1 : s.1.2 ≤ c := le_trans (le_min hp1 hy'1) hc1
        have hcs2 : c ≤ s.2.2 := le_trans hc2 (max_le hp2 hy'2)
        have hmS : ((xAt sR c, c) : Point) ∈ seg s := by
          rw [show xAt sR c = xAt s c by linarith]
          exact pt_mem_seg hsu hcs1 hcs2
        have hmR : ((xAt sR c, c) : Point) ∈ seg sR :=
          pt_mem_seg h.upR (h.botR.trans hc1'.le) (hc2'.le.trans h.topR)
        exact h.no_vertex _ (hS.cross s hs sR h.hR hne _ hmS hmR) hc1' hc2'
          (h.walls_ltH hS hc1' hc2').le le_rfl
  · -- a horizontal segment at the height of `p`
    obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hps
    have hwl := h.walls_ltH hS h1 h2
    have e1 : IsVert S ((s.1.1, p.2) : Point) := ⟨s, hs, Or.inl (point_ext rfl hy)⟩
    have e2 : IsVert S ((s.2.1, p.2) : Point) :=
      ⟨s, hs, Or.inr (point_ext rfl (hy.trans hf))⟩
    have out : ∀ x, x = s.1.1 ∨ x = s.2.1 → x < xAt sL p.2 ∨ xAt sR p.2 < x := by
      rintro x hx
      by_contra hc
      push Not at hc
      rcases hx with rfl | rfl
      · exact h.no_vertex _ e1 h1 h2 hc.1 hc.2
      · exact h.no_vertex _ e2 h1 h2 hc.1 hc.2
    have hlo : min s.1.1 s.2.1 < xAt sL p.2 := by
      rcases min_choice s.1.1 s.2.1 with e | e <;> rw [e] <;> rw [e] at hmin
      · rcases out _ (Or.inl rfl) with o | o
        · exact o
        · linarith
      · rcases out _ (Or.inr rfl) with o | o
        · exact o
        · linarith
    have hhi : xAt sR p.2 < max s.1.1 s.2.1 := by
      rcases max_choice s.1.1 s.2.1 with e | e <;> rw [e] <;> rw [e] at hmax
      · rcases out _ (Or.inl rfl) with o | o
        · linarith
        · exact o
      · rcases out _ (Or.inr rfl) with o | o
        · linarith
        · exact o
    have hne : s ≠ sL := by
      intro e; rw [e] at hf; exact absurd hf h.upL.ne
    have hmS : ((xAt sL p.2, p.2) : Point) ∈ seg s :=
      (mem_seg_flat hf).2 ⟨hy, hlo.le, by linarith⟩
    have hmL : ((xAt sL p.2, p.2) : Point) ∈ seg sL :=
      pt_mem_seg h.upL (h.botL.trans h1.le) (h2.le.trans h.topL)
    exact h.no_vertex _ (hS.cross s hs sL h.hL hne _ hmS hmL) h1 h2 le_rfl hwl.le

/-- The trapezoid lies in the domain. -/
theorem tr_subset_domH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) :
    tr sL sR y₁ y₂ ⊆ dom R S := by
  rintro p ⟨h1, h2, h3, h4⟩
  have hlo := (abs_le.1 (hS.inbox sL h.hL _ (lo_mem_seg sL)).2).1
  have hhi := (abs_le.1 (hS.inbox sL h.hL _ (hi_mem_seg sL)).2).2
  have hL := (abs_le.1 (abs_xAt_leH hS h.hL h.upL (h.botL.trans h1.le) (h2.le.trans h.topL))).1
  have hR := (abs_le.1 (abs_xAt_leH hS h.hR h.upR (h.botR.trans h1.le) (h2.le.trans h.topR))).2
  have hbL := h.botL
  have htL := h.topL
  refine ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩,
    fun hp => h.no_obsH hS hp h1 h2 h3 h4⟩

/-- **An obstacle point of the open top side is a vertex or lies on a horizontal segment.** -/
theorem top_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₂) (h3 : xAt sL y₂ < w.1) (h4 : w.1 < xAt sR y₂) :
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s := by
  obtain ⟨s, hs, hws⟩ := mem_iUnion₂.1 hw
  rcases (hS.le s hs).lt_or_eq with hsu | hf
  · by_cases hv : IsVert S w
    · exact Or.inl hv
    obtain ⟨hs1, hs2, hsx⟩ := (mem_seg_iff hsu).1 hws
    have hs1' : s.1.2 < w.2 := lt_of_le_of_ne hs1 fun e => hv ⟨s, hs, Or.inl (eq_lo hsu hws e.symm)⟩
    have hs2' : w.2 < s.2.2 := lt_of_le_of_ne hs2 fun e => hv ⟨s, hs, Or.inr (eq_hi hsu hws e)⟩
    rw [hwy] at hs1' hs2' hsx
    exfalso
    have hev : ∀ᶠ y in 𝓝 y₂, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
      ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
        (by rwa [← hsx])).and
      ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
        (by rwa [← hsx]))
    have hlt : max y₁ s.1.2 < y₂ := max_lt h.y₁_lt_y₂ hs1'
    have e1 : ∀ᶠ y in 𝓝[<] y₂, y ∈ Ioo (max y₁ s.1.2) y₂ := Ioo_mem_nhdsLT hlt
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
    exact h.no_obsH hS (seg_subset_obs hs (pt_mem_seg hsu (le_of_max_le_right hy1.le)
      (hy2.le.trans hs2'.le))) (lt_of_le_of_lt (le_max_left _ _) hy1) hy2 hy3 hy4
  · exact Or.inr ⟨s, hs, hf, hws⟩

/-- **An obstacle point of the open bottom side is a vertex or lies on a horizontal segment.** -/
theorem bot_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {w : Point}
    (hw : w ∈ obs S) (hwy : w.2 = y₁) (h3 : xAt sL y₁ < w.1) (h4 : w.1 < xAt sR y₁) :
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s := by
  obtain ⟨s, hs, hws⟩ := mem_iUnion₂.1 hw
  rcases (hS.le s hs).lt_or_eq with hsu | hf
  · by_cases hv : IsVert S w
    · exact Or.inl hv
    obtain ⟨hs1, hs2, hsx⟩ := (mem_seg_iff hsu).1 hws
    have hs1' : s.1.2 < w.2 := lt_of_le_of_ne hs1 fun e => hv ⟨s, hs, Or.inl (eq_lo hsu hws e.symm)⟩
    have hs2' : w.2 < s.2.2 := lt_of_le_of_ne hs2 fun e => hv ⟨s, hs, Or.inr (eq_hi hsu hws e)⟩
    rw [hwy] at hs1' hs2' hsx
    exfalso
    have hev : ∀ᶠ y in 𝓝 y₁, xAt sL y < xAt s y ∧ xAt s y < xAt sR y :=
      ((continuous_xAt sL).continuousAt.eventually_lt (continuous_xAt s).continuousAt
        (by rwa [← hsx])).and
      ((continuous_xAt s).continuousAt.eventually_lt (continuous_xAt sR).continuousAt
        (by rwa [← hsx]))
    have hlt : y₁ < min y₂ s.2.2 := lt_min h.y₁_lt_y₂ hs2'
    have e1 : ∀ᶠ y in 𝓝[>] y₁, y ∈ Ioo y₁ (min y₂ s.2.2) := Ioo_mem_nhdsGT hlt
    obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := (e1.and (nhdsWithin_le_nhds hev)).exists
    exact h.no_obsH hS (seg_subset_obs hs (pt_mem_seg hsu (hs1'.le.trans hy1.le)
      (le_of_lt (lt_of_lt_of_le hy2 (min_le_right _ _))))) hy1
      (lt_of_lt_of_le hy2 (min_le_left _ _)) hy3 hy4
  · exact Or.inr ⟨s, hs, hf, hws⟩

end Trap

end SegObs

end

end Chazelle.Core
