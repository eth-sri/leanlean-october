module

public import Chazelle.Core.DownPhaseDegTrap

/-!
# Degree bound on host curves, part 3: the horizontal sides of the trapezoid

At a side height `Y` of the trapezoid whose open side carries only vertices and points of
horizontal segments as obstacle points (`SideOK`):

* `Trap.vert_between`: between two domain points of the open side that are not joined through
  the domain lies a vertex;
* `Trap.side_full`: a domain point of the open side lies on a chord of `G` (seen from the first
  vertex towards a vertex of the closed side);
* `Trap.ncard_sideH`: at most `t + 1` chords of the domain touch the closed side (distinct chords
  are separated by vertices, at most `t` at that height);
* `Trap.region_subsetH`: the region of `q` lies in its trapezoid.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace SegObs

namespace Trap

open HSegObs

variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}
variable {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

/-- The obstacle points of the open side at height `Y` are vertices or points of horizontal
segments. -/
def SideOK (S : Set (Point × Point)) (sL sR : Point × Point) (Y : ℝ) : Prop :=
  ∀ w ∈ obs S, w.2 = Y → xAt sL Y < w.1 → w.1 < xAt sR Y →
    IsVert S w ∨ ∃ s ∈ S, s.1.2 = s.2.2 ∧ w ∈ seg s

theorem sideOK_top (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) : SideOK S sL sR y₂ :=
  fun _ hw hwy h3 h4 => h.top_sideH hS hw hwy h3 h4

theorem sideOK_bot (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) : SideOK S sL sR y₁ :=
  fun _ hw hwy h3 h4 => h.bot_sideH hS hw hwy h3 h4

/-- The lower end of a horizontal segment containing a point of the line of a domain point, on
the side away from it, is a vertex between them. -/
theorem flat_vertex {s : Point × Point} (hs : s ∈ S) (hf : s.1.2 = s.2.2) {w z : Point}
    (hws : w ∈ seg s) (hz : z ∉ obs S) (hzy : z.2 = w.2) (hzw : z.1 < w.1) :
    ∃ v, IsVert S v ∧ v.2 = w.2 ∧ z.1 < v.1 ∧ v.1 ≤ w.1 := by
  obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hws
  have hzmin : z.1 < min s.1.1 s.2.1 := by
    by_contra hc
    push Not at hc
    exact hz (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hzy.trans hy, hc, by linarith⟩))
  rcases min_choice s.1.1 s.2.1 with e | e <;> rw [e] at hzmin hmin
  · exact ⟨s.1, ⟨s, hs, Or.inl rfl⟩, hy.symm, hzmin, hmin⟩
  · exact ⟨s.2, ⟨s, hs, Or.inr rfl⟩, (hy.trans hf).symm, hzmin, hmin⟩

/-- The mirror image of `flat_vertex`. -/
theorem flat_vertex' {s : Point × Point} (hs : s ∈ S) (hf : s.1.2 = s.2.2) {w z : Point}
    (hws : w ∈ seg s) (hz : z ∉ obs S) (hzy : z.2 = w.2) (hzw : w.1 < z.1) :
    ∃ v, IsVert S v ∧ v.2 = w.2 ∧ w.1 ≤ v.1 ∧ v.1 < z.1 := by
  obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hws
  have hzmax : max s.1.1 s.2.1 < z.1 := by
    by_contra hc
    push Not at hc
    exact hz (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hzy.trans hy, by linarith, hc⟩))
  rcases max_choice s.1.1 s.2.1 with e | e <;> rw [e] at hzmax hmax
  · exact ⟨s.1, ⟨s, hs, Or.inl rfl⟩, hy.symm, hmax, hzmax⟩
  · exact ⟨s.2, ⟨s, hs, Or.inr rfl⟩, (hy.trans hf).symm, hmax, hzmax⟩

/-- **A vertex between two domain points of the open side** separated by an obstacle point. -/
theorem vert_between (_hS : GoodH R S t) {Y : ℝ} (hside : SideOK S sL sR Y) {z z' : Point}
    (hz : z ∈ dom R S) (hz' : z' ∈ dom R S) (hzy : z.2 = Y) (_hz'y : z'.2 = Y)
    (hzL : xAt sL Y < z.1) (hz'R : z'.1 < xAt sR Y) {s₀ : ℝ} (hs : z.1 < s₀) (hs' : s₀ < z'.1)
    (hnot : ((s₀, Y) : Point) ∉ dom R S) :
    ∃ v, IsVert S v ∧ v.2 = Y ∧ z.1 < v.1 ∧ v.1 < z'.1 := by
  have hb1 := abs_lt.1 (box_of_dom hz).1
  have hb2 := abs_lt.1 (box_of_dom hz').1
  have hYR : |Y| < R := hzy ▸ (box_of_dom hz).2
  have hw : ((s₀, Y) : Point) ∈ obs S := by
    by_contra hc
    exact hnot ⟨⟨abs_lt.2 ⟨by linarith, by linarith⟩, hYR⟩, hc⟩
  rcases hside _ hw rfl (by simp only; linarith) (by simp only; linarith) with hv | ⟨s, hs1, hf, hws⟩
  · exact ⟨_, hv, rfl, hs, hs'⟩
  · obtain ⟨v, hv, hvy, h1, h2⟩ := flat_vertex hs1 hf hws hz.2 hzy hs
    exact ⟨v, hv, hvy, h1, lt_of_le_of_lt h2 hs'⟩

/-- **A domain point of the open side lies on a chord**, given a vertex of the closed side. -/
theorem side_full (hS : GoodH R S t) (_h : Trap R S q sL sR y₁ y₂) {G : Set (Set Point)}
    (hfull : FullAt R S G) {Y : ℝ} (_hY1 : y₁ ≤ Y) (_hY2 : Y ≤ y₂) (hside : SideOK S sL sR Y)
    {v : Point} (hv : IsVert S v) (hvY : v.2 = Y) (hvL : xAt sL Y ≤ v.1) (hvR : v.1 ≤ xAt sR Y)
    {p : Point} (hp : p ∈ dom R S) (hpy : p.2 = Y) (h3 : xAt sL Y < p.1)
    (h4 : p.1 < xAt sR Y) : p ∈ ⋃₀ G := by
  have hvD : v ∉ dom R S := fun hm => hm.2 (vert_mem_obs hv)
  have hpv : p.1 ≠ v.1 := fun e => hvD (by
    rw [show v = p from point_ext e.symm (hvY.trans hpy.symm)]; exact hp)
  have hYR : |Y| < R := hpy ▸ (box_of_dom hp).2
  rcases lt_or_gt_of_ne hpv with hlt | hgt
  · obtain ⟨b, hb, hbnot, hbin⟩ := exists_hit_eastH hS hp
    have hinb : ∀ x, min b p.1 < x → x < max b p.1 → ((x, p.2) : Point) ∈ dom R S := by
      intro x h1 h2
      rw [min_eq_right hb.le] at h1; rw [max_eq_left hb.le] at h2
      exact hbin x h1.le h2
    have hbv : b ≤ v.1 := by
      by_contra hc
      push Not at hc
      have := hbin v.1 hlt.le hc
      rw [show ((v.1, p.2) : Point) = v from point_ext rfl (hpy.trans hvY.symm)] at this
      exact hvD this
    have hw := hit_mem_obsH hS hp hbnot hinb
    have hwv : IsVert S ((b, p.2) : Point) := by
      rcases lt_or_eq_of_le (show b ≤ xAt sR Y from hbv.trans hvR) with hbR | hbR
      · rcases hside _ hw hpy (by simp only; linarith) hbR with hv' | ⟨s, hs1, hf, hws⟩
        · exact hv'
        · obtain ⟨u, hu, huy, hu1, hu2⟩ := flat_vertex hs1 hf hws hp.2 rfl hb
          rcases hu2.lt_or_eq with hu2 | hu2
          · exfalso
            have := hbin u.1 hu1.le hu2
            rw [show ((u.1, p.2) : Point) = u from point_ext rfl huy.symm] at this
            exact this.2 (vert_mem_obs hu)
          · rw [show ((b, p.2) : Point) = u from point_ext hu2.symm huy.symm]; exact hu
      · have hbv' : b = v.1 := le_antisymm hbv (hbR ▸ hvR)
        rw [show ((b, p.2) : Point) = v from point_ext hbv' (hpy.trans hvY.symm)]; exact hv
    exact hfull _ hwv (by simp only; rw [hpy]; exact hYR) p hp rfl (fun x h1 h2 => by
      rw [min_eq_right hb.le] at h1; rw [max_eq_left hb.le] at h2
      exact hbin x h1.le h2)
  · obtain ⟨a, ha, hanot, hain⟩ := exists_hit_westH hS hp
    have hina : ∀ x, min a p.1 < x → x < max a p.1 → ((x, p.2) : Point) ∈ dom R S := by
      intro x h1 h2
      rw [min_eq_left ha.le] at h1; rw [max_eq_right ha.le] at h2
      exact hain x h1 h2.le
    have hav : v.1 ≤ a := by
      by_contra hc
      push Not at hc
      have := hain v.1 hc hgt.le
      rw [show ((v.1, p.2) : Point) = v from point_ext rfl (hpy.trans hvY.symm)] at this
      exact hvD this
    have hw := hit_mem_obsH hS hp hanot hina
    have hwv : IsVert S ((a, p.2) : Point) := by
      rcases lt_or_eq_of_le (show xAt sL Y ≤ a from hvL.trans hav) with haL | haL
      · rcases hside _ hw hpy haL (by simp only; linarith) with hv' | ⟨s, hs1, hf, hws⟩
        · exact hv'
        · obtain ⟨u, hu, huy, hu1, hu2⟩ := flat_vertex' hs1 hf hws hp.2 rfl ha
          rcases hu1.lt_or_eq with hu1 | hu1
          · exfalso
            have := hain u.1 hu1 hu2.le
            rw [show ((u.1, p.2) : Point) = u from point_ext rfl huy.symm] at this
            exact this.2 (vert_mem_obs hu)
          · rw [show ((a, p.2) : Point) = u from point_ext hu1 huy.symm]; exact hu
      · have hav' : a = v.1 := le_antisymm (haL ▸ hvL) hav
        rw [show ((a, p.2) : Point) = v from point_ext hav' (hpy.trans hvY.symm)]; exact hv
    exact hfull _ hwv (by simp only; rw [hpy]; exact hYR) p hp rfl (fun x h1 h2 => by
      rw [min_eq_left ha.le] at h1; rw [max_eq_right ha.le] at h2
      exact hain x h1 h2.le)

/-- **The region of `q` lies in its trapezoid.** -/
theorem region_subsetH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {G : Set (Set Point)}
    (hfull : FullAt R S G) (hq : q ∈ freeIn (dom R S) G) :
    connectedComponentIn (freeIn (dom R S) G) q ⊆ tr sL sR y₁ y₂ := by
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset (isOpen_tr _ _ _ _)
    ⟨q, mem_connectedComponentIn hq, h.q_mem⟩ ?_
  rintro p ⟨hpc, hpU⟩
  have hpf : p ∈ freeIn (dom R S) G := connectedComponentIn_subset _ _ hpU
  obtain ⟨hp1, hp2, hp3, hp4⟩ := closure_tr_subset _ _ _ _ hpc
  have hpD : p ∈ dom R S := hpf.1
  have hpG : p ∉ ⋃₀ G := hpf.2
  have hx3 : xAt sL p.2 < p.1 := lt_of_le_of_ne hp3 fun e => hpD.2 (h.memLH hp1 hp2 e.symm)
  have hx4 : p.1 < xAt sR p.2 := lt_of_le_of_ne hp4 fun e => hpD.2 (h.memRH hp1 hp2 e)
  refine ⟨lt_of_le_of_ne hp1 fun e => ?_, lt_of_le_of_ne hp2 fun e => ?_, hx3, hx4⟩
  · obtain ⟨v, hv, hvy, hvx⟩ := h.bot_vertex
    rw [← e] at hx3 hx4
    obtain ⟨hv1, hv2⟩ := hvx (by linarith)
    exact hpG (h.side_full hS hfull le_rfl h.y₁_lt_y₂.le (sideOK_bot hS h) hv hvy hv1 hv2 hpD
      e.symm hx3 hx4)
  · obtain ⟨v, hv, hvy, hvx⟩ := h.top_vertex
    rw [e] at hx3 hx4
    obtain ⟨hv1, hv2⟩ := hvx (by linarith)
    exact hpG (h.side_full hS hfull h.y₁_lt_y₂.le le_rfl (sideOK_top hS h) hv hvy hv1 hv2 hpD
      e hx3 hx4)

/-- **At most `t + 1` chords touch the closed side at height `Y`.** -/
theorem ncard_sideH (hS : GoodH R S t) (h : Trap R S q sL sR y₁ y₂) {Y : ℝ} (hY1 : y₁ ≤ Y)
    (hY2 : Y ≤ y₂) (hside : SideOK S sL sR Y) {E : Set (Set Point)}
    (hE : ∀ c ∈ E, HCD (dom R S) c ∧ ∃ z ∈ c, z ∈ dom R S ∧ z.2 = Y ∧
      xAt sL Y ≤ z.1 ∧ z.1 ≤ xAt sR Y) : E.ncard ≤ t + 1 := by
  classical
  by_cases hne : E.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, ncard_empty]; omega
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨-, z₀, -, hz₀D, hz₀y, -⟩ := hE c₀ hc₀
  have hYR : |Y| < R := hz₀y ▸ (box_of_dom hz₀D).2
  have hstrict : ∀ w : Point, w ∈ dom R S → w.2 = Y → xAt sL Y ≤ w.1 → w.1 ≤ xAt sR Y →
      xAt sL Y < w.1 ∧ w.1 < xAt sR Y := by
    intro w hw hwy h1 h2
    refine ⟨lt_of_le_of_ne h1 fun e => hw.2 (h.memLH (hwy ▸ hY1) (hwy ▸ hY2) ?_),
      lt_of_le_of_ne h2 fun e => hw.2 (h.memRH (hwy ▸ hY1) (hwy ▸ hY2) ?_)⟩
    · rw [hwy]; exact e.symm
    · rw [hwy]; exact e
  -- the chosen point of each chord
  let zc : Set Point → Point := fun c =>
    if hc : c ∈ E then Classical.choose (hE c hc).2 else (0, 0)
  have hzc : ∀ c ∈ E, zc c ∈ c ∧ zc c ∈ dom R S ∧ (zc c).2 = Y ∧
      xAt sL Y ≤ (zc c).1 ∧ (zc c).1 ≤ xAt sR Y := fun c hc => by
    simp only [zc, dite_eq_left hc]
    exact Classical.choose_spec (hE c hc).2
  set V := {v | IsVert S v ∧ v.2 = Y} with hV
  have hVf : V.Finite := (finite_vertsH hS).subset fun v hv => hv.1
  let g : Set Point → ℕ := fun c => {v | v ∈ V ∧ v.1 < (zc c).1}.ncard
  have hgle : ∀ c, g c ≤ t := fun c =>
    (ncard_le_ncard (fun v hv => hv.1) hVf).trans (hS.tmany Y hYR)
  -- the key: chords with points in order are separated by a vertex
  have hlt : ∀ c ∈ E, ∀ c' ∈ E, c ≠ c' → (zc c).1 < (zc c').1 → g c < g c' := by
    intro c hc c' hc' hcc' hlt
    obtain ⟨hz, hzD, hzy, hzx⟩ := hzc c hc
    obtain ⟨hz', hz'D, hz'y, hz'x⟩ := hzc c' hc'
    obtain ⟨y, a, b, hh, hceq⟩ := (hE c hc).1
    have hzc1 : zc c ∈ Visibility.hseg y a b := hceq ▸ hz
    have hy : y = Y := by rw [← hzy, hzc1.1]
    have hs1 := hstrict _ hzD hzy hzx.1 hzx.2
    have hs2 := hstrict _ hz'D hz'y hz'x.1 hz'x.2
    by_cases hall : ∀ s : ℝ, (zc c).1 ≤ s → s ≤ (zc c').1 → ((s, Y) : Point) ∈ dom R S
    · exfalso
      have hz'c : zc c' ∈ Visibility.hseg y a b := mem_of_joined hh hzc1 hzD (by rw [hz'y, hy])
        (fun s h1 h2 => by
          rw [min_eq_left hlt.le] at h1; rw [max_eq_right hlt.le] at h2
          rw [hy]; exact hall s h1 h2)
      exact hcc' (eq_of_common (hE c hc).1 (hE c' hc').1 (hceq ▸ hz'c) hz' hz'D)
    · push Not at hall
      obtain ⟨s₀, h1, h2, hnot⟩ := hall
      have h1' : (zc c).1 < s₀ := lt_of_le_of_ne h1 fun e => hnot (by
        rw [← e, show (((zc c).1, Y) : Point) = zc c from point_ext rfl hzy.symm]; exact hzD)
      have h2' : s₀ < (zc c').1 := lt_of_le_of_ne h2 fun e => hnot (by
        rw [e, show (((zc c').1, Y) : Point) = zc c' from point_ext rfl hz'y.symm]; exact hz'D)
      obtain ⟨v, hv, hvy, hv1, hv2⟩ := vert_between hS hside hzD hz'D hzy hz'y hs1.1 hs2.2 h1' h2'
        hnot
      have hsub : {v | v ∈ V ∧ v.1 < (zc c).1} ⊆ {v | v ∈ V ∧ v.1 < (zc c').1} :=
        fun w hw => ⟨hw.1, hw.2.trans hlt⟩
      have hvin : v ∈ {v | v ∈ V ∧ v.1 < (zc c').1} := ⟨⟨hv, hvy⟩, hv2⟩
      have hvout : v ∉ {v | v ∈ V ∧ v.1 < (zc c).1} := fun hh => by
        have := hh.2; linarith
      exact ncard_lt_ncard (ssubset_of_subset_of_ne hsub fun e => hvout (e ▸ hvin))
        (hVf.subset fun w hw => hw.1)
  have hinj : InjOn g E := by
    intro c hc c' hc' hgg
    by_contra hcc'
    obtain ⟨hz, hzD, -, -⟩ := hzc c hc
    obtain ⟨hz', hz'D, -, -⟩ := hzc c' hc'
    have hne : (zc c).1 ≠ (zc c').1 := by
      intro e
      have hzz : zc c = zc c' := point_ext e (by rw [(hzc c hc).2.2.1, (hzc c' hc').2.2.1])
      exact hcc' (eq_of_common (hE c hc).1 (hE c' hc').1 hz (hzz ▸ hz') hzD)
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := hlt c hc c' hc' hcc' h1; simp only [g] at hgg this; omega
    · have := hlt c' hc' c hc (Ne.symm hcc') h1; simp only [g] at hgg this; omega
  calc E.ncard ≤ (Set.Iic t).ncard :=
        ncard_le_ncard_of_injOn g (fun c _ => hgle c) hinj (Set.finite_Iic t)
    _ = t + 1 := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iic]; simp

end Trap

end SegObs

end

end Chazelle.Core
