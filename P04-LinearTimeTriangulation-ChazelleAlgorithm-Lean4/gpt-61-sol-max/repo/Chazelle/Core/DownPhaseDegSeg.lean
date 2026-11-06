module

public import Chazelle.Core.Facts2TrapDeg

/-!
# Degree bound on host curves, part 1: segment obstacles with horizontal segments and ties

A generalisation of `SegObs` (`Chazelle.Core.Facts2Trap`) for the down phase (`HostFullDegSpec`):
the obstacle segments may be **horizontal**, and several vertices may share a height, at most `t`
at each height inside the box (`GoodH`).  The trapezoid of a domain point off the chords
(`SegObs.Trap`) still exists (`exists_trapH`), lies in the domain and contains the region of the
point (`Trap.region_subsetH`); an obstacle point of an open horizontal side is a vertex or a point
of a horizontal segment on that side (`Trap.top_sideH`, `Trap.bot_sideH`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace HSegObs

open SegObs

/-- **The hypotheses on the obstacle segments**, allowing horizontal segments and up to `t`
vertices per height. -/
structure GoodH (R : ℝ) (S : Set (Point × Point)) (t : ℕ) : Prop where
  fin : S.Finite
  le : ∀ s ∈ S, s.1.2 ≤ s.2.2
  inbox : ∀ s ∈ S, ∀ p ∈ seg s, |p.1| ≤ R ∧ |p.2| ≤ R
  sideL : ((-R, -R), (-R, R)) ∈ S
  sideR : ((R, -R), (R, R)) ∈ S
  cross : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∀ p ∈ seg s, p ∈ seg s' → IsVert S p
  tmany : ∀ y : ℝ, |y| < R → {v | IsVert S v ∧ v.2 = y}.ncard ≤ t

variable {R : ℝ} {S : Set (Point × Point)} {t : ℕ}

/-! ## Horizontal segments -/

theorem mem_seg_flat {s : Point × Point} (hf : s.1.2 = s.2.2) {p : Point} :
    p ∈ seg s ↔ p.2 = s.1.2 ∧ min s.1.1 s.2.1 ≤ p.1 ∧ p.1 ≤ max s.1.1 s.2.1 := by
  constructor
  · rintro ⟨u, hu0, hu1, rfl⟩
    refine ⟨by simp_all, ?_, ?_⟩
    · simp only
      rcases le_total s.1.1 s.2.1 with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · simp only
      rcases le_total s.1.1 s.2.1 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
  · rintro ⟨h1, h2, h3⟩
    by_cases he : s.1.1 = s.2.1
    · refine ⟨0, le_rfl, zero_le_one, point_ext ?_ ?_⟩
      all_goals grind
    · have hd : s.2.1 - s.1.1 ≠ 0 := sub_ne_zero.2 (Ne.symm he)
      refine ⟨(p.1 - s.1.1) / (s.2.1 - s.1.1), ?_, ?_, point_ext ?_ ?_⟩
      · rcases lt_or_gt_of_ne he with h | h
        · rw [min_eq_left h.le] at h2
          positivity
        · rw [max_eq_left h.le] at h3
          exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · rcases lt_or_gt_of_ne he with h | h
        · rw [max_eq_right h.le] at h3
          exact (div_le_one (by linarith)).2 (by linarith)
        · rw [min_eq_right h.le] at h2
          exact (div_le_one_of_neg (by linarith)).2 (by linarith)
      all_goals simp_all

section
variable (hS : GoodH R S t)
include hS
theorem isOpen_domH : IsOpen (dom R S) := by
  refine (Chain.isOpen_box R).sdiff ?_
  refine hS.fin.isClosed_biUnion fun s _ => Geometry.isClosed_segment _ _

theorem finite_vertsH : {v | IsVert S v}.Finite := by
  refine ((hS.fin.image Prod.fst).union (hS.fin.image Prod.snd)).subset ?_
  rintro v ⟨s, hs, rfl | rfl⟩
  all_goals grind

theorem abs_xAt_leH {s : Point × Point} (hs : s ∈ S) (hu : s.1.2 < s.2.2)
    {y : ℝ} (h1 : s.1.2 ≤ y) (h2 : y ≤ s.2.2) : |xAt s y| ≤ R :=
  (hS.inbox s hs _ (pt_mem_seg hu h1 h2)).1

/-! ## Horizontal hits -/


end

section
variable (hS : GoodH R S t) {q : Point} (hq : q ∈ dom R S)
include hS hq
theorem exists_hit_eastH :
    ∃ b, q.1 < b ∧ ((b, q.2) : Point) ∉ dom R S ∧
      ∀ x, q.1 ≤ x → x < b → ((x, q.2) : Point) ∈ dom R S := by
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit (isOpen_domH hS) hq (R := R)
    (fun x hx => (abs_lt.1 (box_of_dom hx).1).2)
  refine ⟨q.1 + s, by linarith, hout, fun x h1 h2 => ?_⟩
  have := hin (x - q.1) ⟨by linarith, by linarith⟩
  simp_all

theorem exists_hit_westH :
    ∃ a, a < q.1 ∧ ((a, q.2) : Point) ∉ dom R S ∧
      ∀ x, a < x → x ≤ q.1 → ((x, q.2) : Point) ∈ dom R S := by
  set D' := {p : Point | ((-p.1, p.2) : Point) ∈ dom R S} with hD'
  have hD'o : IsOpen D' := (isOpen_domH hS).preimage (by fun_prop)
  have hq' : ((-q.1, q.2) : Point) ∈ D' := by simp_all
  obtain ⟨s, hs, hin, hout⟩ := exists_first_exit hD'o hq' (R := R)
    (fun x hx => by
      have := (abs_lt.1 (box_of_dom hx).1).1
      simp_all)
  refine ⟨q.1 - s, by linarith, by simpa [hD', sub_eq_add_neg, add_comm] using hout,
    fun x h1 h2 => ?_⟩
  have := hin (q.1 - x) ⟨by linarith, by linarith⟩
  simp_all +arith

theorem hit_mem_obsH {a : ℝ}
    (hnot : ((a, q.2) : Point) ∉ dom R S)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S) :
    ((a, q.2) : Point) ∈ obs S := by
  obtain ⟨hq1, hq2⟩ := box_of_dom hq
  by_cases hab : |a| < R
  · by_contra hobs
    exact hnot ⟨⟨hab, hq2⟩, hobs⟩
  · push Not at hab
    have hq1' := abs_lt.1 hq1
    have hq2' := abs_lt.1 hq2
    rcases le_abs'.1 hab with ha | ha
    · have haR : a = -R := by
        by_contra hne
        have hlt : a < -R := lt_of_le_of_ne ha hne
        have := box_of_dom (hin (-R) (by
          simp_all) (by
          simp_all))
        grind
      
      refine seg_subset_obs hS.sideL ((mem_seg_iff (by linarith)).2
        ⟨by linarith, by linarith, ?_⟩)
      grind [xAt]
    · have haR : a = R := by
        by_contra hne
        have hlt : R < a := lt_of_le_of_ne ha (Ne.symm hne)
        have := box_of_dom (hin R (by
          simp_all) (by
          simp_all))
        grind
      
      refine seg_subset_obs hS.sideR ((mem_seg_iff (by linarith)).2
        ⟨by linarith, by linarith, ?_⟩)
      grind [xAt]


end

/-- **A horizontal hit that is not a vertex lies in the open part of a non-horizontal
segment** (a horizontal segment on the line would be entered at a vertex first). -/
theorem hit_wall (hS : GoodH R S t) {q : Point} {a : ℝ} (hobs : ((a, q.2) : Point) ∈ obs S)
    (hv : ¬ IsVert S ((a, q.2) : Point)) (haq : a ≠ q.1)
    (hin : ∀ x, min a q.1 < x → x < max a q.1 → ((x, q.2) : Point) ∈ dom R S) :
    ∃ s ∈ S, s.1.2 < q.2 ∧ q.2 < s.2.2 ∧ a = xAt s q.2 := by
  obtain ⟨s, hs, hps⟩ := mem_iUnion₂.1 hobs
  rcases (hS.le s hs).lt_or_eq with hu | hf
  · obtain ⟨h1, h2, h3⟩ := (mem_seg_iff hu).1 hps
    simp only at h1 h2 h3
    refine ⟨s, hs, lt_of_le_of_ne h1 fun e => hv ⟨s, hs, Or.inl (eq_lo hu hps e.symm)⟩,
      lt_of_le_of_ne h2 fun e => hv ⟨s, hs, Or.inr (eq_hi hu hps e)⟩, h3⟩
  · exfalso
    obtain ⟨hy, hmin, hmax⟩ := (mem_seg_flat hf).1 hps
    simp only at hy hmin hmax
    have hne1 : a ≠ s.1.1 := fun e => hv ⟨s, hs, Or.inl (point_ext e hy)⟩
    have hne2 : a ≠ s.2.1 := fun e => hv ⟨s, hs, Or.inr (point_ext e (hy.trans hf))⟩
    have hmin' : min s.1.1 s.2.1 < a := lt_of_le_of_ne hmin fun e => by
      grind
    have hmax' : a < max s.1.1 s.2.1 := lt_of_le_of_ne hmax fun e => by
      grind
    rcases lt_or_gt_of_ne haq with hlt | hgt
    · set x := min (max s.1.1 s.2.1) ((a + q.1) / 2) with hx
      have hx1 : a < x := lt_min hmax' (by linarith)
      have hx2 : x < q.1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hxD := hin x (by grind) (by grind)
      exact hxD.2 (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hy, by linarith, min_le_left _ _⟩))
    · set x := max (min s.1.1 s.2.1) ((a + q.1) / 2) with hx
      have hx1 : x < a := max_lt hmin' (by linarith)
      have hx2 : q.1 < x := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hxD := hin x (by grind) (by grind)
      exact hxD.2 (seg_subset_obs hs ((mem_seg_flat hf).2 ⟨hy, le_max_left _ _, by linarith⟩))

end HSegObs

end

end Chazelle.Core
