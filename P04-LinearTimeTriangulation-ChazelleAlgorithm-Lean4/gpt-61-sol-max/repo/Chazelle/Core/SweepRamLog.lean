module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepRamTie

/-!
# The sweep RAM (WP-D), part 2: labels near a position, and the event log

The sweep writes an **event log**: a list of keys of the `C₁` part of the walk of `C` with labels.
A query at a position `y` of the `C₁` part is answered with the label of the last entry at or
before `y`; what the answer lemmas need is that the regions faced just after and just before `y`
have no other label (`LabOK`, the first half of `Valid`):

* `LabOK`, `NearLab`: the labels of a region, of the regions faced near a position;
* `nearLab_gap`: after an event key with `AfterOK`, every later position up to the next cut
  (`nearLab_gap`) and the next cut key from before (`beforeLab_next`) have the label;
* `faces_near_after`, `faces_near_before`: a region faced just after/before a position is faced at
  non-cut positions arbitrarily close (so an interval of unlabelled positions, a bracket or a
  pocket, gives `NearLab` for every label: `nearLab_of_unlabelled`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

/-! ## Non-cut positions near a position -/

section Near

variable {M : Model}

/-- **A region faced just after a position is faced at nearby later non-cut positions.** -/
theorem faces_near_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) {U : Set Point}
    (hW : AfterFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ s < ε ∧ t + s < 1 ∧ ¬ M.IsCut F ((p : ℝ) + (t + s)) ∧ M.Faces p (t + s) U := by
  obtain ⟨δ, hδ, hW'⟩ := hW
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hF hfin ((p : ℝ) + t))
  have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
  set s := min (min δ δ₁) (min ε (1 - t)) / 2 with hs
  have hm : 0 < min (min δ δ₁) (min ε (1 - t)) :=
    lt_min (lt_min hδ hδ₁') (lt_min hε (by linarith))
  have h1 := min_le_left (min δ δ₁) (min ε (1 - t))
  have h2 := min_le_right (min δ δ₁) (min ε (1 - t))
  have h3 := min_le_left δ δ₁
  have h4 := min_le_right δ δ₁
  have h5 := min_le_left ε (1 - t)
  have h6 := min_le_right ε (1 - t)
  refine ⟨s, by linarith, by linarith, by linarith, ?_, hW' s (by linarith) (by linarith)
    (by linarith)⟩
  have := hsub ⟨show 0 < s by linarith, show s < δ₁ by linarith⟩
  grind

section
variable {n g p : ℕ} (hg : g < n) (hp : p < n)
include hg hp
/-- The offset of the position just before a walk vertex. -/
theorem off_before_vertex {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hpos : 0 < off n g ((p : ℝ) + 0)) :
    off n g ((((p + n - 1) % n : ℕ) : ℝ) + (1 - s)) = off n g ((p : ℝ) + 0) - s := by
  have hpg : p ≠ g := by
    core_grind
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · have e : (0 + n - 1) % n = n - 1 := by simp_all
    rw [e]
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simp_all
    rw [hn1]
    unfold off
    have hg0 : (0 : ℝ) < g := by
      positivity
    have hgn : (g : ℝ) + 1 ≤ n := by exact_mod_cast hg
    grind
  · have e : (p + n - 1) % n = p - 1 := by
      rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have hp1' : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by simp_all
    rw [hp1']
    unfold off
    rcases lt_or_gt_of_ne hpg with h | h
    · have h' : (p : ℝ) + 1 ≤ g := by exact_mod_cast h
      grind
    · have h' : (g : ℝ) + 1 ≤ p := by exact_mod_cast h
      grind

/-- The offset of a position before `(p, t)` on the same edge. -/
theorem off_before_edge {t s : ℝ} (hs0 : 0 < s)
    (hst : s < t) (ht1 : t < 1) :
    off n g ((p : ℝ) + (t - s)) = off n g ((p : ℝ) + t) - s := by
  have := off_add_small hg hp (t := t - s) (s := s) (by linarith) hs0.le (by linarith)
  simp_all


end

/-- **A region faced just before a position is faced at nearby earlier non-cut positions**
(at positive offset). -/
theorem faces_near_before (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hpos : 0 < off M.W.n g ((p : ℝ) + t)) {U : Set Point}
    (hW : BeforeFaces M p t U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℕ) (u : ℝ), q < M.W.n ∧ u ∈ Ioo (0 : ℝ) 1 ∧ ¬ M.IsCut F ((q : ℝ) + u) ∧
      M.Faces q u U ∧ off M.W.n g ((p : ℝ) + t) - ε < off M.W.n g ((q : ℝ) + u) ∧
      off M.W.n g ((q : ℝ) + u) < off M.W.n g ((p : ℝ) + t) := by
  obtain ⟨δ, hδ, hWp, hW0⟩ := hW
  rcases ht0.lt_or_eq with htp | rfl
  · obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (eventually_not_cut_before hM hF hfin ((p : ℝ) + t))
    have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
    set s := min (min δ δ₁) (min ε t) / 2 with hs
    have hm : 0 < min (min δ δ₁) (min ε t) := lt_min (lt_min hδ hδ₁') (lt_min hε htp)
    have h1 := min_le_left (min δ δ₁) (min ε t)
    have h2 := min_le_right (min δ δ₁) (min ε t)
    have h3 := min_le_left δ δ₁
    have h4 := min_le_right δ δ₁
    have h5 := min_le_left ε t
    have h6 := min_le_right ε t
    have hst : s < t := by linarith
    have hoff := off_before_edge hg hp (show 0 < s by linarith) hst ht1
    refine ⟨p, t - s, hp, ⟨by linarith, by linarith⟩, ?_, hWp htp s (by linarith) (by linarith) hst,
      by linarith, by linarith⟩
    have := hsub ⟨show 0 < s by linarith, show s < δ₁ by linarith⟩
    grind
  · -- at a walk vertex: the end of the previous edge
    set q := (p + M.W.n - 1) % M.W.n with hq
    have hqn : q < M.W.n := Nat.mod_lt _ (by omega)
    have hkey : ∀ s : ℝ, (q : ℝ) + (1 - s) = (p : ℝ) - s ∨ (q : ℝ) + (1 - s) = (M.W.n : ℝ) - s := by
      intro s
      rcases Nat.eq_zero_or_pos p with rfl | hp1
      · right
        have e : (0 + M.W.n - 1) % M.W.n = M.W.n - 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        rw [hq, e, Nat.cast_sub (by omega)]; grind
      · left
        have e : (p + M.W.n - 1) % M.W.n = p - 1 := by
          rw [show p + M.W.n - 1 = (p - 1) + M.W.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hq, e, Nat.cast_sub (by omega)]; grind
    obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      ((eventually_not_cut_before hM hF hfin (p : ℝ)).and
        (eventually_not_cut_before hM hF hfin (M.W.n : ℝ)))
    have hδ₁' : (0 : ℝ) < δ₁ := hδ₁
    set s := min (min δ δ₁) (min ε 1) / 2 with hs
    have hm : 0 < min (min δ δ₁) (min ε 1) := lt_min (lt_min hδ hδ₁') (lt_min hε one_pos)
    have h1 := min_le_left (min δ δ₁) (min ε 1)
    have h2 := min_le_right (min δ δ₁) (min ε 1)
    have h3 := min_le_left δ δ₁
    have h4 := min_le_right δ δ₁
    have h5 := min_le_left ε (1 : ℝ)
    have h6 := min_le_right ε (1 : ℝ)
    have hs0 : 0 < s := by linarith
    have hs1 : s < 1 := by linarith
    have hoff := off_before_vertex hg hp hs0 hs1 (by omega)
    simp only [add_zero] at hoff hpos ⊢
    refine ⟨q, 1 - s, hqn, ⟨by linarith, by linarith⟩, ?_, hW0 rfl s hs0 (by linarith),
      by grind, by grind⟩
    have hns := hsub ⟨hs0, show s < δ₁ by linarith⟩
    simp only [mem_ofPred_eq] at hns
    rcases hkey s with h | h <;> rw [h]
    · exact hns.1
    grind

end Near

section Machine

variable (J : Merge.Junction)

end Machine

end Sweep

end

end Chazelle.Core
