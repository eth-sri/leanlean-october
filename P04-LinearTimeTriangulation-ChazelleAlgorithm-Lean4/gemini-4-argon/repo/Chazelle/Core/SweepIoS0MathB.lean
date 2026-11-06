module

public import Chazelle.Core.SweepIoS0MathA

/-!
# The side-0 answer cases (sweep, `Side0MathSpec`), part 2: labels from the event log

**`labels_of_log`**: for a position `(p, t)` of the `C₁` part (offset beyond the start) whose log
entry is `i`, every label of a region `U` of `F₂⁺` faced just after or just before the position
is in the label set of the entry `i`, or of the entry `i - 1` (`i > 0`), or is a gap label.
-/

namespace Chazelle.Core

namespace S0Math

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep

@[expose] public section

variable (J : Merge.Junction)

theorem gW_lt : gW J < (chainModel J.whole).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have := tpos_lt J.whole J.m₁
  unfold gW; omega

theorem getD_mem {α : Type*} {l : List α} {i : ℕ} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

set_option maxHeartbeats 2000000 in
/-- **The labels of the region faced at a position, from the event log.** -/
theorem labels_of_log (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite)
    {es : List (ℕ × ℝ × Set (Set Point))} (hlog : LogOK J S₂ es) {i : ℕ} (hi : i < es.length)
    {pz : ℕ} {tz : ℝ} (hpz : pz < (chainModel J.whole).W.n) (htz0 : 0 ≤ tz) (htz1 : tz < 1)
    (hLst : (Lst J : ℝ) < oW J (pz + tz))
    (hlo : oW J ((es.getD i (0, 0, ∅)).1 + (es.getD i (0, 0, ∅)).2.1) ≤ oW J (pz + tz))
    (hhi : i + 1 < es.length →
      oW J (pz + tz) < oW J ((es.getD (i + 1) (0, 0, ∅)).1 + (es.getD (i + 1) (0, 0, ∅)).2.1))
    {U : Set Point} (hU : U ∈ (chainModel J.whole).regions (F₂plus J S₂))
    (hface : AfterFaces (chainModel J.whole) pz tz U ∨ BeforeFaces (chainModel J.whole) pz tz U) :
    ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ U V →
      V ∈ (es.getD i (0, 0, ∅)).2.2 ∨ (0 < i ∧ V ∈ (es.getD (i - 1) (0, 0, ∅)).2.2) ∨
        GapLab J S₂ V := by
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  have hF : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := F₂plus_subset J hS₂
  have hfin : (F₂plus J S₂).Finite := F₂plus_finite J hS₂f
  have hg := gW_lt J
  have hg0 : (0 : ℝ) ≤ (gW J : ℝ) := Nat.cast_nonneg _
  have hgn : (gW J : ℝ) < (chainModel J.whole).W.n := by exact_mod_cast hg
  set d : ℕ × ℝ × Set (Set Point) := (0, 0, ∅) with hd
  have hent : ∀ j, j < es.length → (es.getD j d).1 < (chainModel J.whole).W.n ∧
      0 ≤ (es.getD j d).2.1 ∧ (es.getD j d).2.1 < 1 :=
    fun j hj => by
      obtain ⟨h1, h2, h3, -⟩ := hlog.2.1 _ (getD_mem hj d)
      exact ⟨h1, h2, h3⟩
  have hlab : ∀ j, j < es.length →
      LabIn J S₂ (es.getD j d).1 (es.getD j d).2.1 (es.getD j d).2.2 :=
    fun j hj => hlog.2.2.2.2.2.2 _ (getD_mem hj d)
  -- the offsets
  set x := oW J ((pz : ℝ) + tz)
  set k := oW J (((es.getD i d).1 : ℝ) + (es.getD i d).2.1) with hk
  have hxn : x < (chainModel J.whole).W.n := off_lt (Corr.key_mem hpz htz0 htz1).2 hg0
  -- the next cut after the entry `i`
  obtain ⟨ub, hxub, hgub⟩ : ∃ ub : ℝ, x < ub ∧ ∀ y, (chainModel J.whole).IsCut (F₂plus J S₂) y →
      0 ≤ y → y < (chainModel J.whole).W.n → ¬ (k < oW J y ∧ oW J y < ub) := by
    by_cases h : i + 1 < es.length
    · exact ⟨_, hhi h, hlog.2.2.2.2.1 i h⟩
    · refine ⟨(chainModel J.whole).W.n, hxn, ?_⟩
      have hlast : es.getD i d ∈ es.getLast? := by
        rw [List.getLast?_eq_getElem?, show es.length - 1 = i by omega,
          List.getD_eq_getElem _ _ hi]
        simp [hi]
      exact hlog.2.2.2.2.2.1 _ hlast
  -- positions with the offset of the entry are the entry
  have hpos_eq : x = k → pz = (es.getD i d).1 ∧ tz = (es.getD i d).2.1 := fun h => by
    obtain ⟨e1, e2, e3⟩ := hent i hi
    have := off_inj hg0 hgn (Corr.key_mem hpz htz0 htz1).1 (Corr.key_mem hpz htz0 htz1).2
      (Corr.key_mem e1 e2 e3).1 (Corr.key_mem e1 e2 e3).2 h
    exact Chazelle.Chain.sideKey_inj htz0 htz1 e2 e3 this
  -- the label conclusion from the region faced just after the entry `i` or `i - 1`
  have finI : AfterFaces (chainModel J.whole) (es.getD i d).1 (es.getD i d).2.1 U →
      ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ U V →
        V ∈ (es.getD i d).2.2 ∨ (0 < i ∧ V ∈ (es.getD (i - 1) d).2.2) ∨ GapLab J S₂ V := by
    intro hA V hV hl
    rcases hlab i hi U hU hA V hV hl with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  -- the region after a non-cut position after the entry
  have viaNear : ∀ (q : ℕ) (u : ℝ), q < (chainModel J.whole).W.n → u ∈ Ioo (0 : ℝ) 1 →
      ¬ (chainModel J.whole).IsCut (F₂plus J S₂) (q + u) → (chainModel J.whole).Faces q u U →
      k < oW J (q + u) → oW J (q + u) < ub →
      AfterFaces (chainModel J.whole) (es.getD i d).1 (es.getD i d).2.1 U := by
    intro q u hq hu hnc hf h1 h2
    obtain ⟨e1, e2, -⟩ := hent i hi
    exact after_of_near hM hF hfin hg hU e1 e2 hq hu hnc hf h1
      (fun y hy hy0 hyn ⟨a1, a2⟩ => hgub y hy hy0 hyn ⟨a1, lt_trans a2 h2⟩)
  rcases hface with hA | hB
  · rcases hlo.lt_or_eq with hlt | heq
    · obtain ⟨s, hs0, hsε, hts, hnc, hf, hoff⟩ :=
        near_after hM hF hfin hg hpz htz0 htz1 hA (ε := ub - x) (by linarith)
      have hoff' : oW J ((pz : ℝ) + (tz + s)) = x + s := hoff
      refine finI (viaNear pz (tz + s) hpz hts hnc hf ?_ ?_)
      · rw [hoff']; linarith
      · rw [hoff']; linarith
    · obtain ⟨e1, e2⟩ := hpos_eq heq.symm
      rw [e1, e2] at hA
      exact finI hA
  · rcases hlo.lt_or_eq with hlt | heq
    · obtain ⟨q, u, hq, hu, hnc, hf, h1, h2⟩ := faces_near_before hM hF hfin hg hpz htz0 htz1
        (show (0 : ℝ) < x from lt_of_le_of_lt (Nat.cast_nonneg _) hLst) hB (ε := x - k) (by linarith)
      have h1' : x - (x - k) < oW J ((q : ℝ) + u) := h1
      have h2' : oW J ((q : ℝ) + u) < x := h2
      exact finI (viaNear q u hq hu hnc hf (by linarith) (by linarith))
    · -- the position is the entry `i`: `i > 0` and the entry `i - 1` faces the region
      have hi0 : 0 < i := by
        by_contra h0
        push Not at h0
        have hi0 : i = 0 := by omega
        have hhead : es.getD 0 d ∈ es.head? := by
          cases es with
          | nil => simp at hi
          | cons a l => simp [hd]
        have := hlog.2.2.1 _ hhead
        have hk' : k = oW J (((es.getD 0 d).1 : ℝ) + (es.getD 0 d).2.1) := by rw [hk, hi0]
        linarith
      have hi1 : i - 1 < es.length := by omega
      have hcons : i - 1 + 1 < es.length := by omega
      have hgap' := hlog.2.2.2.2.1 (i - 1) hcons
      rw [show i - 1 + 1 = i by omega] at hgap'
      have hsort : oW J (((es.getD (i - 1) d).1 : ℝ) + (es.getD (i - 1) d).2.1) < k := by
        have := List.pairwise_iff_getElem.1 hlog.2.2.2.1 (i - 1) i hi1 hi (by omega)
        rw [hk, List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi]
        exact this
      obtain ⟨q, u, hq, hu, hnc, hf, h1, h2⟩ := faces_near_before hM hF hfin hg hpz htz0 htz1
        (show (0 : ℝ) < x from lt_of_le_of_lt (Nat.cast_nonneg _) hLst) hB
        (ε := k - oW J (((es.getD (i - 1) d).1 : ℝ) + (es.getD (i - 1) d).2.1)) (by linarith)
      obtain ⟨e1, e2, -⟩ := hent (i - 1) hi1
      have h1' : x - (k - oW J (((es.getD (i - 1) d).1 : ℝ) + (es.getD (i - 1) d).2.1)) <
          oW J ((q : ℝ) + u) := h1
      have h2' : oW J ((q : ℝ) + u) < x := h2
      have hA' := after_of_near hM hF hfin hg hU e1 e2 hq hu hnc hf
        (show oW J _ < oW J ((q : ℝ) + u) by linarith)
        (fun y hy hy0 hyn ⟨a1, a2⟩ => hgap' y hy hy0 hyn ⟨a1, by
          have a2' : oW J y < oW J ((q : ℝ) + u) := a2
          show oW J y < k; linarith⟩)
      intro V hV hl
      rcases hlab (i - 1) hi1 U hU hA' V hV hl with h | h
      · exact Or.inr (Or.inl ⟨hi0, h⟩)
      · exact Or.inr (Or.inr h)

end

end S0Math

end Chazelle.Core
