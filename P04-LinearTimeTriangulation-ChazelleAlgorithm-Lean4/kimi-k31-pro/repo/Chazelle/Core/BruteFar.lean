module

public import Chazelle.Core.BruteCorner
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-K: the far end of a vertex chord by a naive scan

The chord of the chain vertex `v_k` in direction `σ` ends at the nearest point, on the side `σ`,
of the chain edges that straddle the height of `v_k` (`Strad`, `Cand`), or on the side `σ` of the
box if there is none.  `scan` is the left-to-right minimum search the RAM performs over the chain
edges (`scan_some`, `scan_none`), and `far_end` identifies its result with `C.chordEnd k σ`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt SideAttach)
open Chazelle.Visibility (rayPt OpenEdgePt xAt)

namespace Brute

variable {C : Chain}

/-- The chain edge `j` straddles the height of the vertex `v_k` (strictly). -/
def Strad (C : Chain) (j k : ℕ) : Prop :=
  ((C.vertex j).2 < (C.vertex k).2 ∧ (C.vertex k).2 < (C.vertex (j + 1)).2) ∨
    ((C.vertex (j + 1)).2 < (C.vertex k).2 ∧ (C.vertex k).2 < (C.vertex j).2)

/-- The abscissa of (the line of) chain edge `j` at the height of `v_k`. -/
noncomputable def edgeXk (C : Chain) (j k : ℕ) : ℝ :=
  xAt (C.vertex j) (C.vertex (j + 1)) (C.vertex k).2

/-- Chain edge `j` is a candidate for the chord of `v_k` in direction `σ`. -/
def Cand (C : Chain) (k : ℕ) (σ : ℝ) (j : ℕ) : Prop :=
  j < C.m ∧ Strad C j k ∧ 0 < σ * (edgeXk C j k - (C.vertex k).1)

open Classical in
/-- **The scan**: the first candidate among the chain edges `< J` with the nearest point
(strictly nearer points replace the current one). -/
noncomputable def scan (C : Chain) (k : ℕ) (σ : ℝ) : ℕ → Option ℕ
  | 0 => none
  | j + 1 =>
    if Cand C k σ j then
      (match scan C k σ j with
        | none => some j
        | some b => if σ * edgeXk C j k < σ * edgeXk C b k then some j else some b)
    else scan C k σ j

theorem scan_some {k : ℕ} {σ : ℝ} : ∀ {J b : ℕ}, scan C k σ J = some b →
    b < J ∧ Cand C k σ b ∧ ∀ j, j < J → Cand C k σ j → σ * edgeXk C b k ≤ σ * edgeXk C j k
  | 0, b, h => by simp [scan] at h
  | J + 1, b, h => by
    unfold scan at h
    split_ifs at h with hc
    · rcases hr : scan C k σ J with _ | b'
      · rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨by omega, hc, fun j hj hcj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have := scan_none_aux hr j hj
          exact absurd hcj this
        · exact le_rfl
      · rw [hr] at h
        obtain ⟨hb'J, hb'c, hb'min⟩ := scan_some hr
        simp only at h
        split_ifs at h with hlt
        · simp only [Option.some.injEq] at h
          subst h
          refine ⟨by omega, hc, fun j hj hcj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hlt.le.trans (hb'min j hj hcj)
          · exact le_rfl
        · simp only [Option.some.injEq] at h
          subst h
          refine ⟨by omega, hb'c, fun j hj hcj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hb'min j hj hcj
          · exact not_lt.1 hlt
    · obtain ⟨h1, h2, h3⟩ := scan_some h
      refine ⟨by omega, h2, fun j hj hcj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h3 j hj hcj
      · exact absurd hcj hc
where
  scan_none_aux : ∀ {J : ℕ}, scan C k σ J = none → ∀ j, j < J → ¬ Cand C k σ j
    | 0, _, j, hj => by omega
    | J + 1, h, j, hj => by
      unfold scan at h
      split_ifs at h with hc
      · rcases hr : scan C k σ J with _ | b' <;> rw [hr] at h
        · simp at h
        · simp only at h; split_ifs at h
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact scan_none_aux h j hj
        · exact hc

theorem scan_none {k : ℕ} {σ : ℝ} {J : ℕ} (h : scan C k σ J = none) :
    ∀ j, j < J → ¬ Cand C k σ j :=
  scan_some.scan_none_aux h

/-! ## The far end of a vertex chord -/

theorem xAt_mem_edge (hDH : DistinctHeights C.P) {j k : ℕ} (hj : j < C.m)
    (hs : Strad C j k) : ((edgeXk C j k, (C.vertex k).2) : Point) ∈ C.chainEdge j := by
  have hne : (C.vertex j).2 ≠ (C.vertex (j + 1)).2 :=
    ChainObs.vertex_snd_ne hDH (by omega) (by omega) (by omega)
  rw [C.chainEdge_eq, Visibility.mem_segment_iff_xAt hne]
  refine ⟨⟨?_, ?_⟩, rfl⟩ <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only
  · exact (min_le_left _ _).trans h1.le
  · exact (min_le_right _ _).trans h1.le
  · exact h2.le.trans (le_max_right _ _)
  · exact h2.le.trans (le_max_left _ _)

/-- **The far end of a vertex chord** is the nearest candidate point, or on the box. -/
theorem far_end (hDH : DistinctHeights C.P) {k : ℕ} (hk : k ≤ C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : C.DirFree k σ) :
    (∀ b, scan C k σ C.m = some b →
      C.chordEnd k σ = (edgeXk C b k, (C.vertex k).2) ∧ Cand C k σ b) ∧
    (scan C k σ C.m = none → C.chordEnd k σ = (σ * C.radius, (C.vertex k).2)) := by
  obtain ⟨hpos, hend, hint⟩ := C.chord_spec hk hσ hf
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set v := C.vertex k with hv
  have he1 : (C.chordEnd k σ).1 = v.1 + σ * C.chordParam k σ := rfl
  have he2 : (C.chordEnd k σ).2 = v.2 := rfl
  -- candidates are not nearer than the end
  have hA : ∀ j, Cand C k σ j → C.chordParam k σ ≤ σ * (edgeXk C j k - v.1) := by
    intro j ⟨hj, hs, hx⟩
    by_contra hlt
    push Not at hlt
    have hin := hint _ hx hlt
    have hpt : rayPt v σ (σ * (edgeXk C j k - v.1)) = ((edgeXk C j k, v.2) : Point) := by
      ext
      · simp only [rayPt]; rwring [← mul_assoc, hσσ]
      · rfl
    rw [hpt] at hin
    exact C.not_mem_set_of_mem_dom hin ⟨j, hj, xAt_mem_edge hDH hj hs⟩
  -- an end on the chain is a candidate point
  have hB : C.chordEnd k σ ∈ C.set → ∃ j, Cand C k σ j ∧ edgeXk C j k = (C.chordEnd k σ).1 := by
    rintro ⟨j, hj, hmem⟩
    have hne : (C.vertex j).2 ≠ (C.vertex (j + 1)).2 :=
      ChainObs.vertex_snd_ne hDH (by omega) (by omega) (by omega)
    rw [C.chainEdge_eq, Visibility.mem_segment_iff_xAt hne] at hmem
    obtain ⟨⟨hm1, hm2⟩, hx⟩ := hmem
    have hnev := C.chordEnd_ne_vertex hk hσ hf
    have hne1 : (C.vertex j).2 ≠ v.2 := by
      intro e
      apply hnev
      have : j = k := by
        by_contra hjk; exact ChainObs.vertex_snd_ne hDH (by omega) hk hjk e
      subst this
      ext
      · rw [hx, he2, ← e, Visibility.xAt_left]
      · exact he2
    have hne2 : (C.vertex (j + 1)).2 ≠ v.2 := by
      intro e
      apply hnev
      have : j + 1 = k := by
        by_contra hjk; exact ChainObs.vertex_snd_ne hDH (by omega) hk hjk e
      subst this
      ext
      · rw [hx, he2, ← e, Visibility.xAt_right hne]
      · exact he2
    rw [he2] at hm1 hm2 hx
    have hs : Strad C j k := by
      unfold Strad
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_left hlt.le] at hm1; rw [max_eq_right hlt.le] at hm2
        exact Or.inl ⟨lt_of_le_of_ne hm1 hne1, lt_of_le_of_ne hm2 (Ne.symm hne2)⟩
      · rw [min_eq_right hgt.le] at hm1; rw [max_eq_left hgt.le] at hm2
        exact Or.inr ⟨lt_of_le_of_ne hm1 hne2, lt_of_le_of_ne hm2 (Ne.symm hne1)⟩
    have hX : edgeXk C j k = (C.chordEnd k σ).1 := hx.symm
    refine ⟨j, ⟨hj, hs, ?_⟩, hX⟩
    rw [hX, he1]
    have : σ * (v.1 + σ * C.chordParam k σ - v.1) = C.chordParam k σ := by
      rw [add_sub_cancel_left, ← mul_assoc, hσσ, one_mul]
    rwx [this]
  -- candidate points are inside the box
  have hbox : ∀ j, Cand C k σ j → σ * edgeXk C j k < C.radius := by
    rintro j ⟨hj, hs, -⟩
    have hmem := C.set_subset_box ⟨j, hj, xAt_mem_edge hDH hj hs⟩
    have h1 := (abs_lt.1 hmem.1)
    simp only at h1
    rcases hσ with rfl | rfl
    · linarith
    · linarith
  refine ⟨fun b hb => ?_, fun hb => ?_⟩
  · obtain ⟨-, hcb, hmin⟩ := scan_some hb
    have hA' := hA b hcb
    rcases C.chordEnd_cases hk hσ hf with hset | hwall
    · obtain ⟨j0, hc0, hX0⟩ := hB hset
      have h1 := hmin j0 (hc0.1) hc0
      rw [hX0, he1] at h1
      have h2 : σ * edgeXk C b k = σ * (C.chordEnd k σ).1 := by
        rw [he1]
        have : σ * (v.1 + σ * C.chordParam k σ) = σ * v.1 + C.chordParam k σ := by
          rw [mul_add, ← mul_assoc, hσσ, one_mul]
        rw [this]
        rw [this] at h1
        have : σ * (edgeXk C b k - v.1) = σ * edgeXk C b k - σ * v.1 := by ring
        rw [this] at hA'
        linarith
      have h3 : edgeXk C b k = (C.chordEnd k σ).1 := by
        rcases hσ with rfl | rfl
        · linarith
        · linarith
      refine ⟨?_, hcb⟩
      ext
      · exact h3.symm
      · exact he2
    · exfalso
      have h1 := hbox b hcb
      have : σ * (edgeXk C b k - v.1) = σ * edgeXk C b k - σ * v.1 := by ring
      rw [this] at hA'
      have hv1 : v.1 + σ * C.chordParam k σ = σ * C.radius := by rwx [← he1]
      have : σ * (v.1 + σ * C.chordParam k σ) = σ * v.1 + C.chordParam k σ := by
        rw [mul_add, ← mul_assoc, hσσ, one_mul]
      rw [hv1, ← mul_assoc, hσσ, one_mul] at this
      linarith
  · rcases C.chordEnd_cases hk hσ hf with hset | hwall
    · obtain ⟨j0, hc0, -⟩ := hB hset
      exact absurd hc0 (scan_none hb j0 hc0.1)
    · ext
      · exact hwall
      · exact he2

end Brute

end

end Chazelle.Core
