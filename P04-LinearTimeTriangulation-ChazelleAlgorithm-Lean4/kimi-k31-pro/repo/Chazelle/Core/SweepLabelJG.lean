module

public import Chazelle.Core.SweepLabelJ
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# The sweep (WP-D), part 5b: the right correspondence without `TopStrict` (F2)

With ties at the top of `C₂` the top chord at the split vertex may end on `C₂`, so the
correspondence of `SweepLabelJ.corr_right` loses its separating chord.  This file gives the
correspondence without it (`corr_right0 : Corr0 …`) and the gap facts of case G
(`corrGap_right : CorrGap …`), so that lemma (K3) (`SweepLabelGap.Corr0.label_gen3`) applies.

* `ccw_up_left`, `ccw_up_right`, `ccw_lower_left`, `ccw_lower_right`: horizontal directions in
  corners at a top vertex, next to a vertical slit.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot)
open Chazelle.Visibility (rayPt)
open WalkEmbed

namespace Sweep

/-! ## Horizontal directions next to a slit -/

/-- A horizontal direction in the corner from the upward slit to a direction `A` not above the
horizontal points west. -/
theorem ccw_up_left {a x : ℝ} {A : Point} (ha : 0 < a) (hA : A.2 ≤ 0)
    (h : sideCcw ((0, a) : Point) ((x, 0) : Point) A) : x < 0 := by
  unfold sideCcw sideCross sideDot at h
  simp only at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- A horizontal direction in the corner from a direction `B` not above the horizontal to the
upward slit points east. -/
theorem ccw_up_right {a x : ℝ} {B : Point} (ha : 0 < a) (hB : B.2 ≤ 0)
    (h : sideCcw B ((x, 0) : Point) ((0, a) : Point)) : 0 < x := by
  unfold sideCcw sideCross sideDot at h
  simp only at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- **A horizontal direction in a corner below the horizontal** forces the corner to turn
clockwise or to be a straight angle turned upwards: for `B`, `A` not above the horizontal,
`sideCcw B (σ₀, 0) A` gives `sideCross B A < 0` or `sideCross B A = 0 ∧ 0 < sideDot B A`. -/
theorem ccw_horiz_lower {σ₀ : ℝ} {A B : Point} (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B ((σ₀, 0) : Point) A) :
    sideCross B A < 0 ∨ (sideCross B A = 0 ∧ 0 < sideDot B A) := by
  obtain ⟨b1, b2⟩ := B
  obtain ⟨a1, a2⟩ := A
  simp only at hA hB
  simp only [sideCcw, sideCross, sideDot] at h0 ⊢
  rcases h0 with ⟨h1, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, -⟩
  · exfalso
    have : 0 < (-(b2 * σ₀)) * (σ₀ * a2) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg (neg_nonneg.2 hB) (neg_nonneg.2 hA), sq_nonneg σ₀]
  · exact Or.inl (by linarith)
  · exfalso
    have key : a2 * (b1 * a1 + b2 * a2) = b2 * (a1 ^ 2 + a2 ^ 2) := by
      have : b1 * a2 = b2 * a1 := by linarith
      linear_combination a1 * this
    have hl  := mul_nonneg_of_nonpos_of_nonpos hA h2.le
    have hsq : 0 < a1 ^ 2 + a2 ^ 2 := by
      by_contra hc
      have ha1 : a1 = 0 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
      have ha2 : a2 = 0 := by nlinarith [sq_nonneg a1, sq_nonneg a2]
      rw [ha1, ha2] at h2
      linarith
    have hb2 : b2 = 0 := by
      have : 0 ≤ b2 * (a1 ^ 2 + a2 ^ 2) := key ▸ hl
      have : 0 ≤ b2 := by
        by_contra hc; push Not at hc
        nlinarith
      linarith
    rw [hb2] at h3
    linarith
  · exact Or.inr ⟨by linarith, h2⟩

/-- **The corner of a top vertex contains the corner before the slit**: if the corner from `B`
to `A` (both not above the horizontal) contains a horizontal direction, it contains every
horizontal direction of the corner from the upward slit to `A`. -/
theorem ccw_lower_left {a x σ₀ : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B ((σ₀, 0) : Point) A) (h : sideCcw ((0, a) : Point) ((x, 0) : Point) A) :
    sideCcw B ((x, 0) : Point) A := by
  have hx := ccw_up_left ha hA h
  have hAw : A.2 < 0 ∨ 0 < A.1 := by
    unfold sideCcw sideCross sideDot at h
    simp only at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
  have hc := ccw_horiz_lower hA hB h0
  obtain ⟨b1, b2⟩ := B
  obtain ⟨a1, a2⟩ := A
  simp only at hA hB hAw
  simp only [sideCcw, sideCross, sideDot] at hc ⊢
  rcases hc with hc | ⟨hc, hd⟩
  · refine Or.inr (Or.inl ⟨hc, Or.inr ?_⟩)
    rcases lt_or_eq_of_le hA with ha2 | ha2
    · nlinarith
    · exfalso
      subst ha2
      rcases hAw with h' | h'
      · linarith
      · nlinarith
  · refine Or.inr (Or.inr (Or.inr ⟨hc, hd, ?_⟩))
    by_cases hb2 : b2 = 0
    · right
      subst hb2
      have hb1 : b1 ≠ 0 := by rintro rfl; simp at hd
      have ha2 : a2 = 0 := by
        have : b1 * a2 = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · exact absurd h' hb1
        · exact h'
      subst ha2
      rcases hAw with h' | h'
      · linarith
      · have : 0 < b1 := by nlinarith
        nlinarith
    · left
      intro h'
      have : b2 * x = 0 := by linarith
      rcases mul_eq_zero.1 this with h'' | h''
      · exact hb2 h''
      · linarith

/-- **The corner of a top vertex contains the corner after the slit**: if the corner from `B`
to `A` (both not above the horizontal) contains a horizontal direction, it contains every
horizontal direction of the corner from `B` to the upward slit. -/
theorem ccw_lower_right {a x σ₀ : ℝ} {A B : Point} (ha : 0 < a) (hA : A.2 ≤ 0) (hB : B.2 ≤ 0)
    (h0 : sideCcw B ((σ₀, 0) : Point) A) (h : sideCcw B ((x, 0) : Point) ((0, a) : Point)) :
    sideCcw B ((x, 0) : Point) A := by
  have hx := ccw_up_right ha hB h
  have hBw : B.2 < 0 ∨ B.1 < 0 := by
    unfold sideCcw sideCross sideDot at h
    simp only at h
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
  have hc := ccw_horiz_lower hA hB h0
  obtain ⟨b1, b2⟩ := B
  obtain ⟨a1, a2⟩ := A
  simp only at hA hB hBw
  simp only [sideCcw, sideCross, sideDot] at hc ⊢
  rcases hc with hc | ⟨hc, hd⟩
  · refine Or.inr (Or.inl ⟨hc, Or.inl ?_⟩)
    rcases lt_or_eq_of_le hB with hb2 | hb2
    · nlinarith
    · exfalso
      subst hb2
      rcases hBw with h' | h'
      · linarith
      · nlinarith
  · refine Or.inr (Or.inr (Or.inr ⟨hc, hd, ?_⟩))
    by_cases hb2 : b2 = 0
    · right
      subst hb2
      rcases hBw with h' | h'
      · linarith
      · nlinarith
    · left
      intro h'
      have : b2 * x = 0 := by linarith
      rcases mul_eq_zero.1 this with h'' | h''
      · exact hb2 h''
      · linarith

/-! ## The correspondence without a separating chord -/

section CorrRight0

variable (J : Merge.Junction)

theorem corr_right0 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    Corr0 (chainModel J.whole) (chainModel J.right) (F₂plus J S₂) S₂
      (6 + tpos J.whole J.m₁) (6 + tpos J.right 0) (rL1 J) (rL2 J) (rδ J) := by
  unfold rL1 rL2 rδ
  set C := J.whole with hC
  set C₂ := J.right with hC₂
  set W := (chainModel C).W with hW
  set W₂ := (chainModel C₂).W with hW₂
  have hn : W.n = 2 * C.m + 7 := cm_n C
  have hn₂ : W₂.n = 2 * C₂.m + 7 := cm_n C₂
  have hwm : C.m = J.m₁ + J.m₂ := rfl
  have hm2 : C₂.m = J.m₂ := rfl
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  set τ := tpos C J.m₁ with hτ_def
  set τ' := tpos C₂ 0 with hτ'_def
  have hτ : τ < 2 * C.m := tpos_lt C J.m₁
  have hτ' : τ' < 2 * C₂.m := tpos_lt C₂ 0
  set ℓ := 2 * J.m₂ with hℓ_def
  set s := 2 * C.m - τ with hs_def
  set s' := 2 * C₂.m - τ' with hs'_def
  have hT : ∀ e, e ≤ ℓ → tourV C J.m₁ e = tourV C₂ 0 e := fun e he => tourV_right J he
  have hM := walkAx_chainModel (C := C) hP
  have hM₂ := walkAx_chainModel (C := C₂) hP
  have hR : C₂.radius = C.radius := FuseMath.radius_of_P J rfl
  have hg : 6 + τ < W.n := by rwo [hn]
  have hg' : 6 + τ' < W₂.n := by rwo [hn₂]
  have hv0 : W₂.vtx (6 + τ') = J.shared := by
    have := walk_tour C₂ 0 0 (by omega)
    rw [add_zero, Nat.mod_eq_of_lt hg', tourV_right_zero] at this
    exact this
  have hnoV : ∀ L : ℝ, (τ' = 0 → L ≤ 2 * C₂.m) → ∀ p < W₂.n, ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < off W₂.n ((6 + τ' : ℕ) : ℝ) (p + t) → off W₂.n ((6 + τ' : ℕ) : ℝ) (p + t) < L →
      sidePt W₂ p t ≠ W₂.vtx (6 + τ') := by
    intro L hL p hp t ht ht1 hpos hlt heq
    rw [hv0, ← J.right_vertex_zero] at heq
    rcases off_vertex0 C₂ hP hp ht ht1 heq with h | ⟨h0, h⟩
    · rw [h] at hpos; exact lt_irrefl _ hpos
    · have := hL h0
      rw [h] at hlt
      linarith
  have htrans : ∀ c ∈ S₂, ∀ q ∈ c, q ∉ (chainModel C₂).D → q ≠ W₂.vtx (6 + τ') →
      ∃ e ∈ F₂plus J S₂, q ∈ e ∧ e ⊆ c := by
    rw [hv0]; exact trans_right J hP hS₂
  have hnest : ∀ e ∈ F₂plus J S₂, ∀ e' ∈ F₂plus J S₂, e ⊆ e' → e = e' :=
    fun e he e' he' h => augChords_nest (F₂plus_subset J hS₂ he) (F₂plus_subset J hS₂ he') h
  have hFs := F₂plus_subset J hS₂
  have hFf := F₂plus_finite J hS₂f
  have hℓ : ℓ < 2 * C.m := by omega
  have hℓ' : ℓ ≤ 2 * C₂.m := by omega
  have hℓ'R : (ℓ : ℝ) ≤ 2 * C₂.m := by exact_mod_cast hℓ'
  by_cases hsl : s < ℓ
  · -- case Sh: the two boxes at the same offset
    have hss : s = s' := (right_box_eq J hsl).symm
    have hA := agree_Sh hT hR.symm hℓ.le hℓ' hss hsl
    rw [ite_eq_left hsl, ite_eq_left hsl, ite_eq_left hsl]
    refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by rwo [hn],
      by rwo [hn₂], fun _ => rfl, fun h => absurd h (lt_irrefl 0), hA, ?_,
      hnoV _ (fun h0 => absurd h0 (by omega)), htrans, hnest⟩
    intro d hd
    obtain rfl : d = 0 := by omega
    simpa using hA (ℓ + 7) le_rfl
  push Not at hsl
  by_cases hsl' : ℓ ≤ s'
  · -- case N: no box inside the stretch
    have hA := agree_N hT hsl hsl'
    rw [ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ s < ℓ by omega),
      ite_eq_right (show ¬ s < ℓ by omega), ite_eq_left hsl', ite_eq_left hsl', ite_eq_left hsl']
    refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by rwo [hn],
      by rwo [hn₂], fun _ => rfl, fun h => absurd h (lt_irrefl 0), hA, ?_,
      hnoV _ (fun _ => by pcl), htrans, hnest⟩
    intro d hd
    obtain rfl : d = 0 := by omega
    simpa using hA ℓ le_rfl
  -- case G: only the box of `C₂` inside the stretch
  push Not at hsl'
  have hA1 := agree_G1 hT hsl hsl'
  have hA2 := agree_G2 hT hℓ' hsl hsl'
  have hs'1 : 1 ≤ s' := by omega
  rw [ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ s < ℓ by omega),
    ite_eq_right (show ¬ s < ℓ by omega), ite_eq_right (show ¬ ℓ ≤ s' by omega),
    ite_eq_right (show ¬ ℓ ≤ s' by omega), ite_eq_right (show ¬ ℓ ≤ s' by omega)]
  refine ⟨hM, hM₂, hFs, hFf, hS₂, hS₂f, hg, hg', by rwo [hn],
    by rwo [hn₂], fun h => absurd h (by norm_num), fun _ => by rwo [hn₂], hA1, ?_,
    hnoV _ (fun h0 => absurd h0 (by omega)), htrans, hnest⟩
  intro d hd
  have := hA2 d hd
  rwa [Nat.mod_add_mod, Nat.mod_add_mod] at this
end CorrRight0

/-! ## The gap facts in case G -/

section GapRight

variable (J : Merge.Junction)

/-- **The constants of case G** (a gap). -/
theorem caseG_consts (hδ : 0 < rδ J) : rL1 J = 2 * J.right.m - tpos J.right 0 ∧ rδ J = 7 ∧
    rL2 J = 2 * J.m₂ - (2 * J.right.m - tpos J.right 0) ∧
    2 * J.m₂ ≤ 2 * J.whole.m - tpos J.whole J.m₁ ∧
    2 * J.right.m - tpos J.right 0 < 2 * J.m₂ := by
  unfold rL1 rδ rL2 at *
  split_ifs at * <;> first | omega

/-- **Points of the stretch are points of `C₂`** in case G. -/
theorem strPt_mem_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) {x : Point}
    (hx : StrPt (chainModel J.whole) (6 + tpos J.whole J.m₁) (rL1 J + rL2 J) x) :
    x ∈ J.right.set := by
  obtain ⟨d, hd, t, ht0, ht1, -, rfl⟩ := hx
  have hC := corr_right0 J hP hS₂ hS₂f
  rw [hC.sidePt_eq hd t]
  have hn₂ := cm_n J.right
  have hτ' := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  obtain ⟨h1, h2, h3, -, -⟩ := caseG_consts J hδ
  obtain ⟨i, hi, hq⟩ : ∃ i, i < 2 * J.right.m ∧
      (6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n = i + 6 := by
    unfold dq
    rw [hn₂, h1, h2]
    split_ifs with hdl
    · exact ⟨tpos J.right 0 + d, by omega, by rwring [Nat.mod_eq_of_lt (by omega)]⟩
    · refine ⟨d - (2 * J.right.m - tpos J.right 0), by omega, ?_⟩
      rw [show 6 + tpos J.right 0 + (d + 7) = (d - (2 * J.right.m - tpos J.right 0) + 6) +
        (2 * J.right.m + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hq]
  exact J.right.sideWalk_tour_pt_mem _ hi.le (fun h => by omega) ht0 ht1

/-- **Points strictly inside the gap are not points of `C₂`**: the slit above the top and the
sides of the box. -/
theorem gap_not_mem (hδ : 0 < rδ J) {pa : ℕ} {ta : ℝ} (hpa : pa < (chainModel J.right).W.n)
    (hta0 : 0 ≤ ta) (hta1 : ta < 1)
    (h1 : (rL1 J : ℝ) < off (chainModel J.right).W.n (6 + tpos J.right 0 : ℕ) (pa + ta))
    (h2 : off (chainModel J.right).W.n (6 + tpos J.right 0 : ℕ) (pa + ta) < rL1 J + rδ J) :
    sidePt (chainModel J.right).W pa ta ∉ J.right.set := by
  obtain ⟨hL1, hδ7, -, -, -⟩ := caseG_consts J hδ
  set C₂ := J.right with hC₂
  have hn₂ : (chainModel C₂).W.n = 2 * C₂.m + 7 := cm_n C₂
  have hτ' := tpos_lt C₂ 0
  have hg' : 6 + tpos C₂ 0 < (chainModel C₂).W.n := by omega
  rw [off_key' hg' hpa hta0 hta1, hL1] at h1 h2
  rw [hδ7] at h2
  set e := dOf (chainModel C₂).W.n (6 + tpos C₂ 0) pa with he
  have hpae : (6 + tpos C₂ 0 + e) % (chainModel C₂).W.n = pa := add_dOf hg' hpa
  have hge : 2 * C₂.m - tpos C₂ 0 ≤ e := by
    by_contra hc; push Not at hc
    have : (e : ℝ) + 1 ≤ ((2 * C₂.m - tpos C₂ 0 : ℕ) : ℝ) := by exact_mod_cast hc
    linarith
  have hle : e ≤ 2 * C₂.m - tpos C₂ 0 + 6 := by
    by_contra hc; push Not at hc
    have : ((2 * C₂.m - tpos C₂ 0 : ℕ) : ℝ) + 7 ≤ e := by exact_mod_cast hc
    push_cast at h2
    linarith
  have hR := C₂.top_snd_lt_radius
  have hRp := C₂.radius_pos
  have hout : ∀ z : Point, (C₂.top.2 < z.2 ∨ C₂.radius ≤ |z.1| ∨ C₂.radius ≤ |z.2|) →
      z ∉ C₂.set := by
    intro z hz hmem
    have hb := C₂.set_subset_box hmem
    have htop := C₂.snd_le_top_of_mem_set hmem
    rcases hz with hz | hz | hz
    · linarith
    · exact absurd hb.1 (not_lt.2 hz)
    · exact absurd hb.2 (not_lt.2 hz)
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C₂.sidePt_box C₂.sideBeta ta
  rw [cm_W] at hpa hpae ⊢
  rw [show (C₂.sideWalk C₂.sideBeta).n = 2 * C₂.m + 7 from hn₂] at hpae
  rw [← hpae]
  apply hout
  rcases Nat.eq_or_lt_of_le hge with heq | hlt
  · -- the slit above the top
    rw [← heq, show 6 + tpos C₂ 0 + (2 * C₂.m - tpos C₂ 0) = 2 * C₂.m + 6 by omega,
      Nat.mod_eq_of_lt (by omega), b6]
    left
    have hta : 0 < ta := by
      rw [← heq] at h1; push_cast [show tpos C₂ 0 ≤ 2 * C₂.m by omega] at h1; linarith
    simp only
    nlinarith
  · obtain ⟨j, hj⟩ : ∃ j, e = 2 * C₂.m - tpos C₂ 0 + 1 + j := ⟨e - (2 * C₂.m - tpos C₂ 0 + 1),
      by omega⟩
    rw [show 6 + tpos C₂ 0 + e = j + (2 * C₂.m + 7) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    have hj5 : j ≤ 5 := by omega
    interval_cases j
    · rw [b0]; right; right; simp only; rw [abs_of_pos hRp]
    · rw [b1]; right; left; simp only; rw [abs_neg, abs_of_pos hRp]
    · rw [b2]; right; right; simp only; rw [abs_neg, abs_of_pos hRp]
    · rw [b3]; right; left; simp only; rw [abs_of_pos hRp]
    · rw [b4]; right; right; simp only; rw [abs_of_pos hRp]
    · rw [b5]; left; sinl only

/-- **The split vertex of the walk of `C`** in case G: its point is the top of `C₂`, and its
left sector is the corner `tour(2m₂-1) → top → tour(1)` of the walk of `C₂`. -/
theorem split_facts (hδ : 0 < rδ J) :
    sidePt (chainModel J.whole).W
        ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 = J.right.top ∧
      ∀ x, sideLeft (chainModel J.whole).W
          ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 x ↔
        sideLeftOf (J.right.sideTour J.right.sideBeta (2 * J.right.m - 1)) J.right.top
          (J.right.sideTour J.right.sideBeta 1) x := by
  obtain ⟨hL1, -, -, hsl0, hsl0'⟩ := caseG_consts J hδ
  rw [hL1]
  set C := J.whole with hC
  set C₂ := J.right with hC₂
  set W := (chainModel C).W with hW
  set W₂ := (chainModel C₂).W with hW₂
  have hn : W.n = 2 * C.m + 7 := cm_n C
  have hn₂ : W₂.n = 2 * C₂.m + 7 := cm_n C₂
  have hwm : C.m = J.m₁ + J.m₂ := rfl
  have hm2 : C₂.m = J.m₂ := rfl
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  set τ := tpos C J.m₁ with hτ_def
  set τ' := tpos C₂ 0 with hτ'_def
  have hτ : τ < 2 * C.m := tpos_lt C J.m₁
  have hτ' : τ' < 2 * C₂.m := tpos_lt C₂ 0
  set ℓ := 2 * J.m₂ with hℓ_def
  set s' := 2 * C₂.m - τ' with hs'_def
  have hT : ∀ e, e ≤ ℓ → tourV C J.m₁ e = tourV C₂ 0 e := fun e he => tourV_right J he
  have hℓ' : ℓ ≤ 2 * C₂.m := by omega
  have hsl : ℓ ≤ 2 * C.m - τ := hsl0
  have hsl' : s' < ℓ := hsl0'
  have hA1 := agree_G1 hT hsl hsl'
  have hA2 := agree_G2 hT hℓ' hsl hsl'
  have hs'1 : 1 ≤ s' := by omega
  set k₀ := (6 + τ + s') % W.n with hk₀
  have hpt : W.vtx k₀ = C₂.top := by
    rw [hA1 s' le_rfl]
    have := walk_box C₂ 0 0 (by omega)
    rw [add_zero] at this
    exact this
  have hprev : Chazelle.Chain.sidePrev W k₀ 0 = C₂.sideTour C₂.sideBeta (2 * C₂.m - 1) := by
    unfold Chazelle.Chain.sidePrev
    rw [ite_eq_left rfl, hk₀, mod_pred_mod (by omega) _ hs'1, hA1 (s' - 1) (by omega),
      show 6 + τ' + (s' - 1) = (2 * C₂.m - 1) + 6 by omega,
      Nat.mod_eq_of_lt (by rwo [hn₂])]
    exact C₂.sideWalk_vtx_tour _ (by omega)
  have hnext : Chazelle.Chain.sideNext W k₀ = C₂.sideTour C₂.sideBeta 1 := by
    unfold Chazelle.Chain.sideNext
    rw [hk₀, hA2 1 (by omega)]
    rw [show (6 + τ' + s' + 7) % W₂.n = 6 by
        rw [hn₂, show 6 + τ' + s' + 7 = 6 + (2 * C₂.m + 7) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)],
      Nat.mod_eq_of_lt (show 6 + 1 < W₂.n by rwo [hn₂])]
    exact C₂.sideWalk_vtx_tour _ (by omega)
  have hpt' : sidePt W k₀ 0 = C₂.top := by rw [Chazelle.Chain.sidePt_zero, hpt]
  refine ⟨hpt', fun x => ?_⟩
  unfold sideLeft
  rw [hprev, hnext, hpt']

/-- The walk of `C₂` around the copy of the top before the slit and after it (case G). -/
theorem gap_walk (hδ : 0 < rδ J) :
    (6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n = 2 * J.right.m + 6 ∧
    (6 + tpos J.right 0 + (rL1 J + rδ J)) % (chainModel J.right).W.n = 6 ∧
    (chainModel J.right).W.vtx (2 * J.right.m + 6) = J.right.top ∧
    (chainModel J.right).W.vtx 0 = J.right.slitTop ∧
    (chainModel J.right).W.vtx (2 * J.right.m + 5) =
      J.right.sideTour J.right.sideBeta (2 * J.right.m - 1) ∧
    (chainModel J.right).W.vtx 6 = J.right.top ∧
    (chainModel J.right).W.vtx 5 = J.right.slitTop ∧
    (chainModel J.right).W.vtx 7 = J.right.sideTour J.right.sideBeta 1 := by
  obtain ⟨hL1, hδ7, -, -, -⟩ := caseG_consts J hδ
  have hn₂  := cm_n J.right
  have hτ' := tpos_lt J.right 0
  have hm := J.right.one_le
  rw [hL1, hδ7, hn₂]
  refine ⟨by rw [show 6 + tpos J.right 0 + (2 * J.right.m - tpos J.right 0) = 2 * J.right.m + 6
      by omega]; exact Nat.mod_eq_of_lt (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 6 + tpos J.right 0 + (2 * J.right.m - tpos J.right 0 + 7) = 6 + (2 * J.right.m + 7)
      by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  · rw [cm_W, show 2 * J.right.m + 6 = 2 * J.right.m + 6 from rfl,
      J.right.sideWalk_vtx_tour _ le_rfl, J.right.sideTour_two_m]
  · rw [cm_W]; exact J.right.sideWalk_vtx_zero _
  · rw [cm_W, show 2 * J.right.m + 5 = (2 * J.right.m - 1) + 6 by omega,
      J.right.sideWalk_vtx_tour _ (by omega)]
  · rw [cm_W, show (6 : ℕ) = 0 + 6 from rfl, J.right.sideWalk_vtx_tour _ (by omega),
      J.right.sideTour_zero]
  · rw [cm_W]; exact J.right.sideWalk_vtx_five _
  · rw [cm_W, show (7 : ℕ) = 1 + 6 from rfl, J.right.sideWalk_vtx_tour _ (by omega)]


/-- The slit of a chain leaves its top vertically. -/
theorem slitTop_sub_top (C : Chain) : C.slitTop - C.top = ((0, C.radius - C.top.2) : Point) := by
  apply Geometry.point_ext <;> simp [Chain.slitTop]

theorem rayPt_sub_self (u : Point) (σ : ℝ) : rayPt u σ 1 - u = ((σ, 0) : Point) := by
  apply Geometry.point_ext <;> simp [rayPt]

theorem sideTour_sub_top_snd (C : Chain) (β : Bool) (i : ℕ) : (C.sideTour β i - C.top).2 ≤ 0 := by
  have := C.vertex_snd_le_top (C.sideIdx_le β i)
  simp only [Prod.snd_sub, Chain.sideTour]
  linarith

/-- **At each copy of the top of `C₂` next to the slit at most one chord of `S₂` is attached**
(the sector between the vertical slit and the tour contains only one horizontal direction). -/
theorem oneAt_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hδ : 0 < rδ J) :
    ∀ k : ℕ, (k = rL1 J ∨ k = rL1 J + rδ J) → ∀ c ∈ S₂, ∀ c' ∈ S₂,
      SideAttach (chainModel J.right).W c ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 →
      SideAttach (chainModel J.right).W c' ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 →
        c = c' := by
  intro k hk c hc c' hc' hA hA'
  by_contra hne
  have hM₂ := walkAx_chainModel (C := J.right) hP
  have hS : S₂ ⊆ (chainModel J.right).Adm := hS₂
  obtain ⟨g1, g2, v26, v0, v25, v6, v5, v7⟩ := gap_walk J hδ
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have hm := J.right.one_le
  have hRt := J.right.top_snd_lt_radius
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ S₂ ∧ cw ∈ S₂ ∧
      SideAttach (chainModel J.right).W ce ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 ∧
      SideAttach (chainModel J.right).W cw ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 ∧
      (∀ z ∈ ce, (sidePt (chainModel J.right).W
        ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt (chainModel J.right).W
        ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0).1) := by
    rcases hM₂.tie_pair hS hc hc' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c, c', hc, hc', hA, hA', h1, h2⟩
    · exact ⟨c', c, hc', hc, hA', hA, h2, h1⟩
  obtain ⟨-, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM₂.tie_setup (hS hce) (hS hcw) hAe hAw hE hW
  rcases hk with rfl | rfl
  · rw [g1] at hsE
    have e1 : (chainModel J.right).wb (2 * J.right.m + 6) = (chainModel J.right).W.vtx 0 := by
      rw [WalkAx.wb_eq, hn₂, show 2 * J.right.m + 6 + 1 = 2 * J.right.m + 7 by ring, Nat.mod_self]
    have e2 : ((2 * J.right.m + 6) + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n =
        2 * J.right.m + 5 := by
      rw [hn₂, show 2 * J.right.m + 6 + (2 * J.right.m + 7) - 1 = (2 * J.right.m + 5) +
        (2 * J.right.m + 7) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, WalkAx.wa_eq, v0, v25, v26, slitTop_sub_top] at hsE
    have := ccw_up_left (by linarith) (sideTour_sub_top_snd _ _ _) hsE
    linarith
  · rw [g2] at hsW
    have e1 : (chainModel J.right).wb 6 = (chainModel J.right).W.vtx 7 := by
      rw [WalkAx.wb_eq, hn₂, Nat.mod_eq_of_lt (by omega)]
    have e2 : (6 + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n = 5 := by
      rw [hn₂, show 6 + (2 * J.right.m + 7) - 1 = 5 + (2 * J.right.m + 7) by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, WalkAx.wa_eq, v7, v5, v6, slitTop_sub_top] at hsW
    have := ccw_up_right (by linarith) (sideTour_sub_top_snd _ _ _) hsW
    linarith

/-- **A horizontal segment from a point**, as a set of ray points. -/
theorem seg_ray {u w : Point} (hwu : w ≠ u) (hwy : w.2 = u.2) :
    ∃ σ T : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < T ∧
      (∀ s, 0 ≤ s → s ≤ T → rayPt u σ s ∈ Chazelle.segment u w) ∧
      ∀ z ∈ Chazelle.segment u w, ∃ s, 0 ≤ s ∧ s ≤ T ∧ z = rayPt u σ s := by
  have hne : w.1 ≠ u.1 := fun h => hwu (Geometry.point_ext h hwy)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨-1, u.1 - w.1, Or.inr rfl, by linarith, fun s hs0 hs1 => ?_, fun z hz => ?_⟩
    · refine ⟨s / (u.1 - w.1), div_nonneg hs0 (by linarith), (div_le_one (by linarith)).2 hs1, ?_⟩
      apply Geometry.point_ext
      · simp only [rayPt]; fsr
      · simp only [rayPt]; rwring [hwy]
    · obtain ⟨t, ht0, ht1, rfl⟩ := hz
      refine ⟨t * (u.1 - w.1), mul_nonneg ht0 (by linarith), by nlinarith, ?_⟩
      apply Geometry.point_ext
      · sir only [rayPt]
      · simp only [rayPt]; rwring [hwy]
  · refine ⟨1, w.1 - u.1, Or.inl rfl, by linarith, fun s hs0 hs1 => ?_, fun z hz => ?_⟩
    · refine ⟨s / (w.1 - u.1), div_nonneg hs0 (by linarith), (div_le_one (by linarith)).2 hs1, ?_⟩
      apply Geometry.point_ext
      · simp only [rayPt]; field_simp
      · simp only [rayPt]; rwring [hwy]
    · obtain ⟨t, ht0, ht1, rfl⟩ := hz
      refine ⟨t * (w.1 - u.1), mul_nonneg ht0 (by linarith), by nlinarith, ?_⟩
      apply Geometry.point_ext
      · sir only [rayPt]
      · simp only [rayPt]; rwring [hwy]

/-- **A chord of `F₂⁺` through the top of `C₂`, inside a chord of `S₂` attached at a copy of the
top next to the slit, is attached at the split vertex of the walk of `C`.** -/
theorem splitAttach_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hδ : 0 < rδ J) :
    ∀ k : ℕ, (k = rL1 J ∨ k = rL1 J + rδ J) → ∀ c ∈ S₂,
      SideAttach (chainModel J.right).W c ((6 + tpos J.right 0 + k) % (chainModel J.right).W.n) 0 →
      ∀ e ∈ F₂plus J S₂, e ⊆ c → sidePt (chainModel J.whole).W
        ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 ∈ e →
        SideAttach (chainModel J.whole).W e
          ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 := by
  intro k hk c hc hAc e he hec hue
  obtain ⟨hpt, hsec⟩ := split_facts J hδ
  obtain ⟨g1, g2, v26, v0, v25, v6, v5, v7⟩ := gap_walk J hδ
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hm := J.right.one_le
  have hRt := J.right.top_snd_lt_radius
  have hM := walkAx_chainModel (C := J.whole) hP
  have heA : e ∈ (chainModel J.whole).Adm := F₂plus_subset J hS₂ he
  set u := J.right.top with hu_def
  rw [hpt] at hue
  have huD : u ∉ (chainModel J.whole).D := by
    rw [← hpt]; exact hM.trace _ (Nat.mod_lt _ (by omega)) 0 le_rfl zero_le_one
  -- `e` is a horizontal segment from `u`
  obtain ⟨w, hwu, hwy, hew⟩ : ∃ w, w ≠ u ∧ w.2 = u.2 ∧ e = Chazelle.segment u w := by
    obtain ⟨a, b, hab, heq, hy, hopen, -, -⟩ := hM.ends e heA
    have hue' := hue
    rw [heq] at hue'
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hue'
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · exact absurd (hs ▸ hopen s ⟨hs0, hs1⟩) huD
      · rw [hs1, Geometry.lerp_one] at hs
        exact ⟨a, fun h => hab (h.trans hs), by rwx [hs], by
          rw [heq, hs, Geometry.segment_comm]⟩
    · rw [← hs0, Geometry.lerp_zero] at hs
      exact ⟨b, fun h => hab (hs.symm.trans h.symm), by rw [hs]; exact hy.symm, by rw [heq, hs]⟩
  obtain ⟨σ, T, hσ, hT, hray, hseg⟩ := seg_ray hwu hwy
  rw [hew] at hec
  -- the direction lies in the sector of `M₂` at the copy of the top
  set P := (6 + tpos J.right 0 + k) % (chainModel J.right).W.n with hP_def
  have hvP : (chainModel J.right).W.vtx P = u := by
    rcases hk with rfl | rfl
    · rw [hP_def, g1, v26]
    · rw [hP_def, g2, v6]
  obtain ⟨-, -, -, -, r, hr, hl⟩ := hAc
  have hsl₂ : sideLeft (chainModel J.right).W P 0 (rayPt u σ 1) := by
    set ε := min (r / 2) T with hε
    have hε0 : 0 < ε := lt_min (by linarith) hT
    have hz := hl (rayPt u σ ε) (hec (hray ε hε0.le (min_le_right _ _)))
      (by rw [Chazelle.Chain.sidePt_zero, hvP]; intro h
          have := congrArg Prod.fst h; simp only [rayPt] at this
          rcases hσ with rfl | rfl <;> linarith)
      (by rw [Chazelle.Chain.sidePt_zero, hvP, dist_rayPt _ hσ hε0.le]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hq : u = sidePt (chainModel J.right).W P 0 := by rw [Chazelle.Chain.sidePt_zero, hvP]
    rw [hq] at hz ⊢
    exact (FuseMath.sideLeft_rayPt hε0).1 hz
  -- the direction lies in the sector of `M` at the split vertex
  obtain ⟨σ₀, -, hl₀⟩ := FuseMath.top_sector J.right hP
  have hB := sideTour_sub_top_snd J.right J.right.sideBeta 1
  have hA := sideTour_sub_top_snd J.right J.right.sideBeta (2 * J.right.m - 1)
  unfold sideLeftOf at hl₀
  rw [rayPt_sub_self] at hl₀
  have hsl : sideLeft (chainModel J.whole).W
      ((6 + tpos J.whole J.m₁ + rL1 J) % (chainModel J.whole).W.n) 0 (rayPt u σ 1) := by
    rw [hsec]
    unfold sideLeftOf
    rw [rayPt_sub_self]
    rw [Chazelle.Chain.sideLeft_zero] at hsl₂
    unfold sideLeftOf at hsl₂
    rw [hvP, rayPt_sub_self] at hsl₂
    rcases hk with rfl | rfl
    · have e1 : (P + 1) % (chainModel J.right).W.n = 0 := by
        rw [hP_def, g1, hn₂, show 2 * J.right.m + 6 + 1 = 2 * J.right.m + 7 by ring, Nat.mod_self]
      have e2 : (P + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n =
          2 * J.right.m + 5 := by
        rw [hP_def, g1, hn₂, show 2 * J.right.m + 6 + (2 * J.right.m + 7) - 1 =
          (2 * J.right.m + 5) + (2 * J.right.m + 7) by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2, v0, v25, slitTop_sub_top] at hsl₂
      exact ccw_lower_left (by linarith) hA hB hl₀ hsl₂
    · have e1 : (P + 1) % (chainModel J.right).W.n = 7 := by
        rw [hP_def, g2, hn₂]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (P + (chainModel J.right).W.n - 1) % (chainModel J.right).W.n = 5 := by
        rw [hP_def, g2, hn₂, show 6 + (2 * J.right.m + 7) - 1 = 5 + (2 * J.right.m + 7) by omega,
          Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2, v7, v5, slitTop_sub_top] at hsl₂
      exact ccw_lower_right (by linarith) hA hB hl₀ hsl₂
  -- the attachment
  refine ⟨Nat.mod_lt _ (by omega), le_rfl, zero_lt_one,
    by rw [hpt, hew]; exact ⟨0, le_rfl, zero_le_one, by simp⟩, 1, one_pos, fun z hz hzu _ => ?_⟩
  rw [hew] at hz
  obtain ⟨s, hs0, -, rfl⟩ := hseg z hz
  have hs : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hzu; rw [← h, hpt]; apply Geometry.point_ext <;> simp [rayPt]
  rw [← hpt] at hsl ⊢
  exact (FuseMath.sideLeft_rayPt hs).2 hsl


/-- **The gap facts for the right side of a junction** (case G). -/
theorem corrGap_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hδ : 0 < rδ J) :
    CorrGap (chainModel J.whole) (chainModel J.right) (F₂plus J S₂) S₂
      (6 + tpos J.whole J.m₁) (6 + tpos J.right 0) (rL1 J) (rL2 J) (rδ J) := by
  refine ⟨fun c hc pa ta hA h1 h2 x hx y hy hxS hyS => ?_, oneAt_right J hP hS₂ hδ,
    splitAttach_right J hP hS₂ hδ⟩
  have hM₂ := walkAx_chainModel (C := J.right) hP
  have hw := gap_not_mem J hδ hA.1 hA.2.1 hA.2.2.1 h1 h2
  have hxs := strPt_mem_right J hP hS₂ hS₂f hδ hxS
  have hys := strPt_mem_right J hP hS₂ hS₂f hδ hyS
  obtain ⟨a, b, -, -, hend⟩ := end_of_not_mem hM₂ (hS₂ hc)
  have notD : ∀ z ∈ J.right.set, z ∉ (chainModel J.right).D :=
    fun z hz hD => J.right.not_mem_set_of_mem_dom hD hz
  have hwD := hM₂.trace _ hA.1 _ hA.2.1 hA.2.2.1.le
  rcases hend _ hx (notD _ hxs) with h1 | h1 <;> rcases hend _ hy (notD _ hys) with h2 | h2 <;>
    rcases hend _ hA.2.2.2.1 hwD with h3 | h3 <;>
    first
    | exact h1.trans h2.symm
    | exact absurd (show sidePt (chainModel J.right).W pa ta ∈ J.right.set by
        rwx [h3, ← h1]) hw
    | exact absurd (show sidePt (chainModel J.right).W pa ta ∈ J.right.set by
        rwx [h3, ← h2]) hw

/-- **The regions of `S₂` at the two sides of the slit of `C₂`** (case G): faced just after the
copy of the top before the slit, or just before the copy after it. -/
def GapLab (S₂ : Set (Set Point)) (V : Set Point) : Prop :=
  0 < rδ J ∧ V ∈ (chainModel J.right).regions S₂ ∧
    (AfterFaces (chainModel J.right) ((6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n) 0 V ∨
      BeforeFaces (chainModel J.right)
        ((6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n) 0 V)

/-- **The label triple**: `V` is the label `λ` or a region at a side of the slit of `C₂`. -/
def LabS (S₂ : Set (Set Point)) (L V : Set Point) : Prop := V = L ∨ GapLab J S₂ V

/-- Combining a valid label with lemma (E). -/
theorem labS_trans {S₂ : Set (Set Point)} {L V₀ V' : Set Point} (h1 : LabS J S₂ L V₀)
    (h2 : V₀ = V' ∨ (GapLab J S₂ V₀ ∧ GapLab J S₂ V')) : LabS J S₂ L V' := by
  rcases h2 with rfl | ⟨-, h⟩
  · exact h1
  · exact Or.inr h

/-- **Lemma (K3) for a junction**: two labels of a region of `F₂⁺` are equal, or both are regions
at the sides of the slit of `C₂`. -/
theorem label_right3 (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions (F₂plus J S₂)) {V V' : Set Point}
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (h : RLabel J S₂ G V) (h' : RLabel J S₂ G V') :
    V = V' ∨ (GapLab J S₂ V ∧ GapLab J S₂ V') := by
  obtain ⟨d, hd, t, ht, hc, hf, hfV⟩ := h
  obtain ⟨d', hd', t', ht', hc', hf', hfV'⟩ := h'
  rcases (corr_right0 J hP hS₂ hS₂f).label_gen3 (corrGap_right J hP hS₂ hS₂f) hd hd' ht ht' hc hc'
    hG hf hf' hV hV' hfV hfV' with h | ⟨hδ, h1, h2⟩ | ⟨hδ, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨hδ, hV, Or.inl h1⟩, ⟨hδ, hV', Or.inr h2⟩⟩
  · exact Or.inr ⟨⟨hδ, hV, Or.inr h1⟩, ⟨hδ, hV', Or.inl h2⟩⟩


end GapRight

end Sweep

end

end Chazelle.Core
