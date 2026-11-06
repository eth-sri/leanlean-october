module

public import Chazelle.Golf

public import Chazelle.Core.SweepMachine6

/-!
# The sweep (WP-D), part 23: the abstract machine, the points of `C₂` lie on the right stretch

* `top_left_of_box`: if the box of the walk of `C` lies inside the left stretch, the top of `C` is
  a vertex of `C₁` (so the top of `C₂` is not above the top of `C₁`).
* `left_pos_cases`: a position of the left stretch corresponds (left correspondence) to a tour
  position of the walk of `C₁`, unless the box of `C` lies inside the left stretch.
* `left_stretch_pt`: a point of `C₂` at a position of the left stretch is the shared vertex.
* `off_right_pt` (**the points of `C₂` other than the shared vertex are on the right stretch**):
  every position of the walk of `C` whose point is such a point has its offset in `(0, L)`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- **The top of `C` lies in `C₁` when the box of `C` lies inside the left stretch.** -/
theorem top_left_of_box (h : 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁) :
    J.right.top.2 ≤ J.left.top.2 := by
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hT := J.whole.topIdx_le
  have hTl : J.whole.topIdx < J.m₁ := by
    ϴ' Merge.Junction.whole_m at hT h
    unfold tpos bS Chain.sideS at h
    ϴ' Merge.Junction.whole_m at h
    cases hb : J.whole.sideBeta <;> ϴ' hb, Bool.false_eq_true, ↓reduceIte at h
    · by_contra hc
      rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
          J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - (2 * (J.m₁ + J.m₂) - J.whole.topIdx) by omega),
        Nat.mod_eq_of_lt (⋄)] at h
      omega
    · rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
          J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx by omega),
        Nat.mod_eq_of_lt (⋄)] at h
      omega
  have e : J.left.top = J.whole.top := by
    unfold Chain.top
    Ξ left_topIdx_eq J hTl
    rfl
  Ξ e
  exact J.right_top_le

/-- **The positions of the left stretch in the walk of `C₁`**: tour positions, unless the box of `C`
lies inside the left stretch. -/
theorem left_pos_cases {d : ℕ} (hd : d < lL1 J + lL2 J) :
    (∃ i, i < 2 * J.m₁ ∧
      (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n = i + 6) ∨
    2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁ := by
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hτ := tpos_lt J.left J.m₁
  have hm1 : J.left.m = J.m₁ := rfl
  Ξ' hm1 at hτ hn₁
  unfold lL1 lL2 lδ dq at *
  by_cases hA : 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁
  · exact Or.inr hA
  · left
    ϴ' ite_eq_right hA at hd ⊢
    Ξ hn₁
    by_cases hN : 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁
    · ϴ' ite_eq_left hN at hd ⊢
      Ξ' hm1 at hN
      have hτ0 : tpos J.left J.m₁ = 0 := ⋄
      refine ⟨d, ⋄, ?_⟩
      Ξ hτ0
      split_ifs <;> (rw [Nat.mod_eq_of_lt (⋄)]; ring)
    · ϴ' ite_eq_right hN at hd ⊢
      Ξ' hm1 at hN hd ⊢
      split_ifs with hdl
      · exact ⟨tpos J.left J.m₁ + d, ⋄, by rw [Nat.mod_eq_of_lt (⋄)]; ring⟩
      · refine ⟨tpos J.left J.m₁ + d - 2 * J.m₁, ⋄, ?_⟩
        rw [show 6 + tpos J.left J.m₁ + (d + 7) = (tpos J.left J.m₁ + d - 2 * J.m₁ + 6) +
          (2 * J.m₁ + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (⋄)]

/-- **A point of `C₂` at a position of the left stretch is the shared vertex.** -/
theorem left_stretch_pt (hP : J.P.Simple) 
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt (chainModel J.whole).W
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t ∈ J.right.set) :
    sidePt (chainModel J.whole).W
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t = J.shared := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hleft : ∀ y, y ∈ J.left.set → y ∈ J.right.set → y = J.shared := by
    intro y h1 h2
    have := (Set.ext_iff.1 (J.left_inter_right hP) y).1 ⟨h1, h2⟩
    exact this
  Ξ' hC.sidePt_eq hd t at hx ⊢
  set q := (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n with hq
  have hqn : q < (chainModel J.left).W.n := Nat.mod_lt _ hC.n₂_pos
  -- a tour position gives a point of `C₁`
  have htour : ∀ i, i ≤ 2 * J.left.m → (i = 2 * J.left.m → t = 0) → q = i + 6 →
      sidePt (chainModel J.left).W q t = J.shared := by
    intro i hi hit hqi
    Ξ' hqi at hx ⊢
    exact hleft _ (J.left.sideWalk_tour_pt_mem J.left.sideBeta hi hit ht0 ht1) hx
  rcases left_pos_cases J hd with ⟨i, hi, hqi⟩ | hA
  · exact htour i (by rw [show J.left.m = J.m₁ from rfl]; omega) (fun h => by
      Ξ' show J.left.m = J.m₁ from rfl at h; omega) hqi
  · -- the box of `C` in the left stretch: points of the box block of `C₁` are not on `C₂`
    have htop := top_left_of_box J hA
    Ξ' cm_W at hx hqn
    have hb := J.right.abs_le_coordBound_of_mem_set hx
    have hR : Jordan.coordBound J.right.P < J.left.radius := by
      Ξ FuseMath.radius_of_P J (C' := J.left) rfl, ← FuseMath.radius_of_P J (C' := J.right) rfl
      exact J.right.coordBound_lt_radius
    have htopR := J.left.top_snd_lt_radius
    have hx2 := J.right.snd_le_top_of_mem_set hx
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := J.left.sidePt_box J.left.sideBeta t
    rcases J.left.sideWalk_pos_cases J.left.sideBeta hqn ht0 with (hp5 | ⟨hq6, htp⟩) | ⟨i, hi, hqi, hit⟩
    · exfalso
      have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := ⋄
      rcases hq' with hq' | hq' | hq' | hq' | hq' | hq' <;> Ξ' hq' at hx hb hx2
      · Ξ' h0 at hb; simp only at hb; have := (abs_le.1 hb.2).2; linarith
      · Ξ' h1 at hb; simp only at hb; have := (abs_le.1 hb.1).1; linarith
      · Ξ' h2 at hb; simp only at hb; have := (abs_le.1 hb.2).1; linarith
      · Ξ' h3 at hb; simp only at hb; have := (abs_le.1 hb.1).2; linarith
      · Ξ' h4 at hb; simp only at hb; have := (abs_le.1 hb.2).2; linarith
      · -- down the slit of `C₁`: the point is the top of `C₁`
        Ξ' h5 at hx hx2 hb
        simp only at hx2 hb
        have ht1' := ht1.le
        have hy : J.left.top.2 + (1 - t) * (J.left.radius - J.left.top.2) ≤ J.right.top.2 := by
          nlinarith
        have : 0 < (1 - t) * (J.left.radius - J.left.top.2) := mul_pos (⟡) (⟡)
        linarith
    · exfalso
      Ξ' hq6 at hx hb hx2
      Ξ' h6 at hx hb hx2
      simp only at hx2
      -- up the slit of `C₁` above its top, at a height `≤ top(C₂) ≤ top(C₁)`
      have hpos : 0 < t * (J.left.radius - J.left.top.2) := mul_pos htp (⟡)
      linarith
    · exact htour i hi hit hqi

/-- **The points of `C₂` other than the shared vertex are on the right stretch**: every position of
the walk of `C` whose point is such a point has its offset in `(0, L)`. -/
theorem off_right_pt_of_vnt (hP : J.P.Simple) 
    (hv : VNotTop J) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hx : sidePt (chainModel J.whole).W p t ∈ J.right.set)
    (hxv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hCr := corr_right0 J hP hS₂ hS₂f
  set n := (chainModel J.whole).W.n with hndef
  set gL := 6 + tpos J.whole (J.m₁ + 2 * J.m₂) with hgL
  set g := 6 + tpos J.whole J.m₁ with hg
  have hsum := rlen_add_llen J hv
  have hbase := base_left J hv
  have hrl := rL1_add_rL2 J
  have hll := lL1_add_lL2 J
  obtain ⟨hpd, -⟩ := hC.decomp hp ht0 ht1
  set d := dOf n gL p with hd
  have hdn : d < n := dOf_lt (⋄) _ _
  by_cases hdl : d < llen J
  · exfalso
    apply hxv
    Ξ' ← hpd at hx ⊢
    exact left_stretch_pt J hP (⋄) ht0 ht1 hx
  · -- the position is in the right stretch
    have e : p = (g + (d - llen J)) % n := by
      Ξ ← hpd, hgL, ← hbase, Nat.mod_add_mod, ← hg
      Ξ show g + rlen J + d = (g + (d - llen J)) + n by omega, Nat.add_mod_right
    have hoff : off (n : ℝ) (g : ℝ) (p + t) = ((d - llen J : ℕ) : ℝ) + t := by
      Ξ e
      exact off_key hCr.hg (⋄) ht0 ht1
    Ξ hoff, hrl
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (d - llen J) with h0 | h0
      · rcases ht0.lt_or_eq with htp | htp
        · rw [h0]; push_cast; linarith
        · exfalso
          apply hxv
          Ξ e, h0, ← htp, add_zero
          have := sidePt_off_zero J hP hS₂ hS₂f (p := g % n) (Nat.mod_lt _ (⋄)) le_rfl
            one_pos (by
              Ξ show ((g % n : ℕ) : ℝ) + 0 = ((((g + 0) % n : ℕ)) : ℝ) + 0 by simp
              rw [off_key hCr.hg (⋄) le_rfl one_pos]; simp)
          rwa [show g % n = (g + 0) % n by simp]
      · have : (1 : ℝ) ≤ ((d - llen J : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
    · have hlt : d - llen J < rlen J := ⋄
      have : ((d - llen J : ℕ) : ℝ) + 1 ≤ (rlen J : ℝ) := by exact_mod_cast hlt
      linarith

/-- **The points of `C₂` other than the shared vertex are on the right stretch** (general form;
when the shared vertex is the top of `C`, the box block of `C` lies between the two stretches and
carries no point of `C₂`). -/
theorem off_right_pt (hP : J.P.Simple) 
    {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hx : sidePt (chainModel J.whole).W p t ∈ J.right.set)
    (hxv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
  by_cases hv : VNotTop J
  · exact off_right_pt_of_vnt J hP hv hS₂ hS₂f hp ht0 ht1 hx hxv
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hτ := tpos_lt J.whole J.m₁
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  unfold VNotTop at hv
  have hrl : rL1 J + rL2 J = 2 * J.m₂ := by
    rw [rL1_add_rL2]; unfold rlen; Ξ ite_eq_right (⋄)
  have hT2' : tpos J.whole (J.m₁ + 2 * J.m₂) = 2 * J.m₂ ∨
      tpos J.whole (J.m₁ + 2 * J.m₂) = 0 := by
    Ξ tpos_second J
    rcases (show tpos J.whole J.m₁ = 0 ∨ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m by omega)
      with h | h
    · left; Ξ h, zero_add, Nat.mod_eq_of_lt (⋄)
    · right; Ξ h, Nat.mod_self
  have hll : lL1 J + lL2 J = 2 * J.m₁ := by
    rw [lL1_add_lL2]; unfold llen; Ξ ite_eq_right (⋄)
  -- no box position carries a point of the chain
  have hbox : ¬ (p ≤ 5 ∨ (p = 2 * J.whole.m + 6 ∧ 0 < t)) := fun hb =>
    (J.whole.sideWalk_box_pt J.whole.sideBeta hb ht0 ht1).1 (J.right_set_subset hx)
  have hg : 6 + tpos J.whole J.m₁ < (chainModel J.whole).W.n := ⋄
  -- the copies of the shared vertex at the walk vertices `6 + τ` and `6 + τ + 2 m₂`
  have hv0 : (chainModel J.whole).W.vtx (6 + tpos J.whole J.m₁) = J.shared := by
    have := walk_tour J.whole J.m₁ 0 (⋄)
    Ξ' add_zero, Nat.mod_eq_of_lt hg, tourV_right J (Nat.zero_le _), tourV_right_zero at this
    exact this
  have htop6 : (chainModel J.whole).W.vtx 6 = (chainModel J.whole).W.vtx (2 * J.whole.m + 6) := by
    rw [cm_W, J.whole.sideWalk_vtx_six, J.whole.sideWalk_vtx_tour _ le_rfl,
      J.whole.sideTour_two_m]
  -- the left stretch carries no point of `C₂` but the shared vertex
  have hleft : ∀ d, d < 2 * J.m₁ →
      p = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n → False := by
    intro d hd hpd
    apply hxv
    Ξ' hpd at hx ⊢
    exact left_stretch_pt J hP (⋄) ht0 ht1 hx
  -- the right stretch
  have hright : ∀ d, d < 2 * J.m₂ → p = (6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n →
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (p + t) <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
    intro d hd hpd
    Ξ hpd, off_key hg (⋄) ht0 ht1, hrl
    have hd' : (d : ℝ) + 1 ≤ ((2 * J.m₂ : ℕ) : ℝ) := by exact_mod_cast hd
    refine ⟨?_, ⟡⟩
    rcases Nat.eq_zero_or_pos d with rfl | hdp
    · rcases ht0.lt_or_eq with htp | htp
      · push_cast; linarith
      · exfalso; apply hxv
        Ξ hpd, ← htp, Chazelle.Chain.sidePt_zero, add_zero, Nat.mod_eq_of_lt hg
        exact hv0
    · have : (1 : ℝ) ≤ d := by exact_mod_cast hdp
      linarith
  have hp6 : 6 ≤ p := ⋄
  rcases (show tpos J.whole J.m₁ = 0 ∨ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m by omega)
    with hA | hB
  · -- the right stretch starts at the walk vertex `6`, the box block follows the left stretch
    have hL : tpos J.whole (J.m₁ + 2 * J.m₂) = 2 * J.m₂ := by
      Ξ tpos_second J, hA, zero_add, Nat.mod_eq_of_lt (⋄)
    rcases (show p = 2 * J.whole.m + 6 ∨ p < 2 * J.whole.m + 6 by omega) with hpe | hpe
    · exfalso
      have ht : t = 0 := by
        rcases ht0.lt_or_eq with h | h
        · exact absurd (Or.inr ⟨hpe, h⟩) hbox
        · exact h.symm
      apply hxv
      Ξ hpe, ht, Chazelle.Chain.sidePt_zero, ← htop6, ← hv0, hA
    · by_cases hi : p - 6 < 2 * J.m₂
      · exact hright (p - 6) hi (by rw [hA, Nat.mod_eq_of_lt (⋄)]; omega)
      · exact (hleft (p - 6 - 2 * J.m₂) (⋄)
          (by rw [hL, Nat.mod_eq_of_lt (⋄)]; omega)).elim
  · -- the left stretch starts at the walk vertex `6`, the box block follows the right stretch
    have hL : tpos J.whole (J.m₁ + 2 * J.m₂) = 0 := by
      Ξ tpos_second J, hB, Nat.mod_self
    rcases (show p = 2 * J.whole.m + 6 ∨ p < 2 * J.whole.m + 6 by omega) with hpe | hpe
    · exfalso
      have ht : t = 0 := by
        rcases ht0.lt_or_eq with h | h
        · exact absurd (Or.inr ⟨hpe, h⟩) hbox
        · exact h.symm
      apply hxv
      have := walk_tour J.whole J.m₁ (2 * J.m₂) (⋄)
      rw [tourV_right J le_rfl, tourV_right_end,
        Nat.mod_eq_of_lt (show 6 + tpos J.whole J.m₁ + 2 * J.m₂ < (chainModel J.whole).W.n by
          omega)] at this
      Ξ hpe, ht, Chazelle.Chain.sidePt_zero, ← this
      congr 1; omega
    · by_cases hi : tpos J.whole J.m₁ ≤ p - 6
      · exact hright (p - 6 - tpos J.whole J.m₁) (⋄)
          (by rw [Nat.mod_eq_of_lt (⋄)]; omega)
      · exact (hleft (p - 6) (⋄) (by rw [hL, Nat.mod_eq_of_lt (⋄)]; omega)).elim

end Machine

end Sweep

end

end Chazelle.Core
