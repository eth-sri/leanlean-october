module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvAnchor

/-!
# The sweep (WP-D), stage 3: no tie at a copy of the shared vertex beyond the start

* `noTie_top`: at the copies `6` and `2m + 6` of the top of a chain (next to the slit) at most one
  chord of an admissible family is attached (the sector between the vertical slit and the tour
  contains one horizontal direction only; the argument of `oneAt_right`, for any chain);
* `noTieV_arith`: the positions of the shared vertex `v` with an offset beyond the start `Lst` are
  the copies `6` and `2m + 6` of the top of `C` (then `v` is the top of `C`);
* `noTieV` (**`NoTieV`**): no two distinct chords of `F₂⁺` are attached at a position of `v` with
  offset `> Lst`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

namespace Sweep

/-- **No tie next to the slit**: at the copies `6` and `2m + 6` of the top of a chain at most one
chord of an admissible family is attached. -/
theorem noTie_top (C : Chain) (hP : C.P.Simple) {F : Set (Set Point)}
    (hF : F ⊆ (chainModel C).Adm) {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {k : ℕ}
    (hk : k = 6 ∨ k = 2 * C.m + 6) (hA : SideAttach (chainModel C).W c k 0)
    (hA' : SideAttach (chainModel C).W c' k 0) : c = c' := by
  by_contra hne
  have hM := walkAx_chainModel (C := C) hP
  have hn : (chainModel C).W.n = 2 * C.m + 7 := cm_n C
  have hm := C.one_le
  have hRt := C.top_snd_lt_radius
  obtain ⟨ce, cw, hce, hcw, hAe, hAw, hE, hW⟩ : ∃ ce cw, ce ∈ F ∧ cw ∈ F ∧
      SideAttach (chainModel C).W ce k 0 ∧ SideAttach (chainModel C).W cw k 0 ∧
      (∀ z ∈ ce, (sidePt (chainModel C).W k 0).1 ≤ z.1) ∧
      (∀ z ∈ cw, z.1 ≤ (sidePt (chainModel C).W k 0).1) := by
    rcases hM.tie_pair hF hc hc' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c, c', hc, hc', hA, hA', h1, h2⟩
    · exact ⟨c', c, hc', hc, hA', hA, h2, h1⟩
  obtain ⟨-, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup (hF hce) (hF hcw) hAe hAw hE hW
  have v6 : (chainModel C).W.vtx 6 = C.top := by
    rw [cm_W, show (6 : ℕ) = 0 + 6 from rfl, C.sideWalk_vtx_tour _ (by omega), C.sideTour_zero]
  have v5 : (chainModel C).W.vtx 5 = C.slitTop := by rw [cm_W]; exact C.sideWalk_vtx_five _
  have v7 : (chainModel C).W.vtx 7 = C.sideTour C.sideBeta 1 := by
    rw [cm_W, show (7 : ℕ) = 1 + 6 from rfl, C.sideWalk_vtx_tour _ (by omega)]
  have v26 : (chainModel C).W.vtx (2 * C.m + 6) = C.top := by
    rw [cm_W, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
  have v0 : (chainModel C).W.vtx 0 = C.slitTop := by rw [cm_W]; exact C.sideWalk_vtx_zero _
  have v25 : (chainModel C).W.vtx (2 * C.m + 5) = C.sideTour C.sideBeta (2 * C.m - 1) := by
    rw [cm_W, show 2 * C.m + 5 = (2 * C.m - 1) + 6 by omega, C.sideWalk_vtx_tour _ (by omega)]
  rcases hk with rfl | rfl
  · have e1 : (chainModel C).wb 6 = (chainModel C).W.vtx 7 := by
      rw [WalkAx.wb_eq, hn, Nat.mod_eq_of_lt (by omega)]
    have e2 : (6 + (chainModel C).W.n - 1) % (chainModel C).W.n = 5 := by
      rw [hn, show 6 + (2 * C.m + 7) - 1 = 5 + (2 * C.m + 7) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, WalkAx.wa_eq, v7, v5, v6, slitTop_sub_top] at hsW
    have := ccw_up_right (by linarith) (sideTour_sub_top_snd _ _ _) hsW
    linarith
  · have e1 : (chainModel C).wb (2 * C.m + 6) = (chainModel C).W.vtx 0 := by
      rw [WalkAx.wb_eq, hn, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]
    have e2 : ((2 * C.m + 6) + (chainModel C).W.n - 1) % (chainModel C).W.n = 2 * C.m + 5 := by
      rw [hn, show 2 * C.m + 6 + (2 * C.m + 7) - 1 = (2 * C.m + 5) + (2 * C.m + 7) by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, WalkAx.wa_eq, v0, v25, v26, slitTop_sub_top] at hsE
    have := ccw_up_left (by linarith) (sideTour_sub_top_snd _ _ _) hsE
    linarith

/-- The arithmetic of the positions of the shared vertex beyond the start. -/
theorem noTieV_arith {m m₁ m₂ b i : ℕ} (hm : m = m₁ + m₂) (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂)
    (hb : b ≤ 2 * m) (hi : i ≤ 2 * m) (hj : Chazelle.Chain.sideE m ((b + i) % (2 * m)) = m₁)
    (hL : (if 2 * m - (m₁ + 2 * m - b) % (2 * m) < 2 * m₂ then 2 * m₂ + 7 else 2 * m₂) <
      (i + 6 + (2 * m + 7) - (6 + (m₁ + 2 * m - b) % (2 * m))) % (2 * m + 7)) :
    i = 0 ∨ i = 2 * m := by
  have hm0 : 0 < 2 * m := by omega
  have d1 := Nat.div_add_mod (b + i) (2 * m)
  have d2 := Nat.div_add_mod (m₁ + 2 * m - b) (2 * m)
  have l1 := Nat.mod_lt (b + i) hm0
  have l2 := Nat.mod_lt (m₁ + 2 * m - b) hm0
  set q1 := (b + i) / (2 * m)
  set r1 := (b + i) % (2 * m)
  set q2 := (m₁ + 2 * m - b) / (2 * m)
  set r2 := (m₁ + 2 * m - b) % (2 * m)
  have hq1 : q1 ≤ 2 := by
    by_contra hc; push Not at hc
    have : 2 * m * 3 ≤ 2 * m * q1 := Nat.mul_le_mul_left _ hc
    omega
  have hq2 : q2 ≤ 1 := by
    by_contra hc; push Not at hc
    have : 2 * m * 2 ≤ 2 * m * q2 := Nat.mul_le_mul_left _ hc
    omega
  have d3 := Nat.div_add_mod (i + 6 + (2 * m + 7) - (6 + r2)) (2 * m + 7)
  have l3 := Nat.mod_lt (i + 6 + (2 * m + 7) - (6 + r2)) (show 0 < 2 * m + 7 by omega)
  set q3 := (i + 6 + (2 * m + 7) - (6 + r2)) / (2 * m + 7)
  set r3 := (i + 6 + (2 * m + 7) - (6 + r2)) % (2 * m + 7)
  have hq3 : q3 ≤ 1 := by
    by_contra hc; push Not at hc
    have : (2 * m + 7) * 2 ≤ (2 * m + 7) * q3 := Nat.mul_le_mul_left _ hc
    omega
  unfold Chazelle.Chain.sideE at hj
  interval_cases q1 <;> interval_cases q2 <;> interval_cases q3 <;> split_ifs at hj hL <;> omega

variable {J : Merge.Junction}

/-- **No tie at a copy of the shared vertex beyond the start.** -/
theorem noTieV (hP : J.P.Simple) {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right) :
    NoTieV J S₂ := by
  intro e he e' he' hne p t hA hA' hpt hL
  have hF : F₂plus J S₂ ⊆ (chainModel J.whole).Adm := F₂plus_subset J hS₂
  have hm1 : J.m₁ ≤ J.whole.m := by
    show J.m₁ ≤ J.m₁ + J.m₂; omega
  obtain ⟨rfl, i, hi, rfl, hidx⟩ := pos_eq_vertex J.whole hP J.whole.sideBeta hA.1 hA.2.1 hA.2.2.1 hm1
    (hpt.trans J.whole_vertex_m₁.symm)
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hp := hA.1
  have hg : gW J < (chainModel J.whole).W.n := by unfold gW; omega
  have hoff : oW J (((i + 6 : ℕ) : ℝ) + 0) = (dOf (chainModel J.whole).W.n (gW J) (i + 6) : ℝ) :=
    Ρ oW, off_key' hg hp le_rfl one_pos, add_zero
  rw [hoff, Lst, rL1_add_rL2] at hL
  have hL' : rlen J < dOf (chainModel J.whole).W.n (gW J) (i + 6) := by exact_mod_cast hL
  have hcase : i = 0 ∨ i = 2 * J.whole.m := by
    have h2 := J.right.one_le
    have h1 := J.one_le_m₁
    unfold rlen dOf gW tpos at hL'
    rw [hn] at hL'
    rw [Chazelle.Chain.sideIdx_eq] at hidx
    exact noTieV_arith (m := J.whole.m) (m₁ := J.m₁) (m₂ := J.m₂) (b := bS J.whole) rfl h1 h2
      (bS_le J.whole) hi hidx hL'
  exact hne (noTie_top J.whole hP hF he he' (by rcases hcase with rfl | rfl <;> simp) hA hA')

end Sweep

end

end Chazelle.Core
