module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepMachine19

/-!
# The sweep (WP-D), part 36: the abstract machine when the shared vertex is the top of `C`

When the shared vertex `v` is the top of `C` (`¬ VNotTop J`), it is also the top of `C₁` and of
`C₂` (`TopStrict`), and the box block of the walk of `C` lies between the two stretches: after
the left stretch (`τ = 0`, then the start of the `C₁` part follows the right stretch as usual) or
before it (`τ + 2 m₂ = 2 m`, then the `C₁` part is the box block followed by the left stretch).
The box block of `C` agrees with the box block of `C₁` (same top, same radius), so detection shots
of the model of `C₁` arriving on its box block give attachments on the box block of `C`.

* `vtop_cases`, `shared_eq_top`, `left_top_eq`, `right_top_eq`: the three tops are `v`;
* `box_agree`: the box blocks of `C` and `C₁` agree;
* `lOff`, `lOff_eq`, `off_left_gen`, `cut_of_genuine_gen`: offsets of the left stretch in all
  cases (`lOff = L` unless the box block precedes the left stretch, then `L + 7`);
* `off_box_pos`, `attach_box_of_arrival`, `genuine_of_attach_box`, `cut_of_genuine_box`: detection
  on the box block of `C` (soundness and completeness), when `v` is the top of `C`.

(`off_right_pt` and its consequences `stretch_end`, `next_event_origin`, `sideLabel_piece`,
`afterOK_piece`, `afterOK_piece_tie` hold without `VNotTop`.)
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

/-- The box block is determined by the top and the radius. -/
theorem boxPt_congr {C C' : Chain} (ht : C.top = C'.top) (hR : C.radius = C'.radius) (e : ℕ) :
    boxPt C e = boxPt C' e := by
  simp_all [boxPt, Chazelle.Chain.slitTop] 

section Machine

variable (J : Merge.Junction)

section
variable (hv : ¬ VNotTop J)
include hv
/-- The two cases of `¬ VNotTop`. -/
theorem vtop_cases :
    tpos J.whole J.m₁ = 0 ∨ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m := by
  grind [VNotTop]

/-- **The shared vertex is the top of `C`** (`¬ VNotTop`). -/
theorem shared_eq_top : J.shared = J.whole.top := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  
  rcases vtop_cases J hv with hA | hB
  · have := walk_tour J.whole J.m₁ 0 (by omega)
    rw [add_zero, hA, add_zero, Nat.mod_eq_of_lt (by omega), tourV_right J (Nat.zero_le _),
      tourV_right_zero, cm_W, J.whole.sideWalk_vtx_six] at this
    simp_all
  · have := walk_tour J.whole J.m₁ (2 * J.m₂) (by omega)
    rw [tourV_right J le_rfl, tourV_right_end,
      show 6 + tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m + 6 by omega,
      Nat.mod_eq_of_lt (by omega), cm_W, J.whole.sideWalk_vtx_tour _ le_rfl,
      J.whole.sideTour_two_m] at this
    simp_all

/-- The top of `C₁` is the shared vertex (`¬ VNotTop`). -/
theorem left_top_eq : J.left.top = J.shared := by
  have h := shared_eq_top J hv
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hm1 : J.left.m = J.m₁ := rfl
  have hv1 : J.whole.vertex J.m₁ = J.shared := rfl
  have hkm : J.whole.topIdx ≤ J.m₁ :=
    J.whole.topIdx_min (j := J.m₁) (by omega) fun i hi => by
      rw [hv1, h]; exact J.whole.vertex_snd_le_top hi
  have hle : J.left.topIdx ≤ J.whole.topIdx :=
    J.left.topIdx_min (j := J.whole.topIdx) (by omega) fun i hi => by
      rw [← J.whole_vertex, ← J.whole_vertex]
      exact J.whole.vertex_snd_le_top (by omega)
  have hge : J.whole.topIdx ≤ J.left.topIdx := by
    have hlt := J.left.topIdx_le
    refine J.whole.topIdx_min (j := J.left.topIdx) (by omega) fun i hi => ?_
    rw [J.whole_vertex J.left.topIdx]
    have h3 : (J.left.vertex J.m₁).2 ≤ (J.left.vertex J.left.topIdx).2 :=
      J.left.vertex_snd_le_top (by omega)
    have h4 : J.left.vertex J.m₁ = J.whole.top := by aesop
    rw [h4] at h3
    exact (J.whole.vertex_snd_le_top hi).trans h3
  show J.left.vertex J.left.topIdx = J.shared
  rw [le_antisymm hle hge, ← J.whole_vertex, h]; rfl

/-- **The box blocks of `C` and `C₁` agree** (`¬ VNotTop`): from the end of the tour of `C` and
of `C₁` (walk vertices `2m + 6` and `2m₁ + 6`), seven edges. -/
theorem box_agree :
    Agree (chainModel J.whole).W (chainModel J.left).W (2 * J.whole.m + 6) (2 * J.left.m + 6) 7 := by
  intro e he
  have h1 := walk_box J.whole 0 e he
  have h2 := walk_box J.left 0 e he
  have hτ := tpos_lt J.whole 0
  have hτ₁ := tpos_lt J.left 0
  rw [show 6 + tpos J.whole 0 + (2 * J.whole.m - tpos J.whole 0) + e = 2 * J.whole.m + 6 + e by
    omega] at h1
  rw [show 6 + tpos J.left 0 + (2 * J.left.m - tpos J.left 0) + e = 2 * J.left.m + 6 + e by
    omega] at h2
  rw [h1, h2]
  refine boxPt_congr ?_ ?_ e
  · rw [← shared_eq_top J hv, left_top_eq J hv]
  aesop

/-! ## Offsets of the left stretch in all cases -/


end

/-- The offset of the base of the left stretch. -/
noncomputable def lOff : ℕ :=
  dOf (chainModel J.whole).W.n (6 + tpos J.whole J.m₁) (6 + tpos J.whole (J.m₁ + 2 * J.m₂))

/-- **The offset of the left base**: `2 m₂` when the second copy of `v` comes before the end of
the tour of `C`, else `2 m₂ + 7` (the box block of `C` is passed in between). -/
theorem lOff_eq : lOff J = if tpos J.whole J.m₁ + 2 * J.m₂ < 2 * J.whole.m then 2 * J.m₂
    else 2 * J.m₂ + 7 := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have h1 := J.one_le_m₁
  unfold lOff dOf
  rw [tpos_second J, hn]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h, show 6 + (tpos J.whole J.m₁ + 2 * J.m₂) + (2 * J.whole.m + 7) -
      (6 + tpos J.whole J.m₁) = 2 * J.m₂ + (2 * J.whole.m + 7) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · have e : (tpos J.whole J.m₁ + 2 * J.m₂) % (2 * J.whole.m) =
        tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, show 6 + (tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m) + (2 * J.whole.m + 7) -
        (6 + tpos J.whole J.m₁) = 2 * J.m₂ + 7 by omega, Nat.mod_eq_of_lt (by omega)]

/-- The left stretch fits after its base offset. -/
theorem lOff_add_llen : lOff J + llen J ≤ (chainModel J.whole).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have h1 := J.one_le_m₁
  rw [lOff_eq, hn]
  unfold llen
  rw [tpos_second J]
  by_cases h : tpos J.whole J.m₁ + 2 * J.m₂ < 2 * J.whole.m
  · grind
  · have e : (tpos J.whole J.m₁ + 2 * J.m₂) % (2 * J.whole.m) =
        tpos J.whole J.m₁ + 2 * J.m₂ - 2 * J.whole.m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e]; split_ifs <;> omega

/-- `lOff = L` when the shared vertex is not the top of `C`. -/
theorem lOff_of_vnt (hv : VNotTop J) : lOff J = rlen J := by
  have hτ := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  obtain ⟨hv1, hv2⟩ := hv
  grind [lOff_eq, rlen]

/-- **Offsets of the left stretch** (all cases): the position `d` of the left stretch has offset
`lOff + d`. -/
theorem off_left_gen {d : ℕ} (hd : d < llen J) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ((((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t) =
      (lOff J : ℝ) + d + t := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hτ' := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have hg : 6 + tpos J.whole J.m₁ < (chainModel J.whole).W.n := by omega
  have hgL : 6 + tpos J.whole (J.m₁ + 2 * J.m₂) < (chainModel J.whole).W.n := by omega
  have hsum := lOff_add_llen J
  have e : (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n =
      (6 + tpos J.whole J.m₁ + (lOff J + d)) % (chainModel J.whole).W.n := by
    have hb := add_dOf hg hgL
    unfold lOff
    rw [← add_assoc]
    conv_rhs => rw [← Nat.mod_add_mod, hb]
  rw [e, off_key hg (by omega) ht ht1]
  grind

/-- **A genuine hit on the left stretch is a cut at offset `lOff + d + t`** (all cases; see
`cut_of_genuine`). -/
theorem cut_of_genuine_gen (hP : J.P.Simple) {a : Point}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ)
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ
      ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t) :
    SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ)
        ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ((((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t) =
        (lOff J : ℝ) + d + t := by
  refine ⟨?_, ?_⟩
  · unfold Merge.shoot
    rw [hhit]
    exact attach_whole_of_arrival J hP hσ hτ hd hsec hA
  · exact off_left_gen J (by rw [← lL1_add_lL2 J]; exact hd) hA.2.1 hA.2.2.1

/-! ## Detection on the box block of `C` (`¬ VNotTop`) -/

/-- **Offsets of the box block of `C`**: the position `(2m + 6 + d, t)` has offset
`2m - τ + d + t`. -/
theorem off_box_pos {d : ℕ} (hd : d < 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ((((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t) =
      ((2 * J.whole.m - tpos J.whole J.m₁ : ℕ) : ℝ) + d + t := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ := tpos_lt J.whole J.m₁
  have hg : 6 + tpos J.whole J.m₁ < (chainModel J.whole).W.n := by omega
  rw [show 2 * J.whole.m + 6 + d = 6 + tpos J.whole J.m₁ + (2 * J.whole.m - tpos J.whole J.m₁ + d)
    by omega, off_key hg (by omega) ht ht1]
  grind

/-- **Soundness on the box block**: a detection hit arriving at a position of the box block of the
model of `C₁` (not its first vertex) gives the piece attached at the corresponding position of
the box block of `C`. -/
theorem attach_box_of_arrival (hv : ¬ VNotTop J) {a : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) {d : ℕ} (hd : d < 7) {t : ℝ}
    (hsec : t = 0 → 1 ≤ d)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ
      ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t) :
    SideAttach (chainModel J.whole).W (Chazelle.segment a (rayPt a σ τ))
      ((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n) t := by
  have hB := box_agree J hv
  have hn : 0 < (chainModel J.whole).W.n := by rw [cm_n]; omega
  have hn₁ : 0 < (chainModel J.left).W.n := by rw [cm_n]; omega
  exact (hB.sideAttach_iff hn hn₁ hd hsec _).2 (attach_left_of_arrival hσ hτ hA)

/-- **Completeness on the box block**: a shot of `C` (free, from a point not above the top of
`C₁`) whose chord is attached at a position of the box block of `C` (not its first vertex) at its
first hit is genuine in the model of `C₁`, arriving at the corresponding position of its box
block. -/
theorem genuine_of_attach_box (hP : J.P.Simple) (hv : ¬ VNotTop J)
    {a : Point} (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hfree : FreeAt J.whole a σ) {d : ℕ} (hd : d < 7) {t : ℝ} (hsec : t = 0 → 1 ≤ d)
    (hA : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ)
      ((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n) t)
    (hend : sidePt (chainModel J.whole).W
      ((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n) t =
        rayPt a σ (J.whole.hitParam a σ)) :
    Genuine J.left a σ (J.whole.hitParam a σ) ∧
      Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
        ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t := by
  have hB := box_agree J hv
  have hn : 0 < (chainModel J.whole).W.n := by rw [cm_n]; omega
  have hn₁ : 0 < (chainModel J.left).W.n := by rw [cm_n]; omega
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hM₁ : WalkAx (chainModel J.left) := hC.hM₂
  set T := J.whole.hitParam a σ with hT
  have hz' : a.2 ≤ J.whole.top.2 := ha₁.trans J.left_top_le
  obtain ⟨hT0, -, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  have hA₁ := (hB.sideAttach_iff hn hn₁ hd hsec _).1 hA
  have hpt : sidePt (chainModel J.left).W
      ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t = rayPt a σ T := by
    rw [← hB.sidePt_eq hd t]; exact hend
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J (hdom s h0 h1) (by simp_all), ?_⟩, ?_⟩
  · rw [← hpt]
    exact hM₁.trace _ hA₁.1 t hA₁.2.1 hA₁.2.2.1.le
  · refine ⟨hA₁.1, hA₁.2.1, hA₁.2.2.1, hpt, ?_⟩
    obtain ⟨r, hr, hnear⟩ := hA₁.2.2.2.2
    set s := min (T / 2) (r / 2) with hs
    have hs0 : 0 < s := lt_min (by linarith) (by linarith)
    have hsT : s < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsr : s < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmem : rayPt (rayPt a σ T) (-σ) s ∈ Merge.shoot J.whole a σ := by
      unfold Merge.shoot
      rw [← hT, rayPt_back]
      have hT' : T ≠ 0 := hT0.ne'
      have e : rayPt a σ (T - s) = lerp a (rayPt a σ T) ((T - s) / T) := by
        apply point_ext <;> simp [rayPt, lerp]; field_simp
      rw [e]
      exact Geometry.lerp_mem_segment _ _ (by positivity)
        (by rw [div_le_one hT0]; linarith)
    have hne : rayPt (rayPt a σ T) (-σ) s ≠ rayPt a σ T := by
      intro h
      have := congrArg Prod.fst h
      simp only [rayPt_fst] at this
      rcases hσ with rfl | rfl <;> linarith
    have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
    have hdist : dist (rayPt (rayPt a σ T) (-σ) s) (rayPt a σ T) < r := by
      rw [dist_rayPt _ hnσ hs0.le]; exact hsr
    have hl := hnear _ hmem (by grind) (by grind)
    have h1 : sideLeft (chainModel J.left).W ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t
        (rayPt (sidePt (chainModel J.left).W
          ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t) (-σ) s) := by
      grind
    have := (sideLeft_rayPt_iff _ _ t (-σ) hs0 one_pos).1 h1
    grind

/-- **A genuine hit on the box block is a cut** of `F` at the corresponding position of the box
block of `C`, at the offset `2m - τ + d + t`. -/
theorem cut_of_genuine_box (hv : ¬ VNotTop J) {a : Point}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ)
    {d : ℕ} (hd : d < 7) {t : ℝ} (hsec : t = 0 → 1 ≤ d)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ
      ((2 * J.left.m + 6 + d) % (chainModel J.left).W.n) t) :
    SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ)
        ((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n) t ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ((((2 * J.whole.m + 6 + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + t) =
        ((2 * J.whole.m - tpos J.whole J.m₁ : ℕ) : ℝ) + d + t := by
  refine ⟨?_, off_box_pos J hd hA.2.1 hA.2.2.1⟩
  unfold Merge.shoot
  rw [hhit]
  exact attach_box_of_arrival J hv hσ hτ hd hsec hA

end Machine

end Sweep

end

end Chazelle.Core
