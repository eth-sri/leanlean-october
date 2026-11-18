module

public import Chazelle.Core.SweepMachine3
public import Chazelle.Core.SweepWalkL
public import Chazelle.Core.SweepLabelJL0

/-!
# The sweep (WP-D), part 20: the abstract machine, detection shots in the model of `C`

A detection shot is made in the model of `C₁` from an endpoint `a` of a chord `c ∈ S₂`, along `c`.
This file connects a genuine hit of such a shot (`Genuine`, `SweepDetect2`) with the attachment of
the fused piece from `a` in the model of `C` (the event of the sweep):

* `rlen_add_llen`, `base_left`, `off_left`: the left stretch starts where the right stretch ends and
  fills the rest of the walk of `C`; offsets of its positions;
* `fused_of_genuine` (**soundness**): a genuine hit in the model of `C₁` before the far end of `c`
  is the first hit in `C`, so the piece from `a` to the hit is the fused chord of `F₂⁺` from `a`,
  inside `c`;
* `attach_left_of_arrival`, `attach_whole_of_arrival`: the piece is attached at the arrival
  position of the hit, in the model of `C₁` and (through the left correspondence) of `C`;
* `genuine_of_attach` (**completeness**): conversely, a fused chord from `a` attached at a position
  of the left stretch of `C` is a genuine hit in the model of `C₁`, arriving at the corresponding
  position.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Machine

variable (J : Merge.Junction)

/-- The tour position of the second copy of the shared vertex. -/
theorem tpos_second : tpos J.whole (J.m₁ + 2 * J.m₂) =
    (tpos J.whole J.m₁ + 2 * J.m₂) % (2 * J.whole.m) := by
  unfold tpos
  have hb := bS_le J.whole
  rw [Nat.mod_add_mod]
  congr 1
  have : J.whole.m = J.m₁ + J.m₂ := rfl
  omega

/-- **The shared vertex is not the top of `C`** (arithmetic form): neither copy of the shared vertex
is at the ends of the tour.  (When it is, the box block of `C` lies between the two stretches.) -/
def VNotTop : Prop :=
  0 < tpos J.whole J.m₁ ∧ tpos J.whole J.m₁ + 2 * J.m₂ ≠ 2 * J.whole.m

/-- The two stretches fill the walk of `C` (the shared vertex is not the top of `C`). -/
theorem rlen_add_llen (hv : VNotTop J) : rlen J + llen J = (chainModel J.whole).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := J.whole.sideWalk_n J.whole.sideBeta
  have h1 := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  obtain ⟨hv1, hv2⟩ := hv
  rw [hn]
  unfold rlen llen
  rw [tpos_second J]
  rw [hm] at h1 hv2 ⊢
  by_cases hc : tpos J.whole J.m₁ + 2 * J.m₂ < 2 * (J.m₁ + J.m₂)
  · rw [Nat.mod_eq_of_lt hc]
    split_ifs <;> omega
  · rw [show tpos J.whole J.m₁ + 2 * J.m₂ = (tpos J.whole J.m₁ + 2 * J.m₂ - 2 * (J.m₁ + J.m₂)) +
      2 * (J.m₁ + J.m₂) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

/-- The left stretch starts where the right stretch ends (the shared vertex is not the top of
`C`). -/
theorem base_left (hv : VNotTop J) :
    (6 + tpos J.whole J.m₁ + rlen J) % (chainModel J.whole).W.n =
      6 + tpos J.whole (J.m₁ + 2 * J.m₂) := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := J.whole.sideWalk_n J.whole.sideBeta
  have h1 := tpos_lt J.whole J.m₁
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  obtain ⟨hv1, hv2⟩ := hv
  rw [hn, tpos_second J]
  unfold rlen
  rw [hm] at h1 hv2 ⊢
  by_cases hc : tpos J.whole J.m₁ + 2 * J.m₂ < 2 * (J.m₁ + J.m₂)
  · rw [Nat.mod_eq_of_lt hc, ite_eq_right (by omega), Nat.mod_eq_of_lt (by omega)]; ring
  · have hc' : 2 * (J.m₁ + J.m₂) < tpos J.whole J.m₁ + 2 * J.m₂ := by omega
    rw [ite_eq_left (by omega)]
    rw [show tpos J.whole J.m₁ + 2 * J.m₂ = (tpos J.whole J.m₁ + 2 * J.m₂ -
      2 * (J.m₁ + J.m₂)) + 2 * (J.m₁ + J.m₂) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show tpos J.whole J.m₁ + 2 * J.m₂ - 2 * (J.m₁ + J.m₂) < 2 * (J.m₁ + J.m₂)
        by omega)]
    rw [show 6 + tpos J.whole J.m₁ + (2 * J.m₂ + 7) = (6 + (tpos J.whole J.m₁ + 2 * J.m₂ -
        2 * (J.m₁ + J.m₂))) + (2 * (J.m₁ + J.m₂) + 7) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-! ## Soundness: a genuine hit is a fused chord -/

/-- **The piece is attached at the arrival position** (model of `C₁`). -/
theorem attach_left_of_arrival {C : Chain} {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ}
    (hτ : 0 < τ) {p : ℕ} {t : ℝ} (hA : Arrival (chainModel C).W (rayPt a σ τ) σ p t) :
    SideAttach (chainModel C).W (Chazelle.segment a (rayPt a σ τ)) p t := by
  obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := hA
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨hp, ht0, ht1, by rw [hpt]; exact Geometry.right_mem_segment _ _, τ, hτ,
    fun x hx hxw _ => ?_⟩
  rw [hpt] at hxw
  obtain ⟨u, hu0, hu1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  have hu1' : u < 1 := by
    rcases hu1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hxw; rw [h, Geometry.lerp_one]
  have e : lerp a (rayPt a σ τ) u = rayPt (rayPt a σ τ) (-σ) (τ * (1 - u)) := by
    apply point_ext <;> simp [rayPt, lerp]; ring
  rw [e]
  have h1 : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) (-σ) 1) := by
    rw [hpt]; exact hsec
  have := (sideLeft_rayPt_iff _ p t (-σ) one_pos (show 0 < τ * (1 - u) by nlinarith)).1 h1
  rwa [hpt] at this

/-- **The piece is attached at the corresponding position of `C`** (left correspondence, away from
its base and its split vertex). -/
theorem attach_whole_of_arrival (hP : J.P.Simple) {a : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : Arrival (chainModel J.left).W (rayPt a σ τ) σ
      ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t) :
    SideAttach (chainModel J.whole).W (Chazelle.segment a (rayPt a σ τ))
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  exact (hC.attach_iff hd hsec _).2 (attach_left_of_arrival hσ hτ hA)

/-! ## Completeness: a fused chord is a genuine hit -/

/-- **A fused chord attached on the left stretch is a genuine detection hit**: if the direction
`σ` is free for `C` at `a` (not above the top of `C₁`) and the chord `shoot J.whole a σ` is attached
at a position of the left stretch of `C` (away from its base and split vertex), then the shot from
`a` in the model of `C₁` is genuine at the first hit of `C`, and arrives at the corresponding
position. -/
theorem genuine_of_attach (hP : J.P.Simple) {a : Point}
    (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ)
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ)
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t)
    (hend : sidePt (chainModel J.whole).W
      ((6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d) % (chainModel J.whole).W.n) t =
        rayPt a σ (J.whole.hitParam a σ)) :
    Genuine J.left a σ (J.whole.hitParam a σ) ∧
      Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
        ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t := by
  have hC := corr_left0 J hP (S₁ := ∅) (empty_subset _) finite_empty
  have hM₁ : WalkAx (chainModel J.left) := hC.hM₂
  set T := J.whole.hitParam a σ with hT
  have hz' : a.2 ≤ J.whole.top.2 := ha₁.trans J.left_top_le
  obtain ⟨hT0, hwD, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  have hA₁ := (hC.attach_iff hd hsec _).1 hA
  have hpt : sidePt (chainModel J.left).W
      ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t =
        rayPt a σ T := by
    rw [← hC.sidePt_eq hd t]; exact hend
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J (hdom s h0 h1) (by simpa [rayPt] using ha₁), ?_⟩, ?_⟩
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
      exact Geometry.lerp_mem_segment _ _ (by apply div_nonneg <;> linarith)
        (by rw [div_le_one hT0]; linarith)
    have hne : rayPt (rayPt a σ T) (-σ) s ≠ rayPt a σ T := by
      intro h
      have := congrArg Prod.fst h
      simp only [rayPt_fst] at this
      rcases hσ with rfl | rfl <;> linarith
    have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
    have hdist : dist (rayPt (rayPt a σ T) (-σ) s) (rayPt a σ T) < r := by
      rw [dist_rayPt _ hnσ hs0.le]; exact hsr
    have hl := hnear _ hmem (by rw [hpt]; exact hne) (by rw [hpt]; exact hdist)
    have h1 : sideLeft (chainModel J.left).W
        ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t
        (rayPt (sidePt (chainModel J.left).W
          ((6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d) % (chainModel J.left).W.n) t) (-σ) s) := by
      rw [hpt]; exact hl
    have := (sideLeft_rayPt_iff _ _ t (-σ) hs0 one_pos).1 h1
    rwa [hpt] at this

end Machine

end Sweep

end

end Chazelle.Core
