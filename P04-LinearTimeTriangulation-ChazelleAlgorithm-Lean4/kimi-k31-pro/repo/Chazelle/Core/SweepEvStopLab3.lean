module

public import Chazelle.Core.SweepEvStopLab2
public import Chazelle.Core.SweepEvStep
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The sweep (WP-D), stage 2: the side labels of an anchored stop chord (part 3)

* `slb_nonfused_kind`: a chord of `F₂⁺` in no chord of `S₂` is shot from the shared vertex or the
  top of `C₂`;
* `slb_nonfused_tie`: two such chords never make a tie at a vertex position of the open right
  stretch other than the split vertex;
* `slb_tieOut`: at the split vertex, a tie of a chord attached on the `C₁` part and a chord whose
  other attachments are off the stretch is `TieOut`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open WalkEmbed

@[expose] public section

variable {J : Merge.Junction}

/-- A point of a shoot lies on the ray. -/
theorem slb_shoot_pt {C : Chain} {a w : Point} {σ : ℝ} (hw : w ∈ Merge.shoot C a σ) :
    w.2 = a.2 ∧ ∃ s : ℝ, 0 ≤ s ∧ w.1 = a.1 + σ * s := by
  unfold Merge.shoot at hw
  obtain ⟨u, hu0, hu1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hw
  have hT : 0 ≤ C.hitParam a σ := Real.sInf_nonneg fun _ ht => ht.1.le
  refine ⟨by simp [Geometry.lerp_snd, Visibility.rayPt_snd], u * C.hitParam a σ,
    mul_nonneg hu0 hT, ?_⟩
  simp [Geometry.lerp_fst, Visibility.rayPt_fst]
  ring

/-- A chord of `F₂⁺` in no chord of `S₂`: a shared chord or a top chord. -/
theorem slb_nonfused_kind {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {e : Set Point} (he : e ∈ F₂plus J S₂) (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) :
    ∃ (a : Point) (σ : ℝ), (a = J.shared ∨ a = J.right.top) ∧ (σ = 1 ∨ σ = -1) ∧
      e = Merge.shoot J.whole a σ := by
  rcases f2_cases hS₂ he with ⟨c, hc, a, σ, ha, -, rfl⟩ | ⟨σ, hσ, -, rfl⟩ | ⟨σ, hσ, -, rfl⟩
  · exact absurd (shoot_sub_end hS₂ hc ha) (hnf c hc)
  · exact ⟨_, σ, Or.inl rfl, hσ, rfl⟩
  · exact ⟨_, σ, Or.inr rfl, hσ, rfl⟩

/-- **No tie of two non-fused chords** at a point other than the shared vertex and the top of
`C₂`. -/
theorem slb_nonfused_pt {S₂ : Set (Set Point)} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {e e' : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hnf' : ∀ c ∈ S₂, ¬ e' ⊆ c) {w : Point} (hw : w ∈ e)
    (hw' : w ∈ e') (hwv : w ≠ J.shared) (hwt : w ≠ J.right.top) : False := by
  obtain ⟨a, σ, ha, hσ, rfl⟩ := slb_nonfused_kind hS₂ he hnf
  obtain ⟨a', σ', ha', hσ', rfl⟩ := slb_nonfused_kind hS₂ he' hnf'
  obtain ⟨h2, s, hs, h1⟩ := slb_shoot_pt hw
  obtain ⟨h2', s', hs', h1'⟩ := slb_shoot_pt hw'
  have haa : a = a' := by
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · rfl
    · exact shared_eq_top_of_snd J (by rw [← h2', h2])
    · exact (shared_eq_top_of_snd J (by rw [← h2, h2'])).symm
    · rfl
  subst haa
  have hσσ : σ' ≠ σ := fun h => hne (by rw [h])
  have hσ' : σ' = -σ := by
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> simp_all
  have hss : σ * (s + s') = 0 := by rwli [hσ'] at h1'
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hs0 : s = 0 := by
    have := (mul_eq_zero.1 hss).resolve_left hσ0
    linarith
  have hwa : w = a := Prod.ext (by rwring [h1, hs0]) h2
  rcases ha with rfl | rfl
  · exact hwv hwa
  · exact hwt hwa

/-- **No tie of two non-fused chords** at a vertex position of the open right stretch other than
the split vertex. -/
theorem slb_nonfused_tie (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e)
    (hnf : ∀ c ∈ S₂, ¬ e ⊆ c) (hnf' : ∀ c ∈ S₂, ¬ e' ⊆ c) {d : ℕ} (hd : d < Lst J)
    (hd0 : d ≠ 0) (hdr : d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + d) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e' ((gW J + d) % (chainModel J.whole).W.n) 0) :
    False := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hoff := hC.off_M hd le_rfl zero_lt_one
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
  have h2 : (d : ℝ) + 1 ≤ ((rL1 J + rL2 J : ℕ) : ℝ) := by
    have : d + 1 ≤ rL1 J + rL2 J := hd
    exact_mod_cast this
  have hin : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
      ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + 0) ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ((((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n : ℕ) : ℝ) + 0) <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
    rw [hoff]; constructor <;> linarith
  have hwv : sidePt (chainModel J.whole).W ((gW J + d) % (chainModel J.whole).W.n) 0 ≠
      J.shared := fun h =>
    off_shared_out J hP hS₂.2.1 hS₂.1 (Nat.mod_lt _ hC.n_pos) le_rfl zero_lt_one h hin
  by_cases hwt : sidePt (chainModel J.whole).W ((gW J + d) % (chainModel J.whole).W.n) 0 =
      J.right.top
  · exact no_tie_at_top2 J hP hS₂.2.1 hS₂.1 hd ⟨hd0, hdr⟩ he he' (Ne.symm hne) hA hA' hwt
  · exact slb_nonfused_pt hS₂.2.1 he he' hne hnf hnf' hA.2.2.2.1 hA'.2.2.2.1 hwv hwt

/-- In case G the slit has positive length. -/
theorem slb_rδ_pos (h : rL1 J < Lst J) : 0 < rδ J := by
  unfold Lst at h
  unfold rL2 at h
  unfold rδ
  split_ifs at h ⊢ <;> omega

/-- **The tie at the split vertex leaving the stretch** (`TieOut`). -/
theorem slb_tieOut (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q (F₂plus J S₂)) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) (hlt : rL1 J < Lst J)
    (hd0 : rL1 J ≠ 0)
    (hA : SideAttach (chainModel J.whole).W e ((gW J + rL1 J) % (chainModel J.whole).W.n) 0)
    (hA' : SideAttach (chainModel J.whole).W e' ((gW J + rL1 J) % (chainModel J.whole).W.n) 0)
    (hK : ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ (Lst J : ℝ) ≤ oW J (q + s))
    (hOff : OffOut J e' ((gW J + rL1 J) % (chainModel J.whole).W.n) 0)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hS : SideOf (chainModel J.whole) ρ e G) (hS' : SideOf (chainModel J.whole) ρ e' G) :
    TieOut J S₂ G := by
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hM := hC.hM
  have hsplit : sidePt (chainModel J.whole).W ((gW J + rL1 J) % (chainModel J.whole).W.n) 0 =
      J.right.top := sidePt_split J hP hS₂.2.1 hS₂.1 hlt
  have hsplit' := sidePt_split J hP hS₂.2.1 hS₂.1 hlt
  obtain ⟨q, s, hB, hBo⟩ := hK
  obtain ⟨pb', tb', hB', hBne'⟩ := far_attach hM (hF.2.1 he') J.right.top
  have hoff := hC.off_M hlt le_rfl zero_lt_one
  have hBne : sidePt (chainModel J.whole).W q s ≠
      sidePt (chainModel J.whole).W ((gW J + rL1 J) % (chainModel J.whole).W.n) 0 := by
    intro h
    obtain ⟨rfl, rfl⟩ := hM.attach_unique (hC.hF he) hB hA h
    have : oW J (((gW J + rL1 J) % (chainModel J.whole).W.n : ℕ) + 0) = rL1 J + 0 := hoff
    rw [this] at hBo
    have : (rL1 J : ℝ) < (Lst J : ℝ) := by exact_mod_cast hlt
    linarith
  refine ⟨e, e', rL1 J, q, pb', s, tb', ρ, he, he', hne, hd0, hlt, hA, hA', hB, hB', hBne,
    by first | (rwx [hsplit']), fun h => ?_, hOff pb' tb' hB' (by first | (rwx [hsplit])), hρ,
    hS, hS', hsplit ▸ hA.2.2.2.1, hsplit ▸ hA'.2.2.2.1⟩
  have : (Lst J : ℝ) ≤ off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) (q + s) :=
    hBo
  have h2 := h.2
  have : ((rL1 J + rL2 J : ℕ) : ℝ) = (Lst J : ℝ) := rfl
  linarith

end

end SweepEv

end Chazelle.Core
