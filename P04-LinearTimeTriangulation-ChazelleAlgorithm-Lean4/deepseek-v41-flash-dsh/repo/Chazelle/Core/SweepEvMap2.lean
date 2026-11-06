module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvMap

/-!
# The sweep (WP-D), stage 3: soundness of the reading of the `C₁` part in the walk of `C₁`

`map_sound`: a hit of `C` (from `a`, at parameter `τ`) arriving in the model of `C₁` at the
position of `b₁`-offset `d` (`MValid`) is the chord of `C` attached at the walk edge `mEdge d` of
`M`, at the offset `Lst + ψ d + t`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section MapSound

variable {J : Merge.Junction}

theorem mEdge_def (d : ℕ) :
    mEdge J d = (gW J + (Lst J + ψ J d)) % (chainModel J.whole).W.n := rfl

theorem oW_def (x : ℝ) : oW J x = off (chainModel J.whole).W.n ((gW J : ℕ) : ℝ) x := rfl

/-- The point of `v` in the walk of `C₁` at its tour position. -/
theorem left_v_pt :
    sidePt (chainModel J.left).W (6 + tpos J.left J.m₁) 0 = J.shared := by
  rw [Chazelle.Chain.sidePt_zero, vtx_tpos' J.left (k := J.m₁) (show J.m₁ ≤ J.left.m from le_refl _)]; rfl

/-- The points of the copies of the top of `C₁` (when `v` is the top of `C`). -/
theorem left_top_pts (hv : ¬ VNotTop J) :
    sidePt (chainModel J.left).W 6 0 = J.shared ∧
      sidePt (chainModel J.left).W (2 * J.left.m + 6) 0 = J.shared := by
  obtain ⟨h1, h2⟩ := sidePt_top_copies J.left
  Ξ' left_top_eq J hv at h1 h2
  exact ⟨h1, h2⟩

/-- `lδ = 0` forces `lL2 = 0`. -/
theorem lL2_of_lδ (h : lδ J = 0) : lL2 J = 0 := by
  unfold lδ lL2 at *; split_ifs at * <;> omega

/-- The left case G. -/
theorem left_G (h : 0 < lδ J) :
    lδ J = 7 ∧ lL1 J = 2 * J.m₁ - tpos J.left J.m₁ ∧ lL2 J = tpos J.left J.m₁ ∧
      0 < tpos J.left J.m₁ ∧ tpos J.left J.m₁ < 2 * J.m₁ := by
  have := tpos_lt J.left J.m₁
  have hm1 : J.left.m = J.m₁ := rfl
  Ξ' hm1 at this
  unfold lδ lL1 lL2 at *
  split_ifs at * <;> omega

/-- **Soundness of the reading of the `C₁` part.** -/
theorem map_sound (hP : J.P.Simple) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ}
    (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ) {d : ℕ} {t : ℝ} (hv : MValid J d t)
    (hA : Sweep.Arrival (chainModel J.left).W (rayPt a σ τ) σ
      ((b₁ J + d) % (chainModel J.left).W.n) t) :
    SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) (mEdge J d) t ∧
      oW J ((mEdge J d : ℝ) + t) = (Lst J : ℝ) + ψ J d + t := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hm1 : J.left.m = J.m₁ := rfl
  have h1 := J.one_le_m₁
  have hτ₁ := tpos_lt J.left J.m₁
  have hτw := tpos_lt J.whole J.m₁
  have ht0 := hA.2.1
  have ht1 := hA.2.2.1
  obtain ⟨hdE, hgap, hsplit, hnv⟩ := hv
  -- the left stretch, at position `d'` (`dq d' = D`)
  have viaGen : ∀ d' : ℕ, d' < lL1 J + lL2 J → (t = 0 → d' ≠ 0 ∧ d' ≠ lL1 J) →
      (b₁ J + d) % (chainModel J.left).W.n =
        (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) d') % (chainModel J.left).W.n →
      lOff J + d' = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) (mEdge J d) t ∧
        oW J ((mEdge J d : ℝ) + t) = (Lst J : ℝ) + ψ J d + t := by
    intro d' hd' hsec he hoff
    Ξ' he at hA
    obtain ⟨hS, hO⟩ := cut_of_genuine_gen J hP hσ hτ hhit hd' hsec hA
    have hE : mEdge J d = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + d') % (chainModel J.whole).W.n := by
      Ξ mEdge_def, left_edge_eq, hoff
    Ξ hE
    refine ⟨hS, ?_⟩
    Ξ oW_def, show ((gW J : ℕ) : ℝ) = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) from rfl, hO
    have : ((lOff J + d' : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := Ρ hoff
    push_cast at this
    linarith
  -- the split vertex
  have viaSplit : lL1 J < lL1 J + lL2 J → t = 0 →
      ((b₁ J + d) % (chainModel J.left).W.n = 6 ∨
        (b₁ J + d) % (chainModel J.left).W.n = 2 * J.left.m + 6) →
      lOff J + lL1 J = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) (mEdge J d) t ∧
        oW J ((mEdge J d : ℝ) + t) = (Lst J : ℝ) + ψ J d + t := by
    intro hlt ht hk hoff
    subst ht
    have hS := attach_split_of_arrival J hP hlt hσ hτ hk hA
    have hshoot : Merge.shoot J.whole a σ = Chazelle.segment a (rayPt a σ τ) := by
      unfold Merge.shoot; Ξ hhit
    have hE : mEdge J d = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + lL1 J) %
        (chainModel J.whole).W.n := by
      Ξ mEdge_def, left_edge_eq, hoff
    Ξ hE, hshoot
    refine ⟨hS, ?_⟩
    rw [oW_def, show ((gW J : ℕ) : ℝ) = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) from rfl,
      off_left_gen J (by rw [← lL1_add_lL2 J]; exact hlt) le_rfl one_pos]
    have : ((lOff J + lL1 J : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := Ρ hoff
    push_cast at this
    linarith
  -- the box block of `C`
  have viaBox : ∀ d'' : ℕ, (hv' : ¬ VNotTop J) → d'' < 7 → (t = 0 → 1 ≤ d'') →
      (b₁ J + d) % (chainModel J.left).W.n = (2 * J.left.m + 6 + d'') % (chainModel J.left).W.n →
      gW J + (Lst J + ψ J d) = 2 * J.whole.m + 6 + d'' →
      2 * J.whole.m - tpos J.whole J.m₁ + d'' = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) (mEdge J d) t ∧
        oW J ((mEdge J d : ℝ) + t) = (Lst J : ℝ) + ψ J d + t := by
    intro d'' hv' hd'' hsec he hidx hoff
    Ξ' he at hA
    obtain ⟨hS, hO⟩ := cut_of_genuine_box J hv' hσ hτ hhit hd'' hsec hA
    have hE : mEdge J d = (2 * J.whole.m + 6 + d'') % (chainModel J.whole).W.n := by
      Ξ mEdge_def, hidx
    Ξ hE
    refine ⟨hS, ?_⟩
    Ξ oW_def, show ((gW J : ℕ) : ℝ) = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) from rfl, hO
    have : ((2 * J.whole.m - tpos J.whole J.m₁ + d'' : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := by
      Ξ hoff
    push_cast at this ⊢
    linarith
  by_cases hVNT : VNotTop J
  · -- case a: the left stretch fills the `C₁` part
    have hlOff : lOff J = Lst J := Ρ lOff_of_vnt J hVNT, Lst_rlen
    have hlen : Lst J + llen J = (chainModel J.whole).W.n := by
      rw [Lst_rlen]; exact rlen_add_llen J hVNT
    have hb : b₁ J = 6 + tpos J.left J.m₁ := by unfold b₁; Ξ ite_eq_right (⋄)
    have hE₁ : E₁ J = llen J + lδ J := by unfold E₁; omega
    have hL := lL1_add_lL2 J
    Ξ' hE₁ at hdE
    Ξ' hb at hA hnv viaGen viaSplit
    by_cases hdl : d < lL1 J
    · have hψ : ψ J d = d := by unfold ψ; Ξ ite_eq_right (⋄)
      refine viaGen d (⋄) (fun ht => ⟨fun hd0 => ?_, ⋄⟩) ?_ (Ρ hψ, hlOff)
      · apply hnv ht
        Ξ hd0, add_zero, Nat.mod_eq_of_lt (⋄)
        exact left_v_pt
      · unfold dq; Ξ ite_eq_left hdl
    · by_cases hδ : lδ J = 0
      · have := lL2_of_lδ hδ; omega
      · have hδ' : 0 < lδ J := ⋄
        obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ'
        Ξ' h7 at hgap hsplit hdE
        by_cases hd1 : d = lL1 J
        · have ht : t = 0 := by by_contra h; exact hsplit ⟨⋄, hd1, h⟩
          refine viaSplit (⋄) ht (Or.inr ?_) ?_
          · rw [hd1, hl1, hn₁, hm1, Nat.mod_eq_of_lt (⋄)]; omega
          · have hψ : ψ J d = lL1 J := by unfold ψ; rw [ite_eq_right (⋄)]; exact hd1
            Ξ hψ, hlOff
        · have hd2 : lL1 J + 7 ≤ d := by
            by_contra h; exact hgap ⟨⋄, ⋄, ⋄⟩
          have hψ : ψ J d = d - 7 := by
            unfold ψ; Ξ ite_eq_left ⟨hδ', ⋄⟩, ite_eq_right (⋄), h7
          by_cases hs : d = lL1 J + 7 ∧ t = 0
          · refine viaSplit (⋄) hs.2 (Or.inl ?_) ?_
            · Ξ hs.1, hl1, hn₁, hm1
              rw [show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁ + 7) =
                6 + (2 * J.m₁ + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (⋄)]
            · rw [hψ, hlOff]; omega
          · refine viaGen (d - 7) (⋄) (fun ht => ⟨⋄, fun h => hs ⟨⋄, ht⟩⟩)
              ?_ (Ρ hψ, hlOff)
            unfold dq; Ξ ite_eq_right (⋄), h7, show d - 7 + 7 = d by omega
  · -- `v` is the top of `C`: no gap, `ψ = id`
    obtain ⟨hτ0, hδ0, hl1, hl2, hll⟩ := nvt_left J hP hVNT
    have hψ : ψ J d = d := by unfold ψ; Ξ ite_eq_right (⋄)
    obtain ⟨hp6, hp26⟩ := left_top_pts hVNT
    by_cases hbox : Lst J < lOff J
    · obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
      have hb : b₁ J = 2 * J.left.m + 6 := by unfold b₁; Ξ ite_eq_left hbox
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by unfold E₁; rw [hn, hδ0]; omega
      Ξ' hE₁ at hdE
      Ξ' hb at hA hnv viaGen viaSplit
      by_cases hd7 : d < 7
      · refine viaBox d hVNT hd7 (fun ht => ?_) (Ρ hb) (by rw [hψ]; unfold gW; omega)
          (by rw [hψ]; omega)
        by_contra h0
        apply hnv ht
        Ξ show d = 0 by omega, add_zero, Nat.mod_eq_of_lt (⋄)
        exact hp26
      · refine viaGen (d - 7) (⋄) (fun ht => ⟨fun h0 => ?_, ⋄⟩) ?_
          (by rw [hψ]; omega)
        · apply hnv ht
          rw [hn₁, show 2 * J.left.m + 6 + d = 6 + (2 * J.left.m + 7) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (⋄)]
          exact hp6
        · unfold dq; Ξ ite_eq_left (⋄), hτ0, hn₁
          rw [show 2 * J.left.m + 6 + d = (6 + 0 + (d - 7)) + (2 * J.left.m + 7) by omega,
            Nat.add_mod_right]
    · obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
      have hb : b₁ J = 6 + tpos J.left J.m₁ := by unfold b₁; Ξ ite_eq_right hbox
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by unfold E₁; rw [hn, hδ0]; omega
      Ξ' hE₁ at hdE
      Ξ' hb, hτ0 at hA hnv viaGen viaSplit
      by_cases hd2 : d < 2 * J.m₁
      · refine viaGen d (⋄) (fun ht => ⟨fun h0 => ?_, ⋄⟩) ?_ (Ρ hψ, hlo)
        · apply hnv ht
          Ξ h0, Nat.mod_eq_of_lt (⋄)
          exact hp6
        · unfold dq; Ξ ite_eq_left (⋄)
      · refine viaBox (d - 2 * J.m₁) hVNT (⋄) (fun ht => ?_) ?_ ?_ ?_
        · by_contra h0
          apply hnv ht
          Ξ show 6 + 0 + d = 2 * J.left.m + 6 by omega, Nat.mod_eq_of_lt (⋄)
          exact hp26
        · Ξ hb, hτ0
          congr 1
          omega
        · rw [hψ]; unfold gW; omega
        · rw [hψ]; omega

end MapSound

end Sweep

end

end Chazelle.Core
