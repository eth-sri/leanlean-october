module

public import Chazelle.Core.SweepEvMap2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# The sweep (WP-D), stage 3: completeness of the reading of the `C₁` part in the walk of `C₁`

`map_complete`: a chord of `C` seen from `a` (not above the top of `C₁`) attached at a position
of the `C₁` part beyond the start, whose point is not `v`, is a genuine hit of the model of `C₁`,
arriving at the position of some valid `b₁`-offset `d` with `mEdge d = p`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section MapComplete

variable {J : Merge.Junction}

/-- **Completeness of the reading of the `C₁` part.** -/
theorem map_complete (hP : J.P.Simple) {a : Point} (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t)
    (hend : sidePt (chainModel J.whole).W p t = rayPt a σ (J.whole.hitParam a σ))
    (hoff : (Lst J : ℝ) < oW J (p + t)) (hnv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    Genuine J.left a σ (J.whole.hitParam a σ) ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
      Sweep.Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
        ((b₁ J + d) % (chainModel J.left).W.n) t := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hm1 : J.left.m = J.m₁ := rfl
  have h1 := J.one_le_m₁
  have hτ₁ := tpos_lt J.left J.m₁
  have hτw := tpos_lt J.whole J.m₁
  have hτw' := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have hp := hA.1
  have ht0 := hA.2.1
  have ht1 := hA.2.2.1
  have hg : gW J < (chainModel J.whole).W.n := by ufo gW
  set D := dOf (chainModel J.whole).W.n (gW J) p with hDdef
  have hD := dOf_lt (show 0 < (chainModel J.whole).W.n by omega) (gW J) p
  have hoW : oW J ((p : ℝ) + t) = (D : ℝ) + t := by rw [oW_def, off_key' hg hp ht0 ht1]
  rw [hoW] at hoff
  have hDL : Lst J ≤ D := by
    by_contra h
    have : (D : ℝ) + 1 ≤ Lst J := by exact_mod_cast (show D + 1 ≤ Lst J by omega)
    linarith
  have hpD : p = (gW J + (Lst J + (D - Lst J))) % (chainModel J.whole).W.n := by
    rw [show Lst J + (D - Lst J) = D by omega, hDdef, add_dOf hg hp]
  set r := D - Lst J with hr
  -- the left stretch
  have viaLeft : ∀ r' : ℕ, r' < llen J → p = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + r') %
      (chainModel J.whole).W.n → (t = 0 → r' ≠ 0 ∧ r' ≠ lL1 J) →
      ∀ d, (b₁ J + d) % (chainModel J.left).W.n =
        (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) r') % (chainModel J.left).W.n →
      MValid J d t → mEdge J d = p →
      Genuine J.left a σ (J.whole.hitParam a σ) ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Sweep.Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
          ((b₁ J + d) % (chainModel J.left).W.n) t := by
    intro r' hr' hp' hsec d hd hvd hmd
    rw [hp'] at hA hend
    obtain ⟨hg', hArr⟩ := genuine_of_attach J hP ha₁ hσ hfree (by rwx [lL1_add_lL2])
      hsec hA hend
    exact ⟨hg', d, hvd, hmd, by rwx [hd]⟩
  -- the box block of `C`
  have viaBox : ∀ (hv : ¬ VNotTop J) (r'' : ℕ), r'' < 7 →
      p = (2 * J.whole.m + 6 + r'') % (chainModel J.whole).W.n → (t = 0 → 1 ≤ r'') →
      ∀ d, (b₁ J + d) % (chainModel J.left).W.n =
        (2 * J.left.m + 6 + r'') % (chainModel J.left).W.n →
      MValid J d t → mEdge J d = p →
      Genuine J.left a σ (J.whole.hitParam a σ) ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Sweep.Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ
          ((b₁ J + d) % (chainModel J.left).W.n) t := by
    intro hv r'' hr'' hp' hsec d hd hvd hmd
    rw [hp'] at hA hend
    obtain ⟨hg', hArr⟩ := genuine_of_attach_box J hP hv ha₁ hσ hfree hr'' hsec hA hend
    exact ⟨hg', d, hvd, hmd, by rwx [hd]⟩
  -- the point of the arrival position is the point of `p`
  have hpt₁ : ∀ e₁, Sweep.Arrival (chainModel J.left).W (rayPt a σ (J.whole.hitParam a σ)) σ e₁ t →
      sidePt (chainModel J.left).W e₁ t ≠ J.shared := by
    intro e₁ hArr h
    rw [hArr.2.2.2.1, ← hend] at h
    exact hnv h
  have hvM : sidePt (chainModel J.whole).W (6 + tpos J.whole (J.m₁ + 2 * J.m₂)) 0 = J.shared := by
    have := start_pt J hP
    rwa [add_zero, Nat.mod_eq_of_lt (by omega)] at this
  by_cases hVNT : VNotTop J
  · have hlOff : lOff J = Lst J := by rw [lOff_of_vnt J hVNT, Lst_rlen]
    have hlen : Lst J + llen J = (chainModel J.whole).W.n := by
      rw [Lst_rlen]; exact rlen_add_llen J hVNT
    have hb : b₁ J = 6 + tpos J.left J.m₁ := by unfold b₁; rw [ite_eq_right (by omega)]
    have hE₁ : E₁ J = llen J + lδ J := by ufo E₁
    have hL := lL1_add_lL2 J
    have hrl : r < llen J := by omega
    have hpL : p = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + r) % (chainModel J.whole).W.n := by
      rwx [left_edge_eq, hlOff]
    by_cases hsp : t = 0 ∧ r = lL1 J ∧ lL1 J < llen J
    · -- the split vertex
      obtain ⟨ht, hrl1, hlt⟩ := hsp
      have hδ : 0 < lδ J := by
        by_contra h; have := lL2_of_lδ (J := J) (by omega); omega
      obtain ⟨h7, hl1, hl2, hτp, hτl⟩ := left_G hδ
      have htop : sidePt (chainModel J.whole).W p t = J.left.top := by
        rw [hpL, hrl1, ht]
        exact sidePt_splitL0 J hP (S₁ := ∅) (empty_subset _) finite_empty (by omega)
      obtain ⟨hgen, hA1, hA2⟩ := genuine_of_split J hP ha₁ hσ hfree (by rw [← hend, htop])
      obtain ⟨hp6, hp26⟩ := sidePt_top_copies J.left
      have hψ1 : ψ J (lL1 J) = lL1 J := by unfold ψ; rw [ite_eq_right (by omega)]
      have hψ2 : ψ J (lL1 J + 7) = lL1 J := by
        uro ψ [ite_eq_left ⟨hδ, by omega⟩, ite_eq_right (by omega), h7]
      have hvtop : J.left.top ≠ J.shared := fun h => hnv (htop.trans h)
      rcases hσ with hσ1 | hσ1
      · refine ⟨hgen, lL1 J, ⟨by omega, by omega, fun h => h.2.2 ht, fun _ => ?_⟩, ?_, ?_⟩
        · rw [hb, hl1, hn₁, hm1, Nat.mod_eq_of_lt (by omega),
            show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁) = 2 * J.left.m + 6 by omega,
            hp26]
          exact hvtop
        · rw [mEdge_def, hψ1, hpD, hrl1]
        · rw [hb, hl1, hn₁, hm1, Nat.mod_eq_of_lt (by omega),
            show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁) = 2 * J.left.m + 6 by omega,
            ht]
          exact hA1 hσ1
      · refine ⟨hgen, lL1 J + 7, ⟨by omega, by omega, by omega, fun _ => ?_⟩, ?_, ?_⟩
        · have e6 : (b₁ J + (lL1 J + 7)) % (chainModel J.left).W.n = 6 := by
            rw [hb, hl1, hn₁, hm1, show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁ + 7) =
              6 + (2 * J.m₁ + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [e6, hp6]
          exact hvtop
        · rw [mEdge_def, hψ2, hpD, hrl1]
        · rw [hb, hl1, hn₁, hm1, show 6 + tpos J.left J.m₁ + (2 * J.m₁ - tpos J.left J.m₁ + 7) =
            6 + (2 * J.m₁ + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), ht]
          exact hA2 hσ1
    · have hsec : t = 0 → r ≠ 0 ∧ r ≠ lL1 J := by
        intro ht
        refine ⟨fun h0 => hnv ?_, fun h => hsp ⟨ht, h, by omega⟩⟩
        rw [hpL, h0, ht, add_zero, Nat.mod_eq_of_lt (by omega)]
        exact hvM
      -- the position `dq r` of the walk of `C₁`
      have hdq : dq (lL1 J) (lδ J) r < E₁ J := by
        rw [hE₁]; unfold dq; splao
      have hψ : ψ J (dq (lL1 J) (lδ J) r) = r := by
        unfold ψ dq
        by_cases hr1 : r < lL1 J
        · rw [ite_eq_left hr1, ite_eq_right (by omega)]
        · rw [ite_eq_right hr1]
          by_cases hδ : lδ J = 0
          · rwo [ite_eq_right (by omega)]
          · rwo [ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (by omega)]
      refine viaLeft r hrl hpL hsec (dq (lL1 J) (lδ J) r) (by rw [hb]) ⟨hdq, ?_, ?_, ?_⟩ ?_
      · unfold dq; splao
      · unfold dq; splao
      · intro ht h
        have hArr := (genuine_of_attach J hP ha₁ hσ hfree (by rwx [lL1_add_lL2]) hsec
          (hpL ▸ hA) (hpL ▸ hend)).2
        rw [← hb] at hArr
        exact hpt₁ _ (by rw [ht] at hArr ⊢; exact hArr) (by rwx [ht])
      · rw [mEdge_def, hψ, ← hpD]
  · obtain ⟨hτ0, hδ0, hl1, hl2, hll⟩ := nvt_left J hP hVNT
    have hψ : ∀ d, ψ J d = d := fun d => by unfold ψ; rw [ite_eq_right (by omega)]
    have htopC : sidePt (chainModel J.whole).W (2 * J.whole.m + 6) 0 = J.shared := by
      rw [(sidePt_top_copies J.whole).2, shared_eq_top J hVNT]
    have hsplit : ∀ d, ¬ (0 < lδ J ∧ d = lL1 J ∧ t ≠ 0) := fun d h => by omega
    have hgap : ∀ d, ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J) := fun d h => by omega
    by_cases hbox : Lst J < lOff J
    · obtain ⟨-, hlo, hτs, hLst⟩ := caseB_facts J hbox
      have hb : b₁ J = 2 * J.left.m + 6 := by unfold b₁; rw [ite_eq_left hbox]
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by uro E₁ [hn, hδ0]
      have hrn : r < 2 * J.m₁ + 7 := by omega
      by_cases hr7 : r < 7
      · have hpB : p = (2 * J.whole.m + 6 + r) % (chainModel J.whole).W.n := by
          rw [hpD]; congr 1; ufo gW
        have hsec : t = 0 → 1 ≤ r := by
          intro ht; by_contra h0
          apply hnv
          rw [hpB, ht, show r = 0 by omega, add_zero, Nat.mod_eq_of_lt (by omega)]
          exact htopC
        refine viaBox hVNT r hr7 hpB hsec r (by rw [hb]) ⟨by omega, hgap r, hsplit r, ?_⟩ ?_
        · intro ht h
          have hArr := (genuine_of_attach_box J hP hVNT ha₁ hσ hfree hr7 hsec (hpB ▸ hA)
            (hpB ▸ hend)).2
          rw [← hb] at hArr
          exact hpt₁ _ (by rw [ht] at hArr ⊢; exact hArr) (by rwx [ht])
        · rw [mEdge_def, hψ, ← hpD]
      · have hpL : p = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + (r - 7)) % (chainModel J.whole).W.n := by
          rw [left_edge_eq, hlo, hpD]; congr 1; omega
        have hsec : t = 0 → r - 7 ≠ 0 ∧ r - 7 ≠ lL1 J := by
          intro ht
          refine ⟨fun h0 => hnv ?_, by omega⟩
          rw [hpL, h0, ht, add_zero, Nat.mod_eq_of_lt (by omega)]
          exact hvM
        refine viaLeft (r - 7) (by omega) hpL hsec r ?_ ⟨by omega, hgap r, hsplit r, ?_⟩ ?_
        · unfold dq; rw [ite_eq_left (by omega), hb, hτ0, hn₁]
          rw [show 2 * J.left.m + 6 + r = (6 + 0 + (r - 7)) + (2 * J.left.m + 7) by omega,
            Nat.add_mod_right]
        · intro ht h
          have hArr := (genuine_of_attach J hP ha₁ hσ hfree
            (by rwo [lL1_add_lL2]) hsec (hpL ▸ hA) (hpL ▸ hend)).2
          have e : (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) (r - 7)) %
              (chainModel J.left).W.n = (b₁ J + r) % (chainModel J.left).W.n := by
            unfold dq; rw [ite_eq_left (by omega), hb, hτ0, hn₁]
            rw [show 2 * J.left.m + 6 + r = (6 + 0 + (r - 7)) + (2 * J.left.m + 7) by omega,
              Nat.add_mod_right]
          rw [e] at hArr
          exact hpt₁ _ (by rw [ht] at hArr ⊢; exact hArr) (by rwx [ht])
        · rw [mEdge_def, hψ, ← hpD]
    · obtain ⟨hτs, hlo, hLst⟩ := caseC_facts J hVNT hbox
      have hb : b₁ J = 6 + tpos J.left J.m₁ := by unfold b₁; rw [ite_eq_right hbox]
      have hE₁ : E₁ J = 2 * J.m₁ + 7 := by uro E₁ [hn, hδ0]
      have hrn : r < 2 * J.m₁ + 7 := by omega
      by_cases hr2 : r < 2 * J.m₁
      · have hpL : p = (6 + tpos J.whole (J.m₁ + 2 * J.m₂) + r) % (chainModel J.whole).W.n := by
          rw [left_edge_eq, hlo, hpD]
        have hsec : t = 0 → r ≠ 0 ∧ r ≠ lL1 J := by
          intro ht
          refine ⟨fun h0 => hnv ?_, by omega⟩
          rw [hpL, h0, ht, add_zero, Nat.mod_eq_of_lt (by omega)]
          exact hvM
        refine viaLeft r (by omega) hpL hsec r ?_ ⟨by omega, hgap r, hsplit r, ?_⟩ ?_
        · unfold dq; rw [ite_eq_left (by omega), hb]
        · intro ht h
          have hArr := (genuine_of_attach J hP ha₁ hσ hfree
            (by rwo [lL1_add_lL2]) hsec (hpL ▸ hA) (hpL ▸ hend)).2
          have e : (6 + tpos J.left J.m₁ + dq (lL1 J) (lδ J) r) % (chainModel J.left).W.n =
              (b₁ J + r) % (chainModel J.left).W.n := by
            unfold dq; rw [ite_eq_left (by omega), hb]
          rw [e] at hArr
          exact hpt₁ _ (by rw [ht] at hArr ⊢; exact hArr) (by rwx [ht])
        · rw [mEdge_def, hψ, ← hpD]
      · have hpB : p = (2 * J.whole.m + 6 + (r - 2 * J.m₁)) % (chainModel J.whole).W.n := by
          rw [hpD]; congr 1; ufo gW
        have hsec : t = 0 → 1 ≤ r - 2 * J.m₁ := by
          intro ht; by_contra h0
          apply hnv
          rw [hpB, ht, show r - 2 * J.m₁ = 0 by omega, add_zero, Nat.mod_eq_of_lt (by omega)]
          exact htopC
        have e : (b₁ J + r) % (chainModel J.left).W.n =
            (2 * J.left.m + 6 + (r - 2 * J.m₁)) % (chainModel J.left).W.n := by
          rw [hb, hτ0]; congr 1; omega
        refine viaBox hVNT (r - 2 * J.m₁) (by omega) hpB hsec r e
          ⟨by omega, hgap r, hsplit r, ?_⟩ ?_
        · intro ht h
          have hArr := (genuine_of_attach_box J hP hVNT ha₁ hσ hfree (by omega) hsec (hpB ▸ hA)
            (hpB ▸ hend)).2
          rw [← e] at hArr
          exact hpt₁ _ (by rw [ht] at hArr ⊢; exact hArr) (by rwx [ht])
        · rw [mEdge_def, hψ, ← hpD]

end MapComplete

end Sweep

end

end Chazelle.Core
