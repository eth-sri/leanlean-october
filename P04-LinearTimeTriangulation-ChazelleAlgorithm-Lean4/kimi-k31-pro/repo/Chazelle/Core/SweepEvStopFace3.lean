module

public import Chazelle.Core.SweepEvStopFace2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 2: the regions faced at a position of the walk of `C₂` (task F, RAM 2)

`frTail pe ph dst ye yh src` (after `frLoc pe ph`): normalise the arc end `(ye, yh)`, set
`dst := lR1` (the region of the arc at `j`), and if the position `x = (pe, ph)` is a walk vertex
of the tour (edge `≥ 6`, normalised height code `0`) and the arc end is that vertex, `dst := src`
(the region of the arc at `j + 1` for the end, at `j - 1` for the start).  `frTail_irs`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

def frGE : ℕ := sw 1206
def frGH : ℕ := sw 1207

/-- `dst := src` if `x` (normalised in `frGE, frGH`) is a vertex and equals the end `(ye, yh)`. -/
def frChk (dst ye yh src : ℕ) : Stmt :=
  .ifLtN K0 frGH .skip (.ifLtN ye frGE .skip (.ifLtN frGE ye .skip
    (.ifLtN K0 yh .skip (block [.copyN dst src]))))

/-- The tail of one side. -/
def frTail (pe ph dst ye yh src : ℕ) : Stmt :=
  .seq (normS (sw 21) ye yh fO) (.seq (block [.copyN dst lR1])
    (.ifLtN pe K6 .skip (.seq (block [.copyN frGE pe, .copyN frGH ph])
      (.seq (normS (sw 21) frGE frGH fO) (frChk dst ye yh src)))))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem frChk_irs {dst ye yh src : ℕ} (hI : IInv W c₀ c) (hk0 : c.nreg K0 = 0)
    (hd : 240700 ≤ dst ∧ dst < 250000) :
    IRS P W c₀ (frChk dst ye yh src) c 9 (fun c' =>
      c'.nreg dst = (if c.nreg frGH = 0 ∧ c.nreg ye = c.nreg frGE ∧ c.nreg yh = 0 then c.nreg src
        else c.nreg dst) ∧
      (∀ r, r ≠ dst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold frChk
  by_cases h0 : c.nreg K0 < c.nreg frGH
  · refine (IRS.ifT h0 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (by omega)
      (fun _ => id)
    rw [ite_eq_right (by omega)]
  by_cases h1 : c.nreg ye < c.nreg frGE
  · refine (IRS.ifF h0 (IRS.ifT h1 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩))).mono
      (by omega) (fun _ => id)
    rw [ite_eq_right (by omega)]
  by_cases h2 : c.nreg frGE < c.nreg ye
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifT h2 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩))))
      |>.mono (by omega) (fun _ => id)
    rw [ite_eq_right (by omega)]
  by_cases h3 : c.nreg K0 < c.nreg yh
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifF h2 (IRS.ifT h3
      (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩))))) |>.mono (by omega) (fun _ => id)
    rw [ite_eq_right (by omega)]
  · refine (IRS.ifF h0 (IRS.ifF h1 (IRS.ifF h2 (IRS.ifF h3 (IRS.block [.copyN dst src] hI
      ⟨iscr_sw hd.1 hd.2, trivial⟩))))).mono (by simp) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · simp only [regB, regI, upd, ite_true]
      rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
    · simp only [regB, regI, upd, ite_eq_right hr]

/-- `nhgt` vanishes exactly at parameter `0`. -/
theorem nhgt_zero_iff {M : Model} {Q : Polygon} (x : WPos) :
    nhgt M Q x = 0 ↔ M.param Q x = 0 := by
  unfold nhgt Restore.normOf
  split_ifs with h
  · simp [h]
  · constructor
    · intro hx; simp [Model.param, hx]
    · intro h'; exact absurd h' h

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The tail of one side.** -/
theorem frTail_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {pe ph dst ye yh src : ℕ}
    (hpe : sw 4110 ≤ pe ∧ pe ≤ sw 4113) (hph : sw 4110 ≤ ph ∧ ph ≤ sw 4113)
    (hdst : dst = sw 4114 ∨ dst = sw 4115) (hye : sw 1200 ≤ ye ∧ ye ≤ sw 1203)
    (hyh : sw 1200 ≤ yh ∧ yh ≤ sw 1203) (hyy : ye ≠ yh) (hsrc : src = lR0 ∨ src = lR2)
    {Y : WPos} (vye : c.nreg ye = Y.edge) (vyh : c.nreg yh = Y.hgt)
    (hYpp : ProperPos (chainModel J.right) (Qof P) P.n Y)
    (hYe : Y.edge < (chainModel J.right).W.n)
    (hYy : Y.edge < 6 → Y.edge ≠ 0 → Y.edge ≠ 2 → Y.edge ≠ 4 →
      |((chainModel J.right).pos (Qof P) Y).2| < J.right.radius)
    (hxe : c.nreg pe < (chainModel J.right).W.n)
    (hxpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pe, c.nreg ph⟩)
    (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ (frTail pe ph dst ye yh src) c 22100 (fun c' =>
      c'.nreg dst = (if 6 ≤ c.nreg pe ∧
          nhgt (chainModel J.right) (Qof P) ⟨c.nreg pe, c.nreg ph⟩ = 0 ∧
          Y.edge = c.nreg pe ∧ nhgt (chainModel J.right) (Qof P) Y = 0
        then c.nreg src else c.nreg lR1) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ dst → (r < sw 1200 ∨ sw 1207 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hctx := E.ctx2' hI
  have hfO : fO = sw 1204 := rfl
  have hfrGE : frGE = sw 1206 := rfl
  have hfrGH : frGH = sw 1207 := rfl
  have hd : 240700 ≤ dst ∧ dst < 250000 := by rcases hdst with rfl | rfl <;> unfold sw <;> omega
  unfold frTail
  -- 1. normalise the end
  refine IRS.mono (K := 11015 + (1 + (11015 + 2 + 7 + 9 + 2))) (IRS.seq
    (normS_irs (dsc := sw 21) (pe := ye) (ph := yh) (o := fO) (C := J.right) hI (E.hK.fix hI) hctx
      ⟨by ufn sw, by ufn sw, by ufo sw at hye,
        by ufo sw at hye, by ufo sw at hyh, by ufo sw at hyh⟩
      ⟨by rw [hfO]; ufn sw, by rw [hfO]; ufn sw,
        by ruo [hfO] sw at hye ⊢, by ruo [hfO] sw at hyh ⊢,
        by ruo [hfO] sw at hye ⊢, by ruo [hfO] sw at hyh ⊢, hyy⟩
      (by rwx [vye]) (by rwx [vye, vyh]) (by rwx [vye, vyh])
      (by omega)) ?_) (by norm_num) (fun _ => id)
  rintro c₁ hI₁ - hA₁' ⟨v1e, v1h, k1, hA1, hm1⟩
  rw [vye, vyh] at v1h
  rw [vye] at v1e
  have keep1 : ∀ r, bandOf r ∉ oracleBands → (r < sw 1200 ∨ sw 1207 < r) → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1 r h1 (by ufo sw at hyh h2) (by ruo [hfO] sw at h2 ⊢)
      (by ruo [hfO] sw at h2 ⊢) h3
  have nsw : ∀ q, (sw 4000 ≤ q ∧ q < sw 5000) ∨ (sw 600 ≤ q ∧ q < sw 700) ∨
      (sw 1100 ≤ q ∧ q < sw 1200) → bandOf q ∉ oracleBands ∧ (q < sw 1200 ∨ sw 1207 < q) ∧
      q ≠ ALLOC := by
    intro q hq
    refine ⟨not_oracle_sw (by ufo sw at hq) (by ufo sw at hq),
      by ufo sw at hq ⊢, by unfold ALLOC; ufo sw at hq⟩
  have kq : ∀ q, (sw 4000 ≤ q ∧ q < sw 5000) ∨ (sw 600 ≤ q ∧ q < sw 700) ∨
      (sw 1100 ≤ q ∧ q < sw 1200) → c₁.nreg q = c.nreg q := fun q hq => by
    obtain ⟨a, b, d⟩ := nsw q hq; exact keep1 q a b d
  have hK₁ := E.hK.fix hI₁
  -- 2. the default
  refine IRS.seq (IRS.block [.copyN dst lR1] hI₁ ⟨iscr_sw hd.1 hd.2, trivial⟩) ?_
  rintro c₂ hI₂ hA₂ hA₂' hc2
  have v2 : c₂.nreg dst = c.nreg lR1 := by
    rw [hc2]; simp only [regB, regI, upd, ite_true]
    exact kq _ (Or.inr (Or.inr (by ufo lR1 sw)))
  have k2 : ∀ r, r ≠ dst → c₂.nreg r = c₁.nreg r := fun r hr => by
    rw [hc2]; simp only [regB, regI, upd, ite_eq_right hr]
  have hm2 : c₂.nmem = c₁.nmem := by rw [hc2]
  have hdpe : pe ≠ dst := by rcases hdst with rfl | rfl <;> unfold sw at hpe ⊢ <;> omega
  have hdph : ph ≠ dst := by rcases hdst with rfl | rfl <;> unfold sw at hph ⊢ <;> omega
  have e2pe : c₂.nreg pe = c.nreg pe := by
    rw [k2 _ hdpe]; exact kq _ (Or.inl (by ufo sw at hpe ⊢))
  have e2ph : c₂.nreg ph = c.nreg ph := by
    rw [k2 _ hdph]; exact kq _ (Or.inl (by ufo sw at hph ⊢))
  have e2K6 : c₂.nreg K6 = 6 := (E.hK.fix hI₂).2.2.1
  have hframe2 : ∀ r, bandOf r ∉ oracleBands → r ≠ dst → (r < sw 1200 ∨ sw 1207 < r) →
      r ≠ ALLOC → c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 => (k2 r h2).trans (keep1 r h1 h3 h4)
  by_cases hb : c₂.nreg pe < c₂.nreg K6
  · -- a box position: the default
    refine (IRS.ifT hb (IRS.skip (K := 0) hI₂ ⟨?_, hframe2, ?_, ?_⟩)).mono (by omega)
      (fun _ => id)
    · rw [v2, ite_eq_right (by rwo [e2pe, e2K6] at hb)]
    · omega
    · intro a ha; rw [hm2, hm1 a ha]
  refine IRS.mono (IRS.ifF hb ?_) (K := 2 + (11015 + 9) + 2) (by omega) (fun _ => id)
  rw [e2pe, e2K6] at hb
  -- 3. copy `x` and normalise it
  refine IRS.seq (IRS.block [.copyN frGE pe, .copyN frGH ph] hI₂
    ⟨iscr_sw (by rw [hfrGE]; ufn sw) (by rw [hfrGE]; ufn sw),
      iscr_sw (by rw [hfrGH]; ufn sw) (by rw [hfrGH]; ufn sw), trivial⟩) ?_
  rintro c₃ hI₃ hA₃ hA₃' hc3
  have hfrGEph : frGE ≠ ph := by ruo [hfrGE] sw at hph ⊢
  have v3E : c₃.nreg frGE = c.nreg pe := by
    rw [hc3]; simp only [regB, regI, upd, ite_true]; exact e2pe
  have v3H : c₃.nreg frGH = c.nreg ph := by
    rw [hc3]; simp only [regB, regI, upd, ite_true]
    rw [ite_eq_right (show ph ≠ frGE from fun h => hfrGEph h.symm)]; exact e2ph
  have k3 : ∀ r, r ≠ frGE → r ≠ frGH → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [hc3]; simp only [regB, regI, upd, ite_eq_right h1, ite_eq_right h2]
  have hm3 : c₃.nmem = c₂.nmem := by rw [hc3]
  refine IRS.seq (normS_irs (dsc := sw 21) (pe := frGE) (ph := frGH) (o := fO) (C := J.right) hI₃
    (E.hK.fix hI₃) (E.ctx2' hI₃)
    ⟨by ufn sw, by ufn sw, by rw [hfrGE]; ufn sw,
      by rw [hfrGE]; ufn sw, by rw [hfrGH]; ufn sw,
      by rw [hfrGH]; ufn sw⟩
    ⟨by rw [hfO]; ufn sw, by rw [hfO]; ufn sw,
      by ruo [hfO, hfrGE] sw, by ruo [hfO, hfrGH] sw,
      by ruo [hfO, hfrGE] sw, by ruo [hfO, hfrGH] sw,
      by ruo [hfrGE, hfrGH] sw⟩
    (by rwx [v3E]) (by rwx [v3E, v3H])
    (fun h => by rwo [v3E] at h) (by omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨v4E, v4H, k4, hA4, hm4⟩
  rw [v3E] at v4E
  rw [v3E, v3H] at v4H
  have nO : ∀ q, (q < sw 1204 ∨ sw 1207 < q) → q ≠ frGE → q ≠ frGH → bandOf q ∉ oracleBands →
      q ≠ ALLOC → c₄.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 h5 => by
    rw [k4 q h4 h3 (by ruo [hfO] sw at h1 ⊢)
      (by ruo [hfO] sw at h1 ⊢) h5, k3 q h2 h3]
  have ry : ∀ q, sw 1200 ≤ q → q ≤ sw 1203 → c₄.nreg q = c₁.nreg q := fun q h1 h2 => by
    rw [nO q (Or.inl (by ufo sw at h2 ⊢)) (by ruo [hfrGE] sw at h2 ⊢)
      (by ruo [hfrGH] sw at h2 ⊢) (not_oracle_sw (by ufo sw at h1)
        (by ufo sw at h2)) (by unfold ALLOC; ufo sw at h1)]
    exact k2 q (by rcases hdst with rfl | rfl <;> unfold sw at h2 ⊢ <;> omega)
  have r4ye : c₄.nreg ye = Y.edge := by rw [ry ye hye.1 hye.2, v1e]
  have r4yh : c₄.nreg yh = nhgt (chainModel J.right) (Qof P) Y := by rw [ry yh hyh.1 hyh.2, v1h]
  have hsrcR : sw 1109 ≤ src ∧ src ≤ sw 1111 := by
    rcases hsrc with rfl | rfl <;> refine ⟨?_, ?_⟩ <;> simp [lR0, lR2, sw]
  have r4src : c₄.nreg src = c.nreg src := by
    rw [nO src (Or.inl (by ufo sw at hsrcR ⊢)) (by ruo [hfrGE] sw at hsrcR ⊢)
      (by ruo [hfrGH] sw at hsrcR ⊢)
      (not_oracle_sw (by ufo sw at hsrcR) (by ufo sw at hsrcR))
      (by unfold ALLOC; ufo sw at hsrcR),
      k2 _ (by rcases hdst with rfl | rfl <;> unfold sw at hsrcR ⊢ <;> omega)]
    exact kq _ (Or.inr (Or.inr (by ufo sw at hsrcR ⊢)))
  have r4dst : c₄.nreg dst = c.nreg lR1 := by
    rw [nO dst (Or.inr (by rcases hdst with rfl | rfl <;> unfold sw <;> omega))
      (by rw [hfrGE]; rcases hdst with rfl | rfl <;> unfold sw <;> omega)
      (by rw [hfrGH]; rcases hdst with rfl | rfl <;> unfold sw <;> omega)
      (not_oracle_sw (by omega) (by omega)) (by ufo ALLOC), v2]
  have hk0 : c₄.nreg K0 = 0 := (E.hK.fix hI₄).1
  refine (frChk_irs (P := P) (dst := dst) (ye := ye) (yh := yh) (src := src) hI₄ hk0 hd).mono le_rfl ?_
  rintro c₅ ⟨v5, k5, hm5⟩
  have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := k3 _ (by ruo [hfrGE] sw ALLOC)
    (by ruo [hfrGH] sw ALLOC)
  have hA2 : c₂.nreg ALLOC = c₁.nreg ALLOC := k2 _ (by
    rcases hdst with rfl | rfl <;> unfold sw ALLOC <;> omega)
  have hA5 : c₅.nreg ALLOC = c₄.nreg ALLOC := k5 _ (by
    rcases hdst with rfl | rfl <;> unfold sw ALLOC <;> omega)
  refine ⟨?_, fun r h1 h2 h3 h4 => ?_, by omega, fun a ha => ?_⟩
  · rw [v5, v4H, r4ye, r4yh, v4E, r4src, r4dst]
    by_cases hc : nhgt (chainModel J.right) (Qof P) ⟨c.nreg pe, c.nreg ph⟩ = 0 ∧
        Y.edge = c.nreg pe ∧ nhgt (chainModel J.right) (Qof P) Y = 0
    · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc⟩]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2)]
  · rw [k5 r h2, nO r (by ufo sw at h3 ⊢) (by ruo [hfrGE] sw at h3 ⊢)
      (by ruo [hfrGH] sw at h3 ⊢) h1 h4]
    exact hframe2 r h1 h2 h3 h4
  · rw [hm5, hm4 a (by omega), hm3, hm2, hm1 a ha]

end

end SweepEv

end Chazelle.Core
