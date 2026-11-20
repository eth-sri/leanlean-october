module

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepEvStopTasks

/-!
# The sweep (WP-D), stage 2: the fixed facts, conversions, the attachment at the origin (RAM)

* `Fx`: the facts of the fixed registers used by stage 2 (`EvEnv.fx`);
* `convR_irs`, `convL_irs`: a position of the model of `C₂` (`C₁`) of the class of `convS` to a
  position of the model of `C` with the same point and parameter;
* `stA`: the origin's position in `M` and its arrival position there (`stA_irs`): the flag is
  the freeness of the direction, the position the attachment of the stop chord at its origin.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The fixed facts** at a configuration of the run steps. -/
structure Fx (P : Polygon) (W : ℕ) (J : Merge.Junction) (c : Config) : Prop where
  k : Consts c
  r40 : ∀ k, k < 5 → c.nreg (sw (40 + k)) = cstR J k
  r45 : ∀ k, k < 5 → c.nreg (sw (45 + k)) = cstL J k
  n1 : c.nreg (sw 33) = 2 * J.left.m + 7
  n2 : c.nreg (sw 34) = 2 * J.right.m + 7
  nw : c.nreg (sw 35) = 2 * J.whole.m + 7
  gw : c.nreg cGW = gW J
  mpk : MapK J c
  ctxW : ChainCtx P W c (sw 2) J.whole
  ctx2 : ChainCtx P W c (sw 21) J.right
  ctx1 : ChainCtx P W c CD₁ J.left

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

theorem EvEnv.fx (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) : Fx P W J c := by
  obtain ⟨H, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := hst
  have fix : ∀ i, i < 700 → c.nreg (sw i) = c₀.nreg (sw i) := fun i hi =>
    hI.hin _ (by reg_omega)
  refine ⟨E.hK.fix hI, fun k hk => by ram_finish,
    fun k hk => by ram_finish, by simp_all,
    by simp_all, by simp_all, E.gw' hI,
    E.hM.fix hI, E.ctxW' hI, E.ctx2' hI, E.ctx1' hI⟩

/-! ## Conversions -/

/-- The converted walk position and its frame. -/
abbrev ConvPost (P : Polygon) (M M' : Model) (pe po h : ℕ) (c c' : Config) : Prop :=
  c'.nreg po < M.W.n ∧
  M.param (Qof P) ⟨c'.nreg po, h⟩ = M'.param (Qof P) ⟨c.nreg pe, h⟩ ∧
  M.pos (Qof P) ⟨c'.nreg po, h⟩ = M'.pos (Qof P) ⟨c.nreg pe, h⟩ ∧
  (∀ r, ¬ CvSet po r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem

/-- Run the same conversion on either child; only the descriptor constants differ. -/
private theorem conv_irs (hI : IInv W c₀ c) (hK : Consts c₀) {C : Chain} {b nr pe po h g g' L₁ L₂ δ : ℕ}
    (hS : SideConv J.wholeModel (chainModel C) C g g' L₁ L₂ δ) (hC : C.m ≤ J.whole.m)
    (hb : b = sw 40 ∨ b = sw 45) (hr : nr = sw 33 ∨ nr = sw 34)
    (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd) (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd)
    (hcl : PosClass C (Qof P) ⟨c.nreg pe, h⟩) (hW : J.wholeModel.W.n ≤ W)
    (e0 : c.nreg b = g) (e1 : c.nreg (b + 1) = g') (e2 : c.nreg (b + 2) = L₁)
    (e4 : c.nreg (b + 4) = δ) (en : c.nreg nr = (chainModel C).W.n)
    (eW : c.nreg (sw 35) = J.wholeModel.W.n) :
    IRS P W c₀ (convS b nr pe po) c 22 (ConvPost P J.wholeModel (chainModel C) pe po h c) := by
  have hn := cm_n C
  have hw : J.wholeModel.W.n = 2 * J.whole.m + 7 := cm_n J.whole
  rw [hw] at hW
  have hg := hS.hg
  obtain ⟨τ, rfl, hτ, -⟩ := hS.hτ
  have hpn : c.nreg pe < c.nreg nr := by
    rw [en, hn]
    rcases hcl with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
  refine (convS_irs hb hr hpe hpo hI hK hpn (by rw [e1, en, hn]; omega)
    (by rw [en, hn]; omega) (by rwa [e0, eW]) (eW.trans_le (hw.trans_le hW))).mono le_rfl ?_
  rintro c' ⟨hv, hr', hm⟩
  rw [e0, e1, e2, e4, en, eW] at hv
  obtain ⟨hi, ht, hz⟩ := conv_pos hS (Qof P) hcl
  exact ⟨hv ▸ hi, hv ▸ ht, hv ▸ hz, hr', hm⟩

section

variable (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {pe po : ℕ} (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd ∧ 240000 ≤ pe)
    (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd) {h : ℕ}
include hP hI hK hfx hpe hpo h

/-- Convert a position in `C₂` to the whole chain's model. -/
theorem convR_irs
    (hcl : PosClass J.right (Qof P) ⟨c.nreg pe, h⟩) (hW : J.wholeModel.W.n ≤ W) :
    IRS P W c₀ (convS (sw 40) (sw 34) pe po) c 22 (ConvPost P J.wholeModel J.rightModel pe po h c) :=
  conv_irs hI hK (sideConvR J hP) (by change J.right.m ≤ J.left.m + J.right.m; omega)
    (Or.inl rfl) (Or.inr rfl) ⟨hpe.1, hpe.2.1, hpe.2.2.1⟩ hpo hcl hW
    (hfx.r40 0 (by decide)) (hfx.r40 1 (by decide)) (hfx.r40 2 (by decide)) (hfx.r40 4 (by decide))
    (hfx.n2.trans (cm_n J.right).symm) (hfx.nw.trans (cm_n J.whole).symm)

/-- Convert a position in `C₁` to the whole chain's model. -/
theorem convL_irs
    (hcl : PosClass J.left (Qof P) ⟨c.nreg pe, h⟩) (hW : J.wholeModel.W.n ≤ W) :
    IRS P W c₀ (convS (sw 45) (sw 33) pe po) c 22 (ConvPost P J.wholeModel J.leftModel pe po h c) :=
  conv_irs hI hK (sideConvL J hP) (by change J.left.m ≤ J.left.m + J.right.m; omega)
    (Or.inr rfl) (Or.inl rfl) ⟨hpe.1, hpe.2.1, hpe.2.2.1⟩ hpo hcl hW
    (hfx.r45 0 (by decide)) (hfx.r45 1 (by decide)) (hfx.r45 2 (by decide)) (hfx.r45 4 (by decide))
    (hfx.n1.trans (cm_n J.left).symm) (hfx.nw.trans (cm_n J.whole).symm)

end

/-! ## The attachment at the origin -/

@[ram_layout] def oKd : ℕ := sw 4010
@[ram_layout] def oKk : ℕ := sw 4011
@[ram_layout] def oB : ℕ := sw 4012
@[ram_layout] def oNB : ℕ := sw 4013
@[ram_layout] def oPE : ℕ := sw 4014
@[ram_layout] def oPH : ℕ := sw 4015
@[ram_layout] def oXE : ℕ := sw 4018
@[ram_layout] def oF0 : ℕ := sw 4020

/-- **The origin's position in `M` and its arrival position** (direction code `oB`). -/
def stA : Stmt := .seq (convS (sw 40) (sw 34) oPE oXE) (callArr (sw 2) oXE oPH oB oF0)

/-- The registers `stA` writes (besides the oracle bands). -/
def StAW (r : ℕ) : Prop := CvSet oXE r ∨ (oF0 ≤ r ∧ r ≤ oF0 + 2)

set_option maxRecDepth 20000 in
theorem stA_irs (hP : J.P.Simple) (hNF : IsNF J.rightModel (Qof P) N₂)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {kind k b : ℕ} (hok : StOK P J N₂ kind k b) (hb : c.nreg oB = b)
    (hpos : J.rightModel.pos (Qof P) ⟨c.nreg oPE, c.nreg oPH⟩ = stOrig J (Qof P) N₂ kind k b)
    (hcl : PosClass J.right (Qof P) ⟨c.nreg oPE, c.nreg oPH⟩)
    (hpp : ProperPos J.rightModel (Qof P) P.n ⟨c.nreg oPE, c.nreg oPH⟩)
    (hW : J.wholeModel.W.n ≤ W) (hroom : c.nreg ALLOC + 35029 ≤ W) :
    IRS P W c₀ stA c 35029 (fun c' => c'.nreg oF0 ≤ 1 ∧
      (c'.nreg oF0 = 1 ↔ FreeAt J.whole (stOrig J (Qof P) N₂ kind k b) (dirOf b)) ∧
      (c'.nreg oF0 = 1 → c'.nreg (oF0 + 1) < J.wholeModel.W.n ∧
        ProperPos J.wholeModel (Qof P) P.n ⟨c'.nreg (oF0 + 1), c'.nreg (oF0 + 2)⟩ ∧
        Arrival J.wholeModel.W (stOrig J (Qof P) N₂ kind k b) (-dirOf b)
          (c'.nreg (oF0 + 1))
          (J.wholeModel.param (Qof P) ⟨c'.nreg (oF0 + 1), c'.nreg (oF0 + 2)⟩)) ∧
      EFr StAW c c') := by
  obtain ⟨-, -, hay, hset, hwall⟩ := stOrig_facts hP hNF hok
  set a := stOrig J (Qof P) N₂ kind k b with ha
  unfold stA
  refine IRS.seq (K₁ := 22) (K₂ := 35007) (convR_irs hP hI hK hfx
    (by reg_omega)
    ⟨iscr_sw (by reg_omega) (by reg_omega), by reg_omega,
      by reg_omega, by reg_omega⟩ hcl hW) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hxn, hxpar, hxpos, hr1, hm1⟩
  have k1 : ∀ r, r ≠ oXE → r ≠ cX → r ≠ cT → r ≠ cDd → c₁.nreg r = c.nreg r :=
    fun r a b d e => hr1 r (by unfold CvSet; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by reg_omega)
    (by reg_omega) (by reg_omega) (by reg_omega)
  have hH1 : c₁.nreg oPH = c.nreg oPH := k1 _ (by reg_omega)
    (by reg_omega) (by reg_omega) (by reg_omega)
  have hB1 : c₁.nreg oB = c.nreg oB := k1 _ (by reg_omega)
    (by reg_omega) (by reg_omega) (by reg_omega)
  have hctx := hfx.ctxW.transport
    (k1 _ (by reg_omega) (by reg_omega) (by reg_omega)
      (by reg_omega)) (fun x _ => by rw [hm1]) (by rw [hA1])
  have hposM : J.wholeModel.pos (Qof P) ⟨c₁.nreg oXE, c₁.nreg oPH⟩ = a := by
    rw [hH1, hxpos, hpos]
  
  refine (callArr_irs (o := oF0) hI₁ hctx
    (by reg_omega) (by reg_omega) hxn
    ⟨by rw [hH1, hxpar]; exact hpp.1, by rw [hH1, hxpar]; exact hpp.2.1,
      by rw [hH1]; exact hpp.2.2⟩ (by rwa [hposM]) (by rw [hA1]; omega)).mono le_rfl ?_
  rintro c' ⟨⟨hf1, hf2, hf3⟩, hr2, hA2, hm2⟩
  rw [hposM, hB1, hb] at hf2 hf3
  have hσ := SweepStop.dirOf_cases' b
  have hon : a ∈ J.whole.set ∨ (|a.1| = J.whole.radius ∧ |a.2| < J.whole.radius) := by
    by_cases h1 : kind = 1
    · exact Or.inr ⟨hwall h1, hay⟩
    · exact Or.inl (J.right_set_subset (hset h1))
  have hiff := freeAt_iff_arr J.whole hP hσ hon
  refine ⟨hf1, ⟨fun h => hiff.2 ⟨_, _, (hf2 h).2.2⟩, fun h => ?_⟩, hf2, ?_⟩
  · by_contra hne
    obtain ⟨p, t, harr⟩ := hiff.1 h
    exact hf3 hne p t harr
  · refine ⟨fun r h1 h2 h3 => ?_, by rwa [← hA1], fun x hx => by
      rw [hm2 x (by rwa [hA1]), hm1]⟩
    have h2' := h2
    rw [hr2 r h1 (fun h => h2' (Or.inr (by omega))) (fun h => h2' (Or.inr (by omega)))
      (fun h => h2' (Or.inr (by omega))) h3]
    exact hr1 r (fun h => h2' (Or.inl h))

end

end SweepEv

end Chazelle.Core
