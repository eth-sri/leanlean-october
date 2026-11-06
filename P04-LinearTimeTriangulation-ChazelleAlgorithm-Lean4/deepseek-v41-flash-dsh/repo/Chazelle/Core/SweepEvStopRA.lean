module

public import Chazelle.Golf

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
    hI.hin _ (by unfold IFix sw; omega)
  refine ⟨E.hK.fix hI, fun k hk => by rw [fix _ (⋄)]; exact h40 k hk,
    fun k hk => by rw [fix _ (⋄)]; exact h45 k hk, by rw [fix _ (⋄)]; exact h33,
    by rw [fix _ (⋄)]; exact h34, by rw [fix _ (⋄)]; exact h35, E.gw' hI,
    E.hM.fix hI, E.ctxW' hI, E.ctx2' hI, E.ctx1' hI⟩

/-! ## Conversions -/

/-- **A position of the model of `C₂` converted to the model of `C`.** -/
theorem convR_irs (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {pe po : ℕ} (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd ∧ 240000 ≤ pe)
    (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd) {h : ℕ}
    (hcl : PosClass J.right (Qof P) ⟨c.nreg pe, h⟩) (hW : (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ (convS (sw 40) (sw 34) pe po) c 22 (fun c' =>
      c'.nreg po < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param (Qof P) ⟨c'.nreg po, h⟩ =
        (chainModel J.right).param (Qof P) ⟨c.nreg pe, h⟩ ∧
      (chainModel J.whole).pos (Qof P) ⟨c'.nreg po, h⟩ =
        (chainModel J.right).pos (Qof P) ⟨c.nreg pe, h⟩ ∧
      (∀ r, ¬ CvSet po r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hn₂ : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have g0 := hfx.r40 0 (⊛)
  have g1 := hfx.r40 1 (⊛)
  have g2 := hfx.r40 2 (⊛)
  have g4 := hfx.r40 4 (⊛)
  ϴ' cstR, List.getD_cons_zero, List.getD_cons_succ at g0 g1 g2 g4
  have hpen : c.nreg pe < c.nreg (sw 34) := by
    Ξ hfx.n2
    rcases hcl with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
  have hτ := tpos_lt J.right 0
  have hτw := tpos_lt J.whole J.m₁
  have hmm : J.whole.m = J.left.m + J.right.m := rfl
  Ξ' hn at hW
  refine (convS_irs (Or.inl rfl) (Or.inr rfl) ⟨hpe.1, hpe.2.1, hpe.2.2.1⟩ hpo hI hK hpen
    (by show c.nreg (sw (40 + 1)) < _; rw [g1, hfx.n2]; omega) (by rw [hfx.n2]; omega)
    (by show c.nreg (sw (40 + 0)) < _; rw [g0, hfx.nw]; omega) (by rw [hfx.nw]; omega)).mono
    le_rfl ?_
  rintro c' ⟨hv, hr, hm⟩
  have hS := sideConvR J hP
  have e0 := g0
  have e1 : c.nreg (sw 40 + 1) = 6 + tpos J.right 0 := g1
  have e2 : c.nreg (sw 40 + 2) = rL1 J := g2
  have e4 : c.nreg (sw 40 + 4) = rδ J := g4
  Ξ' e0, e1, e2, e4, hfx.n2, hfx.nw, ← hn₂, ← hn at hv
  obtain ⟨a1, a2, a3⟩ := conv_pos hS (Qof P) (e := c.nreg pe) (h := h) (by
    rcases hcl with h' | ⟨h6, h'⟩ | ⟨h', h''⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨h6, h'⟩)
    · exact Or.inr (Or.inr ⟨h', h''⟩))
  Ξ' ← hv at a1 a2 a3
  exact ⟨a1, a2, a3, hr, hm⟩

/-- **A position of the model of `C₁` converted to the model of `C`.** -/
theorem convL_irs (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {pe po : ℕ} (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd ∧ 240000 ≤ pe)
    (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd) {h : ℕ}
    (hcl : PosClass J.left (Qof P) ⟨c.nreg pe, h⟩) (hW : (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ (convS (sw 45) (sw 33) pe po) c 22 (fun c' =>
      c'.nreg po < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param (Qof P) ⟨c'.nreg po, h⟩ =
        (chainModel J.left).param (Qof P) ⟨c.nreg pe, h⟩ ∧
      (chainModel J.whole).pos (Qof P) ⟨c'.nreg po, h⟩ =
        (chainModel J.left).pos (Qof P) ⟨c.nreg pe, h⟩ ∧
      (∀ r, ¬ CvSet po r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hn₁ : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have g0 := hfx.r45 0 (⊛)
  have g1 := hfx.r45 1 (⊛)
  have g2 := hfx.r45 2 (⊛)
  have g4 := hfx.r45 4 (⊛)
  ϴ' cstL, List.getD_cons_zero, List.getD_cons_succ at g0 g1 g2 g4
  have hpen : c.nreg pe < c.nreg (sw 33) := by
    Ξ hfx.n1
    rcases hcl with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
  have hτ := tpos_lt J.left J.m₁
  have hτw := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have hmm : J.whole.m = J.left.m + J.right.m := rfl
  Ξ' hn at hW
  refine (convS_irs (Or.inr rfl) (Or.inl rfl) ⟨hpe.1, hpe.2.1, hpe.2.2.1⟩ hpo hI hK hpen
    (by show c.nreg (sw (45 + 1)) < _; rw [g1, hfx.n1]; omega) (by rw [hfx.n1]; omega)
    (by show c.nreg (sw (45 + 0)) < _; rw [g0, hfx.nw]; omega) (by rw [hfx.nw]; omega)).mono
    le_rfl ?_
  rintro c' ⟨hv, hr, hm⟩
  have hS := sideConvL J hP
  have e0 := g0
  have e1 : c.nreg (sw 45 + 1) = 6 + tpos J.left J.m₁ := g1
  have e2 : c.nreg (sw 45 + 2) = lL1 J := g2
  have e4 : c.nreg (sw 45 + 4) = lδ J := g4
  Ξ' e0, e1, e2, e4, hfx.n1, hfx.nw, ← hn₁, ← hn at hv
  obtain ⟨a1, a2, a3⟩ := conv_pos hS (Qof P) (e := c.nreg pe) (h := h) (by
    rcases hcl with h' | ⟨h6, h'⟩ | ⟨h', h''⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨h6, h'⟩)
    · exact Or.inr (Or.inr ⟨h', h''⟩))
  Ξ' ← hv at a1 a2 a3
  exact ⟨a1, a2, a3, hr, hm⟩

/-! ## The attachment at the origin -/

def oKd : ℕ := sw 4010
def oKk : ℕ := sw 4011
def oB : ℕ := sw 4012
def oNB : ℕ := sw 4013
def oPE : ℕ := sw 4014
def oPH : ℕ := sw 4015
def oXE : ℕ := sw 4018
def oF0 : ℕ := sw 4020

/-- **The origin's position in `M` and its arrival position** (direction code `oB`). -/
def stA : Stmt := .seq (convS (sw 40) (sw 34) oPE oXE) (callArr (sw 2) oXE oPH oB oF0)

/-- The registers `stA` writes (besides the oracle bands). -/
def StAW (r : ℕ) : Prop := CvSet oXE r ∨ (oF0 ≤ r ∧ r ≤ oF0 + 2)


theorem stA_irs (hP : J.P.Simple) (hNF : IsNF (chainModel J.right) (Qof P) N₂)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hfx : Fx P W J c)
    {kind k b : ℕ} (hok : StOK P J N₂ kind k b) (hb : c.nreg oB = b)
    (hpos : (chainModel J.right).pos (Qof P) ⟨c.nreg oPE, c.nreg oPH⟩ = stOrig J (Qof P) N₂ kind k b)
    (hcl : PosClass J.right (Qof P) ⟨c.nreg oPE, c.nreg oPH⟩)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg oPE, c.nreg oPH⟩)
    (hW : (chainModel J.whole).W.n ≤ W) (hroom : c.nreg ALLOC + 35029 ≤ W) :
    IRS P W c₀ stA c 35029 (fun c' => c'.nreg oF0 ≤ 1 ∧
      (c'.nreg oF0 = 1 ↔ FreeAt J.whole (stOrig J (Qof P) N₂ kind k b) (dirOf b)) ∧
      (c'.nreg oF0 = 1 → c'.nreg (oF0 + 1) < (chainModel J.whole).W.n ∧
        ProperPos (chainModel J.whole) (Qof P) P.n ⟨c'.nreg (oF0 + 1), c'.nreg (oF0 + 2)⟩ ∧
        Arrival (chainModel J.whole).W (stOrig J (Qof P) N₂ kind k b) (-dirOf b)
          (c'.nreg (oF0 + 1))
          ((chainModel J.whole).param (Qof P) ⟨c'.nreg (oF0 + 1), c'.nreg (oF0 + 2)⟩)) ∧
      EFr StAW c c') := by
  obtain ⟨-, -, hay, hset, hwall⟩ := stOrig_facts hP hNF hok
  set a := stOrig J (Qof P) N₂ kind k b with ha
  unfold stA
  refine IRS.seq (K₁ := 22) (K₂ := 35007) (convR_irs hP hI hK hfx
    ⟨by unfold oPE cX sw; omega, by unfold oPE cT sw; omega, by unfold oPE cDd sw; omega,
      by unfold oPE sw; omega⟩
    ⟨iscr_sw (by unfold oXE sw; omega) (by unfold oXE sw; omega), by unfold oXE cX sw; omega,
      by unfold oXE cT sw; omega, by unfold oXE cDd sw; omega⟩ hcl hW) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hxn, hxpar, hxpos, hr1, hm1⟩
  have k1 : ∀ r, r ≠ oXE → r ≠ cX → r ≠ cT → r ≠ cDd → c₁.nreg r = c.nreg r :=
    fun r a b d e => hr1 r (by unfold CvSet; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold oXE ALLOC sw; omega)
    (by unfold cX ALLOC sw; omega) (by unfold cT ALLOC sw; omega) (by unfold cDd ALLOC sw; omega)
  have hH1 : c₁.nreg oPH = c.nreg oPH := k1 _ (by unfold oXE oPH sw; omega)
    (by unfold cX oPH sw; omega) (by unfold cT oPH sw; omega) (by unfold cDd oPH sw; omega)
  have hB1 : c₁.nreg oB = c.nreg oB := k1 _ (by unfold oXE oB sw; omega)
    (by unfold cX oB sw; omega) (by unfold cT oB sw; omega) (by unfold cDd oB sw; omega)
  have hctx := hfx.ctxW.transport
    (k1 _ (by unfold oXE sw; omega) (by unfold cX sw; omega) (by unfold cT sw; omega)
      (by unfold cDd sw; omega)) (fun x _ => Ρ hm1) (Ρ hA1)
  have hposM : (chainModel J.whole).pos (Qof P) ⟨c₁.nreg oXE, c₁.nreg oPH⟩ = a := by
    Ξ hH1, hxpos, hpos
  have hR : J.right.radius = J.whole.radius := rfl
  refine (callArr_irs (o := oF0) hI₁ hctx
    ⟨by unfold sw; omega, by unfold sw; omega, by unfold oXE sw; omega, by unfold oXE sw; omega,
      by unfold oPH sw; omega, by unfold oPH sw; omega, by unfold oB sw; omega,
      by unfold oB sw; omega⟩ ⟨by unfold oF0 sw; omega, by unfold oF0 sw; omega⟩ hxn
    ⟨by rw [hH1, hxpar]; exact hpp.1, by rw [hH1, hxpar]; exact hpp.2.1,
      by rw [hH1]; exact hpp.2.2⟩ (by rw [hposM]; exact hay) (by rw [hA1]; omega)).mono le_rfl ?_
  rintro c' ⟨⟨hf1, hf2, hf3⟩, hr2, hA2, hm2⟩
  Ξ' hposM, hB1, hb at hf2 hf3
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
  · refine ⟨fun r h1 h2 h3 => ?_, by rw [← hA1]; exact hA2, fun x hx => by
      rw [hm2 x (by rw [hA1]; exact hx), hm1]⟩
    have h2' := h2
    rw [hr2 r h1 (fun h => h2' (Or.inr (⋄))) (fun h => h2' (Or.inr (⋄)))
      (fun h => h2' (Or.inr (⋄))) h3]
    exact hr1 r (fun h => h2' (Or.inl h))

end

end SweepEv

end Chazelle.Core
