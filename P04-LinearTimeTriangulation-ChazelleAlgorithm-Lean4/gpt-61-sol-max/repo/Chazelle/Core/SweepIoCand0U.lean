module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoCand0T

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0`, the main class

`mainS lab0 candC sh`: for a query point `z` of `C₁` other than the shared vertex, not above the
top of `C₂`: the symbolic point of `z` (`callSym` on the descriptor of `C` at `(zE, qH)`, into
`sO`), the label candidates (`Lab0Spec`), the stop and table candidates (`S0CandSpec`).  The
first hit of `C` is among the candidates by `Side0MathSpec` (cases C1 (the local hit in the model
of `C₁`, already offered), C2 (the label shots), C3 (the stops), C4 (the table)).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The main class.** -/
def mainS (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (callSym (sw 2) zE qH (sw 3230)) (.seq (lab0 sh) candC)

/-- The cost of the main class. -/
def Kmain (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  16707 + (κL (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
    κS (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1))

section Steps

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}

set_option maxHeartbeats 8000000 in
/-- **The main class** completes the candidates. -/
theorem main_irs {lab0 : Stmt → Stmt} {candC : Stmt}
    {Aux : Polygon → Merge.Junction → NF → Config → Prop} {κL κS : ℕ → ℕ}
    (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L)
    (hzL : z ∈ J.left.set) (hzs : z ≠ J.shared) (hbR : c.nreg bR = 1)
    (hroom : c'.nreg ALLOC + Kmain κL κS c₀ F ≤ W) :
    IRS P W c₀ (mainS lab0 candC sh) c' (Kmain κL κS c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  have q := q0_of hQ
  have hσ := q.hσ
  have hz2 : z.2 ≤ J.right.top.2 := (hQ.hbR.2).1 hbR
  obtain ⟨-, -, eD, eZ, eP, ePh, eL, eR⟩ := pipe8 hfr
  -- the chain context of `C`
  have hctx₀ : ChainCtx P W c₀ (sw 2) J.whole := by
    obtain ⟨-, -, -, -, hJ, hJW, -⟩ := hA.hst
    exact ctx_of_aenv hA hJ.2.2 hJW.2.2.1 hA.hP le_rfl
  have hctx : ChainCtx P W c' (sw 2) J.whole :=
    hctx₀.transport (hI.hin _ (by omega_nf)) (fun a ha => hI.hm a ha) hI.hA
  have hzW : (chainModel J.whole).pos (Qof P) ⟨c.nreg zE, c.nreg qH⟩ = z := hQ.hzM
  have hcls := posClass_of (C := J.whole) hQ.hzE hQ.hzpp.1 hQ.hzpp.2.1
    (by rw [hzW]; exact q.hy) (Or.inl (by rw [hzW]; exact q.hz1.trans J.left_top_le))
  have hcls' : (6 ≤ c.nreg zE ∧ c.nreg zE < 2 * J.whole.m + 6) ∨
      (c.nreg zE = 2 * J.whole.m + 6 ∧
        (chainModel J.whole).param (Qof P) ⟨c.nreg zE, c.nreg qH⟩ = 0) := by
    rcases hcls with h | h | h
    · exact absurd (hzW ▸ J.left_set_subset hzL) (fun hm => box_not_mem h hm)
    all_goals ram_grind
  obtain ⟨-, eH, -, -, -, -, -, -⟩ := pipe8 hfr
  -- 1. the symbolic point
  unfold mainS Kmain
  unfold Kmain at hroom
  refine IRS.seq (K₁ := 16707) (callSym_irs (dsc := sw 2) (re := zE) (rh := qH) (o := sw 3230)
    hI hctx (by omega_nf) (by omega_nf) (by rw [eZ]; exact hQ.hzE)
    (by rw [eZ, eH]; exact hQ.hzpp) (by rw [eZ, eH, hzW]; exact q.hy)
    (by simp_all) (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨sp, hsp, hspl, hspe, fr2, hA2, hm2⟩
  rw [eZ, eH, hzW] at hspe
  have hfr₂ : CandFr c c₂ := hfr.trans (candFr_of_set (S := fun r => sw 3230 ≤ r ∧ r ≤ sw 3233)
    (fun r hr => Or.inl (by ram_grind))
    (fun r h1 h2 h3 => fr2 r h1 (by grind [sw]) h3) hA2 hm2)
  obtain ⟨-, -, eD2, -, eP2, ePh2, eL2, eR2⟩ := pipe8 hfr₂
  have hacc₂ : AccOK P accA (ModB J (c₂.nreg bL) (c₂.nreg bR)) J.whole.radius z
      (dirOf (c₂.nreg qD)) L c₂ := by
    rw [eL2, eR2, eD2]
    exact hst.1.transport (fun j hj => by
      rw [fr2 _ (not_oracle_sw (by omega_nf) (by omega_nf))
        (by omega_nf) (by omega_nf)])
  -- 2. the label candidates
  refine IRS.seq (hLab sh Bs F X Ok hsh hBs hXl P W c₀ c₂ J H N₁ N₂ E L sp z hA hI₂ hzL hzs hz2
    (by rw [eD2]; exact q.hfree) (by rw [eP2]; exact hQ.hzP) (by rw [eP2, ePh2]; exact hQ.hzPp)
    (by rw [eP2, ePh2, eD2]; exact hQ.harr) (by unfold sO; exact hsp) hspl hspe
    (by omega) hacc₂ (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨L₃, a3, s3, g3, comp3⟩, fr3⟩
  rw [eL2, eR2, eD2] at a3
  rw [eD2] at g3 comp3
  rw [eP2, ePh2] at comp3
  have hfr₃ : CandFr c c₃ := hfr₂.trans (candFr_of_part fr3)
  obtain ⟨-, -, eD3, -, eP3, ePh3, eL3, eR3⟩ := pipe8 hfr₃
  -- 3. the stop and table candidates
  refine (hSC P W X Ok J H N₁ N₂ E c₀ c₃ L₃ z hA hAux hI₃ hzL hzs hz2
    (by rw [eD3]; exact q.hfree) (by rw [eP3]; exact hQ.hzP) (by rw [eP3, ePh3]; exact hQ.hzPp)
    (by rw [eP3, ePh3, eD3]; exact hQ.harr) (by rw [eL3]; exact q.hbL) (by omega)
    (by ram_grind) (by omega)).mono le_rfl ?_
  rintro c₄ ⟨⟨L₄, a4, s4, g4, stp, tab⟩, fr4⟩
  rw [eL3, eR3, eD3] at a4
  rw [eD3] at g4 stp tab
  rw [eP3, ePh3] at stp tab
  have hfr₄ : CandFr c c₄ := hfr₃.trans (candFr_of_part fr4)
  refine ⟨⟨L₄, a4, fun τ hτ => ?_, ?_⟩, hfr₄⟩
  · rcases g4 τ hτ with h | h
    · rcases g3 τ h with h' | ⟨h1, h2⟩
      · exact hst.2 τ h'
      · exact ⟨h1, onCB_right h2⟩
    · exact h
  -- completeness
  obtain ⟨rs, ls, hrsl, hrsAt, hStops, -, hlsl, hlsAt, hLog, -, hTab, -⟩ := hA.hout
  obtain ⟨hLst, hcases⟩ := hM P J N₂ rs ls (tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302)) hA.hG
    hA.hP hA.hNF₂ hLog hStops hTab z (dirOf (c.nreg qD)) hσ hzL hzs hz2 q.hfree (c.nreg zP)
    ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) hQ.harr
  obtain ⟨i, hi⟩ := logIdx_exists hLog hLst
  have hpos : 0 < J.whole.hitParam z (dirOf (c.nreg qD)) :=
    (Merge.hit_of_freeAt J.whole (q.hz1.trans J.left_top_le) hσ q.hfree).1
  rcases hcases i hi with h1 | ⟨h2, V, hV, hlab, hev⟩ | ⟨r, hr, hr1, hr2, hr3, hr4⟩ |
      ⟨j, hj, hT, hd, ho1, ho2, ho3, ho4⟩
  · grind
  · rw [← h2]; exact s4 (comp3 ls hlsl hlsAt i hi V hV hlab hev)
  · exact stp rs hrsl hrsAt r hr hr1 hr2 hr3 _ hpos hr4
  · exact tab j hj hT hd ho1 ho2 ho3 _ hpos ho4

end Steps

end

end SweepIo

end Chazelle.Core
