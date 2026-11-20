module

public import Chazelle.Core.SweepIoCand0S

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0`, the shared vertex and the main
class

* `sharedS sh`: the arrival position of the shared vertex in the model of `C₂` (`callArr` on
  `sw 21` at `(cstR 1, qH)`), then the local hit there (`shared_irs`);
* `mainS lab0 candC sh`: the symbolic point of the query point (`callSym` into `sO`), the label
  candidates (`Lab0Spec`), the stop and table candidates (`S0CandSpec`); complete by
  `Side0MathSpec` (`main_irs`).
* `Lab0Body`, `S0Body`: the bodies of the contracts `Lab0Spec`, `S0CandSpec`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The bodies of the part contracts -/

/-- The body of `Lab0Spec` for the program `lab0` and the cost constant `κ`. -/
def Lab0Body (lab0 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z (dirOf (c.nreg qD)) →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩ →
      Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
        ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
      SymPtIn c sO s → s.Lt P.n → s.eval (Qof P) = z →
      c.nreg bR = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (lab0 sh) c (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.right (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            ∀ (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)), ls.length = rd c₀ bSweep 301 →
              LogRecsAt c₀.nmem (rd c₀ bSweep 300) ls →
              ∀ i, LogIdx J (Qof P) N₂ ls
                  (c.nreg zP + (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) i →
                ∀ V ∈ (chainModel J.right).regions (N₂.F (chainModel J.right) (Qof P)),
                  (V ∈ logLab J (Qof P) N₂ ls i ∨ (0 < i ∧ V ∈ logLab J (Qof P) N₂ ls (i - 1)) ∨
                    GapLab J (N₂.F (chainModel J.right) (Qof P)) V) →
                  (∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), rayPt z (dirOf (c.nreg qD)) s ∈ V) →
                  J.right.hitParam z (dirOf (c.nreg qD)) ∈ L') ∧
          PartFr c c')

theorem lab0Spec_iff : Lab0Spec ↔ ∃ lab0 κ, Lab0Body lab0 κ := Iff.rfl

/-- The per-query body of `S0CandSpec`. -/
def S0Body (candC : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ) :
    Prop :=
  ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
      (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z (dirOf (c.nreg qD)) →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩ →
      Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
        ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
      c.nreg bL = 1 → c.nreg bR = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ candC c (κ (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            (∀ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
                  (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩ →
                dirOf r.2.2.2.2 = -dirOf (c.nreg qD) →
                ∀ τ, 0 < τ → stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z (dirOf (c.nreg qD)) τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
                some (c.nreg zP, (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
              endDir j = -dirOf (c.nreg qD) → endOrigin J (Qof P) N₂ j ∈ J.right.set →
              endOrigin J (Qof P) N₂ j ≠ J.shared → endOrigin J (Qof P) N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J (Qof P) N₂ j = rayPt z (dirOf (c.nreg qD)) τ →
                τ ∈ L')) ∧
          PartFr c c')

theorem s0CandSpec_iff : S0CandSpec ↔ ∃ initC candC Aux κ, InitSpec initC Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧ S0Body candC Aux κ := Iff.rfl

/-! ## The pipeline registers -/

/-- The pipeline registers of a later configuration. -/
theorem pipe8 {c c' : Config} (h : CandFr c c') :
    c'.nreg qE = c.nreg qE ∧ c'.nreg qH = c.nreg qH ∧ c'.nreg qD = c.nreg qD ∧
    c'.nreg zE = c.nreg zE ∧ c'.nreg zP = c.nreg zP ∧ c'.nreg zPh = c.nreg zPh ∧
    c'.nreg bL = c.nreg bL ∧ c'.nreg bR = c.nreg bR :=
  ⟨h.pipe (by unfold qE sw; omega) (by unfold qE sw; omega),
    h.pipe (by unfold qH sw; omega) (by unfold qH sw; omega),
    h.pipe (by unfold qD sw; omega) (by unfold qD sw; omega),
    h.pipe (by unfold zE sw; omega) (by unfold zE sw; omega),
    h.pipe (by unfold zP sw; omega) (by unfold zP sw; omega),
    h.pipe (by unfold zPh sw; omega) (by unfold zPh sw; omega),
    h.pipe (by unfold bL sw; omega) (by unfold bL sw; omega),
    h.pipe (by unfold bR sw; omega) (by unfold bR sw; omega)⟩

/-! ## The shared vertex -/

/-- The outputs of the arrival position of the shared vertex (`aO`, `aO + 1`, `aO + 2`). -/
def aO : ℕ := sw 4820

/-- **The shared vertex**: its arrival position in the model of `C₂`, then the local hit there. -/
def sharedS (sh : Stmt) : Stmt :=
  .seq (callArr (sw 21) (sw 41) qH qD aO)
    (.ifLtN aO K1 .skip (lhs (sw 31) (sw 4) (sw 34) (aO + 1) 1 sh))

section Steps

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}

set_option maxHeartbeats 4000000 in
/-- **The shared vertex** completes the candidates. -/
theorem shared_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {c' : Config} (hI : IInv W c₀ c') (hQ : QState P J 0 z c)
    (hfr : CandFr c c') {L : Set ℝ} (hst : AccSt P J z c L c')
    (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L) (hzs : z = J.shared)
    (hroom : c'.nreg ALLOC + (35007 + (Klh c₀ F + 2)) ≤ W) :
    IRS P W c₀ (sharedS sh) c' (35007 + (Klh c₀ F + 2)) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  have q := q0_of hQ
  obtain ⟨eE, eH, eD, -, -, -, -, -⟩ := pipe8 hfr
  have hP := hA.hP
  have hz2 : z.2 ≤ J.right.top.2 := by
    rw [hzs, ← J.right_vertex_zero]; exact J.right.vertex_snd_le_top (Nat.zero_le _)
  have hbR : c.nreg bR = 1 := (hQ.hbR.2).2 hz2
  have hS := sideD₂ hA
  have hctx : ChainCtx P W c' (sw 21) J.right :=
    hS.hctx.transport (hI.hin _ (by unfold IFix sw; omega)) (fun a ha => hI.hm a ha) hI.hA
  have e41 : c'.nreg (sw 41) = cstR J 1 := by
    rw [hI.hin _ (by unfold IFix sw; omega)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -⟩ := hA.hst
    exact h40 1 (by norm_num)
  obtain ⟨hlt, hpar0, hpos0⟩ := shared_pos₂ (h := c.nreg qH - 1) hP (Qof P)
    (by rw [q.hzh, hzs])
  have hqh : c.nreg qH - 1 + 1 = c.nreg qH := by have := q.hh1; omega
  rw [hqh] at hpar0 hpos0
  have hyS : |J.shared.2| < J.right.radius := absy_lt J.right J.shared_mem_right
  unfold sharedS
  refine IRS.seq (K₁ := 35007) (K₂ := Klh c₀ F + 2)
    (callArr_irs (dsc := sw 21) (re := sw 41) (rh := qH) (rd := qD) (o := aO) hI hctx
      (by unfold qH qD sw; omega) (by unfold aO sw; omega) (by rw [e41]; exact hlt)
      (by rw [e41, eH]; exact ⟨by rw [hpar0], by rw [hpar0]; exact one_pos, q.hhn⟩)
      (by rw [e41, eH, hpos0]; exact hyS) (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨harr, fr2, hA2, hm2⟩
  rw [e41, eH, eD] at harr
  unfold ArrAt at harr
  rw [hpos0] at harr
  have k2 : ∀ r, sw 3200 ≤ r → r < sw 3230 → c₂.nreg r = c'.nreg r := fun r h1 h2 =>
    fr2 r (not_oracle_sw (by unfold sw at *; omega) (by unfold sw at *; omega))
      (by unfold aO sw at *; omega) (by unfold aO sw at *; omega) (by unfold aO sw at *; omega)
      (by unfold ALLOC sw at *; omega)
  have hfr₂ : CandFr c c₂ := hfr.trans (candFr_of_set (S := fun r => r = aO ∨ r = aO + 1 ∨
      r = aO + 2) (fun r hr => Or.inr (by rcases hr with rfl | rfl | rfl <;> unfold aO sw <;> omega))
    (fun r h1 h2 h3 => fr2 r h1 (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr (Or.inl h)))
      (fun h => h2 (Or.inr (Or.inr h))) h3) hA2 hm2)
  obtain ⟨eE2, eH2, eD2, -, -, -, -, -⟩ := pipe8 hfr₂
  have hk1 : c₂.nreg K1 = 1 := (hA.hK.fix hI₂).2.1
  have hσ := q.hσ
  refine IRS.ite (fun hf => ?_) (fun hf => ?_)
  · -- no arrival position: impossible, the direction is free for `C₂`
    exfalso
    rw [hk1] at hf
    have hne : c₂.nreg aO ≠ 1 := by omega
    obtain ⟨p, t, hpt⟩ := arrival_of_freeC J.right hP hσ (Or.inl (hzs ▸ J.shared_mem_right))
      (freeAt_right_of_whole hz2 q.hfree)
    rw [← hzs] at harr
    exact harr.2.2 hne p t hpt
  · rw [hk1] at hf
    have hf1 : c₂.nreg aO = 1 := by have := harr.1; omega
    obtain ⟨hp, hpp, hA'⟩ := harr.2.1 hf1
    rw [← hzs] at hA'
    have hzh' : ((Qof P).vtx (c.nreg qH - 1)).2 = z.2 := q.hzh
    obtain ⟨hgeo, hposA, hparA⟩ := lhGeo_arr hA' (h := c.nreg qH - 1) (by have := q.hhn; have := q.hh1; omega)
      hzh' hz2 (d := c.nreg qD) rfl
    rw [hqh] at hgeo hposA hparA
    have hcls := posClass_of (C := J.right) (Q := Qof P) (x := ⟨c₂.nreg (aO + 1), c.nreg qH⟩) hp
      (by rw [hparA]; exact hpp.1) (by rw [hparA]; exact hpp.2.1) (by rw [hposA]; exact q.hy)
      (Or.inl (by rw [hposA]; exact hz2))
    have hloc : (c₂.nreg (aO + 1) = 1 ∨ c₂.nreg (aO + 1) = 3) ∨
        (6 ≤ c₂.nreg (aO + 1) ∧ z ∈ J.right.set) := by
      have hzr : z ∈ J.right.set := hzs ▸ J.shared_mem_right
      rcases hcls with h | ⟨h6, -⟩ | ⟨h6, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h6, hzr⟩
      · have h6' : c₂.nreg (aO + 1) = 2 * J.right.m + 6 := h6
        exact Or.inr ⟨by omega, hzr⟩
    have hacc₂ : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
        (dirOf (c₂.nreg qD)) L c₂ := by
      rw [eD2]
      exact hst.1.transport (fun j hj => by
        rw [fr2 _ (not_oracle_sw (by unfold accA sw; omega) (by unfold accA sw; omega))
          (by unfold accA aO sw; omega) (by unfold accA aO sw; omega)
          (by unfold accA aO sw; omega) (by unfold accA ALLOC sw; omega)])
    refine (lhs_irs hsh hBs hXl hA hS ⟨by unfold IFix sw; omega, by unfold IFix sw; omega,
      by unfold IFix sw; omega⟩ (by unfold OutL aO sw; omega) hI₂ (L := L)
      (Mod := ModB J (c.nreg bL) (c.nreg bR)) (R₀ := J.whole.radius) (t := 1) (z := z)
      hp (by rw [eH2]; exact ⟨by rw [hparA]; exact hpp.1, by rw [hparA]; exact hpp.2.1, q.hhn⟩)
      (by rw [eH2]; exact hposA) q.hy hloc hacc₂ (by norm_num)
      (by rw [q.hbL, hbR]; exact modB_right J) rfl
      (by show c₂.nreg ALLOC + Klh c₀ F ≤ W; omega)).mono le_rfl ?_
    rintro c'' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
    rw [eD2] at a' g' geo'
    rw [eH2] at geo'
    have hr := geo' hgeo
    refine ⟨⟨L', a', fun τ hτ => ?_, whole_mem_of_both q.hz1 hz2 hσ (s' hl) hr⟩,
      hfr₂.trans (candFr_of_lh fr hA' hm')⟩
    rcases g' τ hτ with h | ⟨h1, h2⟩
    · exact hst.2 τ h
    · exact ⟨h1, onCB_right h2⟩

end Steps

end

end SweepIo

end Chazelle.Core
