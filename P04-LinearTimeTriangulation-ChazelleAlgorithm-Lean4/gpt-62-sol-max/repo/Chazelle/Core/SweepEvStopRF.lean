module

public import Chazelle.Core.SweepEvStopRE

/-!
# The sweep (WP-D), stage 2: the per-origin step (RAM, composition)

`orgProg m2 m1 fin sh`: `stLoad`; for an admissible code `stA`; for a free direction the candidate
of `C₂` (`M2Task`), the candidate of `C₁` (`M1Task`), the far end and its attachment (`stWin`),
and the finish (`FinTask`).

**`orgTask_of' : M2Task → M1Task → FinTask → OrgTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The per-origin step.** -/
def orgProg (m2 m1 : Stmt → Stmt) (fin : Stmt) (sh : Stmt) : Stmt :=
  .seq stLoad (.ifLtN K0 oAd (.seq stA (.ifLtN K0 oF0
    (.seq (m2 sh) (.seq (m1 sh) (.seq stWin fin))) .skip)) .skip)

/-- A register outside the frame of a step is kept. -/
theorem EFr.keep {X : ℕ → Prop} {c c' : Config} (h : EFr X c c') {r : ℕ} (h1 : 240000 ≤ r)
    (h2 : r < 250000) (hX : ¬ X r) (hA : r ≠ ALLOC) : c'.nreg r = c.nreg r :=
  h.1 r (not_oracle_sw h1 h2) hX hA

/-- **`OrgOut` lifts** over a prefix keeping the raw array, the memory and the registers outside
`SOrgR`. -/
theorem OrgOut.lift {J : Merge.Junction} {N : NF} {kind k b : ℕ} {c₁ c' : Config}
    (h : OrgOut P J N kind k b c₁ c') (hC : c₁.nreg gRC = c.nreg gRC)
    (hB : c₁.nreg gRB = c.nreg gRB) (hA : c.nreg ALLOC ≤ c₁.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c₁.nmem a = c.nmem a)
    (hr : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c₁.nreg r = c.nreg r) :
    OrgOut P J N kind k b c c' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := h
  rw [hC, hB] at *
  refine ⟨o1, o2, o3, o4, fun a ha hs => ?_, le_trans hA o6, fun r h1 h2 h3 => ?_⟩
  · rw [o5 a (lt_of_lt_of_le ha hA) hs, hm a ha]
  · rw [o7 r h1 h2 h3, hr r h1 h2 h3]

/-- **`OrgOut` without records**: for a code that is not admissible or not free. -/
theorem OrgOut.none {J : Merge.Junction} {N : NF} {kind k b : ℕ} {c' : Config}
    (hD : ¬ OrgD P J N kind k b) (hC : c'.nreg gRC = c.nreg gRC)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hr : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r) :
    OrgOut P J N kind k b c c' := by
  refine ⟨by rw [hC], by rw [hC]; omega, fun i h1 h2 => by rw [hC] at h2; omega,
    fun h => absurd h hD, fun a ha _ => hm a ha, hA, hr⟩

/-! ## The specifications of the pieces -/

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The body of `M2Task`. -/
def M2Spec (m2 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH) →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (m2 sh) c (κ (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => M2Out P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr M2R c c')

/-- The body of `M1Task`. -/
def M1Spec (m1 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH) →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (m1 sh) c (κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (fun c' => ResOK P J.left (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
          (dirOf (c.nreg oB))
          (FreeAt J.left (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
              (dirOf (c.nreg oB)) ∧
            (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB)).2 ≤ J.left.top.2)
          r1F c' ∧ EFr M1R c c')

/-- The body of `FinTask`. -/
def FinSpec (fin : Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) →
      FinPre P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ fin c (κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (OrgOut P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c)

/-! ## The main path -/

set_option maxHeartbeats 2000000 in
/-- **The main path** of the per-origin step: the candidates, the far end, the finish. -/
theorem orgMain_irs {m2 m1 : Stmt → Stmt} {fin : Stmt} {κ2 κ1 κF : ℕ → ℕ}
    (H2 : M2Spec m2 κ2) (H1 : M1Spec m1 κ1) (HF : FinSpec fin κF)
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hpos : OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH))
    (hNB : c.nreg oNB = 1 - c.nreg oB)
    (hA0 : c.nreg (oF0 + 1) < (chainModel J.whole).W.n ∧
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩ ∧
      Arrival (chainModel J.whole).W (stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
        (-dirOf (c.nreg oB)) (c.nreg (oF0 + 1))
        ((chainModel J.whole).param (Qof P) ⟨c.nreg (oF0 + 1), c.nreg (oF0 + 2)⟩))
    (hR0 : c₀.nreg ALLOC ≤ c.nreg gRB) (hR1 : c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + (κ2 (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
      (κ1 (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) *
        (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) + (35600 + κF (c₀.nreg (sw 6)) *
        (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) *
        (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)))) ≤ W) :
    IRS P W c₀ (.seq (m2 sh) (.seq (m1 sh) (.seq stWin fin))) c
      (κ2 (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
      (κ1 (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) *
        (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) + (35600 + κF (c₀.nreg (sw 6)) *
        (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) *
        (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))))
      (OrgOut P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c) := by
  set kind := c.nreg oKd with hkind
  set k := c.nreg oKk with hk
  set b := c.nreg oB with hb
  set a := stOrig J (Qof P) N₂ kind k b with ha
  obtain ⟨-, ha2, -, -, -⟩ := stOrig_facts E.hP E.hNF₂ hD.ok
  -- 1. the candidate of `C₂`
  refine IRS.seq (H2 sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hD hpos (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨⟨r2, par2⟩, fr2⟩
  have e2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ M2R r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr2.keep h1 h2 h3 h4
  have n2 : ∀ r, sw 4010 ≤ r → r ≤ sw 4023 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    e2 r (by unfold sw at *; omega) (by unfold sw at *; omega) (by unfold M2R sw at *; omega)
      (by unfold ALLOC sw at *; omega)
  have c2Kd : c₂.nreg oKd = kind := n2 _ (by unfold oKd; omega) (by unfold oKd sw; omega)
  have c2Kk : c₂.nreg oKk = k := n2 _ (by unfold oKk sw; omega) (by unfold oKk sw; omega)
  have c2B : c₂.nreg oB = b := n2 _ (by unfold oB sw; omega) (by unfold oB sw; omega)
  have c2PE : c₂.nreg oPE = c.nreg oPE := n2 _ (by unfold oPE sw; omega) (by unfold oPE sw; omega)
  have c2PH : c₂.nreg oPH = c.nreg oPH := n2 _ (by unfold oPH sw; omega) (by unfold oPH sw; omega)
  have hD₂ : OrgD P J N₂ (c₂.nreg oKd) (c₂.nreg oKk) (c₂.nreg oB) := by
    rw [c2Kd, c2Kk, c2B]; exact hD
  have hpos₂ : OrgPos P J N₂ (c₂.nreg oKd) (c₂.nreg oKk) (c₂.nreg oB) (c₂.nreg oPE)
      (c₂.nreg oPH) := by rw [c2Kd, c2Kk, c2B, c2PE, c2PH]; exact hpos
  -- 2. the candidate of `C₁`
  refine IRS.seq ((H1 sh Bs F X Ok P W c₀ c₂ J N₁ N₂ E hI₂ hD₂ hpos₂ (by rw [c2Kd]; omega)).mono
    (by rw [c2Kd]) (fun _ h => h)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨r1, fr3⟩
  rw [c2Kd, c2Kk, c2B] at r1
  have e3 : ∀ r, 240000 ≤ r → r < 250000 → ¬ M1R r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => fr3.keep h1 h2 h3 h4
  have n3 : ∀ r, (sw 4010 ≤ r ∧ r ≤ sw 4026) ∨ (sw 4040 ≤ r ∧ r ≤ sw 4046) →
      c₃.nreg r = c₂.nreg r := fun r h =>
    e3 r (by unfold sw at *; omega) (by unfold sw at *; omega) (by unfold M1R sw at *; omega)
      (by unfold ALLOC sw at *; omega)
  have c3B : c₃.nreg oB = b := by rw [n3 _ (Or.inl ⟨by unfold oB sw; omega, by unfold oB sw; omega⟩), c2B]
  have c3NB : c₃.nreg oNB = 1 - b := by
    rw [n3 _ (Or.inl ⟨by unfold oNB sw; omega, by unfold oNB sw; omega⟩),
      n2 _ (by unfold oNB sw; omega) (by unfold oNB sw; omega), hNB]
  have r2' : ResOK P J.right a (dirOf b) (FreeAt J.right a (dirOf b)) r2F c₃ :=
    r2.transport fun i hi => n3 _ (Or.inr ⟨by unfold r2F sw; omega, by unfold r2F sw; omega⟩)
  -- 3. the far end
  refine IRS.seq (stWin_irs E hI₃ hD c3B c3NB r1 r2' (by omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨w1, w2, w3, fr4⟩
  have e4 : ∀ r, 240000 ≤ r → r < 250000 → ¬ WinR r → r ≠ ALLOC → c₄.nreg r = c₃.nreg r :=
    fun r h1 h2 h3 h4 => fr4.keep h1 h2 h3 h4
  have n4 : ∀ r, sw 4000 ≤ r → r ≤ sw 4023 → c₄.nreg r = c.nreg r := by
    intro r h1 h2
    rw [e4 r (by unfold sw at *; omega) (by unfold sw at *; omega) (by unfold WinR sw at *; omega)
      (by unfold ALLOC sw at *; omega),
      e3 r (by unfold sw at *; omega) (by unfold sw at *; omega) (by unfold M1R sw at *; omega)
      (by unfold ALLOC sw at *; omega),
      e2 r (by unfold sw at *; omega) (by unfold sw at *; omega) (by unfold M2R sw at *; omega)
      (by unfold ALLOC sw at *; omega)]
  have c4Kd : c₄.nreg oKd = kind := n4 _ (by unfold oKd sw; omega) (by unfold oKd sw; omega)
  have c4Kk : c₄.nreg oKk = k := n4 _ (by unfold oKk sw; omega) (by unfold oKk sw; omega)
  have c4B : c₄.nreg oB = b := n4 _ (by unfold oB sw; omega) (by unfold oB sw; omega)
  have c4RB : c₄.nreg gRB = c.nreg gRB := n4 _ (by unfold gRB; omega) (by unfold gRB sw; omega)
  have c4RC : c₄.nreg gRC = c.nreg gRC := n4 _ (by unfold gRC sw; omega) (by unfold gRC sw; omega)
  have hD₄ : OrgD P J N₂ (c₄.nreg oKd) (c₄.nreg oKk) (c₄.nreg oB) := by
    rw [c4Kd, c4Kk, c4B]; exact hD
  have hpre : FinPre P J N₂ (c₄.nreg oKd) (c₄.nreg oKk) (c₄.nreg oB) c₄ := by
    rw [c4Kd, c4Kk, c4B]
    have f1 : c₄.nreg (oF0 + 1) = c.nreg (oF0 + 1) :=
      n4 _ (by unfold oF0 sw; omega) (by unfold oF0 sw; omega)
    have f2 : c₄.nreg (oF0 + 2) = c.nreg (oF0 + 2) :=
      n4 _ (by unfold oF0 sw; omega) (by unfold oF0 sw; omega)
    refine ⟨by rw [f1]; exact hA0.1, by rw [f1, f2]; exact hA0.2.1, by rw [f1, f2]; exact hA0.2.2,
      w1, w2, w3, fun hk1 => ?_⟩
    have p1 : c₄.nreg pE2 = c₂.nreg pE2 := by
      rw [e4 _ (by unfold pE2 sw; omega) (by unfold pE2 sw; omega) (by unfold WinR pE2 sw; omega)
        (by unfold ALLOC pE2 sw; omega),
        e3 _ (by unfold pE2 sw; omega) (by unfold pE2 sw; omega) (by unfold M1R pE2 sw; omega)
        (by unfold ALLOC pE2 sw; omega)]
    have p2 : c₄.nreg pH2 = c₂.nreg pH2 := by
      rw [e4 _ (by unfold pH2 sw; omega) (by unfold pH2 sw; omega) (by unfold WinR pH2 sw; omega)
        (by unfold ALLOC pH2 sw; omega),
        e3 _ (by unfold pH2 sw; omega) (by unfold pH2 sw; omega) (by unfold M1R pH2 sw; omega)
        (by unfold ALLOC pH2 sw; omega)]
    rw [p1, p2]
    exact par2 hk1 (free_right hD.free ha2)
  have hAl : c.nreg ALLOC ≤ c₄.nreg ALLOC := by omega
  refine (HF sh Bs F X Ok P W c₀ c₄ J N₁ N₂ E hI₄ hD₄ hpre (by rw [c4RB]; exact hR0)
    (by rw [c4RB, c4RC]; omega) (by rw [c4Kd]; omega)).mono (by rw [c4Kd]) ?_
  intro c' hout
  rw [c4Kd, c4Kk, c4B] at hout
  refine OrgOut.lift hout c4RC c4RB hAl (fun x hx => ?_) (fun r h1 h2 h3 => ?_)
  · rw [fr4.2.2 x (by omega), fr3.2.2 x (by omega), fr2.2.2 x hx]
  · have h2' : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ r = gRC ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
      (sw 4010 ≤ r ∧ r < sw 4200) ∨ (sw 5000 ≤ r ∧ r < sw 6000)) := h2
    rw [fr4.1 r h1 (by unfold WinR at *; unfold sw at *; omega) h3,
      fr3.1 r h1 (by unfold M1R at *; unfold sw at *; omega) h3,
      fr2.1 r h1 (by unfold M2R at *; unfold sw at *; omega) h3]

/-! ## The per-origin step -/

/-- The cost constant of the per-origin step. -/
def κOrg (κ2 κ1 κF : ℕ → ℕ) (D : ℕ) : ℕ := 70663 + κ2 D + κ1 D + κF D

theorem org_cost_le (κ2 κ1 κF : ℕ → ℕ) (D M G : ℕ) (hM : 1 ≤ M) (hG : 1 ≤ G) :
    30 + (35029 + (κ2 D * G + (κ1 D * M * G + (35600 + κF D * M * G)) + 2) + 2) ≤
      κOrg κ2 κ1 κF D * M * G := by
  have hMG : 1 ≤ M * G := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have e : κOrg κ2 κ1 κF D * M * G =
      70663 * (M * G) + κ2 D * (M * G) + κ1 D * M * G + κF D * M * G := by
    unfold κOrg; ring
  have h2 : κ2 D * G ≤ κ2 D * (M * G) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h0 : 70663 ≤ 70663 * (M * G) := by omega
  omega

set_option maxHeartbeats 2000000 in
/-- **The per-origin step** from its pieces. -/
theorem orgTask_of' (h2 : M2Task) (h1 : M1Task) (hF : FinTask) : OrgTask := by
  obtain ⟨m2, κ2, H2⟩ := h2
  obtain ⟨m1, κ1, H1⟩ := h1
  obtain ⟨fin, κF, HF⟩ := hF
  refine ⟨orgProg m2 m1 fin, κOrg κ2 κ1 κF, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hkd hb hk hR0 hR1 hroom
  set D := c₀.nreg (sw 6) with hD
  set G := F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1 with hG
  set M := (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; split_ifs <;> omega
  have hG1 : 1 ≤ G := by omega
  have hcost := org_cost_le κ2 κ1 κF D M G hM1 hG1
  set Km := κ2 D * G + (κ1 D * M * G + (35600 + κF D * M * G)) with hKm
  set kind := c.nreg oKd with hkind
  set k := c.nreg oKk with hkk
  set b := c.nreg oB with hbb
  have hK := E.hK.fix hI
  unfold orgProg
  refine (IRS.seq (K₁ := 30) (K₂ := 35029 + (Km + 2) + 2) (stLoad_irs E hI hkd hb hk (by
    have := Nat.zero_le Km; omega)) ?_).mono hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨ld1, ld2, ld3, ld4⟩, fr1⟩
  have e1 : ∀ r, 240000 ≤ r → r < 250000 → ¬ LdW r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => fr1.keep h1 h2 h3 h4
  have k1 : ∀ r, (sw 4000 ≤ r ∧ r ≤ sw 4012) ∨ (sw 4020 ≤ r ∧ r ≤ sw 4023) → c₁.nreg r = c.nreg r :=
    fun r h => e1 r (by unfold sw at *; omega) (by unfold sw at *; omega)
      (by unfold LdW LdW₀ oNB oPE oPH oAd tX tR sw at *; omega) (by unfold ALLOC sw at *; omega)
  have c1Kd : c₁.nreg oKd = kind := k1 _ (Or.inl ⟨by unfold oKd sw; omega, by unfold oKd sw; omega⟩)
  have c1Kk : c₁.nreg oKk = k := k1 _ (Or.inl ⟨by unfold oKk sw; omega, by unfold oKk sw; omega⟩)
  have c1B : c₁.nreg oB = b := k1 _ (Or.inl ⟨by unfold oB sw; omega, by unfold oB sw; omega⟩)
  have c1RB : c₁.nreg gRB = c.nreg gRB := k1 _ (Or.inl ⟨by unfold gRB; omega, by unfold gRB sw; omega⟩)
  have c1RC : c₁.nreg gRC = c.nreg gRC := k1 _ (Or.inl ⟨by unfold gRC sw; omega, by unfold gRC sw; omega⟩)
  have k1K0 : c₁.nreg K0 = 0 := hK.1 ▸ (E.hK.fix hI₁).1
  have fr1S : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1.1 r h1 (fun hx => h2 (by
      unfold LdW LdW₀ oNB oPE oPH oAd tX tR at hx; unfold SOrgR; unfold sw at *; omega)) h3
  refine IRS.ite (fun hAd => ?_) (fun hAd => ?_)
  · -- an admissible code
    have hAd1 : c₁.nreg oAd = 1 := by rw [k1K0] at hAd; omega
    have hok : StOK P J N₂ kind k b := ld3.1 hAd1
    have hpos := ld4 hAd1
    refine IRS.seq (K₁ := 35029) (K₂ := Km + 2) (stA_irs E.hP E.hNF₂ hI₁ E.hK (E.fx hI₁) hok c1B
      hpos.2.2.2.1 hpos.2.2.1 hpos.2.1 (by have := E.hWn; omega) (by omega)) ?_
    rintro c₂ hI₂ hA₂ hA₂' ⟨f1, f2, f3, fr2⟩
    have e2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ StAW r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
      fun r h1 h2 h3 h4 => fr2.keep h1 h2 h3 h4
    have k2 : ∀ r, sw 4000 ≤ r → r ≤ sw 4017 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
      e2 r (by unfold sw at *; omega) (by unfold sw at *; omega)
        (by unfold StAW CvSet oXE cX cT cDd oF0 sw at *; omega) (by unfold ALLOC sw at *; omega)
    have c2Kd : c₂.nreg oKd = kind := by rw [k2 _ (by unfold oKd sw; omega) (by unfold oKd sw; omega), c1Kd]
    have c2Kk : c₂.nreg oKk = k := by rw [k2 _ (by unfold oKk sw; omega) (by unfold oKk sw; omega), c1Kk]
    have c2B : c₂.nreg oB = b := by rw [k2 _ (by unfold oB sw; omega) (by unfold oB sw; omega), c1B]
    have c2NB : c₂.nreg oNB = 1 - b := by
      rw [k2 _ (by unfold oNB sw; omega) (by unfold oNB sw; omega), ld1]
    have c2PE : c₂.nreg oPE = c₁.nreg oPE := k2 _ (by unfold oPE sw; omega) (by unfold oPE sw; omega)
    have c2PH : c₂.nreg oPH = c₁.nreg oPH := k2 _ (by unfold oPH sw; omega) (by unfold oPH sw; omega)
    have c2RB : c₂.nreg gRB = c.nreg gRB := by rw [k2 _ (by unfold gRB; omega) (by unfold gRB sw; omega), c1RB]
    have c2RC : c₂.nreg gRC = c.nreg gRC := by rw [k2 _ (by unfold gRC sw; omega) (by unfold gRC sw; omega), c1RC]
    have k2K0 : c₂.nreg K0 = 0 := hK.1 ▸ (E.hK.fix hI₂).1
    have fr2S : ∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
      fun r h1 h2 h3 => (fr2.1 r h1 (fun hx => h2 (by
        unfold StAW CvSet oXE cX cT cDd oF0 at hx; unfold SOrgR; unfold sw at *; omega)) h3).trans
        (fr1S r h1 h2 h3)
    have hmem2 : ∀ x, x < c.nreg ALLOC → c₂.nmem x = c.nmem x := fun x hx => by
      rw [fr2.2.2 x (by omega), fr1.2.2 x hx]
    refine IRS.ite (fun hF0 => ?_) (fun hF0 => ?_)
    · -- a free direction
      have hF1 : c₂.nreg oF0 = 1 := by rw [k2K0] at hF0; omega
      have hDo : OrgD P J N₂ kind k b := ⟨hok, f2.1 hF1⟩
      have hM₂ : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c₂ := by
        refine (hM.transport (fun r hr => ?_) fr1.2.2 fr1.2.1).transport (fun r hr => ?_)
          fr2.2.2 fr2.2.1
        · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            exact e1 _ (by simp only [gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [LdW, LdW₀, oNB, oPE, oPH, oAd, tX, tR, gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [ALLOC, gMD2, gCD2, TBR, TLR, sw]; omega)
        · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
            exact e2 _ (by simp only [gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [StAW, CvSet, oXE, cX, cT, cDd, oF0, gMD2, gCD2, TBR, TLR, sw]; omega)
              (by simp only [ALLOC, gMD2, gCD2, TBR, TLR, sw]; omega)
      have hD₂ : OrgD P J N₂ (c₂.nreg oKd) (c₂.nreg oKk) (c₂.nreg oB) := by
        rw [c2Kd, c2Kk, c2B]; exact hDo
      have hpos₂ : OrgPos P J N₂ (c₂.nreg oKd) (c₂.nreg oKk) (c₂.nreg oB) (c₂.nreg oPE)
          (c₂.nreg oPH) := by rw [c2Kd, c2Kk, c2B, c2PE, c2PH]; exact hpos
      have hA0 := f3 hF1
      have hmain := orgMain_irs (sh := sh) H2 H1 HF E hI₂ hM₂ hD₂ hpos₂ (by rw [c2NB, c2B])
        (by rw [c2Kd, c2Kk, c2B]; exact hA0) (by rw [c2RB]; exact hR0) (by rw [c2RB, c2RC]; omega)
        (by rw [c2Kd]; show c₂.nreg ALLOC + Km ≤ W; omega)
      rw [c2Kd, c2Kk, c2B] at hmain
      refine hmain.mono le_rfl (fun c' hout => OrgOut.lift hout c2RC c2RB (by omega) hmem2 fr2S)
    · -- not free
      have hF0' : c₂.nreg oF0 ≠ 1 := by rw [k2K0] at hF0; omega
      refine IRS.skip hI₂ (OrgOut.none (fun hDo => hF0' (f2.2 hDo.free)) c2RC (by omega) hmem2
        fr2S)
  · -- not admissible
    have hAd0 : c₁.nreg oAd ≠ 1 := by rw [k1K0] at hAd; omega
    refine IRS.skip hI₁ (OrgOut.none (fun hDo => hAd0 (ld3.2 hDo.ok)) c1RC fr1.2.1 fr1.2.2 fr1S)

end

end SweepEv

end Chazelle.Core
