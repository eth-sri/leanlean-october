module

public import Chazelle.Core.SweepEvStopTasks3

/-!
# The sweep (WP-D), stage 2: the far end of a stop chord (RAM)

`stWin`: from the candidates of `C₁` (`r1F`) and `C₂` (`r2F`) for the first hit of `C` from the
origin, the nearer one (`callAbsCmp` of their abscissas): the far end `farPt` (`win_min`,
`win_only2`); its position in the walk of `C` (`convS`), and its arrival position there in the
direction `σ` (`callArr` with the reversed code `oNB`): the attachment `A₁` at `a1F + 1, a1F + 2`
(`stWin_irs`).
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

def wC1 : ℕ := sw 4096
def wC2 : ℕ := sw 4097
def wBit : ℕ := sw 4047
def wnE : ℕ := sw 4048
def wnH : ℕ := sw 4049

/-- Compare the two candidates (the nearer along the ray). -/
def winCmp : Stmt :=
  .seq (callAbsCmp (r1F + 3) (r2F + 3) wC1) (.seq (callAbsCmp (r2F + 3) (r1F + 3) wC2)
    (.ifLtN K0 oB (.instr (.copyN wBit wC1)) (.instr (.copyN wBit wC2))))

/-- Select the candidate: `wBit = 1` for the candidate of `C₁`. -/
def winSel : Stmt := .ifLtN K0 r1F winCmp (.instr (.constN wBit 0))

/-- Its position in the walk of `C`. -/
def winConv : Stmt :=
  .ifLtN K0 wBit (.seq (convS (sw 45) (sw 33) (r1F + 1) wnE) (.instr (.copyN wnH (r1F + 2))))
    (.seq (convS (sw 40) (sw 34) (r2F + 1) wnE) (.instr (.copyN wnH (r2F + 2))))

/-- **The far end and its attachment.** -/
def stWin : Stmt := .seq winSel (.seq winConv (callArr (sw 2) wnE wnH oNB a1F))

/-- The registers `stWin` writes (besides the oracle bands). -/
def WinR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨ (sw 4047 ≤ r ∧ r ≤ sw 4052) ∨
    (sw 4096 ≤ r ∧ r ≤ sw 4097)

/-! ## The comparison -/

/-- The order of the abscissas along the ray. -/
theorem ray_lt_iff {a : Point} {b : ℕ} (hb : b ≤ 1) {τ₁ τ₂ : ℝ} :
    (if b = 1 then (rayPt a (dirOf b) τ₁).1 < (rayPt a (dirOf b) τ₂).1
      else (rayPt a (dirOf b) τ₂).1 < (rayPt a (dirOf b) τ₁).1) ↔ τ₁ < τ₂ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
  · rw [ite_eq_right (by norm_num), rayPt_fst, rayPt_fst, dirOf_zero]
    constructor <;> intro h <;> linarith
  · rw [ite_eq_left rfl, rayPt_fst, rayPt_fst, dirOf_one]
    constructor <;> intro h <;> linarith

theorem winCmp_irs (hI : IInv W c₀ c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hK : Consts c)
    {b : ℕ} (hb : b ≤ 1) (hB : c.nreg oB = b) {x₁ x₂ R : ℝ} (h₁ : AbsRec P c (r1F + 3) x₁ R)
    (h₂ : AbsRec P c (r2F + 3) x₂ R) (hroom : c.nreg ALLOC + 600 ≤ W) :
    IRS P W c₀ winCmp c 541 (fun c' => c'.nreg wBit ≤ 1 ∧
      (c'.nreg wBit = 1 ↔ (if b = 1 then x₁ < x₂ else x₂ < x₁)) ∧
      EFr (fun r => r = wC1 ∨ r = wC2 ∨ r = wBit) c c') := by
  unfold winCmp
  refine IRS.seq (K₁ := 269) (K₂ := 272) (callAbsCmp_irs hI hG hW
    ⟨by unfold r1F sw; omega, by unfold r1F sw; omega, by unfold r2F sw; omega,
      by unfold r2F sw; omega⟩ ⟨by unfold wC1 sw; omega, by unfold wC1 sw; omega⟩ h₁ h₂
    (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hb1, k1, -, m1⟩
  have kr : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1 r (not_oracle_sw h1 h2) h3 (by unfold ALLOC; omega)
  have h₁' : AbsRec P c₁ (r1F + 3) x₁ R := absRec_transport h₁
    (kr _ (by unfold r1F sw; omega) (by unfold r1F sw; omega) (by unfold r1F wC1 sw; omega))
    (kr _ (by unfold r1F sw; omega) (by unfold r1F sw; omega) (by unfold r1F wC1 sw; omega))
    (kr _ (by unfold r1F sw; omega) (by unfold r1F sw; omega) (by unfold r1F wC1 sw; omega))
    (kr _ (by unfold r1F sw; omega) (by unfold r1F sw; omega) (by unfold r1F wC1 sw; omega))
  have h₂' : AbsRec P c₁ (r2F + 3) x₂ R := absRec_transport h₂
    (kr _ (by unfold r2F sw; omega) (by unfold r2F sw; omega) (by unfold r2F wC1 sw; omega))
    (kr _ (by unfold r2F sw; omega) (by unfold r2F sw; omega) (by unfold r2F wC1 sw; omega))
    (kr _ (by unfold r2F sw; omega) (by unfold r2F sw; omega) (by unfold r2F wC1 sw; omega))
    (kr _ (by unfold r2F sw; omega) (by unfold r2F sw; omega) (by unfold r2F wC1 sw; omega))
  refine IRS.seq (K₁ := 269) (K₂ := 3) (callAbsCmp_irs hI₁ hG hW
    ⟨by unfold r2F sw; omega, by unfold r2F sw; omega, by unfold r1F sw; omega,
      by unfold r1F sw; omega⟩ ⟨by unfold wC2 sw; omega, by unfold wC2 sw; omega⟩ h₂' h₁'
    (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hb2, k2, -, m2⟩
  have kr2 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => (k2 r (not_oracle_sw h1 h2) h4 (by unfold ALLOC; omega)).trans
      (kr r h1 h2 h3)
  have c2B : c₂.nreg oB = b := by
    rw [kr2 _ (by unfold oB sw; omega) (by unfold oB sw; omega) (by unfold oB wC1 sw; omega)
      (by unfold oB wC2 sw; omega), hB]
  have c2K0 : c₂.nreg K0 = 0 := by
    rw [kr2 _ (by unfold K0 sw; omega) (by unfold K0 sw; omega) (by unfold K0 wC1 sw; omega)
      (by unfold K0 wC2 sw; omega)]; exact hK.1
  have c2C1 : c₂.nreg wC1 = c₁.nreg wC1 :=
    k2 _ (not_oracle_sw (by unfold wC1 sw; omega) (by unfold wC1 sw; omega))
      (by unfold wC1 wC2 sw; omega) (by unfold wC1 ALLOC sw; omega)
  have fr : ∀ c', (∀ q, q ≠ wBit → c'.nreg q = c₂.nreg q) →
      c'.nmem = c₂.nmem → EFr (fun r => r = wC1 ∨ r = wC2 ∨ r = wBit) c c' := by
    intro c' hq hm
    refine ⟨fun r hr hX hra => ?_, ?_, fun a ha => ?_⟩
    · rw [hq r (fun h => hX (Or.inr (Or.inr h))), k2 r hr (fun h => hX (Or.inr (Or.inl h))) hra,
        k1 r hr (fun h => hX (Or.inl h)) hra]
    · rw [hq _ (by unfold ALLOC wBit sw; omega)]; omega
    · rw [hm, m2 a (by omega), m1 a ha]
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · have hb1' : b = 1 := by rw [c2K0, c2B] at h; omega
    refine (copy1_irs hI₂ ⟨by unfold wBit sw; omega, by unfold wBit sw; omega⟩).mono le_rfl ?_
    rintro c' ⟨a1, a2, a3⟩
    refine ⟨by rw [a1, c2C1]; exact hb1.1, ?_, fr c' a2 a3⟩
    rw [a1, c2C1, ite_eq_left hb1']; exact hb1.2
  · have hb0 : b ≠ 1 := by rw [c2K0, c2B] at h; omega
    refine (copy1_irs hI₂ ⟨by unfold wBit sw; omega, by unfold wBit sw; omega⟩).mono le_rfl ?_
    rintro c' ⟨a1, a2, a3⟩
    refine ⟨by rw [a1]; exact hb2.1, ?_, fr c' a2 a3⟩
    rw [a1, ite_eq_right hb0]; exact hb2.2

/-! ## The selected position -/

theorem dirOf_rev' {b : ℕ} (hb : b ≤ 1) : dirOf (1 - b) = -dirOf b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
  · rw [show 1 - 0 = 1 from rfl, dirOf_one, dirOf_zero]; norm_num
  · rw [show 1 - 1 = 0 from rfl, dirOf_one, dirOf_zero]

/-- A candidate position: of the class of `convS`, its point on the chain or on a wall. -/
theorem winPos {C : Chain} {Q : Polygon} {n : ℕ} {a : Point} {σ τ : ℝ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hpp : ProperPos (chainModel C) Q n x)
    (hpos : (chainModel C).pos Q x = rayPt a σ τ) (hon : OnCB C (rayPt a σ τ))
    (hy : |a.2| < C.radius) :
    PosClass C Q x ∧ (rayPt a σ τ ∈ C.set ∨
      (|(rayPt a σ τ).1| = C.radius ∧ |(rayPt a σ τ).2| < C.radius)) := by
  have hy' : |((chainModel C).pos Q x).2| < C.radius := by rw [hpos, rayPt_snd]; exact hy
  rcases hon with h | h | h
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' (Or.inl ?_), Or.inl h⟩
    rw [hpos]; exact C.snd_le_top_of_mem_set h
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' (Or.inr (by rw [hpos]; exact h)), Or.inr ⟨h, ?_⟩⟩
    rw [rayPt_snd]; exact hy
  · rw [rayPt_snd] at h; rw [h] at hy; exact absurd hy (lt_irrefl _)

/-- **The selected position in the walk of `C`.** -/
theorem winConv_irs {J : Merge.Junction} (hP : J.P.Simple) (hI : IInv W c₀ c) (hK : Consts c₀)
    (hfx : Fx P W J c) (hW : (chainModel J.whole).W.n ≤ W) {Z : Point}
    (h1 : c.nreg wBit = 1 → c.nreg (r1F + 1) < (chainModel J.left).W.n ∧
      ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg (r1F + 1), c.nreg (r1F + 2)⟩ ∧
      PosClass J.left (Qof P) ⟨c.nreg (r1F + 1), c.nreg (r1F + 2)⟩ ∧
      (chainModel J.left).pos (Qof P) ⟨c.nreg (r1F + 1), c.nreg (r1F + 2)⟩ = Z)
    (h0 : c.nreg wBit ≠ 1 → c.nreg (r2F + 1) < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg (r2F + 1), c.nreg (r2F + 2)⟩ ∧
      PosClass J.right (Qof P) ⟨c.nreg (r2F + 1), c.nreg (r2F + 2)⟩ ∧
      (chainModel J.right).pos (Qof P) ⟨c.nreg (r2F + 1), c.nreg (r2F + 2)⟩ = Z)
    (hK0 : c.nreg K0 = 0) (hb : c.nreg wBit ≤ 1) :
    IRS P W c₀ winConv c 25 (fun c' => c'.nreg wnE < (chainModel J.whole).W.n ∧
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c'.nreg wnE, c'.nreg wnH⟩ ∧
      (chainModel J.whole).pos (Qof P) ⟨c'.nreg wnE, c'.nreg wnH⟩ = Z ∧
      (∀ r, ¬ CvSet wnE r → r ≠ wnH → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold winConv
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · have hw : c.nreg wBit = 1 := by rw [hK0] at h; omega
    obtain ⟨a1, a2, a3, a4⟩ := h1 hw
    refine IRS.seq (K₁ := 22) (K₂ := 1) (convL_irs hP hI hK hfx
      ⟨by unfold r1F cX sw; omega, by unfold r1F cT sw; omega, by unfold r1F cDd sw; omega,
        by unfold r1F sw; omega⟩
      ⟨iscr_sw (by unfold wnE sw; omega) (by unfold wnE sw; omega), by unfold wnE cX sw; omega,
        by unfold wnE cT sw; omega, by unfold wnE cDd sw; omega⟩ a3 hW) ?_
    rintro c₁ hI₁ - - ⟨v1, v2, v3, k1, m1⟩
    refine (copy1_irs hI₁ ⟨by unfold wnH sw; omega, by unfold wnH sw; omega⟩).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3⟩
    have eE : c'.nreg wnE = c₁.nreg wnE := b2 _ (by unfold wnE wnH sw; omega)
    have eH : c'.nreg wnH = c.nreg (r1F + 2) := by
      rw [b1, k1 _ (by unfold CvSet wnE cX cT cDd r1F sw; omega)]
    refine ⟨by rw [eE]; exact v1, ?_, by rw [eE, eH, v3, a4], fun r hr hr2 => ?_, by rw [b3, m1]⟩
    · rw [eE, eH]
      exact ⟨by rw [v2]; exact a2.1, by rw [v2]; exact a2.2.1, a2.2.2⟩
    · rw [b2 r hr2, k1 r hr]
  · have hw : c.nreg wBit ≠ 1 := by rw [hK0] at h; omega
    obtain ⟨a1, a2, a3, a4⟩ := h0 hw
    refine IRS.seq (K₁ := 22) (K₂ := 1) (convR_irs hP hI hK hfx
      ⟨by unfold r2F cX sw; omega, by unfold r2F cT sw; omega, by unfold r2F cDd sw; omega,
        by unfold r2F sw; omega⟩
      ⟨iscr_sw (by unfold wnE sw; omega) (by unfold wnE sw; omega), by unfold wnE cX sw; omega,
        by unfold wnE cT sw; omega, by unfold wnE cDd sw; omega⟩ a3 hW) ?_
    rintro c₁ hI₁ - - ⟨v1, v2, v3, k1, m1⟩
    refine (copy1_irs hI₁ ⟨by unfold wnH sw; omega, by unfold wnH sw; omega⟩).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3⟩
    have eE : c'.nreg wnE = c₁.nreg wnE := b2 _ (by unfold wnE wnH sw; omega)
    have eH : c'.nreg wnH = c.nreg (r2F + 2) := by
      rw [b1, k1 _ (by unfold CvSet wnE cX cT cDd r2F sw; omega)]
    refine ⟨by rw [eE]; exact v1, ?_, by rw [eE, eH, v3, a4], fun r hr hr2 => ?_, by rw [b3, m1]⟩
    · rw [eE, eH]
      exact ⟨by rw [v2]; exact a2.1, by rw [v2]; exact a2.2.1, a2.2.2⟩
    · rw [b2 r hr2, k1 r hr]

/-! ## The far end and its attachment -/

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

set_option maxHeartbeats 1000000 in
/-- **The far end of the stop chord and its attachment `A₁`.** -/
theorem stWin_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {kind k b : ℕ}
    (hD : OrgD P J N₂ kind k b) (hB : c.nreg oB = b) (hNB : c.nreg oNB = 1 - b)
    (h1 : ResOK P J.left (stOrig J (Qof P) N₂ kind k b) (dirOf b)
      (FreeAt J.left (stOrig J (Qof P) N₂ kind k b) (dirOf b) ∧
        (stOrig J (Qof P) N₂ kind k b).2 ≤ J.left.top.2) r1F c)
    (h2 : ResOK P J.right (stOrig J (Qof P) N₂ kind k b) (dirOf b)
      (FreeAt J.right (stOrig J (Qof P) N₂ kind k b) (dirOf b)) r2F c)
    (hroom : c.nreg ALLOC + 35600 ≤ W) :
    IRS P W c₀ stWin c 35600 (fun c' => c'.nreg (a1F + 1) < (chainModel J.whole).W.n ∧
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c'.nreg (a1F + 1), c'.nreg (a1F + 2)⟩ ∧
      Arrival (chainModel J.whole).W (farPt J.whole (stOrig J (Qof P) N₂ kind k b) (dirOf b))
        (dirOf b) (c'.nreg (a1F + 1))
        ((chainModel J.whole).param (Qof P) ⟨c'.nreg (a1F + 1), c'.nreg (a1F + 2)⟩) ∧
      EFr WinR c c') := by
  have hP := E.hP
  have hb : b ≤ 1 := hD.ok.2.1
  have hσ := SweepStop.dirOf_cases' b
  obtain ⟨-, ha2, hay, -, -⟩ := stOrig_facts hP E.hNF₂ hD.ok
  set a := stOrig J (Qof P) N₂ kind k b with ha
  set σ := dirOf b with hσdef
  have hf : FreeAt J.whole a σ := hD.free
  have hf2 : FreeAt J.right a σ := free_right hf ha2
  have hK := E.hK.fix hI
  -- the candidate of `C₂`
  obtain ⟨τ₂, t2p, t2on, t2e, t2pp, t2pos, t2abs, t2g⟩ := h2.2.1 (h2.2.2 hf2)
  have t2h := t2g hf2
  obtain ⟨t2cl, t2z⟩ := winPos t2e t2pp t2pos t2on hay
  have hGood1 : ∀ h : FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2, c.nreg r1F = 1 := fun h => h1.2.2 h
  -- the far end is on `C` or a wall
  have hZ : farPt J.whole a σ ∈ J.whole.set ∨
      (|(farPt J.whole a σ).1| = J.whole.radius ∧ |(farPt J.whole a σ).2| < J.whole.radius) := by
    rcases hit_cases ha2 hσ with hh | ⟨hl, hh⟩
    · unfold farPt; rw [hh, ← t2h]
      rcases t2z with z | z
      · exact Or.inl (J.right_set_subset z)
      · exact Or.inr z
    · have g1 : FreeAt J.left a σ ∧ a.2 ≤ J.left.top.2 := ⟨free_left hf hl, hl⟩
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, -, t1g⟩ := h1.2.1 (hGood1 g1)
      obtain ⟨-, t1z⟩ := winPos t1e t1pp t1pos t1on hay
      unfold farPt; rw [hh, ← t1g g1]
      rcases t1z with z | z
      · exact Or.inl (J.left_set_subset z)
      · exact Or.inr z
  unfold stWin
  -- the selection
  have hsel : IRS P W c₀ winSel c 543 (fun c₁ => c₁.nreg wBit ≤ 1 ∧
      (c₁.nreg wBit = 1 → ∃ τ₁, 0 < τ₁ ∧ OnCB J.left (rayPt a σ τ₁) ∧
        c.nreg (r1F + 1) < (chainModel J.left).W.n ∧
        ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg (r1F + 1), c.nreg (r1F + 2)⟩ ∧
        (chainModel J.left).pos (Qof P) ⟨c.nreg (r1F + 1), c.nreg (r1F + 2)⟩ = rayPt a σ τ₁ ∧
        τ₁ = J.whole.hitParam a σ) ∧
      (c₁.nreg wBit ≠ 1 → τ₂ = J.whole.hitParam a σ) ∧
      EFr (fun r => r = wC1 ∨ r = wC2 ∨ r = wBit) c c₁) := by
    unfold winSel
    refine IRS.ite (fun h => ?_) (fun h => ?_)
    · have hf1 : c.nreg r1F = 1 := by have := h1.1; rw [hK.1] at h; omega
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1abs, t1g⟩ := h1.2.1 hf1
      refine (winCmp_irs (R := J.whole.radius) hI E.hG (by have := E.hWh; unfold hostWords at this; omega) hK hb hB
        t1abs t2abs (by omega)).mono (by norm_num) ?_
      rintro c₁ ⟨w1, w2, w3⟩
      rw [ray_lt_iff hb] at w2
      refine ⟨w1, fun hw => ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, ?_⟩, fun hw => ?_, w3⟩
      · have hlt := w2.1 hw
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h (Or.inl rfl) le_rfl hlt.le
      · have hle : τ₂ ≤ τ₁ := by by_contra hc; exact hw (w2.2 (lt_of_not_ge hc))
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h (Or.inr rfl) hle le_rfl
    · have hf0 : c.nreg r1F ≠ 1 := by rw [hK.1] at h; omega
      refine (set1_irs (v := 0) hI ⟨by unfold wBit sw; omega, by unfold wBit sw; omega⟩
        (Nat.zero_le _)).mono (by norm_num) ?_
      rintro c₁ ⟨w1, w2, w3⟩
      refine ⟨by rw [w1]; norm_num, fun hw => by rw [w1] at hw; exact absurd hw (by norm_num),
        fun _ => win_only2 ha2 hσ hf (fun g => hf0 (hGood1 g)) t2h, ?_⟩
      refine ⟨fun r _ hX _ => w2 r (fun h => hX (Or.inr (Or.inr h))), ?_, fun a _ => by rw [w3]⟩
      rw [w2 _ (by unfold ALLOC wBit sw; omega)]
  refine IRS.seq (K₁ := 543) (K₂ := 25 + 35007) hsel ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - hA₁ ⟨s1, s2, s3, s4⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → r ≠ wBit → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 => s4.1 r (not_oracle_sw h1 h2) (by tauto) (by unfold ALLOC; omega)
  have kreg : ∀ i, i < 3 → c₁.nreg (r1F + i) = c.nreg (r1F + i) ∧
      c₁.nreg (r2F + i) = c.nreg (r2F + i) := fun i hi =>
    ⟨k1 _ (by unfold r1F sw; omega) (by unfold r1F sw; omega) (by unfold r1F wC1 sw; omega)
      (by unfold r1F wC2 sw; omega) (by unfold r1F wBit sw; omega),
     k1 _ (by unfold r2F sw; omega) (by unfold r2F sw; omega) (by unfold r2F wC1 sw; omega)
      (by unfold r2F wC2 sw; omega) (by unfold r2F wBit sw; omega)⟩
  have hyL : |a.2| < J.left.radius := hay
  have hfar : farPt J.whole a σ = rayPt a σ (J.whole.hitParam a σ) := rfl
  have hc1 : c₁.nreg K0 = 0 := by
    rw [k1 _ (by unfold K0 sw; omega) (by unfold K0 sw; omega) (by unfold K0 wC1 sw; omega)
      (by unfold K0 wC2 sw; omega) (by unfold K0 wBit sw; omega)]; exact hK.1
  have hconv := winConv_irs (Z := farPt J.whole a σ) hP hI₁ E.hK (E.fx hI₁)
    (by have := E.hWn; omega)
    (fun hw => by
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1h⟩ := s2 hw
      obtain ⟨t1cl, -⟩ := winPos t1e t1pp t1pos t1on hyL
      rw [(kreg 1 (by norm_num)).1, (kreg 2 (by norm_num)).1]
      exact ⟨t1e, t1pp, t1cl, by rw [t1pos, hfar, t1h]⟩)
    (fun hw => by
      rw [(kreg 1 (by norm_num)).2, (kreg 2 (by norm_num)).2]
      exact ⟨t2e, t2pp, t2cl, by rw [t2pos, hfar, s3 hw]⟩) hc1 s1
  refine IRS.seq (K₁ := 25) (K₂ := 35007) hconv ?_
  rintro c₂ hI₂ - hA₂ ⟨v1, v2, v3, k2, m2⟩
  have hfx₂ := E.fx hI₂
  have kA : c₂.nreg ALLOC = c₁.nreg ALLOC := k2 _ (by unfold CvSet wnE cX cT cDd ALLOC sw; omega)
    (by unfold wnH ALLOC sw; omega)
  have c2NB : c₂.nreg oNB = 1 - b := by
    rw [k2 _ (by unfold CvSet wnE cX cT cDd oNB sw; omega) (by unfold wnH oNB sw; omega),
      k1 _ (by unfold oNB sw; omega) (by unfold oNB sw; omega) (by unfold oNB wC1 sw; omega)
        (by unfold oNB wC2 sw; omega) (by unfold oNB wBit sw; omega), hNB]
  have hyZ : |((chainModel J.whole).pos (Qof P) ⟨c₂.nreg wnE, c₂.nreg wnH⟩).2| < J.whole.radius := by
    rw [v3, hfar, rayPt_snd]; exact hay
  refine (callArr_irs hI₂ hfx₂.ctxW ⟨by unfold sw; omega, by unfold sw; omega,
    by unfold wnE sw; omega, by unfold wnE sw; omega, by unfold wnH sw; omega,
    by unfold wnH sw; omega, by unfold oNB sw; omega, by unfold oNB sw; omega⟩
    ⟨by unfold a1F sw; omega, by unfold a1F sw; omega⟩ v1 v2 hyZ (by omega)).mono le_rfl ?_
  rintro c' ⟨⟨f1, f2, f3⟩, k3, hA3, m3⟩
  rw [v3, c2NB, dirOf_rev' hb, neg_neg] at f2 f3
  have hσ' : -σ = 1 ∨ -σ = -1 := SweepStop.neg_cases hσ
  have hfb := far_free J.whole (le_trans ha2 J.right_top_le) hσ hf
  have hexist := (freeAt_iff_arr J.whole hP hσ' hZ).1 hfb
  rw [neg_neg] at hexist
  have hf1 : c'.nreg a1F = 1 := by
    by_contra hne
    obtain ⟨p, t, hA⟩ := hexist
    exact f3 hne p t hA
  obtain ⟨e1, e2, e3⟩ := f2 hf1
  refine ⟨e1, e2, e3, fun r hr hX hra => ?_, ?_, fun x hx => ?_⟩
  · have hX' : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
      (sw 4047 ≤ r ∧ r ≤ sw 4052) ∨ (sw 4096 ≤ r ∧ r ≤ sw 4097)) := hX
    rw [k3 r hr (by unfold a1F sw at *; omega) (by unfold a1F sw at *; omega)
      (by unfold a1F sw at *; omega) hra,
      k2 r (by unfold CvSet wnE cX cT cDd sw at *; omega) (by unfold wnH sw at *; omega),
      s4.1 r hr (by unfold wC1 wC2 wBit sw at *; omega) hra]
  · have := s4.2.1; omega
  · rw [m3 x (by have := s4.2.1; omega), m2, s4.2.2 x hx]

end

end SweepEv

end Chazelle.Core
