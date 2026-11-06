module

public meta import Chazelle.Arithmetic

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
    grind
  simp_all [rayPt_fst, dirOf_one] 

theorem winCmp_irs (hI : IInv W c₀ c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hK : Consts c)
    {b : ℕ} (hb : b ≤ 1) (hB : c.nreg oB = b) {x₁ x₂ R : ℝ} (h₁ : AbsRec P c (r1F + 3) x₁ R)
    (h₂ : AbsRec P c (r2F + 3) x₂ R) (hroom : c.nreg ALLOC + 600 ≤ W) :
    IRS P W c₀ winCmp c 541 (fun c' => c'.nreg wBit ≤ 1 ∧
      (c'.nreg wBit = 1 ↔ (if b = 1 then x₁ < x₂ else x₂ < x₁)) ∧
      EFr (fun r => r = wC1 ∨ r = wC2 ∨ r = wBit) c c') := by
  unfold winCmp
  refine IRS.seq (K₁ := 269) (K₂ := 272) (callAbsCmp_irs hI hG hW
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf⟩ ⟨by omega_nf, by omega_nf⟩ h₁ h₂
    (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hb1, k1, -, m1⟩
  have kr : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1 r (not_oracle_sw h1 h2) h3 (by omega_nf)
  have h₁' : AbsRec P c₁ (r1F + 3) x₁ R := absRec_transport h₁
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
  have h₂' : AbsRec P c₁ (r2F + 3) x₂ R := absRec_transport h₂
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
    (kr _ (by omega_nf) (by omega_nf) (by omega_nf))
  refine IRS.seq (K₁ := 269) (K₂ := 3) (callAbsCmp_irs hI₁ hG hW
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf⟩ ⟨by omega_nf, by omega_nf⟩ h₂' h₁'
    (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hb2, k2, -, m2⟩
  have kr2 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => (k2 r (not_oracle_sw h1 h2) h4 (by omega_nf)).trans
      (kr r h1 h2 h3)
  have c2B : c₂.nreg oB = b := by
    grind [oB, sw, wC1, wC2]
  have c2K0 : c₂.nreg K0 = 0 := by
    rw [kr2 _ (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf)]; exact hK.1
  have c2C1 : c₂.nreg wC1 = c₁.nreg wC1 :=
    k2 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf)
  have fr : ∀ c', (∀ q, q ≠ wBit → c'.nreg q = c₂.nreg q) →
      c'.nmem = c₂.nmem → EFr (fun r => r = wC1 ∨ r = wC2 ∨ r = wBit) c c' := by
    intro c' hq hm
    grind [Chazelle.Core.SweepEv.EFr, ALLOC, wBit, sw]
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · have hb1' : b = 1 := by omega
    refine (copy1_irs hI₂ ⟨by omega_nf, by omega_nf⟩).mono le_rfl ?_
    rintro c' ⟨a1, a2, a3⟩
    refine ⟨by rw [a1, c2C1]; exact hb1.1, ?_, fr c' a2 a3⟩
    rw [a1, c2C1, ite_eq_left hb1']; exact hb1.2
  · have hb0 : b ≠ 1 := by omega
    refine (copy1_irs hI₂ ⟨by omega_nf, by omega_nf⟩).mono le_rfl ?_
    rintro c' ⟨a1, a2, a3⟩
    refine ⟨by rw [a1]; exact hb2.1, ?_, fr c' a2 a3⟩
    rw [a1, ite_eq_right hb0]; exact hb2.2

/-! ## The selected position -/

theorem dirOf_rev' {b : ℕ} (hb : b ≤ 1) : dirOf (1 - b) = -dirOf b := by
  core_grind

/-- A candidate position: of the class of `convS`, its point on the chain or on a wall. -/
theorem winPos {C : Chain} {Q : Polygon} {n : ℕ} {a : Point} {σ τ : ℝ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hpp : ProperPos (chainModel C) Q n x)
    (hpos : (chainModel C).pos Q x = rayPt a σ τ) (hon : OnCB C (rayPt a σ τ))
    (hy : |a.2| < C.radius) :
    PosClass C Q x ∧ (rayPt a σ τ ∈ C.set ∨
      (|(rayPt a σ τ).1| = C.radius ∧ |(rayPt a σ τ).2| < C.radius)) := by
  have hy' : |((chainModel C).pos Q x).2| < C.radius := by simp_all
  rcases hon with h | h | h
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' (Or.inl ?_), Or.inl h⟩
    rw [hpos]; exact C.snd_le_top_of_mem_set h
  · refine ⟨posClass_of he hpp.1 hpp.2.1 hy' (Or.inr (by simp_all)), Or.inr ⟨h, ?_⟩⟩
    simp_all
  simp_all

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
  · have hw : c.nreg wBit = 1 := by omega
    obtain ⟨a1, a2, a3, a4⟩ := h1 hw
    refine IRS.seq (K₁ := 22) (K₂ := 1) (convL_irs hP hI hK hfx
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf⟩
      ⟨iscr_sw (by omega_nf) (by omega_nf), by omega_nf,
        by omega_nf, by omega_nf⟩ a3 hW) ?_
    rintro c₁ hI₁ - - ⟨v1, v2, v3, k1, m1⟩
    refine (copy1_irs hI₁ ⟨by omega_nf, by omega_nf⟩).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3⟩
    have eE : c'.nreg wnE = c₁.nreg wnE := b2 _ (by omega_nf)
    have eH : c'.nreg wnH = c.nreg (r1F + 2) := by
      rw [b1, k1 _ (by omega_nf)]
    refine ⟨by omega, ?_, by simp_all, fun r hr hr2 => ?_, by rw [b3, m1]⟩
    all_goals (grind [Chazelle.Core.ProperPos])
  · have hw : c.nreg wBit ≠ 1 := by omega
    obtain ⟨a1, a2, a3, a4⟩ := h0 hw
    refine IRS.seq (K₁ := 22) (K₂ := 1) (convR_irs hP hI hK hfx
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf⟩
      ⟨iscr_sw (by omega_nf) (by omega_nf), by omega_nf,
        by omega_nf, by omega_nf⟩ a3 hW) ?_
    rintro c₁ hI₁ - - ⟨v1, v2, v3, k1, m1⟩
    refine (copy1_irs hI₁ ⟨by omega_nf, by omega_nf⟩).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3⟩
    have eE : c'.nreg wnE = c₁.nreg wnE := b2 _ (by omega_nf)
    have eH : c'.nreg wnH = c.nreg (r2F + 2) := by
      grind [CvSet, wnE, cX, cT, cDd, r2F, sw]
    refine ⟨by omega, ?_, by simp_all, fun r hr hr2 => ?_, by rw [b3, m1]⟩
    all_goals (grind [Chazelle.Core.ProperPos])

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
    · have hf1 : c.nreg r1F = 1 := by have := h1.1; omega
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1abs, t1g⟩ := h1.2.1 hf1
      refine (winCmp_irs (R := J.whole.radius) hI E.hG (by have := E.hWh; grind [hostWords]) hK hb hB
        t1abs t2abs (by omega)).mono (by norm_num) ?_
      rintro c₁ ⟨w1, w2, w3⟩
      rw [ray_lt_iff hb] at w2
      refine ⟨w1, fun hw => ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, ?_⟩, fun hw => ?_, w3⟩
      · have hlt := w2.1 hw
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h (Or.inl rfl) le_rfl hlt.le
      · have hle : τ₂ ≤ τ₁ := by grind
        exact win_min ha2 hσ hf t1p t1on t1g t2p t2on t2h (Or.inr rfl) hle le_rfl
    · have hf0 : c.nreg r1F ≠ 1 := by rw [hK.1] at h; omega
      refine (set1_irs (v := 0) hI ⟨by omega_nf, by omega_nf⟩
        (Nat.zero_le _)).mono (by norm_num) ?_
      rintro c₁ ⟨w1, w2, w3⟩
      refine ⟨by omega, fun hw => by omega,
        fun _ => win_only2 ha2 hσ hf (fun g => hf0 (hGood1 g)) t2h, ?_⟩
      grind [Chazelle.Core.SweepEv.EFr, ALLOC, wBit, sw]
  refine IRS.seq (K₁ := 543) (K₂ := 25 + 35007) hsel ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - hA₁ ⟨s1, s2, s3, s4⟩
  have k1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ wC1 → r ≠ wC2 → r ≠ wBit → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 => s4.1 r (not_oracle_sw h1 h2) (by tauto) (by omega_nf)
  have kreg : ∀ i, i < 3 → c₁.nreg (r1F + i) = c.nreg (r1F + i) ∧
      c₁.nreg (r2F + i) = c.nreg (r2F + i) := fun i hi =>
    ⟨k1 _ (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf),
     k1 _ (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf)⟩
  have hyL : |a.2| < J.left.radius := hay
  have hfar : farPt J.whole a σ = rayPt a σ (J.whole.hitParam a σ) := rfl
  have hc1 : c₁.nreg K0 = 0 := by
    rw [k1 _ (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf)]; exact hK.1
  have hconv := winConv_irs (Z := farPt J.whole a σ) hP hI₁ E.hK (E.fx hI₁)
    (by have := E.hWn; omega)
    (fun hw => by
      obtain ⟨τ₁, t1p, t1on, t1e, t1pp, t1pos, t1h⟩ := s2 hw
      obtain ⟨t1cl, -⟩ := winPos t1e t1pp t1pos t1on hyL
      rw [(kreg 1 (by norm_num)).1, (kreg 2 (by norm_num)).1]
      grind)
    (fun hw => by
      rw [(kreg 1 (by norm_num)).2, (kreg 2 (by norm_num)).2]
      grind) hc1 s1
  refine IRS.seq (K₁ := 25) (K₂ := 35007) hconv ?_
  rintro c₂ hI₂ - hA₂ ⟨v1, v2, v3, k2, m2⟩
  have hfx₂ := E.fx hI₂
  have kA : c₂.nreg ALLOC = c₁.nreg ALLOC := k2 _ (by omega_nf)
    (by omega_nf)
  have c2NB : c₂.nreg oNB = 1 - b := by
    rw [k2 _ (by omega_nf) (by omega_nf),
      k1 _ (by omega_nf) (by omega_nf) (by omega_nf)
        (by omega_nf) (by omega_nf), hNB]
  have hyZ : |((chainModel J.whole).pos (Qof P) ⟨c₂.nreg wnE, c₂.nreg wnH⟩).2| < J.whole.radius := by
    grind [rayPt_snd]
  refine (callArr_irs hI₂ hfx₂.ctxW ⟨by omega_nf, by omega_nf,
    by omega_nf, by omega_nf, by omega_nf,
    by omega_nf, by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf⟩ v1 v2 hyZ (by omega)).mono le_rfl ?_
  rintro c' ⟨⟨f1, f2, f3⟩, k3, hA3, m3⟩
  rw [v3, c2NB, dirOf_rev' hb, neg_neg] at f2 f3
  have hσ' : -σ = 1 ∨ -σ = -1 := SweepStop.neg_cases hσ
  have hfb := far_free J.whole (le_trans ha2 J.right_top_le) hσ hf
  have hexist := (freeAt_iff_arr J.whole hP hσ' hZ).1 hfb
  rw [neg_neg] at hexist
  have hf1 : c'.nreg a1F = 1 := by
    by_contra hne
    obtain ⟨p, t, hA⟩ := hexist
    grind
  obtain ⟨e1, e2, e3⟩ := f2 hf1
  refine ⟨e1, e2, e3, fun r hr hX hra => ?_, ?_, fun x hx => ?_⟩
  · have hX' : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
      (sw 4047 ≤ r ∧ r ≤ sw 4052) ∨ (sw 4096 ≤ r ∧ r ≤ sw 4097)) := hX
    rw [k3 r hr (by grind [a1F, sw]) (by grind [a1F, sw])
      (by grind [a1F, sw]) hra,
      k2 r (by unfold CvSet wnE cX cT cDd sw at *; omega) (by grind [wnH, sw]),
      s4.1 r hr (by unfold wC1 wC2 wBit sw at *; omega) hra]
  · have := s4.2.1; omega
  · rw [m3 x (by have := s4.2.1; omega), m2, s4.2.2 x hx]

end

end SweepEv

end Chazelle.Core
