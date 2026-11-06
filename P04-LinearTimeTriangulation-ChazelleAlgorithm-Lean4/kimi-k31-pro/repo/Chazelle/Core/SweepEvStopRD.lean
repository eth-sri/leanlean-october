module

public import Chazelle.Core.SweepEvStopM4
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 1000000

/-!
# The sweep (WP-D), stage 2: the origin of a code (RAM)

`stLoad`: from the code `(oKd, oKk, oB)`, the reversed code `oNB = 1 - oB`, the admissibility flag
`oAd` (`StOK`) and, for an admissible code, the position `(oPE, oPH)` of its origin in the walk of
`C₂` (`OrgPos`): `(6 + tpos C₂ 0, 0)` for the shared vertex, `(6, 0)` for the top of `C₂`, the end
`1 - b` of the chord `k` of `N₂` for a wall end (`stLoad_irs`).
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

def oAd : ℕ := sw 4019
def tX : ℕ := sw 4092
def tH : ℕ := sw 4093
def tL : ℕ := sw 4094
def tR : ℕ := sw 4095

/-- **The position of the origin** of the code `(kind, k, b)` in the walk of `C₂`. -/
def OrgPos (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b e h : ℕ) : Prop :=
  e < (chainModel J.right).W.n ∧ ProperPos (chainModel J.right) (Qof P) P.n ⟨e, h⟩ ∧
    PosClass J.right (Qof P) ⟨e, h⟩ ∧
    (chainModel J.right).pos (Qof P) ⟨e, h⟩ = stOrig J (Qof P) N kind k b ∧
    (kind ≠ 1 → h = 0 ∧ 6 ≤ e ∧ e < 2 * J.right.m + 6) ∧
    (kind = 1 → (⟨e, h⟩ : WPos) = endPos N k (1 - b))

/-- The post of `stLoad`. -/
def LdOK (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c : Config) : Prop :=
  c.nreg oNB = 1 - b ∧ c.nreg oAd ≤ 1 ∧ (c.nreg oAd = 1 ↔ StOK P J N kind k b) ∧
    (c.nreg oAd = 1 → OrgPos P J N kind k b (c.nreg oPE) (c.nreg oPH))

/-- The registers the branches of `stLoad` write. -/
def LdW₀ (r : ℕ) : Prop := r = oPE ∨ r = oPH ∨ r = oAd ∨ (tX ≤ r ∧ r ≤ tR)

/-- The registers `stLoad` writes. -/
def LdW (r : ℕ) : Prop := r = oNB ∨ LdW₀ r

/-! ## The program -/

def ldV : List Instr := [.copyN oPE (sw 41), .constN oPH 0, .constN oAd 1]

def ldT : Stmt :=
  .seq (block [.constN oPE 6, .constN oPH 0])
    (.ifLtN K0 cTop (.instr (.constN oAd 1)) (.instr (.constN oAd 0)))

def ldRd : List Instr :=
  [.addN tX (sw 4) K3, .loadN tX tX, .addN tX tX oKk, .addN tX tX oKk, .addN tX tX oKk,
    .addN tX tX oKk, .addN tX tX oKk, .loadN tH tX, .addN tX tX K1, .loadN tL tX,
    .addN tX tX K1, .loadN tR tX, .addN oPH tH K1]

def ldW : Stmt :=
  .seq (block ldRd) (.seq (.ifLtN oNB K1 (.instr (.copyN oPE tL)) (.instr (.copyN oPE tR)))
    (.ifLtN oPE K6 (.instr (.constN oAd 1)) (.instr (.constN oAd 0))))

/-- **The origin of a code.** -/
def stLoad : Stmt :=
  .seq (.instr (.subN oNB K1 oB)) (.ifLtN oKd K1 (block ldV) (.ifLtN K1 oKd ldT ldW))

/-! ## A one-register assignment -/

theorem set1_irs (hI : IInv W c₀ c) {r v : ℕ} (hr : 240700 ≤ r ∧ r < 250000) (hv : v ≤ W) :
    IRS P W c₀ (.instr (.constN r v)) c 1 (fun c' => c'.nreg r = v ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN r v) hI ⟨iscr_sw hr.1 hr.2, hv⟩).mono le_rfl ?_
  rintro c' rfl
  refine ⟨by simp [regI, upd], fun q hq => by simp [regI, upd, hq], rfl⟩

theorem copy1_irs (hI : IInv W c₀ c) {r a : ℕ} (hr : 240700 ≤ r ∧ r < 250000) :
    IRS P W c₀ (.instr (.copyN r a)) c 1 (fun c' => c'.nreg r = c.nreg a ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .copyN r a) hI (iscr_sw hr.1 hr.2)).mono le_rfl ?_
  rintro c' rfl
  refine ⟨by simp [regI, upd], fun q hq => by simp [regI, upd, hq], rfl⟩

/-! ## The branches -/

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

theorem orgPos_v (P : Polygon) (N : NF) (k b : ℕ) :
    OrgPos P J N 0 k b (6 + tpos J.right 0) 0 := by
  have hτ := tpos_lt J.right 0
  have hn := cm_n J.right
  have hp0 : (chainModel J.right).param (Qof P) ⟨6 + tpos J.right 0, 0⟩ = 0 := rfl
  refine ⟨by rwo [hn], ⟨by rw [hp0], by rwn [hp0], Nat.zero_le _⟩,
    Or.inr (Or.inl ⟨by sio only, by sio only⟩), ?_, fun _ => ⟨rfl, by omega,
    by omega⟩, fun h => absurd h (by norm_num)⟩
  rw [right_v_pos]; unfold stOrig; rw [ite_eq_left rfl]

theorem orgPos_t (P : Polygon) (N : NF) (k b : ℕ) : OrgPos P J N 2 k b 6 0 := by
  have hn := cm_n J.right
  have h1 := J.right.one_le
  have hp0 : (chainModel J.right).param (Qof P) ⟨6, 0⟩ = 0 := rfl
  refine ⟨by rwo [hn], ⟨by rw [hp0], by rwn [hp0], Nat.zero_le _⟩,
    Or.inr (Or.inl ⟨by sio only, by sio only⟩), ?_, fun _ => ⟨rfl, le_rfl,
    by omega⟩, fun h => absurd h (by norm_num)⟩
  rw [right_top_pos]; unfold stOrig; rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]

theorem orgPos_w (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂) {k b : ℕ}
    (hk : k < N₂.nChords) (hb : b ≤ 1) :
    OrgPos P J N₂ 1 k b (endPos N₂ k (1 - b)).edge (endPos N₂ k (1 - b)).hgt := by
  obtain ⟨hcl, -⟩ := end_off_iff hP hN hk (s := 1 - b)
  have hA := endPos_attach hN hk (1 - b)
  have hhn := (regOf_spec hN).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  refine ⟨hA.1, ⟨hA.2.1, hA.2.2.1, ?_⟩, hcl, ?_, fun h => absurd rfl h, fun _ => rfl⟩
  · unfold endPos; split_ifs <;> show (N₂.chord k).h + 1 ≤ P.n <;> omega
  · exact (stOrig_wall hN hk hb).1.symm

/-! ## The read of the chord record -/

theorem ldRd_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) :
    regB m ldRd f tH = m (m (f (sw 4) + 3) + 5 * f oKk) ∧
    regB m ldRd f tL = m (m (f (sw 4) + 3) + 5 * f oKk + 1) ∧
    regB m ldRd f tR = m (m (f (sw 4) + 3) + 5 * f oKk + 2) ∧
    regB m ldRd f oPH = m (m (f (sw 4) + 3) + 5 * f oKk) + 1 := by
  have e1 : f 240611 = 1 := hk1
  have e3 : f 240616 = 3 := hk3
  simp only [ldRd, regB, regI, upd, tX, oKk, tH, tL, tR, oPH, K1, K3, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e3]
  refine ⟨congrArg m (by ring), congrArg m (by ring), congrArg m (by ring), congrArg m (by ring)⟩

theorem ldRd_other (m f : ℕ → ℕ) {q : ℕ} (h : q ≠ tX ∧ q ≠ tH ∧ q ≠ tL ∧ q ≠ tR ∧ q ≠ oPH) :
    regB m ldRd f q = f q :=
  regB_other m ldRd f (fun i hi => by
    simp only [ldRd, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro he <;> subst he <;> simp at h)

theorem ldRd_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hk3 : f K3 = 3) (hb : f (sw 4) + 3 ≤ W)
    (hb2 : m (f (sw 4) + 3) + 5 * f oKk + 4 ≤ W) (hh : m (m (f (sw 4) + 3) + 5 * f oKk) + 1 ≤ W) :
    okB W m ldRd f := by
  have e1 : f 240611 = 1 := hk1
  have e3 : f 240616 = 3 := hk3
  have s : ∀ j, 4092 ≤ j → j ≤ 4095 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  have sH : IScr (240000 + 4015) := iscr_sw (by omega) (by omega)
  have hb' : f 240004 + 3 ≤ W := hb
  have hb2' : m (f 240004 + 3) + 5 * f 244011 + 4 ≤ W := hb2
  have hh' : m (m (f 240004 + 3) + f 244011 + f 244011 + f 244011 + f 244011 + f 244011) + 1 ≤ W := by
    have : m (f 240004 + 3) + f 244011 + f 244011 + f 244011 + f 244011 + f 244011 =
      m (f 240004 + 3) + 5 * f 244011 := by ring
    rwx [this]
  simp only [ldRd, okB, okI, regI, upd, tX, oKk, tH, tL, tR, oPH, K1, K3, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e3]
  refine ⟨⟨s 4092 (by norm_num) (by norm_num), by omega⟩, s 4092 (by norm_num) (by norm_num),
    ⟨s 4092 (by norm_num) (by norm_num), by omega⟩, ⟨s 4092 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 4092 (by norm_num) (by norm_num), by omega⟩, ⟨s 4092 (by norm_num) (by norm_num), by omega⟩,
    ⟨s 4092 (by norm_num) (by norm_num), by omega⟩, s 4093 (by norm_num) (by norm_num),
    ⟨s 4092 (by norm_num) (by norm_num), by omega⟩, s 4094 (by norm_num) (by norm_num),
    ⟨s 4092 (by norm_num) (by norm_num), by omega⟩, s 4095 (by norm_num) (by norm_num),
    ⟨sH, by omega⟩, trivial⟩

/-! ## The main lemma -/

/-- The post of a branch of `stLoad`. -/
def LdBr (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c₁ c' : Config) : Prop :=
  (∀ q, ¬ LdW₀ q → c'.nreg q = c₁.nreg q) ∧ c'.nmem = c₁.nmem ∧ c'.nreg oAd ≤ 1 ∧
    (c'.nreg oAd = 1 ↔ StOK P J N kind k b) ∧
    (c'.nreg oAd = 1 → OrgPos P J N kind k b (c'.nreg oPE) (c'.nreg oPH))

theorem ldV_irs (hI : IInv W c₀ c) (hfx : Fx P W J c) {k b : ℕ} (hb : b ≤ 1) (hW : 1 ≤ W) :
    IRS P W c₀ (block ldV) c 3 (LdBr P J N₂ 0 k b c) := by
  refine (IRS.block ldV hI ?_).mono (by simp [ldV]) ?_
  · simp only [ldV, okB, okI]
    exact ⟨iscr_sw (by ufo oPE sw) (by ufo oPE sw),
      ⟨iscr_sw (by ufo oPH sw) (by ufo oPH sw), Nat.zero_le _⟩,
      ⟨iscr_sw (by ufo oAd sw) (by ufo oAd sw), hW⟩, trivial⟩
  · rintro c' rfl
    have g1 := hfx.r40 1 (by norm_num)
    simp only [cstR, List.getD_cons_zero, List.getD_cons_succ] at g1
    have vE : regB c.nmem ldV c.nreg oPE = 6 + tpos J.right 0 := by
      simp only [ldV, regB, regI, upd, oPE, oPH, oAd, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
      exact g1
    have vH : regB c.nmem ldV c.nreg oPH = 0 := by
      simp only [ldV, regB, regI, upd, oPE, oPH, oAd, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
    have vA : regB c.nmem ldV c.nreg oAd = 1 := by
      simp only [ldV, regB, regI, upd, oPE, oPH, oAd, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
    refine ⟨fun q hq => ?_, rfl, by simp only; rw [vA], ⟨fun _ => ⟨by norm_num, hb,
      fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩, fun _ => by
        simp only; rw [vA]⟩, fun _ => by simp only; rw [vE, vH]; exact orgPos_v P N₂ k b⟩
    simp only
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [ldV, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold LdW₀ at hq
    rcases hi with rfl | rfl | rfl <;> simp only [dstI] <;> intro he <;> subst he <;> tauto

theorem ldT_irs (hI : IInv W c₀ c) (hO : OrgK P J c) (hK : Consts c) {k b : ℕ} (hb : b ≤ 1)
    (hW : 6 ≤ W) :
    IRS P W c₀ ldT c 7 (LdBr P J N₂ 2 k b c) := by
  unfold ldT
  refine IRS.seq (K₁ := 2) (K₂ := 5) (IRS.block _ hI ?_) ?_
  · simp only [okB, okI]
    exact ⟨⟨iscr_sw (by ufo oPE sw) (by ufo oPE sw), hW⟩,
      ⟨iscr_sw (by ufo oPH sw) (by ufo oPH sw), Nat.zero_le _⟩, trivial⟩
  rintro c₁ hI₁ - - rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.constN oPE 6, .constN oPH 0] c.nreg } with hc₁
  have vE : c₁.nreg oPE = 6 := by
    simp only [hc₁, regB, regI, upd, oPE, oPH, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  have vH : c₁.nreg oPH = 0 := by
    simp only [hc₁, regB, regI, upd, oPE, oPH, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  have ko : ∀ q, q ≠ oPE → q ≠ oPH → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    simp only [hc₁, regB, regI, upd, ite_eq_right h1, ite_eq_right h2]
  have k0 : c₁.nreg K0 = 0 := by rw [ko _ (by ufo K0 oPE sw) (by ufo K0 oPH sw)]; exact hK.1
  have kT : c₁.nreg cTop = J.right.topIdx := by
    rw [ko _ (by ufo cTop oPE sw) (by ufo cTop oPH sw)]; exact hO.top
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ J.right.topIdx ≠ 0) → ∀ c', c'.nreg oAd = v ∧
      (∀ q, q ≠ oAd → c'.nreg q = c₁.nreg q) ∧ c'.nmem = c₁.nmem → LdBr P J N₂ 2 k b c c' := by
    rintro v hv hiff c' ⟨a1, a2, a3⟩
    have e1 : c'.nreg oPE = 6 := by rw [a2 _ (by ufo oPE oAd sw), vE]
    have e2 : c'.nreg oPH = 0 := by rw [a2 _ (by ufo oPH oAd sw), vH]
    refine ⟨fun q hq => ?_, a3, by rwx [a1], ?_, fun _ => by
      rw [e1, e2]; exact orgPos_t P N₂ k b⟩
    · unfold LdW₀ at hq
      rw [a2 q (fun h => hq ((Or.inr (Or.inr (Or.inl h))))),
        ko q (fun h => hq ((Or.inl h))) (fun h => hq ((Or.inr (Or.inl h))))]
    · rw [a1, hiff]
      exact ⟨fun h => ⟨by norm_num, hb, fun h' => absurd h' (by norm_num), fun _ => h⟩,
        fun h => h.2.2.2 rfl⟩
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine (set1_irs (v := 1) hI₁ ⟨by ufo oAd sw, by ufo oAd sw⟩
      (by omega)).mono (by norm_num) (post 1 le_rfl ⟨fun _ => by omega, fun _ => rfl⟩)
  · refine (set1_irs (v := 0) hI₁ ⟨by ufo oAd sw, by ufo oAd sw⟩
      (by omega)).mono (by norm_num) (post 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
        fun h => absurd (by omega) h⟩)

theorem ldW_irs (hI : IInv W c₀ c) (hK : Consts c) (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N₂) {E : ℕ} (hNW : NFWithin c.nmem (c.nreg (sw 4)) E N₂)
    (hEW : E ≤ W) (hPn : P.n ≤ W) {k b : ℕ} (hkk : c.nreg oKk = k) (hk : k < N₂.nChords)
    (hb : b ≤ 1) (hNB : c.nreg oNB = 1 - b) :
    IRS P W c₀ ldW c 21 (LdBr P J N₂ 1 k b c) := by
  obtain ⟨b1, hb2, -⟩ := Restore.nf_bounds hNW
  have hNA : NFAt c.nmem (c.nreg (sw 4)) N₂ := hNW.holds
  obtain ⟨hch, -⟩ := hNA.2.2.2.2.2
  obtain ⟨r0, r1, r2, -, -⟩ := hch k hk
  have hhn := (regOf_spec hN).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  have k1 : c.nreg K1 = 1 := hK.2.1
  have k3 : c.nreg K3 = 3 := hK.2.2.2.2.2.2
  have k6 : c.nreg K6 = 6 := hK.2.2.1
  unfold ldW
  refine IRS.seq (K₁ := 13) (K₂ := 8) (IRS.block ldRd hI (ldRd_ok c.nmem c.nreg k1 k3
    (by omega) (by rw [hkk]; have := hb2 k hk; omega) (by
      rw [hkk]; unfold NF.nChords at hk; rwo [r0]))) ?_
  rintro c₁ hI₁ - - rfl
  obtain ⟨vH, vL, vR, vPH⟩ := ldRd_val c.nmem c.nreg k1 k3
  set c₁ : Config := { c with nreg := regB c.nmem ldRd c.nreg } with hc₁
  rw [hkk] at vH vL vR vPH
  have ko : ∀ q, q ≠ tX → q ≠ tH → q ≠ tL → q ≠ tR → q ≠ oPH → c₁.nreg q = c.nreg q :=
    fun q a1 a2 a3 a4 a5 => ldRd_other _ _ ⟨a1, a2, a3, a4, a5⟩
  have c1NB : c₁.nreg oNB = 1 - b := by
    rw [ko _ (by ufo oNB tX sw) (by ufo oNB tH sw) (by ufo oNB tL sw)
      (by ufo oNB tR sw) (by ufo oNB oPH sw)]; exact hNB
  have c1K1 : c₁.nreg K1 = 1 := by
    rw [ko _ (by ufo K1 tX sw) (by ufo K1 tH sw) (by ufo K1 tL sw)
      (by ufo K1 tR sw) (by ufo K1 oPH sw)]; exact k1
  have c1K6 : c₁.nreg K6 = 6 := by
    rw [ko _ (by ufo K6 tX sw) (by ufo K6 tH sw) (by ufo K6 tL sw)
      (by ufo K6 tR sw) (by ufo K6 oPH sw)]; exact k6
  have c1PH : c₁.nreg oPH = (endPos N₂ k (1 - b)).hgt := by
    show regB c.nmem ldRd c.nreg oPH = _
    rw [vPH, r0]; unfold endPos; split_ifs <;> rfl
  -- the edge
  have hpick : IRS P W c₀ (.ifLtN oNB K1 (.instr (.copyN oPE tL)) (.instr (.copyN oPE tR))) c₁ 3
      (fun c₂ => c₂.nreg oPE = (endPos N₂ k (1 - b)).edge ∧
        (∀ q, q ≠ oPE → c₂.nreg q = c₁.nreg q) ∧ c₂.nmem = c₁.nmem) := by
    refine IRS.ite (fun h => ?_) (fun h => ?_)
    · refine (copy1_irs hI₁ ⟨by ufo oPE sw, by ufo oPE sw⟩).mono le_rfl ?_
      rintro c₂ ⟨a1, a2, a3⟩
      refine ⟨?_, a2, a3⟩
      rw [a1]
      show regB c.nmem ldRd c.nreg tL = _
      rw [vL, r1]; urr endPos [ite_eq_left (by omega)]
    · refine (copy1_irs hI₁ ⟨by ufo oPE sw, by ufo oPE sw⟩).mono le_rfl ?_
      rintro c₂ ⟨a1, a2, a3⟩
      refine ⟨?_, a2, a3⟩
      rw [a1]
      show regB c.nmem ldRd c.nreg tR = _
      rw [vR, r2]; urr endPos [ite_eq_right (by omega)]
  refine (IRS.seq (K₁ := 3) (K₂ := 3) hpick ?_).mono (by norm_num) (fun _ => id)
  rintro c₂ hI₂ - - ⟨e2, k2, m2⟩
  have c2K6 : c₂.nreg K6 = 6 := by rw [k2 _ (by ufo K6 oPE sw), c1K6]
  have hwp := orgPos_w (P := P) hP hN hk hb
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ (endPos N₂ k (1 - b)).edge < 6) → ∀ c', c'.nreg oAd = v ∧
      (∀ q, q ≠ oAd → c'.nreg q = c₂.nreg q) ∧ c'.nmem = c₂.nmem → LdBr P J N₂ 1 k b c c' := by
    rintro v hv hiff c' ⟨a1, a2, a3⟩
    have eE : c'.nreg oPE = (endPos N₂ k (1 - b)).edge := by
      rw [a2 _ (by ufo oPE oAd sw), e2]
    have eH : c'.nreg oPH = (endPos N₂ k (1 - b)).hgt := by
      rw [a2 _ (by ufo oPH oAd sw), k2 _ (by ufo oPH oPE sw), c1PH]
    refine ⟨fun q hq => ?_, by rw [a3, m2], by rwx [a1], ?_, fun _ => by
      rwx [eE, eH]⟩
    · unfold LdW₀ at hq
      rw [a2 q (fun h => hq ((Or.inr (Or.inr (Or.inl h))))),
        k2 q (fun h => hq ((Or.inl h))),
        ko q (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by rw [h], by ruo [h] tX tR sw⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by ruo [h] tX tH sw, by ruo [h] tH tR sw⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by ruo [h] tX tL sw, by ruo [h] tL tR sw⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by ruo [h] tX tR sw, by rw [h]⟩)))))
          (fun h => hq ((Or.inr (Or.inl h))))]
    · rw [a1, hiff]
      exact ⟨fun h => ⟨by norm_num, hb, fun _ => ⟨hk, h⟩, fun h' => absurd h' (by norm_num)⟩,
        fun h => (h.2.2.1 rfl).2⟩
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine (set1_irs (v := 1) hI₂ ⟨by ufo oAd sw, by ufo oAd sw⟩
      (by omega)).mono le_rfl (post 1 le_rfl ⟨fun _ => by rwo [← e2], fun _ => rfl⟩)
  · refine (set1_irs (v := 0) hI₂ ⟨by ufo oAd sw, by ufo oAd sw⟩
      (by omega)).mono le_rfl (post 0 (by norm_num) ⟨fun h => absurd h (by norm_num),
        fun h' => absurd (by rwx [c2K6, e2]) h⟩)

/-- **The origin of a code** as a run step. -/
theorem stLoad_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hkd : c.nreg oKd ≤ 2) (hb : c.nreg oB ≤ 1) (hk : c.nreg oKd = 1 → c.nreg oKk < N₂.nChords)
    (hroom : c.nreg ALLOC + 30 ≤ W) :
    IRS P W c₀ stLoad c 30 (fun c' => LdOK P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧
      EFr LdW c c') := by
  have hK := E.hK.fix hI
  have k1  := hK.2.1
  unfold stLoad
  refine IRS.seq (K₁ := 1) (K₂ := 29) (IRS.instr1 (i := .subN oNB K1 oB) hI
    (iscr_sw (by ufo oNB sw) (by ufo oNB sw))) ?_
  rintro c₁ hI₁ - hA₁ rfl
  set c₁ : Config := { c with nreg := regI c.nmem (.subN oNB K1 oB) c.nreg } with hc₁
  have vNB : c₁.nreg oNB = 1 - c.nreg oB := by simp [hc₁, regI, upd, k1]
  have ko : ∀ q, q ≠ oNB → c₁.nreg q = c.nreg q := fun q hq => by simp [hc₁, regI, upd, hq]
  have kKd : c₁.nreg oKd = c.nreg oKd := ko _ (by ufo oKd oNB sw)
  have kKk : c₁.nreg oKk = c.nreg oKk := ko _ (by ufo oKk oNB sw)
  have kK1 : c₁.nreg K1 = 1 := (ko _ (by ufo K1 oNB sw)).trans k1
  have hW  := hroom
  have post : ∀ kind, kind = c.nreg oKd → ∀ c', LdBr P J N₂ kind (c.nreg oKk) (c.nreg oB) c₁ c' →
      LdOK P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr LdW c c' := by
    rintro kind rfl c' ⟨a1, a2, a3, a4, a5⟩
    have hnb : c'.nreg oNB = c₁.nreg oNB := a1 _ (by ufo LdW₀ oNB oPE oPH oAd tX tR sw)
    have hA : c'.nreg ALLOC = c.nreg ALLOC := by
      rw [a1 _ (by ufo LdW₀ ALLOC oPE oPH oAd tX tR sw), ko _ (by ufo ALLOC oNB sw)]
    refine ⟨⟨by rw [hnb, vNB], a3, a4, a5⟩, fun r _ h2 _ => ?_, by rw [hA], fun a _ => by rw [a2]⟩
    unfold LdW at h2
    rw [a1 r (fun h => h2 (Or.inr h)), ko r (fun h => h2 (Or.inl h))]
  refine IRS.ite (fun h0 => ?_) (fun h0 => ?_)
  · have hk0 : c.nreg oKd = 0 := by rwo [kKd, kK1] at h0
    refine (ldV_irs (N₂ := N₂) (k := c.nreg oKk) hI₁ (E.fx hI₁) hb (by omega)).mono (by norm_num)
      (post 0 hk0.symm)
  refine IRS.ite (fun h2 => ?_) (fun h2 => ?_)
  · have hk2 : c.nreg oKd = 2 := by rwo [kKd, kK1] at h2
    refine (ldT_irs (N₂ := N₂) (k := c.nreg oKk) hI₁ (E.hO.fix hI₁) (E.hK.fix hI₁) hb
      (by omega)).mono (by norm_num) (post 2 hk2.symm)
  · have hk1 : c.nreg oKd = 1 := by rwo [kKd, kK1] at h0 h2
    have hNW : NFWithin c₁.nmem (c₁.nreg (sw 4)) (c₀.nreg ALLOC) N₂ := by
      have h4 : c₁.nreg (sw 4) = c₀.nreg (sw 4) := hI₁.hin _ (by ufo IFix sw)
      rw [h4]
      exact E.hNW₂.transport hI₁.hm
    have hPn : P.n ≤ W := by have := E.hWh; ufo hostWords at this
    refine (ldW_irs (b := c.nreg oB) hI₁ (E.hK.fix hI₁) E.hP E.hNF₂ hNW (by have := hI₁.hA; omega)
      hPn kKk (hk hk1) hb vNB).mono (by norm_num) (post 1 hk1.symm)

end

end SweepEv

end Chazelle.Core
