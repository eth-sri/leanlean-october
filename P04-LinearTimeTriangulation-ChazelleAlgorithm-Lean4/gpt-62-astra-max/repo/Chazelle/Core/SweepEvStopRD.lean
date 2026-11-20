module
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address

public import Chazelle.Core.SweepEvStopM4

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
  refine ⟨by rw [hn]; omega, ⟨by rw [hp0], by rw [hp0]; norm_num, Nat.zero_le _⟩,
    Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩), ?_, fun _ => ⟨rfl, by omega,
    by omega⟩, fun h => at_index absurd h⟩
  grind [stOrig, right_v_pos]

theorem orgPos_t (P : Polygon) (N : NF) (k b : ℕ) : OrgPos P J N 2 k b 6 0 := by
  have hn := cm_n J.right
  have h1 := J.right.one_le
  have hp0 : (chainModel J.right).param (Qof P) ⟨6, 0⟩ = 0 := rfl
  refine ⟨by rw [hn]; omega, ⟨by rw [hp0], by rw [hp0]; norm_num, Nat.zero_le _⟩,
    Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩), ?_, fun _ => ⟨rfl, le_rfl,
    by omega⟩, fun h => at_index absurd h⟩
  grind [stOrig, right_top_pos]

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
  grind

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
    guarded iscr_sw
  have sH : IScr (240000 + 4015) := guarded iscr_sw
  have hb' : f 240004 + 3 ≤ W := hb
  have hb2' : m (f 240004 + 3) + 5 * f 244011 + 4 ≤ W := hb2
  have hh' : m (m (f 240004 + 3) + f 244011 + f 244011 + f 244011 + f 244011 + f 244011) + 1 ≤ W := by
    have : m (f 240004 + 3) + f 244011 + f 244011 + f 244011 + f 244011 + f 244011 =
      m (f 240004 + 3) + 5 * f 244011 := by ring
    rw [this]; exact hh
  simp only [ldRd, okB, okI, regI, upd, tX, oKk, tH, tL, tR, oPH, K1, K3, sw]
  grind

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
    exact ⟨guarded iscr_sw,
      ⟨guarded iscr_sw, Nat.zero_le _⟩,
      ⟨guarded iscr_sw, hW⟩, trivial⟩
  · rintro c' rfl
    have g1 := at_index hfx.r40 1
    simp only [cstR, List.getD_cons_zero, List.getD_cons_succ] at g1
    have vE : regB c.nmem ldV c.nreg oPE = 6 + tpos J.right 0 := g1
    have vH : regB c.nmem ldV c.nreg oPH = 0 := rfl
    have vA : regB c.nmem ldV c.nreg oAd = 1 := rfl
    refine ⟨fun q hq => ?_, rfl, by simp only; rw [vA], ⟨fun _ => ⟨by norm_num, hb,
      fun h => at_index absurd h, fun h => at_index absurd h⟩, fun _ => rfl⟩, fun _ => by grind [orgPos_v]⟩
    simp only
    refine regB_other _ _ _ (fun i hi => ?_)
    grind [LdW₀, ldV, List.mem_cons, List.not_mem_nil, dstI]

theorem ldT_irs (hI : IInv W c₀ c) (hO : OrgK P J c) (hK : Consts c) {k b : ℕ} (hb : b ≤ 1)
    (hW : 6 ≤ W) :
    IRS P W c₀ ldT c 7 (LdBr P J N₂ 2 k b c) := by
  unfold ldT
  refine IRS.seq (K₁ := 2) (K₂ := 5) (IRS.block _ hI ?_) ?_
  · simp only [okB, okI]
    exact ⟨⟨guarded iscr_sw, hW⟩,
      ⟨guarded iscr_sw, Nat.zero_le _⟩, trivial⟩
  rintro c₁ hI₁ - - rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.constN oPE 6, .constN oPH 0] c.nreg } with hc₁
  have vE : c₁.nreg oPE = 6 := rfl
  have vH : c₁.nreg oPH = 0 := rfl
  have ko : ∀ q, q ≠ oPE → q ≠ oPH → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    simp only [hc₁, regB, regI, upd, ite_eq_right h1, ite_eq_right h2]
  have k0 : c₁.nreg K0 = 0 := by rw [at_index ko _]; exact hK.1
  have kT : c₁.nreg cTop = J.right.topIdx := by
    rw [at_index ko _]; exact hO.top
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ J.right.topIdx ≠ 0) → ∀ c', c'.nreg oAd = v ∧
      (AgreeExcept [oAd] c'.nreg c₁.nreg) ∧ c'.nmem = c₁.nmem → LdBr P J N₂ 2 k b c c' := by
    rintro v hv hiff c' ⟨a1, a2, a3⟩
    have e1 : c'.nreg oPE = 6 := by rw [at_index a2 _, vE]
    have e2 : c'.nreg oPH = 0 := by rw [at_index a2 _, vH]
    refine ⟨fun q hq => ?_, a3, by rw [a1]; exact hv, ?_, fun _ => by
      grind [orgPos_t]⟩
    · unfold LdW₀ at hq
      rw [a2 q (fun h => hq ((Or.inr (Or.inr (Or.inl h))))),
        ko q (fun h => hq ((Or.inl h))) (fun h => hq ((Or.inr (Or.inl h))))]
    · rw [a1, hiff]
      exact ⟨fun h => ⟨by norm_num, hb, fun h' => at_index absurd h', fun _ => h⟩,
        fun h => h.2.2.2 rfl⟩
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine (guarded (set1_irs (v := 1) hI₁ ⟨by unfold oAd sw; omega, by unfold oAd sw; omega⟩)).mono (by norm_num) (post 1 le_rfl ⟨fun _ => by omega, fun _ => rfl⟩)
  · refine (guarded (set1_irs (v := 0) hI₁ ⟨by unfold oAd sw; omega, by unfold oAd sw; omega⟩)).mono (by norm_num) (post 0 (by norm_num) ⟨fun h => at_index absurd h,
        fun h => absurd (by omega) h⟩)

set_option maxHeartbeats 1000000 in
theorem ldW_irs (hI : IInv W c₀ c) (hK : Consts c) (hP : J.P.Simple)
    (hN : IsNF (chainModel J.right) (Qof P) N₂) {E : ℕ} (hNW : NFWithin c.nmem (c.nreg (sw 4)) E N₂)
    (hEW : E ≤ W) (hPn : P.n ≤ W) {k b : ℕ} (hkk : c.nreg oKk = k) (hk : k < N₂.nChords)
    (hb : b ≤ 1) (hNB : c.nreg oNB = 1 - b) :
    IRS P W c₀ ldW c 21 (LdBr P J N₂ 1 k b c) := by
  obtain ⟨b1, hb2, -⟩ := Restore.nf_bounds hNW
  obtain ⟨hch, -⟩ := hNW.holds.2.2.2.2.2
  obtain ⟨r0, r1, r2, -, -⟩ := hch k hk
  have hhn := (regOf_spec hN).2.2.2.2.2.1 k hk
  have hQn : (Qof P).n = P.n := shear_n _ _
  have k1 : c.nreg K1 = 1 := hK.2.1
  have k3 : c.nreg K3 = 3 := hK.2.2.2.2.2.2
  have k6 : c.nreg K6 = 6 := hK.2.2.1
  unfold ldW
  refine IRS.seq (K₁ := 13) (K₂ := 8) (IRS.block ldRd hI (ldRd_ok c.nmem c.nreg k1 k3
    (by omega) (by rw [hkk]; have := hb2 k hk; omega) (by
      rw [hkk]; unfold NF.nChords at hk; rw [r0]; omega))) ?_
  rintro c₁ hI₁ - - rfl
  obtain ⟨vH, vL, vR, vPH⟩ := ldRd_val c.nmem c.nreg k1 k3
  set c₁ : Config := { c with nreg := regB c.nmem ldRd c.nreg } with hc₁
  rw [hkk] at vH vL vR vPH
  have ko : AgreeExcept [tX, tH, tL, tR, oPH] c₁.nreg c.nreg :=
    fun q a1 a2 a3 a4 a5 => ldRd_other _ _ ⟨a1, a2, a3, a4, a5⟩
  have c1NB : c₁.nreg oNB = 1 - b := by
    rw [at_index ko _]; exact hNB
  have c1K1 : c₁.nreg K1 = 1 := by
    rw [at_index ko _]; exact k1
  have c1K6 : c₁.nreg K6 = 6 := by
    rw [at_index ko _]; exact k6
  have c1PH : c₁.nreg oPH = (endPos N₂ k (1 - b)).hgt := by
    show regB c.nmem ldRd c.nreg oPH = _
    rw [vPH, r0]; unfold endPos; split_ifs <;> rfl
  -- the edge
  have hpick : IRS P W c₀ (.ifLtN oNB K1 (.instr (.copyN oPE tL)) (.instr (.copyN oPE tR))) c₁ 3
      (fun c₂ => c₂.nreg oPE = (endPos N₂ k (1 - b)).edge ∧
        (AgreeExcept [oPE] c₂.nreg c₁.nreg) ∧ c₂.nmem = c₁.nmem) := by
    refine IRS.ite (fun h => ?_) (fun h => ?_)
    · refine (copy1_irs hI₁ ⟨by unfold oPE sw; omega, by unfold oPE sw; omega⟩).mono le_rfl ?_
      rintro c₂ ⟨a1, a2, a3⟩
      refine ⟨?_, a2, a3⟩
      rw [a1]
      show regB c.nmem ldRd c.nreg tL = _
      rw [vL, r1]; unfold endPos; rw [guarded ite_eq_left]; rfl
    · refine (copy1_irs hI₁ ⟨by unfold oPE sw; omega, by unfold oPE sw; omega⟩).mono le_rfl ?_
      rintro c₂ ⟨a1, a2, a3⟩
      refine ⟨?_, a2, a3⟩
      rw [a1]
      show regB c.nmem ldRd c.nreg tR = _
      rw [vR, r2]; unfold endPos; rw [guarded ite_eq_right]; rfl
  refine (IRS.seq (K₁ := 3) (K₂ := 3) hpick ?_).mono (by norm_num) (fun _ h => h)
  rintro c₂ hI₂ - - ⟨e2, k2, m2⟩
  have c2K6 : c₂.nreg K6 = 6 := by rw [at_index k2 _, c1K6]
  have hwp := orgPos_w (P := P) hP hN hk hb
  have post : ∀ v, v ≤ 1 → (v = 1 ↔ (endPos N₂ k (1 - b)).edge < 6) → ∀ c', c'.nreg oAd = v ∧
      (AgreeExcept [oAd] c'.nreg c₂.nreg) ∧ c'.nmem = c₂.nmem → LdBr P J N₂ 1 k b c c' := by
    rintro v hv hiff c' ⟨a1, a2, a3⟩
    have eE : c'.nreg oPE = (endPos N₂ k (1 - b)).edge := by
      rw [at_index a2 _, e2]
    have eH : c'.nreg oPH = (endPos N₂ k (1 - b)).hgt := by
      rw [at_index a2 _, at_index k2 _, c1PH]
    refine ⟨fun q hq => ?_, by rw [a3, m2], by rwa [a1], ?_, fun _ => by
      rwa [eE, eH]⟩
    · unfold LdW₀ at hq
      rw [a2 q (fun h => hq ((Or.inr (Or.inr (Or.inl h))))),
        k2 q (fun h => hq ((Or.inl h))),
        ko q (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by rw [h], by rw [h]; decide⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by rw [h]; decide, by rw [h]; decide⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by rw [h]; decide, by rw [h]; decide⟩)))))
          (fun h => hq ((Or.inr (Or.inr (Or.inr ⟨by rw [h]; decide, by rw [h]⟩)))))
          (fun h => hq ((Or.inr (Or.inl h))))]
    · rw [a1, hiff]
      exact ⟨fun h => ⟨by norm_num, hb, fun _ => ⟨hk, h⟩, fun h' => at_index absurd h'⟩,
        fun h => (h.2.2.1 rfl).2⟩
  refine IRS.ite (fun h => ?_) (fun h => ?_)
  · refine (guarded (set1_irs (v := 1) hI₂ ⟨by decide, by decide⟩)).mono le_rfl (post 1 le_rfl ⟨fun _ => by rw [← e2]; omega, fun _ => rfl⟩)
  · refine (guarded (set1_irs (v := 0) hI₂ ⟨by unfold oAd sw; omega, by decide⟩)).mono le_rfl (post 0 (by norm_num) ⟨fun h => at_index absurd h,
        fun h' => absurd (by grind) h⟩)

/-- **The origin of a code** as a run step. -/
theorem stLoad_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hkd : c.nreg oKd ≤ 2) (hb : c.nreg oB ≤ 1) (hk : c.nreg oKd = 1 → c.nreg oKk < N₂.nChords)
    (hroom : c.nreg ALLOC + 30 ≤ W) :
    IRS P W c₀ stLoad c 30 (fun c' => LdOK P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧
      EFr LdW c c') := by
  have k1 := (E.hK.fix hI).2.1
  unfold stLoad
  refine IRS.seq (K₁ := 1) (K₂ := 29) (IRS.instr1 hI
    (guarded iscr_sw)) ?_
  rintro c₁ hI₁ - hA₁ rfl
  set c₁ : Config := { c with nreg := regI c.nmem (.subN oNB K1 oB) c.nreg } with hc₁
  have vNB : c₁.nreg oNB = 1 - c.nreg oB := by simp [hc₁, regI, upd, k1]
  have ko : ∀ q, q ≠ oNB → c₁.nreg q = c.nreg q := fun q hq => by simp [hc₁, regI, upd, hq]
  have kKd : c₁.nreg oKd = c.nreg oKd := at_index ko _
  have kK1 := (at_index ko _).trans k1
  have post : ∀ kind, kind = c.nreg oKd → ∀ c', LdBr P J N₂ kind (c.nreg oKk) (c.nreg oB) c₁ c' →
      LdOK P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr LdW c c' := by
    rintro kind rfl c' ⟨a1, a2, a3, a4, a5⟩
    have hA : c'.nreg ALLOC = c.nreg ALLOC := by
      rw [at_index a1 _, at_index ko _]
    refine ⟨⟨by rw [(at_index a1 _), vNB], a3, a4, a5⟩, fun r _ h2 _ => ?_, by simp_all, fun a _ => by simp_all⟩
    rw [a1 r (fun h => h2 (Or.inr h)), ko r (fun h => h2 (Or.inl h))]
  refine IRS.ite (fun h0 => ?_) (fun h0 => ?_)
  · have hk0 : c.nreg oKd = 0 := by rw [kKd, kK1] at h0; omega
    refine (guarded (ldV_irs (N₂ := N₂) (k := c.nreg oKk) hI₁ (E.fx hI₁) hb)).mono (by norm_num)
      (post 0 hk0.symm)
  refine IRS.ite (fun h2 => ?_) (fun h2 => ?_)
  · have hk2 : c.nreg oKd = 2 := by rw [kKd, kK1] at h2; omega
    refine (guarded (ldT_irs (N₂ := N₂) (k := c.nreg oKk) hI₁ (E.hO.fix hI₁) (E.hK.fix hI₁) hb)).mono (by norm_num) (post 2 hk2.symm)
  · have hk1 : c.nreg oKd = 1 := by rw [kKd, kK1] at h0 h2; omega
    have hNW : NFWithin c₁.nmem (c₁.nreg (sw 4)) (c₀.nreg ALLOC) N₂ := by
      rw [(at_index hI₁.hin _)]
      exact E.hNW₂.transport hI₁.hm
    refine (ldW_irs hI₁ (E.hK.fix hI₁) E.hP E.hNF₂ hNW (by have := hI₁.hA; omega)
      (by grind [hostWords, E.hWh]) (at_index ko _) (hk hk1) hb vNB).mono (by norm_num) (post 1 hk1.symm)

end

end SweepEv

end Chazelle.Core
