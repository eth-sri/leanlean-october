module

meta import Chazelle.Programs.RegisterGuard

meta import Chazelle.Programs.RamEval

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepEvWinM

/-!
# The sweep (WP-D), stage 3: the window of the event loop (RAM, part 1)

Registers `sw 3000 …` of the window, single-instruction run steps (`win_irs_add`, …, `win_Upd`), the key
read in the walk of `C₁` (`wKeyS`), the arc at a spine position (`arcS`) and the decision of the
window end (`decS`, `DecOut`).
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

/-! ## Registers -/

@[ram_layout] def wD : ℕ := sw 3000
@[ram_layout] def wE1 : ℕ := sw 3001
@[ram_layout] def wO : ℕ := sw 3002
@[ram_layout] def wT : ℕ := sw 3003
@[ram_layout] def wA : ℕ := sw 3004
@[ram_layout] def wR : ℕ := sw 3005
@[ram_layout] def wEE : ℕ := sw 3006
@[ram_layout] def wEH : ℕ := sw 3007
@[ram_layout] def wL : ℕ := sw 3008
@[ram_layout] def wC : ℕ := sw 3010
@[ram_layout] def wCh : ℕ := sw 3012
@[ram_layout] def wDE : ℕ := sw 3013
@[ram_layout] def wPs : ℕ := sw 3014

/-! ## Single instructions -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- One register update. -/
def win_Upd (c c' : Config) (r v : ℕ) : Prop :=
  c'.nreg r = v ∧ (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem

theorem win_upd_of_eq {c' : Config} {r v : ℕ} (h : c' = { c with nreg := upd c.nreg r v }) :
    win_Upd c c' r v := by
  subst h; exact ⟨by simp, fun q hq => by simp [upd_other _ _ _ hq], rfl⟩

theorem win_irs_add {r a b : ℕ} (hI : IInv W c₀ c) (hr : IScr r) (hw : c.nreg a + c.nreg b ≤ W) :
    IRS P W c₀ (.instr (.addN r a b)) c 1 (fun c' => win_Upd c c' r (c.nreg a + c.nreg b)) :=
  (IRS.reg hI hr (Exec.addN hI.hw r a b hw)).mono le_rfl fun _ h => win_upd_of_eq h

theorem win_irs_sub {r a b : ℕ} (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ (.instr (.subN r a b)) c 1 (fun c' => win_Upd c c' r (c.nreg a - c.nreg b)) :=
  (IRS.reg hI hr (Exec.subN hI.hw r a b)).mono le_rfl fun _ h => win_upd_of_eq h

theorem win_irs_copy {r a : ℕ} (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ (.instr (.copyN r a)) c 1 (fun c' => win_Upd c c' r (c.nreg a)) :=
  (IRS.reg hI hr (Exec.copyN hI.hw r a)).mono le_rfl fun _ h => win_upd_of_eq h

theorem win_irs_load {r a : ℕ} (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ (.instr (.loadN r a)) c 1 (fun c' => win_Upd c c' r (c.nmem (c.nreg a))) :=
  (IRS.reg hI hr (Exec.loadN hI.hw r a)).mono le_rfl fun _ h => win_upd_of_eq h

theorem win_irs_const' {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r) (hv : v ≤ W) :
    IRS P W c₀ (.instr (.constN r v)) c 1 (fun c' => win_Upd c c' r v) :=
  (IRS.reg hI hr (Exec.constN hI.hw r v hv)).mono le_rfl fun _ h => win_upd_of_eq h

theorem win_condSub_irs {dst a b : ℕ} (hI : IInv W c₀ c) (hd : IScr dst) :
    IRS P W c₀ (condSub dst a b) c 3 (fun c' =>
      win_Upd c c' dst (if c.nreg a < c.nreg b then c.nreg a else c.nreg a - c.nreg b)) := by
  obtain ⟨c', k, hk, ex, v, o⟩ := condSub_exec (P := P) hI.hw dst a b
  refine (irs_of_out hI ex hk o (by simp [hd])).mono le_rfl ?_
  rintro _ rfl
  exact ⟨v, fun q hq => o.1 q (by simp [hq]), o.2.2.1⟩

/-- The reduction of `x < 2 n` modulo `n`. -/
theorem win_condSub_mod {x n : ℕ} (h : x < 2 * n) :
    (if x < n then x else x - n) = x % n := by
  split_ifs with h'
  · rw [Nat.mod_eq_of_lt h']
  ram_simp [Nat.mod_eq_sub_mod, Nat.mod_eq_of_lt]

theorem win_sw_ne {i j : ℕ} (h : i ≠ j) : sw i ≠ sw j := by register_guard

/-- Distinct registers. -/
macro "rne" : tactic => `(tactic| (simp only [wD, wE1, wO, wT, wA, wR, wEE, wEH, wL, wC, wCh,
  wDE, wPs, cGL, cNW, cLL, cLD, cLE, cB1, cN1, cE1, kE, kH, K0, K1, K2, K3, K4, K5, K6, wE, wH, wX,
  wGB, wGK, gL, gC, gNF, gBase, gK, ALLOC, MD₁, CD₁, TBR, TLR, sw, ne_eq]; omega))

/-! ## The program -/

/-- The key read in the walk of `C₁`: `wD := kd`, `wE1 := ke₁`. -/
def wKeyS : Stmt :=
  .seq (.instr (.addN wD kE cNW)) (.seq (.instr (.subN wD wD cGL)) (.seq (condSub wD wD cNW)
    (.seq (.ifLtN wD cLL .skip (.instr (.addN wD wD cLD)))
      (.seq (.instr (.addN wE1 cB1 wD)) (condSub wE1 wE1 cN1)))))

set_option maxHeartbeats 4000000 in
/-- **The key in the walk of `C₁`.** -/
theorem wKeyS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (he : c.nreg kE < J.wholeModel.W.n) (hP : J.P.Simple)
    (hWn : 2 * J.wholeModel.W.n ≤ W) (hkdE : kd J (c.nreg kE) < E₁ J) :
    IRS P W c₀ wKeyS c 12 (fun c' => c'.nreg wD = kd J (c.nreg kE) ∧
      c'.nreg wE1 = ke₁ J (c.nreg kE) ∧ (∀ r, r ≠ wD → r ≠ wE1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have hM := hM₀.fix hI
  set n := J.wholeModel.W.n with hn
  set n₁ := J.leftModel.W.n with hn₁
  have hn0 : 0 < n := by have := win_gW_lt (J := J); omega
  have hn7 : 7 ≤ n := by rw [hn, win_n_eq]; omega
  have hgl : (gW J + Lst J) % n < n := Nat.mod_lt _ hn0
  have hn₁n : n₁ ≤ n := by
    simp [hn₁, hn, win_n₁_eq, win_n_eq]
  have sD : IScr wD := iscr_sw' (by norm_num) (by norm_num)
  have wsE : IScr wE1 := iscr_sw' (by norm_num) (by norm_num)
  have nDE : wE1 ≠ wD := win_sw_ne (by norm_num)
  have hkr : kr J (c.nreg kE) < n := dOf_lt hn0 _ _
  have hkd : kd J (c.nreg kE) < n₁ := lt_of_lt_of_le hkdE (E₁_le hP)
  unfold wKeyS
  refine IRS.seq (K₂ := 11) (win_irs_add hI sD (by rw [hM.nw]; omega)) ?_ |>.budget
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := 10) (win_irs_sub hI₁ sD) ?_ |>.budget
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  rw [v1, o1 _ (by rne), hM.gl, hM.nw] at v2
  refine IRS.seq (K₂ := 7) (win_condSub_irs (b := cNW) hI₂ sD) ?_ |>.budget
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  ram_rw [v2, o2 _ (by rne), o1 _ (by rne), hM.nw,
    win_condSub_mod] at v3
  have vr : c₃.nreg wD = kr J (c.nreg kE) := v3
  have hM₃ := hM₀.fix hI₃
  -- beyond the gap
  have step : IRS P W c₀ (.ifLtN wD cLL .skip (.instr (.addN wD wD cLD))) c₃ 3
      (fun c' => win_Upd c₃ c' wD (kd J (c.nreg kE))) := by
    by_cases h : c₃.nreg wD < c₃.nreg cLL
    · refine (IRS.ifT h (IRS.skip (K := 1) hI₃ ⟨?_, fun _ _ => rfl, rfl⟩)).budget
      rw [vr]; rw [vr, hM₃.ll] at h; unfold kd d0Of; ram_rw [ite_eq_right]
    · refine (IRS.ifF h (win_irs_add hI₃ sD ?_)).mono (by norm_num) ?_
      · rw [vr, hM₃.ld]; rcases win_lδ_cases (J := J) with h' | h' <;> rw [h'] <;> omega
      · rintro c' ⟨a, b, d⟩
        refine ⟨?_, b, d⟩
        rw [a, vr, hM₃.ld]; rw [vr, hM₃.ll] at h; unfold kd d0Of; ram_rw [ite_eq_left]
  refine IRS.seq (K₂ := 4) step ?_ |>.budget
  rintro c₄ hI₄ - - ⟨v4, o4, m4⟩
  have hM₄ := hM₀.fix hI₄
  refine IRS.seq (K₂ := 3) (win_irs_add hI₄ wsE (by rw [v4, hM₄.b1]; have := b₁_lt (J := J); omega)) ?_
    |>.budget
  rintro c₅ hI₅ - - ⟨v5, o5, m5⟩
  rw [v4, hM₄.b1] at v5
  refine (win_condSub_irs (b := cN1) hI₅ wsE).mono le_rfl ?_
  rintro c₆ ⟨v6, o6, m6⟩
  have hM₅ := hM₀.fix hI₅
  rw [v5, hM₅.n1, win_condSub_mod (by have := b₁_lt (J := J); omega)] at v6
  have fr : ∀ r, r ≠ wD → r ≠ wE1 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    ram_post
  refine ⟨?_, v6, fr, by rw [m6, m5, m4, m3, m2, m1]⟩
  rw [o6 _ (by rne), o5 _ (by rne), v4]


/-- Load the arc at the spine position `wO`: index `wA`, region `wR`, end `wEE, wEH`. -/
def arcL : List Instr :=
  [.addN wT (sw 3) K6, .loadN wT wT, .addN wT wT wO, .loadN wA wT,
    .addN wT (sw 3) K4, .loadN wT wT, .addN wT wT wA, .addN wT wT wA, .addN wT wT wA,
    .addN wT wT wA, .addN wT wT wA, .loadN wR wT, .addN wT wT K3, .loadN wEE wT, .addN wT wT K1,
    .loadN wEH wT]

def arcS : Stmt := block arcL

theorem arcL_val (m f : ℕ → ℕ) (k6 : f K6 = 6) (k4 : f K4 = 4) (k3 : f K3 = 3) (k1 : f K1 = 1) :
    regB m arcL f wA = m (m (f (sw 3) + 6) + f wO) ∧
    regB m arcL f wR = m (m (f (sw 3) + 4) + 5 * m (m (f (sw 3) + 6) + f wO)) ∧
    regB m arcL f wEE = m (m (f (sw 3) + 4) + 5 * m (m (f (sw 3) + 6) + f wO) + 3) ∧
    regB m arcL f wEH = m (m (f (sw 3) + 4) + 5 * m (m (f (sw 3) + 6) + f wO) + 4) := by
  register_block normalized [arcL]

theorem arcL_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ wT) (h2 : q ≠ wA) (h3 : q ≠ wR)
    (h4 : q ≠ wEE) (h5 : q ≠ wEH) : regB m arcL f q = f q :=
  (by register_keep [arcL])

theorem arcL_ok (m f : ℕ → ℕ) (k6 : f K6 = 6) (k4 : f K4 = 4) (k3 : f K3 = 3) (k1 : f K1 = 1)
    (hb1 : f (sw 3) + 6 ≤ W) (hb2 : m (f (sw 3) + 6) + f wO ≤ W)
    (hb3 : m (f (sw 3) + 4) + 5 * m (m (f (sw 3) + 6) + f wO) + 4 ≤ W) : okB W m arcL f := by
  register_block normalized [arcL]


/-- **The arc at the spine position `wO`.** -/
theorem arcS_irs {M : Model} {Q : Polygon} {N : NF} (hI : IInv W c₀ c) (hK : Consts c)
    (hNF : IsNF M Q N) (hNA : NFAt c.nmem (c.nreg (sw 3)) N)
    (hB1 : c.nreg (sw 3) + 7 ≤ W) (hB2 : c.nmem (c.nreg (sw 3) + 4) + 5 * N.arcs.length ≤ W)
    (hB3 : c.nmem (c.nreg (sw 3) + 6) + N.arcs.length ≤ W) (ho : c.nreg wO < N.arcs.length) :
    IRS P W c₀ arcS c 16 (fun c' => c'.nreg wA = OracleQ.sj N (c.nreg wO) ∧
      c'.nreg wR = (N.arc (OracleQ.sj N (c.nreg wO))).reg ∧
      c'.nreg wEE = (N.arc (OracleQ.sj N (c.nreg wO))).e.edge ∧
      c'.nreg wEH = (N.arc (OracleQ.sj N (c.nreg wO))).e.hgt ∧
      (∀ q, q ≠ wT → q ≠ wA → q ≠ wR → q ≠ wEE → q ≠ wEH → c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem) := by
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  have hsl := NFLoc.seq_length hNF
  have hsj : c.nmem (c.nmem (c.nreg (sw 3) + 6) + c.nreg wO) = OracleQ.sj N (c.nreg wO) :=
    hNA.2.2.2.2.2.2.2.2.1 _ (by omega)
  have hal := NFLoc.seq_lt hNF ho
  have hrec := hNA.2.2.2.2.2.2.1 _ hal
  unfold OracleQ.sj at hsj hal hrec ⊢
  have hok := arcL_ok (W := W) c.nmem c.nreg k6 k4 k3 k1 (by omega) (by omega) (by rw [hsj]; omega)
  refine (IRS.block arcL hI hok).mono (by simp [arcL]) ?_
  rintro c' rfl
  obtain ⟨vA, vR, vE, vH⟩ := arcL_val c.nmem c.nreg k6 k4 k3 k1
  rw [hsj] at vA vR vE vH
  exact ⟨vA, vR.trans hrec.1, vE.trans hrec.2.2.2.1, vH.trans hrec.2.2.2.2,
    fun q h1 h2 h3 h4 h5 => arcL_other _ _ h1 h2 h3 h4 h5, rfl⟩


/-! ## The decision -/

def clipE : Stmt :=
  .seq (.instr (.addN wE cGL cLL)) (.seq (condSub wE wE cNW)
    (.seq (.instr (.constN wH 0)) (.instr (.constN wX 0))))

def normE : Stmt :=
  .seq (.ifLtN wDE cLE (.instr (.copyN wPs wDE)) (.instr (.subN wPs wDE cLD)))
    (.seq (.instr (.addN wE cGL wPs)) (.seq (condSub wE wE cNW)
      (.seq (.instr (.copyN wH wEH)) (.instr (.constN wX 0)))))

def midS : Stmt := .ifLtN K0 cLD (.ifLtN wD cLL (.ifLtN wDE cLL normE clipE) normE) normE

def decS : Stmt :=
  .ifLtN K0 (sw 3011) (.instr (.constN wX 1))
    (.seq (.instr (.addN wDE wEE cN1)) (.seq (.instr (.subN wDE wDE cB1))
      (.seq (condSub wDE wDE cN1) (.ifLtN wDE cE1 midS (.instr (.constN wX 1))))))

/-- The registers the decision writes. -/
def DecW (q : ℕ) : Prop := q = wX ∨ q = wE ∨ q = wH ∨ q = wDE ∨ q = wPs

/-- **The outcomes of the decision.** -/
def DecOut (J : Merge.Junction) (Pw : Prop) (d₀ eE hE : ℕ) (c' : Config) : Prop :=
  (c'.nreg wX = 1 ∧ (Pw ∨ E₁ J ≤ dOf J.leftModel.W.n (b₁ J) eE)) ∨
  (c'.nreg wX = 0 ∧ ¬ Pw ∧ 0 < lδ J ∧ d₀ < lL1 J ∧ lL1 J ≤ dOf J.leftModel.W.n (b₁ J) eE ∧
    dOf J.leftModel.W.n (b₁ J) eE < E₁ J ∧
    c'.nreg wE = (((gW J + Lst J) % J.wholeModel.W.n) + lL1 J) % J.wholeModel.W.n ∧
    c'.nreg wH = 0) ∨
  (c'.nreg wX = 0 ∧ ¬ Pw ∧
    ¬ (0 < lδ J ∧ d₀ < lL1 J ∧ lL1 J ≤ dOf J.leftModel.W.n (b₁ J) eE) ∧
    dOf J.leftModel.W.n (b₁ J) eE < E₁ J ∧
    c'.nreg wE = (((gW J + Lst J) % J.wholeModel.W.n) +
      (if dOf J.leftModel.W.n (b₁ J) eE < lL1 J + lδ J then
        dOf J.leftModel.W.n (b₁ J) eE else dOf J.leftModel.W.n (b₁ J) eE - lδ J)) %
        J.wholeModel.W.n ∧
    c'.nreg wH = hE)


theorem win_lL1_lt_n {J : Merge.Junction} : lL1 J < J.wholeModel.W.n := by
  rw [win_n_eq]; have := J.one_le_m₂; have : J.whole.m = J.m₁ + J.m₂ := rfl
  have := tpos_lt J.left J.m₁
  unfold lL1; split_ifs <;> omega

theorem win_n₁_le_n {J : Merge.Junction} : J.leftModel.W.n ≤ J.wholeModel.W.n := by
  simp [win_n₁_eq, win_n_eq]

theorem decW_X {q : ℕ} (h : ¬ DecW q) : q ≠ wX := fun e => h (Or.inl e)
theorem decW_E {q : ℕ} (h : ¬ DecW q) : q ≠ wE := fun e => h (Or.inr (Or.inl e))
theorem decW_H {q : ℕ} (h : ¬ DecW q) : q ≠ wH := fun e => h (Or.inr (Or.inr (Or.inl e)))
theorem decW_D {q : ℕ} (h : ¬ DecW q) : q ≠ wDE := fun e => h (Or.inr (Or.inr (Or.inr (Or.inl e))))
theorem decW_P {q : ℕ} (h : ¬ DecW q) : q ≠ wPs := fun e => h (Or.inr (Or.inr (Or.inr (Or.inr e))))

theorem wsX : IScr wX := iscr_sw' (by norm_num) (by norm_num)
theorem wsE : IScr wE := iscr_sw' (by norm_num) (by norm_num)
theorem wsH : IScr wH := iscr_sw' (by norm_num) (by norm_num)
theorem wsDE : IScr wDE := iscr_sw' (by norm_num) (by norm_num)
theorem wsP : IScr wPs := iscr_sw' (by norm_num) (by norm_num)

theorem clipE_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hWn : 2 * J.wholeModel.W.n ≤ W) :
    IRS P W c₀ clipE c 6 (fun c' =>
      c'.nreg wE = (((gW J + Lst J) % J.wholeModel.W.n) + lL1 J) %
        J.wholeModel.W.n ∧ c'.nreg wH = 0 ∧ c'.nreg wX = 0 ∧
      (∀ q, ¬ DecW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hM := hM₀.fix hI
  have hgl : (gW J + Lst J) % J.wholeModel.W.n < J.wholeModel.W.n :=
    Nat.mod_lt _ (by have := win_gW_lt (J := J); omega)
  have hl := win_lL1_lt_n (J := J)
  unfold clipE
  refine IRS.seq (K₂ := 5) (win_irs_add hI wsE (by rw [hM.gl, hM.ll]; omega)) ?_ |>.budget
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := 2) (win_condSub_irs (b := cNW) hI₁ wsE) ?_ |>.budget
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  ram_rw [v1, hM.gl, hM.ll, o1 _ (by rne), hM.nw, win_condSub_mod] at v2
  refine IRS.seq (K₂ := 1) (win_irs_const' hI₂ wsH (Nat.zero_le _)) ?_ |>.budget
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  refine (win_irs_const' hI₃ wsX (Nat.zero_le _)).mono le_rfl ?_
  rintro c₄ ⟨v4, o4, m4⟩
  refine ⟨by ram_simp [o4, o3, v2], by rw [o4 _ (by rne), v3], v4,
    fun q hq => ?_, by rw [m4, m3, m2, m1]⟩
  rw [o4 q (decW_X hq), o3 q (decW_H hq), o2 q (decW_E hq), o1 q (decW_E hq)]

theorem normE_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hWn : 2 * J.wholeModel.W.n ≤ W) (hDE : c.nreg wDE < J.wholeModel.W.n) :
    IRS P W c₀ normE c 10 (fun c' =>
      c'.nreg wE = (((gW J + Lst J) % J.wholeModel.W.n) +
        (if c.nreg wDE < lL1 J + lδ J then c.nreg wDE else c.nreg wDE - lδ J)) %
        J.wholeModel.W.n ∧ c'.nreg wH = c.nreg wEH ∧ c'.nreg wX = 0 ∧
      (∀ q, ¬ DecW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hM := hM₀.fix hI
  have hgl : (gW J + Lst J) % J.wholeModel.W.n < J.wholeModel.W.n :=
    Nat.mod_lt _ (by have := win_gW_lt (J := J); omega)
  unfold normE
  have step : IRS P W c₀ (.ifLtN wDE cLE (.instr (.copyN wPs wDE)) (.instr (.subN wPs wDE cLD))) c 3
      (fun c' => win_Upd c c' wPs
        (if c.nreg wDE < lL1 J + lδ J then c.nreg wDE else c.nreg wDE - lδ J)) := by
    by_cases h : c.nreg wDE < c.nreg cLE
    · refine (IRS.ifT h (win_irs_copy hI wsP)).mono (by norm_num) ?_
      rintro c' ⟨a, b, d⟩
      rw [hM.le] at h; exact ⟨by rw [a, ite_eq_left h], b, d⟩
    · refine (IRS.ifF h (win_irs_sub hI wsP)).mono (by norm_num) ?_
      rintro c' ⟨a, b, d⟩
      rw [hM.le] at h; exact ⟨by rw [a, ite_eq_right h, hM.ld], b, d⟩
  refine IRS.seq (K₂ := 7) step ?_ |>.budget
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := 6) (win_irs_add hI₁ wsE (by rw [v1, o1 _ (by rne), hM.gl]; split_ifs <;> omega))
    ?_ |>.budget
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  refine IRS.seq (K₂ := 3) (win_condSub_irs (b := cNW) hI₂ wsE) ?_ |>.budget
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  rw [v2, v1, o1 _ (by rne), hM.gl, o2 _ (by rne), o1 _ (by rne), hM.nw,
    win_condSub_mod (by split_ifs <;> omega)] at v3
  refine IRS.seq (K₂ := 1) (win_irs_copy hI₃ wsH) ?_ |>.budget
  rintro c₄ hI₄ - - ⟨v4, o4, m4⟩
  refine (win_irs_const' hI₄ wsX (Nat.zero_le _)).mono le_rfl ?_
  rintro c₅ ⟨v5, o5, m5⟩
  refine ⟨by ram_simp [o5, o4, v3], ?_, v5, fun q hq => ?_,
    by rw [m5, m4, m3, m2, m1]⟩
  · ram_simp [o5, v4, o3, o2, o1]
  · rw [o5 q (decW_X hq), o4 q (decW_H hq), o3 q (decW_E hq), o2 q (decW_E hq), o1 q (decW_P hq)]


set_option maxHeartbeats 4000000 in
/-- **The decision.** -/
theorem decS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hM₀ : MapK J c₀)
    {Pw : Prop} (hbit : BitIs c (sw 3011) Pw) (hEE : c.nreg wEE < J.leftModel.W.n)
    (hWn : 2 * J.wholeModel.W.n ≤ W) :
    IRS P W c₀ decS c 30 (fun c' => DecOut J Pw (c.nreg wD) (c.nreg wEE) (c.nreg wEH) c' ∧
      (∀ q, ¬ DecW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hK := hK₀.fix hI
  have hM := hM₀.fix hI
  have k0 : c.nreg K0 = 0 := hK.1
  have hnn := win_n₁_le_n (J := J)
  have hb := b₁_lt (J := J)
  unfold decS
  by_cases hb1 : c.nreg K0 < c.nreg (sw 3011)
  · refine (IRS.ifT hb1 (win_irs_const' hI wsX (by omega))).mono (by norm_num) ?_
    rintro c' ⟨v, o, m⟩
    have hp : Pw := hbit.2.1 (by have := hbit.1; omega)
    exact ⟨Or.inl ⟨v, Or.inl hp⟩, fun q hq => o q (decW_X hq), m⟩
  have hnp : ¬ Pw := fun hp => hb1 (by simp [k0, hbit.2.2 hp])
  refine IRS.mono (K := 28 + 2) (IRS.ifF hb1 ?_) le_rfl (fun _ h => h)
  refine IRS.seq (K₂ := 27) (win_irs_add hI wsDE (by rw [hM.n1]; omega)) ?_ |>.budget
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := 26) (win_irs_sub hI₁ wsDE) ?_ |>.budget
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  refine IRS.seq (K₂ := 23) (win_condSub_irs (b := cN1) hI₂ wsDE) ?_ |>.budget
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  have hM₁ := hM₀.fix hI₁
  have hM₂ := hM₀.fix hI₂
  ram_rw [v2, v1, o1 cB1 (by rne), hM.n1, hM.b1, o2 cN1 (by rne), o1 cN1 (by rne), hM.n1,
    win_condSub_mod] at v3
  set dE := dOf J.leftModel.W.n (b₁ J) (c.nreg wEE) with hdE
  have vd : c₃.nreg wDE = dE := v3
  have hM₃ := hM₀.fix hI₃
  have hK₃ := hK₀.fix hI₃
  have o3' : ∀ q, ¬ DecW q → c₃.nreg q = c.nreg q := fun q hq => by
    rw [o3 q (decW_D hq), o2 q (decW_D hq), o1 q (decW_D hq)]
  have m3' : c₃.nmem = c.nmem := by rw [m3, m2, m1]
  have hdn : dE < J.leftModel.W.n := dOf_lt (by omega) _ _
  by_cases hb2 : c₃.nreg wDE < c₃.nreg cE1
  · rw [vd, hM₃.e1] at hb2
    refine IRS.mono (K := 18 + 2) (IRS.ifT (by rwa [vd, hM₃.e1]) ?_) (by norm_num)
      (fun _ h => h)
    unfold midS
    have eD : c₃.nreg wD = c.nreg wD := o3' _ (by unfold DecW; rne)
    have eH : c₃.nreg wEH = c.nreg wEH := o3' _ (by unfold DecW; rne)
    have finN : ∀ c', (c'.nreg wE = (((gW J + Lst J) % J.wholeModel.W.n) +
        (if c₃.nreg wDE < lL1 J + lδ J then c₃.nreg wDE else c₃.nreg wDE - lδ J)) %
        J.wholeModel.W.n ∧ c'.nreg wH = c₃.nreg wEH ∧ c'.nreg wX = 0 ∧
        (∀ q, ¬ DecW q → c'.nreg q = c₃.nreg q) ∧ c'.nmem = c₃.nmem) →
        ¬ (0 < lδ J ∧ c.nreg wD < lL1 J ∧ lL1 J ≤ dE) →
        DecOut J Pw (c.nreg wD) (c.nreg wEE) (c.nreg wEH) c' ∧
          (∀ q, ¬ DecW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
      rintro c' ⟨a1, a2, a3, a4, a5⟩ hn
      rw [vd] at a1
      exact ⟨Or.inr (Or.inr ⟨a3, hnp, hn, hb2, a1, a2.trans eH⟩),
        fun q hq => (a4 q hq).trans (o3' q hq), a5.trans m3'⟩
    have hDEn : c₃.nreg wDE < J.wholeModel.W.n := by omega
    by_cases hδ : c₃.nreg K0 < c₃.nreg cLD
    · have hδ' : 0 < lδ J := by rwa [hK₃.1, hM₃.ld] at hδ
      refine IRS.mono (K := 16 + 2) (IRS.ifT hδ ?_) (by norm_num) (fun _ h => h)
      by_cases hd0 : c₃.nreg wD < c₃.nreg cLL
      · have hd0' : c.nreg wD < lL1 J := by rwa [eD, hM₃.ll] at hd0
        refine IRS.mono (K := 12 + 2) (IRS.ifT hd0 ?_) (by norm_num) (fun _ h => h)
        by_cases hd1 : c₃.nreg wDE < c₃.nreg cLL
        · refine IRS.mono (K := 10 + 2) (IRS.ifT hd1 ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
            fun c' h => finN c' h ?_)) (by norm_num) (fun _ h => h)
          rw [vd, hM₃.ll] at hd1; omega
        · refine IRS.mono (K := 10 + 2) (IRS.ifF hd1 ((clipE_irs hI₃ hM₀ hWn).mono (by norm_num)
            ?_)) (by norm_num) (fun _ h => h)
          rintro c' ⟨a1, a2, a3, a4, a5⟩
          rw [vd, hM₃.ll] at hd1
          exact ⟨Or.inr (Or.inl ⟨a3, hnp, hδ', hd0', by omega, hb2, a1, a2⟩),
            fun q hq => (a4 q hq).trans (o3' q hq), a5.trans m3'⟩
      · have hd0' : ¬ c.nreg wD < lL1 J := by rwa [eD, hM₃.ll] at hd0
        refine IRS.mono (K := 10 + 2) (IRS.ifF hd0 ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
          fun c' h => finN c' h ?_)) (by norm_num) (fun _ h => h)
        omega
    · have hδ' : ¬ 0 < lδ J := by rwa [hK₃.1, hM₃.ld] at hδ
      refine IRS.mono (K := 10 + 2) (IRS.ifF hδ ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
        fun c' h => finN c' h ?_)) (by norm_num) (fun _ h => h)
      omega
  · rw [vd, hM₃.e1] at hb2
    refine IRS.mono (K := 1 + 2) (IRS.ifF (by rwa [vd, hM₃.e1])
      (win_irs_const' hI₃ wsX (by omega))) (by norm_num) ?_
    rintro c' ⟨v, o, m⟩
    exact ⟨Or.inl ⟨v, Or.inr (by omega)⟩, fun q hq => (o q (decW_X hq)).trans (o3' q hq),
      m.trans m3'⟩


end

end SweepEv

end Chazelle.Core
