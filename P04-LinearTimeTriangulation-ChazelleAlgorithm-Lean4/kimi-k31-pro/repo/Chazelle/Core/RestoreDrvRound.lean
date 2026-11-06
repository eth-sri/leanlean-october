module

public import Chazelle.Core.RestoreDrvSeg
public import Chazelle.Core.GranSize
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 16000000

/-!
# WP-E, part 11: the restoration driver — one round

`round_step`: from a configuration satisfying the round invariant `OutI E t` (current normal
form of a family `⊇ S₀`, degree `≤ max D (d₀ - t)`, γ-semigranular, at most
`2^t (K₀ + 1) - 1` chords), one execution of `roundBody` reaches `OutI E (t + 1)`, within the
relative frame and at most `E.Br` steps.
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs
open Chazelle.Chain (regionsIn)

@[expose] public section

/-- The fixed data of the driver. -/
structure DrvEnv where
  P : Polygon
  W : ℕ
  M : Model
  A₀ : ℕ
  m₀ : ℕ → ℕ
  MD : ℕ
  d0 : ℕ
  D : ℕ
  γ : ℕ
  ctx : ℕ
  sF : Stmt
  sB : Stmt
  κf : ℕ → ℕ
  κB : ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  Ok : Polygon → Model → Prop
  S₀ : Set (Set Point)
  K₀ : ℕ

namespace DrvEnv

variable (E : DrvEnv)

/-- A bound on the number of chords during the driver. -/
def Kc : ℕ := 2 ^ (E.d0 + 1) * (E.K₀ + 1)

/-- The body bound of the region loop. -/
def Bf : ℕ := costF E.κf E.F E.G E.Hc (E.d0 + E.D) E.γ + 20

/-- The bound of one round. -/
def Br : ℕ := 40 + 21 * E.Kc + (E.Bf + 2) * E.Kc +
  E.κB * (2 * E.Kc * (Nat.clog 2 (2 * E.Kc) + 1) + 1)

end DrvEnv

/-- The facts about the driver data. -/
structure DrvGood (E : DrvEnv) : Prop where
  hF : FindOK E.sF E.κf E.F E.G E.Hc E.X E.Ok oracleBands
  hB : Gran.BuildOK E.sB E.κB
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, (∀ a, a < E.A₀ → m a = E.m₀ a) → E.γ ≤ E.X.cap E.P m E.ctx
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD (Qof E.P) E.M
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C → C.P.Simple
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hfull : E.M.FullDegLe (Qof E.P) E.D

/-- The mathematical state of a round: the current normal form. -/
structure CurOK (E : DrvEnv) (t : ℕ) (m : ℕ → ℕ) (H A : ℕ) (N : NF) : Prop where
  nw : NFWithin m H A N
  nf : IsNF E.M (Qof E.P) N
  sub : E.S₀ ⊆ N.F E.M (Qof E.P)
  deg : E.M.DegLe (N.F E.M (Qof E.P)) (max E.D (E.d0 - t))
  sg : E.M.Semigranular (N.F E.M (Qof E.P)) E.γ
  size : N.nChords + 1 ≤ 2 ^ t * (E.K₀ + 1)
  fresh : 0 < t → E.A₀ ≤ H

/-- **The round invariant.** -/
structure OutI (E : DrvEnv) (t : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  r00 : c.nreg 80000 = E.MD
  r02 : c.nreg 80002 = E.d0
  r03 : c.nreg 80003 = E.D
  r04 : c.nreg 80004 = E.γ
  r06 : c.nreg 80006 = E.ctx
  r10 : c.nreg 80010 = t
  r11 : c.nreg 80011 = E.d0 + 1
  r19 : c.nreg 80019 = E.d0 + E.D
  r20 : c.nreg 80020 = 1
  r21 : c.nreg 80021 = 2
  r22 : c.nreg 80022 = 3
  r23 : c.nreg 80023 = 5
  r24 : c.nreg 80024 = 0
  cur : ∃ N, CurOK E t c.nmem (c.nreg 80012) (c.nreg ALLOC) N
  low : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a
  alloc : E.A₀ ≤ c.nreg ALLOC
  t_le : t ≤ E.d0 + 1
  room : c.nreg ALLOC + (E.d0 + 1 - t) * (E.Br + 2) + 3 ≤ E.W

/-- The data of the region loop of a round. -/
def regEnvOf (E : DrvEnv) (N : NF) (reg : ℕ → Set Point) (LB H : ℕ) : RegEnv where
  P := E.P
  W := E.W
  M := E.M
  N := N
  reg := reg
  A₀ := E.A₀
  m₀ := E.m₀
  LB := LB
  H := H
  MD := E.MD
  D := E.D
  γ := E.γ
  ctx := E.ctx
  dcap := E.d0 + E.D
  sF := E.sF
  κf := E.κf
  F := E.F
  G := E.G
  Hc := E.Hc
  X := E.X
  Ok := E.Ok

theorem size_le_Kc {E : DrvEnv} {t K : ℕ} (ht : t ≤ E.d0) (h : K + 1 ≤ 2 ^ t * (E.K₀ + 1)) :
    2 * K + 2 ≤ E.Kc := by
  unfold DrvEnv.Kc
  have : 2 ^ t ≤ 2 ^ E.d0 := Nat.pow_le_pow_right (by norm_num) ht
  rw [pow_succ]
  nlinarith

/-- **The first part of a round**: header, copy, reservation, set-up of the region loop. -/
theorem phaseA {E : DrvEnv} (hE : DrvGood E) {t : ℕ} {c : Config} (hI : OutI E t c)
    (ht : t < E.d0 + 1) {N : NF} (hcur : CurOK E t c.nmem (c.nreg 80012) (c.nreg ALLOC) N)
    {reg : ℕ → Set Point} (hregs : NFRegs E.M (Qof E.P) N reg)
    (rest : Stmt) (Qp : Config → ℕ → Prop)
    (hrest : ∀ c₅ k, RegGood (regEnvOf E N reg (c.nreg ALLOC) (c.nreg 80012)) c₅ →
      RF dBands E.A₀ c c₅ k → k ≤ 20 + 15 * N.nChords + 6 * N.nRegions →
      c₅.nreg 80002 = E.d0 → c₅.nreg 80010 = t → c₅.nreg 80011 = E.d0 + 1 →
      c₅.nreg 80021 = 2 → c₅.nreg 80022 = 3 → c₅.nreg 80017 = c.nreg ALLOC →
      c₅.nreg 80012 = c.nreg 80012 →
      ∃ c' k', Exec E.P E.W rest c₅ c' k' ∧ Qp c' (k + k')) :
    ∃ c' k, Exec E.P E.W (.seq headS (.seq copyS (.seq midS (.seq resS (.seq preRegS rest)))))
      c c' k ∧ Qp c' k := by
  set H := c.nreg 80012 with hHd
  set LB := c.nreg ALLOC with hLBd
  set K := N.nChords with hKd
  set R := N.nRegions with hRd
  have hM := walkAx_of_goodModel hE.hGM
  have hRK : R = K + 1 := Gran.nRegions_eq hcur.nf hM
  have hNAt := hcur.nw.nfAt
  have hareas := Gran.nf_areas hcur.nw
  have hW := hI.wb
  have hLBW : LB ≤ E.W := hW.1 ALLOC
  have hKc : 2 * K + 2 ≤ E.Kc := size_le_Kc (by omega) hcur.size
  have hBr : 21 * E.Kc + 40 ≤ E.Br := by ufo DrvEnv.Br
  have hroom := hI.room
  have hroom' : LB + E.Br + 2 ≤ E.W := by
    have : E.Br + 2 ≤ (E.d0 + 1 - t) * (E.Br + 2) :=
      Nat.le_mul_of_pos_left (E.Br + 2) (by omega)
    omega
  -- header
  obtain ⟨c₁, k₁, e₁, hk₁, a13, a14, a15, a16, a17, a31, a30, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    head_exec (P := E.P) c hW rfl hI.r21 hI.r22 (by omega)
  have hK : c.nmem H = K := hNAt.1
  have hR : c.nmem (H + 2) = R := hNAt.2.2.1
  rw [hK] at a13
  rw [hR] at a14
  set CB := c.nmem (H + 3) with hCBd
  set RB := c.nmem (H + 5) with hRBd
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, (r < 80013 ∨ (80017 < r ∧ r < 80030) ∨ (80031 < r ∧ r ≠ 80036)) →
    c₁.nreg r = c.nreg r := R₁
  have A₁ : c₁.nreg ALLOC = LB := g₁ _ (by left; decide)
  -- copy
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, h30, R₂, low₂, cop₂, RF₂⟩ := copy_exec (P := E.P) (A₀ := E.A₀)
    w₁ a13 a30 a31 A₁ (by rw [g₁ _ (by right; left; decide), hI.r20])
    (by rw [g₁ _ (by right; left; decide), hI.r22])
    (hareas.2.1) (by omega) (by omega) hI.alloc
  have w₂ := e₂.wb_right
  -- mid
  obtain ⟨c₃, k₃, e₃, hk₃, b18, b43, b34, R₃, rr₃, m₃, rm₃, o₃⟩ := mid_exec (P := E.P) c₂ w₂
  have w₃ := e₃.wb_right
  have A₃ : c₃.nreg ALLOC = LB + 3 * K := by rw [R₃ _ (by decide) (by decide) (by decide), A₂]
  -- reservation
  obtain ⟨c₄, k₄, e₄, hk₄, A₄, R₄, m₄, RF₄⟩ := res_exec (P := E.P) (A₀ := E.A₀) w₃
    (by rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide)
      (by decide), a14])
    b34 A₃ (by rw [R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide)
      (by decide) (by decide), g₁ _ (by right; left; decide), hI.r20]) (by omega) (by omega)
  have w₄ := e₄.wb_right
  -- region-loop set-up
  have d16 : c₄.nreg 80016 = RB := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide),
      R₂ _ (by decide) (by decide) (by decide) (by decide), a16]
  have d21 : c₄.nreg 80021 = 2 := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide),
      R₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by right; left; decide),
      hI.r21]
  have hRB : RB + 4 < LB := by
    have := hareas.2.2.1 0 (by omega); omega
  obtain ⟨c₅, k₅, e₅, hk₅, f40, f41, R₅, rr₅, m₅, rm₅, o₅⟩ := preReg_exec (P := E.P) c₄ w₄
    (by rwo [d16, d21])
  rw [d16, d21] at f41
  have w₅ := e₅.wb_right
  -- the registers of `c₅`
  have G : ∀ r, 80000 ≤ r → r ≤ 80024 → r ≠ 80013 → r ≠ 80014 → r ≠ 80015 → r ≠ 80016 →
      r ≠ 80017 → r ≠ 80018 → c₅.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8
    have hA : r ≠ ALLOC := by ufo ALLOC
    rw [R₅ r (by omega) (by omega), R₄ r (by omega) hA,
      R₃ r (by omega) (by omega) (by omega), R₂ r (by omega) (by omega) (by omega) hA,
      g₁ r (by omega)]
  have f17 : c₅.nreg 80017 = LB := by
    rw [R₅ _ (by decide) (by decide), R₄ _ (by decide) (by decide),
      R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide)
        (by decide), a17]
  have f14 : c₅.nreg 80014 = R := by
    rw [R₅ _ (by decide) (by decide), R₄ _ (by decide) (by decide),
      R₃ _ (by decide) (by decide) (by decide), R₂ _ (by decide) (by decide) (by decide)
        (by decide), a14]
  have f18 : c₅.nreg 80018 = K := by
    rw [R₅ _ (by decide) (by decide), R₄ _ (by decide) (by decide), b18,
      R₂ _ (by decide) (by decide) (by decide) (by decide), a13]
  have f43 : c₅.nreg 80043 = LB + 3 * K := by
    rw [R₅ _ (by decide) (by decide), R₄ _ (by decide) (by decide), b43, A₂]
  have A₅ : c₅.nreg ALLOC = LB + 3 * K + 3 * R := by
    rw [R₅ _ (by decide) (by decide), A₄]
  -- memory of `c₅`
  have mem5 : ∀ a, a < LB → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅, m₄, m₃, low₂ a ha, m₁]
  have hlist : ChordListAt c₅.nmem LB (oldL N) := by
    intro i hi
    simp [oldL, List.length_map] at hi
    have hc := hNAt.2.2.2.2.2.1 i hi
    have e : (oldL N).getD i (0, 0, 0) = ((N.chord i).h, (N.chord i).lp, (N.chord i).rp) := by
      unfold oldL NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rw [e, m₅, m₄, m₃]
    have c0 := cop₂ i hi 0 (by omega)
    have c1 := cop₂ i hi 1 (by omega)
    have c2 := cop₂ i hi 2 (by omega)
    simp [add_zero] at c0
    rw [m₁] at c0 c1 c2
    refine ⟨?_, ?_, ?_⟩
    · rw [c0]; exact hc.1
    · rw [c1]; exact hc.2.1
    · rw [c2]; exact hc.2.2.1
  -- the frame
  have hb : ∀ r, bandOf r ∉ dBands → r < 80000 ∨ 90000 ≤ r := fun r hr => by
    by_contra h; push Not at h; exact hr (band8 h.1 h.2 ▸ mem_dBands_8)
  have RF₁ : RF dBands E.A₀ c c₁ k₁ := rf_of_regs (fun r hr => g₁ r (by omega)) rr₁ m₁ rm₁ o₁
  have RF₃ : RF dBands E.A₀ c₂ c₃ k₃ :=
    rf_of_regs (fun r hr => R₃ r (by omega) (by omega) (by omega)) rr₃ m₃ rm₃ o₃
  have RF₅ : RF dBands E.A₀ c₄ c₅ k₅ :=
    rf_of_regs (fun r hr => R₅ r (by omega) (by omega)) rr₅ m₅ rm₅ o₅
  have RFA : RF dBands E.A₀ c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans RF₅)))
  -- the region-loop facts
  have hgood : RegGood (regEnvOf E N reg LB H) c₅ := by
    refine ⟨hE.hF, hE.hG, hE.hWh, hE.hX, hE.hcap, hI.alloc, hE.hwf, hE.hMD, hE.hreg, hE.hsimp, hE.hGM, hE.hOk,
      hE.hfull, ?_, hcur.nf, hregs, ?_, hcur.sg, fun a ha => ?_, w₅, ?_, ?_, ?_, ?_, ?_, f14,
      ?_, ?_, ?_, ?_, f40, ?_, f18, f43, ?_, hlist, ?_⟩
    · exact (hcur.nw.transport (mem5))
    · exact Model.DegLe.mono _ hcur.deg (max_le (by show E.D ≤ E.d0 + E.D; omega)
        (by show E.d0 - t ≤ E.d0 + E.D; omega))
    · change a < E.A₀ at ha
      change c₅.nmem a = E.m₀ a
      rw [mem5 a (by have := hI.alloc; omega), hI.low a ha]
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r00]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r03]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r04]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r06]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r19]; rfl
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r20]
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r23]
    · rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hI.r24]
    · show c₅.nreg 80041 = c₅.nmem (H + 5) + 2
      rw [f41, mem5 _ (by have := hareas.1; omega)]
    · show LB + 3 * (K + R) ≤ c₅.nreg ALLOC
      rwo [A₅]
    · show c₅.nreg ALLOC + (E.Bf + 2) * R + 2 ≤ E.W
      rw [A₅]
      have : (E.Bf + 2) * R ≤ (E.Bf + 2) * E.Kc := Nat.mul_le_mul_left _ (by omega)
      have hBr2 : 21 * E.Kc + 40 + (E.Bf + 2) * E.Kc ≤ E.Br := by ufo DrvEnv.Br
      omega
  obtain ⟨c', k', ex, hQ⟩ := hrest c₅ _ hgood RFA (by omega)
    (by rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hI.r02])
    (by rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hI.r10])
    (by rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hI.r11])
    (by rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hI.r21])
    (by rw [G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hI.r22])
    f17
    (G _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ ex)))), by
    have : k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k')))) = k₁ + (k₂ + (k₃ + (k₄ + k₅))) + k' := by ring
    rwx [this]⟩

theorem clog_mul_mono {a b : ℕ} (h : a ≤ b) :
    a * (Nat.clog 2 a + 1) + 1 ≤ b * (Nat.clog 2 b + 1) + 1 := by
  have := Nat.clog_mono_right 2 h
  have : a * (Nat.clog 2 a + 1) ≤ b * (Nat.clog 2 b + 1) := Nat.mul_le_mul h (by omega)
  omega

/-- **One round.** -/
theorem round_step {E : DrvEnv} (hE : DrvGood E) {t : ℕ} {c : Config} (hI : OutI E t c)
    (ht : t < E.d0 + 1) :
    ∃ c' k, Exec E.P E.W (roundBody E.sF E.sB) c c' k ∧ OutI E (t + 1) c' ∧
      RF dBands E.A₀ c c' k ∧ k ≤ E.Br := by
  obtain ⟨N, hcur⟩ := hI.cur
  obtain ⟨reg, hRC, hCS, hAO, hRO, -⟩ := hcur.nf.2.2.2
  have hregs : NFRegs E.M (Qof E.P) N reg := ⟨hRC, hCS, hAO, hRO⟩
  have hM := walkAx_of_goodModel hE.hGM
  have hRK : N.nRegions = N.nChords + 1 := Gran.nRegions_eq hcur.nf hM
  have hKc : 2 * N.nChords + 2 ≤ E.Kc := size_le_Kc (by omega) hcur.size
  have hroom := hI.room
  have hroom' : c.nreg ALLOC + E.Br + 2 ≤ E.W := by
    have : E.Br + 2 ≤ (E.d0 + 1 - t) * (E.Br + 2) :=
      Nat.le_mul_of_pos_left (E.Br + 2) (by omega)
    omega
  unfold roundBody
  refine phaseA hE hI ht hcur hregs _
    (fun c' k => OutI E (t + 1) c' ∧ RF dBands E.A₀ c c' k ∧ k ≤ E.Br) ?_
  intro c₅ k₅ hgood RF₅ hk₅ q02 q10 q11 q21 q22 q17 q12
  -- the region loop
  obtain ⟨c₆, k₆, newL, e₆, I₆, h40, RF₆, hk₆⟩ := reg_exec hgood
  have hNew : NewOK E.M (Qof E.P) N reg E.D newL := ⟨by
    have := I₆.hfst; rw [h40] at this; exact this, I₆.hgood⟩
  set L := oldL N ++ newL.map Prod.snd with hLd
  have hlenNew : newL.length ≤ N.nRegions := by
    have := congrArg List.length hNew.fst
    rw [List.length_map] at this
    rw [this]; exact highList_length_le _ _ _
  have hLlen : L.length = N.nChords + newL.length := by
    simp [hLd, oldL, NF.nChords]
  have hok := round_list_ok hM hcur.nf hregs hNew
  have w₆ := e₆.wb_right
  -- registers after the loop
  have reg6 : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
      q ≠ 80043 → c₆.nreg q = c₅.nreg q := I₆.regs
  -- build: arguments
  obtain ⟨c₇, k₇, e₇, hk₇, b0, b1, b2, R₇, rr₇, m₇, rm₇, o₇⟩ := bargs_exec (P := E.P) c₆ w₆
  have w₇ := e₇.wb_right
  have A₇ : c₇.nreg ALLOC = c₆.nreg ALLOC := R₇ _ (by decide) (by decide) (by decide)
  have x0 : c₇.nreg 40000 = E.MD := by
    rw [b0, reg6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hgood.r00]; rfl
  have x1 : c₇.nreg 40001 = c.nreg ALLOC := by
    rw [b1, reg6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), q17]
  have x2 : c₇.nreg 40002 = L.length := by rwr [b2, I₆.cnt, hLlen]
  -- memory below `A₀` agrees with the initial one
  have RF56 := RF₅.trans RF₆
  have lowc : ∀ a, a < E.A₀ → c₇.nmem a = E.m₀ a := fun a ha => by
    rw [m₇, RF56.2.2.1 a ha, hI.low a ha]
  have hA0₇ : E.A₀ ≤ c₇.nreg ALLOC := by
    rw [A₇]; exact le_trans hI.alloc RF56.2.2.2.2.2.1
  obtain ⟨hMD₇, hwf₇⟩ := Gran.desc_agree' hE.hwf hE.hMD lowc
  have hlist₇ : ChordListAt c₇.nmem (c.nreg ALLOC) L := by rw [m₇]; exact I₆.list
  have hLB₇ : c.nreg ALLOC + 3 * L.length ≤ c₇.nreg ALLOC := by
    rw [A₇, hLlen]
    have h1 := hgood.alloc
    have h2 := I₆.alloc
    change c.nreg ALLOC + 3 * (N.nChords + N.nRegions) ≤ c₅.nreg ALLOC at h1
    omega
  -- cost facts
  have hLK : L.length ≤ 2 * E.Kc := by rwo [hLlen]
  have hcl := clog_mul_mono hLK
  have hA7le : c₇.nreg ALLOC ≤ c.nreg ALLOC + (k₅ + k₆) := by
    rw [A₇]; exact RF56.2.2.2.2.2.2
  have hRKc : N.nRegions ≤ E.Kc := by omega
  have hBfR : (E.Bf + 2) * N.nRegions ≤ (E.Bf + 2) * E.Kc := Nat.mul_le_mul_left _ hRKc
  have hk56 : k₅ + k₆ ≤ 22 + 15 * E.Kc + 6 * E.Kc + (E.Bf + 2) * E.Kc := by
    change k₆ ≤ (E.Bf + 2) * N.nRegions + 2 at hk₆
    omega
  have hκB : E.κB * (L.length * (Nat.clog 2 L.length + 1) + 1) ≤
      E.κB * (2 * E.Kc * (Nat.clog 2 (2 * E.Kc) + 1) + 1) := Nat.mul_le_mul_left _ hcl
  have hBrdef : E.Br = 40 + 21 * E.Kc + (E.Bf + 2) * E.Kc +
      E.κB * (2 * E.Kc * (Nat.clog 2 (2 * E.Kc) + 1) + 1) := rfl
  -- build
  have z0 : rd c₇ bBuild 0 = E.MD := x0
  have z1 : rd c₇ bBuild 1 = c.nreg ALLOC := x1
  have z2 : rd c₇ bBuild 2 = L.length := x2
  have p1 : ModelDescWF E.P (c₇.nreg ALLOC) c₇.nmem (rd c₇ bBuild 0) := by
    rw [z0]; exact hwf₇.mono hA0₇
  have p2 : ModelDescAt c₇.nmem (rd c₇ bBuild 0) (Qof E.P) E.M := by rwx [z0]
  have p3 : rd c₇ bBuild 1 + 3 * L.length ≤ c₇.nreg ALLOC := by rwx [z1]
  have p4 : ChordListAt c₇.nmem (rd c₇ bBuild 1) L := by rwx [z1]
  obtain ⟨c₈, k₈, e₈, hk₈, post₈, F₈⟩ := hE.hB E.P E.W c₇ w₇
    ⟨hE.hG, hE.hWh, p1, E.M, L, p2, hE.hGM, z2, p3, p4, hok⟩
    (by
      beta_reduce
      rw [z2]
      omega)
  beta_reduce at hk₈
  rw [z2] at hk₈
  obtain ⟨N', g₈, hNW₈, hNF₈, hmap₈, -⟩ := post₈ E.M L p2 z2 p4
  have w₈ := e₈.wb_right
  -- handle and counter
  obtain ⟨c₉, k₉, e₉, hk₉, h12, R₉, rr₉, m₉, rm₉, o₉⟩ := copy1_exec' (P := E.P) c₈ w₈ 80012 40003
  have w₉ := e₉.wb_right
  have r8 : ∀ q, 80000 ≤ q → q < 90000 → c₈.nreg q = c₇.nreg q := fun q h1 h2 =>
    F₈.1 q (by rwd [band8 h1 h2]) (by ufo ALLOC)
  have y10 : c₉.nreg 80010 = t := by
    rw [R₉ _ (by decide), r8 _ (by omega) (by omega), R₇ _ (by decide) (by decide) (by decide),
      reg6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), q10]
  have y20 : c₉.nreg 80020 = 1 := by
    rw [R₉ _ (by decide), r8 _ (by omega) (by omega), R₇ _ (by decide) (by decide) (by decide),
      reg6 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hgood.r20]
  have hd0Kc : E.d0 + 1 ≤ E.Kc := by
    unfold DrvEnv.Kc
    have := Nat.lt_two_pow_self (n := E.d0 + 1)
    nlinarith
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, h10, R₁₀, rr₁₀, m₁₀, rm₁₀, o₁₀⟩ := incr_exec (P := E.P) c₉ w₉
    (by rwo [y10, y20])
  rw [y10, y20] at h10
  -- fixed registers
  have Y : ∀ q, 80000 ≤ q → q < 81000 → q ≠ 80040 → q ≠ 80041 → q ≠ 80042 → q ≠ 80018 →
      q ≠ 80043 → q ≠ 80012 → q ≠ 80010 → c₁₀.nreg q = c₅.nreg q := by
    intro q h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [R₁₀ q h9, R₉ q h8, r8 q h1 (by omega), R₇ q (by omega) (by omega) (by omega),
      reg6 q h1 h2 h3 h4 h5 h6 h7]
  -- frames
  have RF₇ : RF dBands E.A₀ c₆ c₇ k₇ := rf_of_regs' (fun r hr => R₇ r
    (fun h => hr (by rwd [h])) (fun h => hr (by rwd [h]))
    (fun h => hr (by rwd [h]))) rr₇ m₇ rm₇ o₇
  have RF₈ : RF dBands E.A₀ c₇ c₈ k₈ := RF.of_frame (F₈.mono (by decide) le_rfl) hA0₇
  have RF₉ : RF dBands E.A₀ c₈ c₉ k₉ := rf_of_regs (fun r hr => R₉ r (by omega)) rr₉ m₉ rm₉ o₉
  have RF₁₀ : RF dBands E.A₀ c₉ c₁₀ k₁₀ := rf_of_regs (fun r hr => R₁₀ r (by omega))
    rr₁₀ m₁₀ rm₁₀ o₁₀
  have RFall := RF56.trans (RF₇.trans (RF₈.trans (RF₉.trans RF₁₀)))
  have hktot : k₅ + k₆ + (k₇ + (k₈ + (k₉ + k₁₀))) ≤ E.Br := by omega
  -- the new family
  have hF' : N'.F E.M (Qof E.P) = N.F E.M (Qof E.P) ∪ newSet E.M (Qof E.P) newL := by
    rw [Gran.F_of_map hmap₈, round_lset]
  have hSa : N.F E.M (Qof E.P) ⊆ E.M.Adm := hcur.nf.1.2.1
  have hSf : (N.F E.M (Qof E.P)).Finite := hcur.nf.1.1
  have hdata := round_data hM hcur.nf hregs hNew
  have hdeg' := round_degLe hM hSa hSf hdata hcur.deg (round_all hcur.nf hregs hNew)
  have hN'len : N'.nChords = L.length := by
    unfold NF.nChords; rw [← hmap₈, List.length_map]
  have e₆' : Exec E.P E.W (regS E.sF) c₅ c₆ k₆ := e₆
  refine ⟨c₁₀, k₆ + ((k₇ + (k₈ + k₉)) + k₁₀),
    .seq e₆' (.seq (.seq e₇ (.seq e₈ e₉)) e₁₀), ?_, RFall.mono subset_rfl (by omega),
    by omega⟩
  · have e5 : ∀ q, 80000 ≤ q → q ≤ 80024 → q ≠ 80018 → q ≠ 80012 → q ≠ 80010 →
        c₁₀.nreg q = c₅.nreg q := fun q h1 h2 h3 h4 h5 =>
      Y q h1 (by omega) (by omega) (by omega) (by omega) h3 (by omega) h4 h5
    have hA10 : c₁₀.nreg ALLOC = c₈.nreg ALLOC := by
      rw [R₁₀ _ (by decide), R₉ _ (by decide)]
    have hmem10 : c₁₀.nmem = c₈.nmem := by rw [m₁₀, m₉]
    have hH10 : c₁₀.nreg 80012 = rd c₈ bBuild 3 := by rwr [R₁₀ _ (by decide), h12]
    have E5 : ∀ q, 80000 ≤ q → q ≤ 80024 → q ≠ 80018 → q ≠ 80012 → q ≠ 80010 →
        c₁₀.nreg q = c₅.nreg q := e5
    have v00 : c₁₀.nreg 80000 = E.MD := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r00
    have v02 : c₁₀.nreg 80002 = E.d0 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans q02
    have v03 : c₁₀.nreg 80003 = E.D := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r03
    have v04 : c₁₀.nreg 80004 = E.γ := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r04
    have v06 : c₁₀.nreg 80006 = E.ctx := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r06
    have v11 : c₁₀.nreg 80011 = E.d0 + 1 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans q11
    have v19 : c₁₀.nreg 80019 = E.d0 + E.D := (E5 _ (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans hgood.r19
    have v20 : c₁₀.nreg 80020 = 1 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r20
    have v21 : c₁₀.nreg 80021 = 2 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans q21
    have v22 : c₁₀.nreg 80022 = 3 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans q22
    have v23 : c₁₀.nreg 80023 = 5 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r23
    have v24 : c₁₀.nreg 80024 = 0 := (E5 _ (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hgood.r24
    have vlow : ∀ a, a < E.A₀ → c₁₀.nmem a = E.m₀ a := fun a ha => by
      rw [RFall.2.2.1 a ha, hI.low a ha]
    refine ⟨e₁₀.wb_right, v00, v02, v03, v04, v06, h10, v11, v19, v20, v21, v22, v23, v24,
      ⟨N', ?_⟩, vlow, le_trans hI.alloc RFall.2.2.2.2.2.1, by omega, ?_⟩
    · refine ⟨by rwx [hmem10, hA10, hH10], hNF₈, ?_, ?_, ?_, ?_, fun _ => ?_⟩
      · rw [hF']; exact hcur.sub.trans Set.subset_union_left
      · rw [hF']
        exact Model.DegLe.mono _ hdeg' (max_le (le_max_left _ _) (by omega))
      · rw [hF']
        exact semigranular_mono hM Set.subset_union_left (Set.union_subset hSa hdata.adm)
          (hSf.union hdata.fin) hcur.sg
      · rw [hN'len, hLlen, pow_succ]
        have := hcur.size
        nlinarith
      · rw [hH10]; exact le_trans hA0₇ g₈
    · have h1 := RFall.2.2.2.2.2.2
      have h2 : (E.d0 + 1 - t) * (E.Br + 2) = (E.d0 + 1 - (t + 1)) * (E.Br + 2) + (E.Br + 2) := by
        rw [show E.d0 + 1 - t = (E.d0 + 1 - (t + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega

end

end Restore

end Chazelle.Core
