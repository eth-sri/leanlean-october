module

public import Chazelle.Core.DownPhaseOracleShB

/-!
# WP-M (E7-B, RAM part 10): one shot of the interior shooter at a chain arc

`shotI sh`: with the ends of a chain arc of the chain `C` of a stretch in `140001 … 140004`, the
shooter's inputs (the descriptor `170078`, the symbolic origin `170020 …`, the direction, `γ`, the
context handle) into band `bShoot`, the chain shooter `sh`, then the update of the running best
hit (`updI`).  `shotI_exec`: the running best then describes the first hit on the union with the
point set of the chain arc (`CArc`); the state of the chain survives (`CEnv`); the frame is that of
the interior oracles (`ioBands`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## Frames of the interior oracles -/

/-- **A register frame inside the adapter's bands is a frame of the interior oracles.** -/
theorem frameIO_of_frameB {B : ℕ → Bool} (hB : ∀ r, B r = true → bandOf r ∈ ioBands ∧ r ≠ ALLOC)
    {c c' : Config} (h : FrameB B c c') (k : ℕ) : Frame ioBands c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := h.1 _ (by
    cases hb : B ALLOC
    · rfl
    · exact absurd rfl (hB _ hb).2)
  refine ⟨fun r hr _ => h.1 r ?_, fun r hr => h.2.1 r ?_, fun a _ => by rw [h.2.2.1],
    fun a _ => by rw [h.2.2.2.1], h.2.2.2.2, by rw [hA], by rw [hA]; omega⟩
  · cases hb : B r
    · rfl
    · exact absurd (hB r hb).1 hr
  · cases hb : B r
    · rfl
    · exact absurd (hB r hb).1 hr

/-- Registers of band `17` or of the kernel are in the adapter's bands. -/
theorem io_of_band {r : ℕ} (h : (170000 ≤ r ∧ r < 180000) ∨ (10000 ≤ r ∧ r < 10500) ∨
    (140000 ≤ r ∧ r < 150000)) : bandOf r ∈ ioBands ∧ r ≠ ALLOC := by
  refine ⟨?_, by unfold ALLOC; omega⟩
  unfold bandOf ioBands oracleBands kernelBands
  rcases h with h | h | h
  · rw [show r / 10000 = 17 by omega]; decide
  · rw [show r / 10000 = 1 by omega]; decide
  · rw [show r / 10000 = 14 by omega]; decide

/-! ## The program -/

/-- The shooter's inputs other than the arc ends. -/
def shSetL : List (ℕ × ℕ) :=
  [(140000, 170078), (140005, 170020), (140006, 170021), (140007, 170022), (140008, 170008),
    (140009, 170009), (140013, 170013)]

/-- **One shot at a chain arc** (its ends in `140001 … 140004`). -/
def shotI (sh : Stmt) : Stmt := .seq (block (copies shSetL)) (.seq sh updI)

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

theorem shSet_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W (block (copies shSetL)) c c' 7 ∧ c'.nreg 140000 = c.nreg 170078 ∧
      c'.nreg 140005 = c.nreg 170020 ∧ c'.nreg 140006 = c.nreg 170021 ∧
      c'.nreg 140007 = c.nreg 170022 ∧ c'.nreg 140008 = c.nreg 170008 ∧
      c'.nreg 140009 = c.nreg 170009 ∧ c'.nreg 140013 = c.nreg 170013 ∧
      (∀ r, r ≠ 140000 → (r < 140005 ∨ 140009 < r) → r ≠ 140013 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) shSetL c hw
    (by intro p hp q hq; simp only [shSetL, List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by simp [shSetL])
  refine ⟨c', e, h1 (140000, 170078) (by simp [shSetL]), h1 (140005, 170020) (by simp [shSetL]),
    h1 (140006, 170021) (by simp [shSetL]), h1 (140007, 170022) (by simp [shSetL]),
    h1 (140008, 170008) (by simp [shSetL]), h1 (140009, 170009) (by simp [shSetL]),
    h1 (140013, 170013) (by simp [shSetL]), fun r r1 r2 r3 => h2 r ?_, h3, h4, h5, h6⟩
  simp only [shSetL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **The context of the up-phase data** at the allocator, from the static environment. -/
theorem SEnv.ctx {c : Config} (hS : SEnv P W O s c) :
    (gradeCtx O).holds P c.nmem s.h (c.nreg ALLOC) ∧
      s.γ ≤ (gradeCtx O).cap P c.nmem s.h := by
  have hloc : (gradeCtx O).holds P c.nmem s.h s.A₀ :=
    (gradeCtx O).local_ P s.m₀ c.nmem s.h s.A₀ (fun a ha => (hS.mem a ha).symm) hS.grade
  refine ⟨(gradeCtx O).mono P _ _ _ _ (by have := hS.alloc; omega) hloc, ?_⟩
  have hh := (ShootCut.grade_low hS.grade).1
  show s.γ ≤ 2 ^ (c.nmem s.h - 1)
  rw [hS.mem _ (by omega)]
  exact hS.cap

/-- **One shot at a chain arc.** -/
theorem shotI_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hC : CEnv P W O s u L h1 h2 c)
    {sa ea : WPos} {Ap Sp : Set Point}
    (ha1 : c.nreg 140001 = sa.edge) (ha2 : c.nreg 140002 = sa.hgt)
    (ha3 : c.nreg 140003 = ea.edge) (ha4 : c.nreg 140004 = ea.hgt)
    (harc : CArc (Qof P) (ch (Qof P) u L h1 h2) sa ea s.γ Ap)
    (hAC : Ap ⊆ (ch (Qof P) u L h1 h2).set)
    (ho1 : |(s.o.eval (Qof P)).1| ≤ Jordan.coordBound (Qof P))
    (ho2 : |(s.o.eval (Qof P)).2| ≤ Jordan.coordBound (Qof P)) (hol : s.o.Lt P.n)
    (hoA : s.o.eval (Qof P) ∉ Ap)
    (hB : BestI P c Sp (s.o.eval (Qof P)) (dirOf s.dir))
    (hroom : c.nreg ALLOC + F s.γ + 700 ≤ W) :
    ∃ c' k, Exec P W (shotI sh) c c' k ∧ k ≤ F s.γ + 700 ∧
      BestI P c' (Sp ∪ Ap) (s.o.eval (Qof P)) (dirOf s.dir) ∧ CEnv P W O s u L h1 h2 c' ∧
      Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → Bupd r = false → c'.nreg r = c.nreg r) := by
  have hS := hC.env
  have hG := hS.good
  have hQ : (Qof P).n = P.n := qn'
  have hW := hS.hW
  set C := ch (Qof P) u L h1 h2 with hCd
  -- the inputs
  obtain ⟨c₁, e₁, i0, i5, i6, i7, i8, i9, i13, r₁, rr₁, m₁, rm₁, o₁⟩ := shSet_exec (P := P) c hw
  have w₁ := e₁.wb_right
  have k₁ : ∀ r, 170000 ≤ r → c₁.nreg r = c.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega)
  have F₁ : Frame ioBands c c₁ 7 := by
    refine frameIO_of_frameB (B := fun r => decide (140000 ≤ r ∧ r < 140014))
      (fun r hr => io_of_band (Or.inr (Or.inr (by simp at hr; omega)))) ⟨fun r hr => ?_,
        fun r _ => by rw [rr₁], m₁, rm₁, o₁⟩ 7
    simp only [decide_eq_false_iff_not] at hr
    exact r₁ r (by omega) (by omega) (by omega)
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => k₁ r h1) (fun a _ => by rw [m₁])
    (by rw [r₁ _ (by decide) (by decide) (by decide)])
  have D₁ : DescOK P c₁.nmem (c₁.nreg 140000) C (c₁.nreg ALLOC) := by
    rw [i0, m₁, r₁ _ (by decide) (by decide) (by decide)]; exact hC.desc
  obtain ⟨hMD, hMWF, hReg⟩ := D₁
  obtain ⟨hctx, hcap⟩ := S₁.ctx
  obtain ⟨sP, eP, sE, eE, sI', eI, hwt, hset⟩ := harc
  have horg : OriginIn c₁ (bandReg bShoot 5) (.sym s.o) := by
    show SymPtIn c₁ 140005 s.o
    exact NFLoc.symPtIn_copy hS.org i5 i6 i7
  have hinner : (chainModel C).InnerPt (s.o.eval (Qof P)) :=
    innerPt_chain C (by rw [hCd, ch_P]; exact ho1) (by rw [hCd, ch_P]; exact ho2)
  have b1 : c₁.nreg 140001 = sa.edge := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha1
  have b2 : c₁.nreg 140002 = sa.hgt := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha2
  have b3 : c₁.nreg 140003 = ea.edge := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha3
  have b4 : c₁.nreg 140004 = ea.hgt := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha4
  have e1 : rd c₁ bShoot 1 = sa.edge := b1
  have e2 : rd c₁ bShoot 2 = sa.hgt := b2
  have e3 : rd c₁ bShoot 3 = ea.edge := b3
  have e4 : rd c₁ bShoot 4 = ea.hgt := b4
  have hsa : (⟨c₁.nreg 140001, c₁.nreg 140002⟩ : WPos) = sa := by rw [b1, b2]
  have hea : (⟨c₁.nreg 140003, c₁.nreg 140004⟩ : WPos) = ea := by rw [b3, b4]
  have h9 : c₁.nreg 140009 = s.γ := by rw [i9]; exact hS.r9
  have h13 : c₁.nreg 140013 = s.h := by rw [i13]; exact hS.r13
  have h8 : c₁.nreg 140008 = s.dir := by rw [i8]; exact hS.r8
  -- the chain shooter
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hsh P W c₁ w₁ ⟨hG, hW,
    by show (gradeCtx O).holds P c₁.nmem (c₁.nreg 140013) (c₁.nreg ALLOC); rw [h13]; exact hctx,
    by show c₁.nreg 140009 ≤ (gradeCtx O).cap P c₁.nmem (c₁.nreg 140013); rw [h9, h13]; exact hcap,
    hMWF, hReg, chainModel C, hMD, okModel_sub hG,
    by show ProperPos _ _ _ ⟨c₁.nreg 140001, c₁.nreg 140002⟩; rw [hsa, ← hQ]; exact sP,
    by show ProperPos _ _ _ ⟨c₁.nreg 140003, c₁.nreg 140004⟩; rw [hea, ← hQ]; exact eP,
    by show c₁.nreg 140001 < _; rw [b1]; exact sE,
    by show c₁.nreg 140003 < _; rw [b3]; exact eE,
    by show c₁.nreg 140002 = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P)
          ⟨c₁.nreg 140001, c₁.nreg 140002⟩)
       rw [hsa, b2]; exact sI',
    by show c₁.nreg 140004 = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P)
          ⟨c₁.nreg 140003, c₁.nreg 140004⟩)
       rw [hea, b4]; exact eI,
    by show _ ≤ c₁.nreg 140009; rw [e1, e2, e3, e4, h9]; exact hwt,
    .sym s.o, hol, horg, Or.inr ⟨hinner, fun x hx => by cases hx⟩,
    by show s.o.eval (Qof P) ∉ _; rw [e1, e2, e3, e4, hset]; exact hoA⟩
    (by show c₁.nreg ALLOC + F (c₁.nreg 140009) ≤ W
        rw [h9, r₁ _ (by decide) (by decide) (by decide)]; omega)
  have hp := hpost (chainModel C) (.sym s.o) hMD horg
  have e8 : rd c₁ bShoot 8 = s.dir := h8
  rw [e1, e2, e3, e4, hset, e8] at hp
  obtain ⟨hhit, hno⟩ := hp
  have w₂ := e₂.wb_right
  -- the registers survive the shooter
  have g₂ : ∀ r, 170000 ≤ r → r < 180000 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by unfold bandOf; rw [show r / 10000 = 17 by omega]; decide)
      (by unfold ALLOC; omega)
  have hA₂ := F₂.2.2.2.2.2.1
  have C₂ : CEnv P W O s u L h1 h2 c₂ := (hC.keep (fun r hr => by
      rw [k₁ r (by unfold CRegs at hr; omega)]) (fun a _ => by rw [m₁])
      (by rw [r₁ _ (by decide) (by decide) (by decide)])).keep
    (fun r hr => g₂ r (by unfold CRegs at hr; omega) (by unfold CRegs at hr; omega))
    F₂.2.2.1 hA₂
  have S₂ := C₂.env
  have hR₂ : HRegs P W c₂ (cStart (Qof P) u L) L (C.sideS C.sideBeta)
      ((cStart (Qof P) u L + C.topIdx) % (Qof P).n) := ⟨S₂.r10, S₂.r11, S₂.r12, C₂.r37,
    C₂.r38, C₂.r76, C₂.r79, C₂.r89, by rw [← qn']; exact cStart_lt (by rw [qn']; exact C₂.hu),
    by have := C.sideS_lt C.sideBeta; rw [hCd, ch_m] at this; exact this, h1,
    by rw [← qn']; exact h2, by unfold hostWords at hW; exact hW⟩
  have hB₂ : BestI P c₂ Sp (s.o.eval (Qof P)) (dirOf s.dir) := (hB.keep (fun r h1 h2 =>
    k₁ r (by omega))).keep (fun r h1 h2 => g₂ r (by omega) (by omega))
  have d8 : c₂.nreg 170008 = s.dir := S₂.r8
  -- the update
  have hcm : (chainModel C).W.n = 2 * L + 7 := cm_n'
  obtain ⟨c₃, k₃, e₃, hk₃, hB₃, F₃⟩ := updI_exec (P := P) c₂ w₂ hG hR₂ (C := C) ch_P rfl ch_m rfl
    rfl (e := c₂.nreg 140011) (h := c₂.nreg 140012) rfl rfl
    (fun hf => by obtain ⟨_, _, _, hlt, _⟩ := hhit hf; rw [hcm] at hlt; exact hlt)
    (A := Ap) (Sp := Sp) (z := s.o.eval (Qof P)) (by rw [d8]) hAC
    (fun hf => by
      obtain ⟨t, hft, hpp, hlt, hpos⟩ := hhit hf
      exact ⟨t, hft, hpp, hpos⟩) hno hB₂
  have f₃ : ∀ r, Bupd r = false → c₃.nreg r = c₂.nreg r := F₃.1
  have ex : Exec P W (shotI sh) c c₃ (7 + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have hk₂' : k₂ ≤ F s.γ := by have := hk₂; simp only [rd, bandReg] at this; rw [← h9]; exact this
  have F₃' : Frame ioBands c₂ c₃ k₃ := frameIO_of_frameB (B := Bupd) (fun r hr => io_of_band (by
    simp only [Bupd, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₃ k₃
  have F₂' : Frame ioBands c₁ c₂ k₂ := F₂.mono oracleBands_sub_io le_rfl
  refine ⟨c₃, _, ex, by omega, hB₃, C₂.keep (fun r hr => f₃ r (by
      unfold CRegs at hr; simp only [Bupd, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
      (fun a _ => by rw [F₃.2.2.1]) (by rw [f₃ _ (by decide)]),
    ((F₁.trans F₂').trans F₃').mono (by simp) (by omega), fun r h1 h2 hr => ?_⟩
  rw [f₃ r hr, g₂ r h1 h2, k₁ r h1]

end exec

end

end IOrc

end Chazelle.Core
