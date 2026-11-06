module

public import Chazelle.Core.DownPhaseOracleChR2
public import Chazelle.Core.ShotListG

/-!
# WP-M (E7-B, RAM part 7): the descriptor of the chain of a stretch

`chainI = topCh ; betaI ; sI ; tauI ; descI` builds, for a stretch of the interior walk (`u` in
`170033`, `L` in `170037`), the chain `C = ch Q u L` and its model descriptor:

* `170089 := 2 L`, `170076 := sideS` (`sI`), `170077 := τ = tau Q u L` (`tauI`, the tour offset
  from which the interior walk reads the chain model walk);
* `descI`: the model descriptor at the allocator `B` (`170078`): `0`, the host handle `A₀`
  (`Host.whole n`), `cs`, `L`, `T`, the orientation bit (six words, the allocator raised by `6`).

`CEnv`: the state after `chainI` (`chainI_exec`); `DescOK`: the descriptor is well formed, of the
chain model of `C`, with a regular host, and survives memory changes above the allocator.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-! ## The programs -/

/-- `170089 := 2 L`; `170076 := S = sideS β` (`T` if the bit is set, else `2 L - T`). -/
def sI : Stmt :=
  .seq (block [.addN 170089 170037 170037])
    (.ifLtN 170075 170011 (block [.subN 170076 170089 170074]) (block [.copyN 170076 170074]))

/-- `170077 := τ = (J + 2 L - S) mod 2 L` (`J = 0` if `LeftInside`, else `L`). -/
def tauI : Stmt :=
  .seq (.ifLtN 170014 170011 (block [.copyN 170077 170037]) (block [.constN 170077 0]))
    (.seq (block [.addN 170077 170077 170089, .subN 170077 170077 170076])
      (.ifLtN 170077 170089 .skip (block [.subN 170077 170077 170089])))

/-- The model descriptor of the chain at the allocator (`170078`). -/
def descI : Stmt :=
  block [.copyN 170078 9999, .storeN 170078 170012,
    .addN 170090 170078 170011, .storeN 170090 170015,
    .addN 170090 170090 170011, .storeN 170090 170038,
    .addN 170090 170090 170011, .storeN 170090 170037,
    .addN 170090 170090 170011, .storeN 170090 170074,
    .addN 170090 170090 170011, .storeN 170090 170075,
    .constN 170091 6, .addN 9999 9999 170091]

/-- **The chain of a stretch and its descriptor.** -/
def chainI : Stmt := .seq topCh (.seq betaI (.seq sI (.seq tauI descI)))

/-! ## The descriptor -/

/-- **The descriptor at `B` is the model descriptor of the chain model of `C`**, well formed below
`E`, with a regular host. -/
def DescOK (P : Polygon) (m : ℕ → ℕ) (B : ℕ) (C : Chain) (E : ℕ) : Prop :=
  ModelDescAt m B (Qof P) (chainModel C) ∧ ModelDescWF P E m B ∧ ShotListG.HReg P m B

/-- **The descriptor survives** memory changes at or above its bound. -/
theorem DescOK.keep {P : Polygon} {m m' : ℕ → ℕ} {B E E' : ℕ} {C : Chain} (h : DescOK P m B C E)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') : DescOK P m' B C E' := by
  obtain ⟨hMD, hwf, hreg⟩ := h
  obtain ⟨hwf', hMD'⟩ := ShotListG.modelDescG_keep hwf hMD he hE
  exact ⟨hMD', hwf', ShotListG.hreg_keep hwf hMD hreg he⟩

/-- **The descriptor of the chain of a stretch**, from its six words. -/
theorem descOK_of {P : Polygon} (hG : GoodEnv P) {m : ℕ → ℕ} {A₀ B E : ℕ} {u L : ℕ}
    {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hu : u < (Qof P).n) (hH : HostAt m A₀ (Host.whole P.n))
    (hA : A₀ + 8 ≤ B) (hBE : B + 6 ≤ E) (m0 : m B = 0) (m1 : m (B + 1) = A₀)
    (m2 : m (B + 2) = cStart (Qof P) u L) (m3 : m (B + 3) = L)
    (m4 : m (B + 4) = (ch (Qof P) u L h1 h2).topIdx)
    (m5 : m (B + 5) = 1 ↔ (ch (Qof P) u L h1 h2).sideBeta = true) :
    DescOK P m B (ch (Qof P) u L h1 h2) E := by
  have hQ : (Qof P).n = P.n := qn'
  have hn : 1 ≤ P.n := by have := hG.1.1; omega
  have hpoly : (Host.whole P.n).poly (Qof P) = Qof P := by
    have := L41.poly_whole (Qof P) (by omega); rw [hQ] at this; exact this
  have hCD : ChainDescAt m (B + 1) (Qof P) (Host.whole P.n) (ch (Qof P) u L h1 h2) :=
    ⟨by rw [m1]; exact hH, by rw [hpoly]; rfl, m2, m3, m4, m5⟩
  have huniq : ∀ H C, ChainDescAt m (B + 1) (Qof P) H C → H = Host.whole P.n := fun H C hC =>
    NFLoc.hostAt_unique hC.1 (by rw [m1]; exact hH)
  refine ⟨Or.inl ⟨m0, _, _, hCD, rfl⟩, ⟨by omega, fun _ => ⟨by omega, fun H C hC => ?_⟩⟩,
    fun _ H C hC => ?_⟩
  · have e := huniq H C hC
    subst e
    refine ⟨by simp [Host.whole], L41.hostWF_whole hn, by rw [m1]; simp [Host.whole]; omega, ?_⟩
    rw [hC.2.1, hpoly, ← hC.2.2.1, m2]
    exact cStart_lt hu
  · rw [huniq H C hC, hQ]; exact L41.hostRegular_whole hn

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **The tour start.** -/
theorem sI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {C : Chain}
    (hL : c.nreg 170037 = C.m) (hT : c.nreg 170074 = C.topIdx) (hb1 : c.nreg 170075 ≤ 1)
    (hb : c.nreg 170075 = 1 ↔ C.sideBeta = true) (hmn : C.m + 1 ≤ P.n) :
    ∃ c' k, Exec P W sI c c' k ∧ k ≤ 4 ∧ c'.nreg 170089 = 2 * C.m ∧
      c'.nreg 170076 = C.sideS C.sideBeta ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170089 → r ≠ 170076 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  unfold sI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hL]; omega
  by_cases h : c.nreg 170075 < c.nreg 170011
  · have hf : C.sideBeta = false := by
      cases hc : C.sideBeta
      · rfl
      · have := hb.2 hc; rw [hS.r11] at h; omega
    refine spec_ifLtN_true (by config_simp; exact h) ?_
    exec_block
    refine ⟨by omega, by config_simp; rw [hL]; ring, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hL, hT]; unfold Chain.sideS; rw [hf]; simp; ring_nf
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · have ht : C.sideBeta = true := hb.1 (by rw [hS.r11] at h; omega)
    refine spec_ifLtN_false (by config_simp; exact h) ?_
    exec_block
    refine ⟨by omega, by config_simp; rw [hL]; ring, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hT]; unfold Chain.sideS; rw [ht]; simp
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The tour offset** of the interior walk's pass. -/
theorem tauI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hL : c.nreg 170037 = L) (h89 : c.nreg 170089 = 2 * L)
    (h76 : c.nreg 170076 = (ch (Qof P) u L h1 h2).sideS (ch (Qof P) u L h1 h2).sideBeta) :
    ∃ c' k, Exec P W tauI c c' k ∧ k ≤ 8 ∧ c'.nreg 170077 = tau (Qof P) u L h1 h2 ∧
      c'.nmem = c.nmem ∧ (∀ r, r ≠ 170077 → c'.nreg r = c.nreg r) := by
  have hW := hS.hW
  unfold hostWords at hW
  have hQ : (Qof P).n = P.n := qn'
  have hSle := (ch (Qof P) u L h1 h2).sideS_lt (ch (Qof P) u L h1 h2).sideBeta
  rw [ch_m] at hSle
  -- the start of the tour position
  obtain ⟨c₁, k₁, e₁, hk₁, a77, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (.ifLtN 170014 170011 (block [.copyN 170077 170037]) (block [.constN 170077 0])) c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 170077 = jStart (Qof P) L ∧ (∀ r, r ≠ 170077 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    by_cases h : c.nreg 170014 < c.nreg 170011
    · have hL' : ¬ Mountain.LeftInside (Qof P) := fun h' => by
        have := hS.lb.2 h'; rw [hS.r11] at h; omega
      refine spec_ifLtN_true h ?_
      exec_block
      refine ⟨by omega, ?_, fun r hr => ?_, rfl⟩
      · config_simp; rw [hL]; unfold jStart; rw [ite_eq_right hL']
      · simp only [Config.nreg_mk, upd, ite_eq_right hr]
    · have hL' : Mountain.LeftInside (Qof P) := hS.lb.1 (by
        rw [hS.r11] at h; have := hS.lb1; omega)
      refine spec_ifLtN_false h ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, fun r hr => ?_, rfl⟩
      · config_simp; unfold jStart; rw [ite_eq_left hL']
      · simp only [Config.nreg_mk, upd, ite_eq_right hr]
  have hJ : jStart (Qof P) L ≤ L := by unfold jStart; split_ifs <;> omega
  have w₁ := e₁.wb_right
  have b89 : c₁.nreg 170089 = 2 * L := by rw [r₁ _ (by decide)]; exact h89
  have b76 : c₁.nreg 170076 = (ch (Qof P) u L h1 h2).sideS (ch (Qof P) u L h1 h2).sideBeta := by
    rw [r₁ _ (by decide)]; exact h76
  have htau : tau (Qof P) u L h1 h2 = (jStart (Qof P) L + 2 * L -
      (ch (Qof P) u L h1 h2).sideS (ch (Qof P) u L h1 h2).sideBeta) % (2 * L) := rfl
  obtain ⟨c₂, k₂, e₂, hk₂, hτ, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W
      (.seq (block [.addN 170077 170077 170089, .subN 170077 170077 170076])
        (.ifLtN 170077 170089 .skip (block [.subN 170077 170077 170089]))) c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
      c₂.nreg 170077 = tau (Qof P) u L h1 h2 ∧ (∀ r, r ≠ 170077 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem := by
    refine spec_seq ?_
    exec_block
    · config_simp; rw [a77, b89]; omega
    by_cases h : jStart (Qof P) L + 2 * L -
        (ch (Qof P) u L h1 h2).sideS (ch (Qof P) u L h1 h2).sideBeta < 2 * L
    · refine spec_ifLtN_true (by config_simp; rw [a77, b89, b76]; exact h) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, fun r hr => ?_, rfl⟩
      · config_simp; rw [a77, b89, b76, htau, Nat.mod_eq_of_lt h]
      · simp only [Config.nreg_mk, upd, ite_eq_right hr]
    · refine spec_ifLtN_false (by config_simp; rw [a77, b89, b76]; exact h) ?_
      exec_block
      refine ⟨by omega, ?_, fun r hr => ?_, rfl⟩
      · config_simp; rw [a77, b89, b76, htau, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
      · simp only [Config.nreg_mk, upd, ite_eq_right hr]
  refine ⟨c₂, _, .seq e₁ e₂, by omega, hτ, by rw [m₂, m₁], fun r hr => ?_⟩
  rw [r₂ r hr, r₁ r hr]

/-- **The descriptor.** -/
theorem descI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hAW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W descI c c' k ∧ k = 14 ∧ c'.nreg 170078 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      c'.nmem (c.nreg ALLOC) = 0 ∧ c'.nmem (c.nreg ALLOC + 1) = s.A₀ ∧
      c'.nmem (c.nreg ALLOC + 2) = c.nreg 170038 ∧ c'.nmem (c.nreg ALLOC + 3) = c.nreg 170037 ∧
      c'.nmem (c.nreg ALLOC + 4) = c.nreg 170074 ∧ c'.nmem (c.nreg ALLOC + 5) = c.nreg 170075 ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 170078 → r ≠ 170090 → r ≠ 170091 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hAW ⊢
  have h11 := hS.r11
  have h12 := hS.r12
  have h15 := hS.r15
  unfold descI
  exec_block
  all_goals first | omega | (config_simp; rw [h11]; omega) | (config_simp; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r r1 r2 r3 r4 => ?_, rfl, rfl,
    rfl⟩
  all_goals simp only [Config.nreg_mk, Config.nmem_mk, h11, h12, h15]
  all_goals simp (disch := omega) only [Machine.upd_apply, ite_eq_left, ite_eq_right, ↓reduceIte]

/-! ## The whole chain -/

/-- The registers `chainI` writes (besides the allocator). -/
def Bchain (r : ℕ) : Bool :=
  decide (170038 ≤ r ∧ r < 170042) || decide (170046 ≤ r ∧ r < 170070) ||
    decide (170074 ≤ r ∧ r < 170092) || Bk r

theorem wr_chain4 : wr Bchain (.seq topCh (.seq betaI (.seq sI tauI))) = true := by
  have h1 := SweepPrim.wr_mono wr_topCh (B' := Bchain) (fun r hr => by
    simp only [Bch, Bchain, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; omega)
  have h2 := SweepPrim.wr_mono wr_betaI (B' := Bchain) (fun r hr => by
    simp only [Bbeta, Bchain, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; omega)
  simp only [wr, sI, tauI, block, wrOK, h1, h2, Bool.and_true, Bool.true_and]
  decide

/-- The registers the state of a chain consists of. -/
def CRegs (r : ℕ) : Prop :=
  (170000 ≤ r ∧ r < 170030) ∨ (170033 ≤ r ∧ r < 170039) ∨ (170074 ≤ r ∧ r < 170080) ∨
    r = 170089

/-- **The state after `chainI`** for the stretch of `L` edges of the interior walk from `u`. -/
structure CEnv (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (u L : ℕ) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (c : Config) : Prop where
  env : SEnv P W O s c
  hu : u < P.n
  r33 : c.nreg 170033 = u
  r37 : c.nreg 170037 = L
  r38 : c.nreg 170038 = cStart (Qof P) u L
  r74 : c.nreg 170074 = (ch (Qof P) u L h1 h2).topIdx
  r75 : c.nreg 170075 = 1 ↔ (ch (Qof P) u L h1 h2).sideBeta = true
  r75' : c.nreg 170075 ≤ 1
  r76 : c.nreg 170076 = (ch (Qof P) u L h1 h2).sideS (ch (Qof P) u L h1 h2).sideBeta
  r77 : c.nreg 170077 = tau (Qof P) u L h1 h2
  r79 : c.nreg 170079 = (cStart (Qof P) u L + (ch (Qof P) u L h1 h2).topIdx) % (Qof P).n
  r89 : c.nreg 170089 = 2 * L
  desc : DescOK P c.nmem (c.nreg 170078) (ch (Qof P) u L h1 h2) (c.nreg ALLOC)
  dlo : s.A₀ + 8 ≤ c.nreg 170078

/-- **The state of a chain survives** steps that keep its registers, the memory below the
allocator, and do not lower the allocator. -/
theorem CEnv.keep {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} {c c' : Config}
    (h : CEnv P W O s u L h1 h2 c) (hr : ∀ r, CRegs r → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    CEnv P W O s u L h1 h2 c' := by
  have k : ∀ r, CRegs r → c'.nreg r = c.nreg r := hr
  refine ⟨h.env.keep (fun r h1 h2 => k r (Or.inl ⟨h1, h2⟩)) hm ha, h.hu, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k _ (by unfold CRegs; omega)]; exact h.r33
  · rw [k _ (by unfold CRegs; omega)]; exact h.r37
  · rw [k _ (by unfold CRegs; omega)]; exact h.r38
  · rw [k _ (by unfold CRegs; omega)]; exact h.r74
  · rw [k _ (by unfold CRegs; omega)]; exact h.r75
  · rw [k _ (by unfold CRegs; omega)]; exact h.r75'
  · rw [k _ (by unfold CRegs; omega)]; exact h.r76
  · rw [k _ (by unfold CRegs; omega)]; exact h.r77
  · rw [k _ (by unfold CRegs; omega)]; exact h.r79
  · rw [k _ (by unfold CRegs; omega)]; exact h.r89
  · rw [k _ (by unfold CRegs; omega)]; exact h.desc.keep hm ha
  · rw [k _ (by unfold CRegs; omega)]; exact h.dlo

/-- **The chain of a stretch and its descriptor.** -/
theorem chainI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (hcap : L ≤ 2 ^ (s.m₀ s.h - 1)) (hAW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W chainI c c' k ∧ k ≤ 1204 * Nat.log 2 (2 * L) + 2500 ∧ 14 ≤ k ∧
      CEnv P W O s u L h1 h2 c' ∧ c'.nreg 170078 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bchain r = false → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, Bchain r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  have hQ : (Qof P).n = P.n := qn'
  have h2' : L + 1 ≤ P.n := by rw [← hQ]; exact h2
  set C := ch (Qof P) u L h1 h2 with hCd
  obtain ⟨c₁, k₁, e₁, hk₁, S₁, a38, a79n, a74, a79, F₁⟩ := topCh_exec c hw hS hu hL hun h1 h2 hcap
  have f₁ : ∀ r, Bch r = false → c₁.nreg r = c.nreg r := F₁.1
  obtain ⟨c₂, k₂, e₂, hk₂, b75', b75, m₂, F₂⟩ := betaI_exec c₁ e₁.wb_right S₁ (C := C) rfl a74
    (by rw [← a79]; rfl)
  have f₂ : ∀ r, Bbeta r = false → c₂.nreg r = c₁.nreg r := F₂.1
  have S₂ : SEnv P W O s c₂ := S₁.keep (fun r r1 r2 => f₂ r (by
    unfold Bbeta Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fun a _ => by rw [m₂]) (by rw [f₂ _ (by decide)])
  have b37 : c₂.nreg 170037 = C.m := by
    rw [f₂ _ (by decide), f₁ _ (by decide)]; exact hL
  have b74 : c₂.nreg 170074 = C.topIdx := by rw [f₂ _ (by decide)]; exact a74
  obtain ⟨c₃, k₃, e₃, hk₃, d89, d76, m₃, r₃⟩ := sI_exec c₂ e₂.wb_right S₂ b37 b74 b75' b75
    (by rw [ch_m]; exact h2')
  have S₃ : SEnv P W O s c₃ := S₂.keep (fun r r1 r2 => r₃ r (by omega) (by omega))
    (fun a _ => by rw [m₃]) (by rw [r₃ _ (by decide) (by decide)])
  obtain ⟨c₄, k₄, e₄, hk₄, d77, m₄, r₄⟩ := tauI_exec c₃ e₃.wb_right S₃ (h1 := h1) (h2 := h2)
    (by rw [r₃ _ (by decide) (by decide)]; exact b37) (by rw [d89, ch_m]) d76
  have S₄ : SEnv P W O s c₄ := S₃.keep (fun r r1 r2 => r₄ r (by omega))
    (fun a _ => by rw [m₄]) (by rw [r₄ _ (by decide)])
  have ex4 : Exec P W (.seq topCh (.seq betaI (.seq sI tauI))) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have F₄ := exec_frameB ex4 wr_chain4
  have hA4 : c₄.nreg ALLOC = c.nreg ALLOC := F₄.1 _ (by decide)
  obtain ⟨c₅, k₅, e₅, hk₅, g78, gA, g0, g1, g2, g3, g4, g5, gm, gr, grr, grm, go⟩ :=
    descI_exec c₄ e₄.wb_right S₄ (by rw [hA4]; exact hAW)
  -- register values at `c₄`
  have v : ∀ r, Bchain r = false → c₄.nreg r = c.nreg r := F₄.1
  have q38 : c₄.nreg 170038 = cStart (Qof P) u L := by
    rw [r₄ _ (by decide), r₃ _ (by decide) (by decide), f₂ _ (by decide)]; exact a38
  have q37 : c₄.nreg 170037 = L := by rw [v _ (by decide)]; exact hL
  have q33 : c₄.nreg 170033 = u := by rw [v _ (by decide)]; exact hu
  have q74 : c₄.nreg 170074 = C.topIdx := by
    rw [r₄ _ (by decide), r₃ _ (by decide) (by decide)]; exact b74
  have q75 : c₄.nreg 170075 = c₂.nreg 170075 := by
    rw [r₄ _ (by decide), r₃ _ (by decide) (by decide)]
  have q79 : c₄.nreg 170079 = c₁.nreg 170079 := by
    rw [r₄ _ (by decide), r₃ _ (by decide) (by decide), f₂ _ (by decide)]
  have q89 : c₄.nreg 170089 = 2 * L := by rw [r₄ _ (by decide), d89, ch_m]
  have q76 : c₄.nreg 170076 = C.sideS C.sideBeta := by rw [r₄ _ (by decide)]; exact d76
  have hm4 : c₄.nmem = c.nmem := F₄.2.2.1
  have S₅ : SEnv P W O s c₅ := S₄.keep (fun r r1 r2 => gr r (by omega) (by omega) (by omega)
    (by unfold ALLOC; omega)) gm (by rw [gA]; omega)
  have hal := S₄.alloc
  have ex : Exec P W chainI c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have keep5 : ∀ r, r ≠ 170078 → r ≠ 170090 → r ≠ 170091 → r ≠ ALLOC →
      c₅.nreg r = c₄.nreg r := gr
  have hlog : Nat.log 2 (2 * L) ≥ 0 := Nat.zero_le _
  refine ⟨c₅, _, ex, by omega, by omega, ⟨S₅, hun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [g78, hA4], by rw [gA, hA4], fun a ha => ?_, fun r hr hra => ?_, fun r hr => ?_,
    by rw [grm, F₄.2.2.2.1], by rw [go, F₄.2.2.2.2]⟩
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q33
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q37
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q38
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q74
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide), q75]; exact b75
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide), q75]; exact b75'
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q76
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact d77
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide), q79]; exact a79.symm
  · rw [keep5 _ (by decide) (by decide) (by decide) (by decide)]; exact q89
  · rw [g78, gA]
    refine descOK_of (u := u) (L := L) (h1 := h1) (h2 := h2) S₄.good (by rw [hQ]; exact hun)
      (S₅.hostAt) hal (by omega) g0 g1 ?_ ?_ ?_ ?_
    · rw [g2, q38]
    · rw [g3, q37]
    · rw [g4, q74]
    · rw [g5, q75]; exact b75
  · rw [g78]; exact hal
  · rw [gm a (by rw [hA4]; exact ha), hm4]
  · have h78 : r ≠ 170078 := fun h => by subst h; revert hr; decide
    have h90 : r ≠ 170090 := fun h => by subst h; revert hr; decide
    have h91 : r ≠ 170091 := fun h => by subst h; revert hr; decide
    rw [gr r h78 h90 h91 hra, v r hr]
  · rw [grr, F₄.2.1 r hr]

end exec

end

end IOrc

end Chazelle.Core
