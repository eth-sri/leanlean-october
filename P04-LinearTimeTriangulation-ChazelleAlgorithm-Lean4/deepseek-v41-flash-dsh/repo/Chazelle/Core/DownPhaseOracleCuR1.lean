module

public import Chazelle.Core.DownPhaseOracleCuM4

/-!
# WP-M (E7-B, RAM part 15): one call of the chain cutter, recorded as a slot

* `arcOneC`, `arcTwoAC`, `arcTwoBC`: the ends of the chain arcs of a sub-query in `150001 … 150004`
  (as `arcOne`, `arcTwoA`, `arcTwoB` for the shooter), with the stretch starts `g₀` (in the chain
  walk, `170145`) and `u₀` (in the interior walk, `170146`);
* `cutR cu k`: the cutter's other inputs (descriptor `170078`, `γ`, context handle) into band
  `bCut`, the chain cutter `cu`, and the record of slot `k` (`170200 + 5 k …`: flag, list address,
  number of pieces, `g₀`, `u₀`).

`cutR_exec`: the slot state advances by the valid slot of the call (`SlotSt.add`); the state of
the chain survives (`CEnv`); the frame is that of the interior oracles.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-- Registers of bands `17`, `14`, `15` and of the kernel are in the adapter's bands. -/
theorem io_of_band' {r : ℕ} (h : (170000 ≤ r ∧ r < 180000) ∨ (10000 ≤ r ∧ r < 10500) ∨
    (140000 ≤ r ∧ r < 160000)) : bandOf r ∈ ioBands ∧ r ≠ ALLOC := by
  refine ⟨?_, by unfold ALLOC; omega⟩
  unfold bandOf ioBands oracleBands kernelBands
  rcases h with h | h | h
  · rw [show r / 10000 = 17 by omega]; decide
  · rw [show r / 10000 = 1 by omega]; decide
  · rcases (show r < 150000 ∨ 150000 ≤ r by omega) with h' | h'
    · rw [show r / 10000 = 14 by omega]; decide
    · rw [show r / 10000 = 15 by omega]; decide

/-! ## The programs -/

/-- The one chain arc `⟨6 + τ, sh⟩ … ⟨6 + τ + ee, eh⟩`, stretch from `6 + τ` and `u`. -/
def arcOneC : Stmt :=
  block [.constN 170133 6, .addN 150001 170133 170077, .copyN 150002 170034,
    .addN 150003 150001 170035, .copyN 150004 170036, .copyN 170145 150001, .copyN 170146 170033]

/-- The first of two chain arcs: `⟨6 + τ, sh⟩ … ⟨2 L + 6, 0⟩`, stretch from `6 + τ` and `u`. -/
def arcTwoAC : Stmt :=
  block [.constN 170133 6, .addN 150001 170133 170077, .copyN 150002 170034,
    .addN 150003 170089 170133, .constN 150004 0, .copyN 170145 150001, .copyN 170146 170033]

/-- The second of two chain arcs: `⟨6, 0⟩ … ⟨6 + (ee - (2 L - τ)), eh⟩`, stretch from `6` and
`(u + (2 L - τ)) mod n`. -/
def arcTwoBC : Stmt :=
  .seq (block [.constN 170133 6, .copyN 150001 170133, .constN 150002 0, .subN 170142 170089 170077,
      .subN 170143 170035 170142, .addN 150003 170133 170143, .copyN 150004 170036,
      .copyN 170145 170133, .addN 170146 170033 170142])
    (.ifLtN 170146 170010 .skip (block [.subN 170146 170146 170010]))

/-- The registers an arc block of the cutter writes. -/
def BarcC (r : ℕ) : Bool :=
  decide (150000 ≤ r ∧ r < 150014) ||
    decide (r = 170133 ∨ r = 170142 ∨ r = 170143 ∨ r = 170145 ∨ r = 170146)

theorem wr_arcOneC : wr BarcC arcOneC = true := by decide
theorem wr_arcTwoAC : wr BarcC arcTwoAC = true := by decide

theorem barcC_io {r : ℕ} (h : BarcC r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band' (by simp only [BarcC, Bool.or_eq_true, decide_eq_true_eq] at h; omega)

/-- The cutter's inputs other than the arc ends. -/
def cuSetL : List (ℕ × ℕ) := [(150000, 170078), (150009, 170009), (150013, 170013)]

/-- **One call of the chain cutter.** -/
def cutI (cu : Stmt) : Stmt := .seq (block (copies cuSetL)) cu

/-- **Recording slot `k`**: flag, list address, number of pieces, stretch starts. -/
def recS (k : ℕ) : Stmt :=
  block [.constN (170200 + 5 * k) 1, .copyN (170201 + 5 * k) 150010,
    .loadN (170202 + 5 * k) 150010, .copyN (170203 + 5 * k) 170145,
    .copyN (170204 + 5 * k) 170146]

/-- **One call of the chain cutter, recorded as slot `k`.** -/
def cutR (cu : Stmt) (k : ℕ) : Stmt := .seq (cutI cu) (recS k)

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

theorem arcOneC_exec (c : Config) (hw : WordsBounded W c) {τ sh ee eh u : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h33 : c.nreg 170033 = u) (hW : 6 + τ + ee ≤ W) :
    ∃ c' k, Exec P W arcOneC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧ c'.nreg 150002 = sh ∧
      c'.nreg 150003 = 6 + τ + ee ∧ c'.nreg 150004 = eh ∧ c'.nreg 170145 = 6 + τ ∧
      c'.nreg 170146 = u ∧ FrameB BarcC c c' := by
  suffices h : ∃ c' k, Exec P W arcOneC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧
      c'.nreg 150002 = sh ∧ c'.nreg 150003 = 6 + τ + ee ∧ c'.nreg 150004 = eh ∧
      c'.nreg 170145 = 6 + τ ∧ c'.nreg 170146 = u by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7, exec_frameB e wr_arcOneC⟩
  unfold arcOneC
  exec_block
  · omega
  · config_simp; rw [h77]; omega
  · config_simp; rw [h77, h35]; omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h77, h34, h35, h36, h33]

theorem arcTwoAC_exec (c : Config) (hw : WordsBounded W c) {τ sh L u : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h89 : c.nreg 170089 = 2 * L)
    (h33 : c.nreg 170033 = u) (hW : 2 * L + 6 ≤ W) (hτ : 6 + τ ≤ W) :
    ∃ c' k, Exec P W arcTwoAC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧ c'.nreg 150002 = sh ∧
      c'.nreg 150003 = 2 * L + 6 ∧ c'.nreg 150004 = 0 ∧ c'.nreg 170145 = 6 + τ ∧
      c'.nreg 170146 = u ∧ FrameB BarcC c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoAC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧
      c'.nreg 150002 = sh ∧ c'.nreg 150003 = 2 * L + 6 ∧ c'.nreg 150004 = 0 ∧
      c'.nreg 170145 = 6 + τ ∧ c'.nreg 170146 = u by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7, exec_frameB e wr_arcTwoAC⟩
  unfold arcTwoAC
  exec_block
  · omega
  · config_simp; rw [h77]; omega
  · config_simp; rw [h89]; omega
  · omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h77, h34, h89, h33]

theorem arcTwoBC_exec (c : Config) (hw : WordsBounded W c) {τ ee eh L u n : ℕ}
    (h77 : c.nreg 170077 = τ) (h35 : c.nreg 170035 = ee) (h36 : c.nreg 170036 = eh)
    (h89 : c.nreg 170089 = 2 * L) (h33 : c.nreg 170033 = u) (h10 : c.nreg 170010 = n)
    (hu : u < n) (hL₁ : 2 * L - τ < n) (hW : 6 + ee ≤ W) (hnW : 2 * n ≤ W) :
    ∃ c' k, Exec P W arcTwoBC c c' k ∧ k ≤ 12 ∧ c'.nreg 150001 = 6 ∧ c'.nreg 150002 = 0 ∧
      c'.nreg 150003 = 6 + (ee - (2 * L - τ)) ∧ c'.nreg 150004 = eh ∧ c'.nreg 170145 = 6 ∧
      c'.nreg 170146 = (u + (2 * L - τ)) % n ∧ FrameB BarcC c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a1, a2, a3, a4, a45, a46, a10⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 170133 6, .copyN 150001 170133, .constN 150002 0, .subN 170142 170089 170077,
        .subN 170143 170035 170142, .addN 150003 170133 170143, .copyN 150004 170036,
        .copyN 170145 170133, .addN 170146 170033 170142]) c c₁ k₁ ∧ k₁ = 9 ∧
      c₁.nreg 150001 = 6 ∧ c₁.nreg 150002 = 0 ∧ c₁.nreg 150003 = 6 + (ee - (2 * L - τ)) ∧
      c₁.nreg 150004 = eh ∧ c₁.nreg 170145 = 6 ∧ c₁.nreg 170146 = u + (2 * L - τ) ∧
      c₁.nreg 170010 = n := by
    exec_block
    · omega
    · omega
    · config_simp; rw [h77, h35, h89]; omega
    · config_simp; rw [h33, h77, h89]; omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h77, h35, h36, h89, h33, h10]
  have w₁ := e₁.wb_right
  have hwr : wr BarcC (block [.constN 170133 6, .copyN 150001 170133, .constN 150002 0,
      .subN 170142 170089 170077, .subN 170143 170035 170142, .addN 150003 170133 170143,
      .copyN 150004 170036, .copyN 170145 170133, .addN 170146 170033 170142]) = true := by decide
  have F₁ := exec_frameB e₁ hwr
  by_cases hlt : c₁.nreg 170146 < c₁.nreg 170010
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_true hlt (.skip w₁)), by omega, a1, a2, a3, a4, a45, ?_, ?_⟩
    · rw [a46, Nat.mod_eq_of_lt (by rw [← a46, ← a10]; exact hlt)]
    · exact (FrameB.trans F₁ (FrameB.refl _ _))
  · have hwr2 : wr BarcC (block [.subN 170146 170146 170010]) = true := by decide
    obtain ⟨c₂, k₂, e₂, hk₂, b46, b⟩ : ∃ c₂ k₂, Exec P W (block [.subN 170146 170146 170010]) c₁ c₂ k₂ ∧
        k₂ = 1 ∧ c₂.nreg 170146 = c₁.nreg 170146 - c₁.nreg 170010 ∧
        (∀ r, r ≠ 170146 → c₂.nreg r = c₁.nreg r) := by
      exec_block
      refine ⟨rfl, by config_simp, fun r hr => by config_simp; simp [upd, hr]⟩
    have F₂ := exec_frameB e₂ hwr2
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false hlt e₂), by omega, by rw [b _ (by decide)]; exact a1,
      by rw [b _ (by decide)]; exact a2, by rw [b _ (by decide)]; exact a3,
      by rw [b _ (by decide)]; exact a4, by rw [b _ (by decide)]; exact a45, ?_, F₁.trans F₂⟩
    rw [b46, a46, a10]
    rw [a46, a10] at hlt
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem cuSet_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W (block (copies cuSetL)) c c' 3 ∧ c'.nreg 150000 = c.nreg 170078 ∧
      c'.nreg 150009 = c.nreg 170009 ∧ c'.nreg 150013 = c.nreg 170013 ∧
      (∀ r, r ≠ 150000 → r ≠ 150009 → r ≠ 150013 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) cuSetL c hw
    (by intro p hp q hq; simp only [cuSetL, List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp)
    (by simp [cuSetL])
  refine ⟨c', e, h1 (150000, 170078) (by simp [cuSetL]), h1 (150009, 170009) (by simp [cuSetL]),
    h1 (150013, 170013) (by simp [cuSetL]), fun r r1 r2 r3 => h2 r ?_, h3, h4, h5, h6⟩
  simp only [cuSetL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem recS_exec (k : ℕ) (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k', Exec P W (recS k) c c' k' ∧ k' = 5 ∧ c'.nreg (170200 + 5 * k) = 1 ∧
      slotAt c' k = ⟨c.nreg 150010, c.nmem (c.nreg 150010), c.nreg 170145, c.nreg 170146⟩ ∧
      (∀ r, (r < 170200 + 5 * k ∨ 170205 + 5 * k ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e1 := Exec.constN (P := P) hw (170200 + 5 * k) 1 hW
  have w1 := e1.wb_right
  have e2 := Exec.copyN (P := P) w1 (170201 + 5 * k) 150010
  have w2 := e2.wb_right
  have e3 := Exec.loadN (P := P) w2 (170202 + 5 * k) 150010
  have w3 := e3.wb_right
  have e4 := Exec.copyN (P := P) w3 (170203 + 5 * k) 170145
  have w4 := e4.wb_right
  have e5 := Exec.copyN (P := P) w4 (170204 + 5 * k) 170146
  have w5 := e5.wb_right
  have e := Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_cons e4
    (Exec.block_cons e5 (Exec.block_nil w5)))))
  refine ⟨_, _, e, rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [Config.nreg_mk, upd]
    split_ifs <;> omega
  · simp only [slotAt, Config.nreg_mk, Config.nmem_mk, upd, Slot.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | rfl | omega
  · simp only [Config.nreg_mk, upd]
    split_ifs <;> first | rfl | omega

/-- **One call of the chain cutter at a chain arc of a stretch, recorded as slot `k`.** -/
theorem cutR_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hC : CEnv P W O s u L h1 h2 c)
    {sa ea : WPos} {Ap : Set Point}
    (ha1 : c.nreg 150001 = sa.edge) (ha2 : c.nreg 150002 = sa.hgt)
    (ha3 : c.nreg 150003 = ea.edge) (ha4 : c.nreg 150004 = ea.hgt)
    (harc : CArc (Qof P) (ch (Qof P) u L h1 h2) sa ea s.γ Ap)
    {u₀ g₀ ℓ off : ℕ} (hg : c.nreg 170145 = g₀) (hu₀ : c.nreg 170146 = u₀)
    (hSt : Stretch (Qof P) (ch (Qof P) u L h1 h2) u₀ g₀ ℓ)
    (hoff : u₀ = (s.e₁ + off) % (Qof P).n)
    (hsa : (g₀ : ℝ) ≤ (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) sa)
    (hea : (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) ea ≤ g₀ + ℓ)
    (hlt : (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) sa <
      (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) ea)
    {k : ℕ} (hk : k < 4) {V0 : ℝ}
    (hT : SlotSt P (H s.γ) (G s.γ) s.e₁ V0
      ((s.e₁ : ℝ) + off - g₀ + (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) sa) k c)
    (hroom : c.nreg ALLOC + G s.γ + 10 ≤ W) :
    ∃ c' k', Exec P W (cutR cu k) c c' k' ∧ k' ≤ G s.γ + 8 ∧
      SlotSt P (H s.γ) (G s.γ) s.e₁ V0
        ((s.e₁ : ℝ) + off - g₀ + (chainModel (ch (Qof P) u L h1 h2)).key (Qof P) ea) (k + 1) c' ∧
      CEnv P W O s u L h1 h2 c' ∧ Frame ioBands c c' k' ∧
      (∀ r, 170000 ≤ r → r < 180000 → (r < 170200 + 5 * k ∨ 170205 + 5 * k ≤ r) →
        c'.nreg r = c.nreg r) := by
  have hS := hC.env
  have hG := hS.good
  have hQ : (Qof P).n = P.n := qn'
  have hW := hS.hW
  set C := ch (Qof P) u L h1 h2 with hCd
  -- the inputs
  obtain ⟨c₁, e₁, i0, i9, i13, r₁, rr₁, m₁, rm₁, o₁⟩ := cuSet_exec (P := P) c hw
  have w₁ := e₁.wb_right
  have k₁ : ∀ r, 170000 ≤ r → c₁.nreg r = c.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega)
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := r₁ _ (by decide) (by decide) (by decide)
  have F₁ : Frame ioBands c c₁ 3 := by
    refine frameIO_of_frameB (B := fun r => decide (150000 ≤ r ∧ r < 150014))
      (fun r hr => io_of_band' (Or.inr (Or.inr (by simp at hr; omega)))) ⟨fun r hr => ?_,
        fun r _ => by rw [rr₁], m₁, rm₁, o₁⟩ 3
    simp only [decide_eq_false_iff_not] at hr
    exact r₁ r (by omega) (by omega) (by omega)
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => k₁ r h1) (fun a _ => by rw [m₁])
    (by rw [hA₁])
  have D₁ : DescOK P c₁.nmem (c₁.nreg 150000) C (c₁.nreg ALLOC) := by
    rw [i0, m₁, hA₁]; exact hC.desc
  obtain ⟨hMD, hMWF, -⟩ := D₁
  obtain ⟨hctx, hcap⟩ := S₁.ctx
  obtain ⟨sP, eP, sE, eE, sI', eI, hwt, -⟩ := harc
  have b1 : c₁.nreg 150001 = sa.edge := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha1
  have b2 : c₁.nreg 150002 = sa.hgt := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha2
  have b3 : c₁.nreg 150003 = ea.edge := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha3
  have b4 : c₁.nreg 150004 = ea.hgt := by rw [r₁ _ (by decide) (by decide) (by decide)]; exact ha4
  have e1 : rd c₁ bCut 1 = sa.edge := b1
  have e2 : rd c₁ bCut 2 = sa.hgt := b2
  have e3 : rd c₁ bCut 3 = ea.edge := b3
  have e4 : rd c₁ bCut 4 = ea.hgt := b4
  have hsa' : (⟨c₁.nreg 150001, c₁.nreg 150002⟩ : WPos) = sa := by rw [b1, b2]
  have hea' : (⟨c₁.nreg 150003, c₁.nreg 150004⟩ : WPos) = ea := by rw [b3, b4]
  have h9 : c₁.nreg 150009 = s.γ := by rw [i9]; exact hS.r9
  have h13 : c₁.nreg 150013 = s.h := by rw [i13]; exact hS.r13
  -- the chain cutter
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hcu P W c₁ w₁ ⟨hG, hW,
    by show (gradeCtx O).holds P c₁.nmem (c₁.nreg 150013) (c₁.nreg ALLOC); rw [h13]; exact hctx,
    by show c₁.nreg 150009 ≤ (gradeCtx O).cap P c₁.nmem (c₁.nreg 150013); rw [h9, h13]; exact hcap,
    hMWF, chainModel C, hMD, okModel_sub hG,
    by show ProperPos _ _ _ ⟨c₁.nreg 150001, c₁.nreg 150002⟩; rw [hsa', ← hQ]; exact sP,
    by show ProperPos _ _ _ ⟨c₁.nreg 150003, c₁.nreg 150004⟩; rw [hea', ← hQ]; exact eP,
    by show c₁.nreg 150001 < _; rw [b1]; exact sE,
    by show c₁.nreg 150003 < _; rw [b3]; exact eE,
    by show c₁.nreg 150002 = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P)
          ⟨c₁.nreg 150001, c₁.nreg 150002⟩)
       rw [hsa', b2]; exact sI',
    by show c₁.nreg 150004 = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P)
          ⟨c₁.nreg 150003, c₁.nreg 150004⟩)
       rw [hea', b4]; exact eI,
    by show _ ≤ c₁.nreg 150009; rw [e1, e2, e3, e4, h9]; exact hwt⟩
    (by show c₁.nreg ALLOC + G (c₁.nreg 150009) ≤ W
        rw [h9, hA₁]; omega)
  have hp := hpost (chainModel C) hMD
  have e9 : rd c₁ bCut 9 = s.γ := h9
  simp only [e1, e2, e3, e4, e9] at hp
  obtain ⟨-, hLE, hqG, hq1, h0, hl, hc, ht, hk0, hk1, hpp, hkd⟩ := hp
  have w₂ := e₂.wb_right
  -- the registers survive the cutter
  have g₂ : ∀ r, 170000 ≤ r → r < 180000 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by unfold bandOf; rw [show r / 10000 = 17 by omega]; decide)
      (by unfold ALLOC; omega)
  have hA₂ := F₂.2.2.2.2.2.1
  have C₂ : CEnv P W O s u L h1 h2 c₂ := (hC.keep (fun r hr => by
      rw [k₁ r (by unfold CRegs at hr; omega)]) (fun a _ => by rw [m₁])
      (by rw [hA₁])).keep
    (fun r hr => g₂ r (by unfold CRegs at hr; omega) (by unfold CRegs at hr; omega))
    F₂.2.2.1 hA₂
  have T₂ : SlotSt P (H s.γ) (G s.γ) s.e₁ V0
      ((s.e₁ : ℝ) + off - g₀ + (chainModel C).key (Qof P) sa) k c₂ :=
    hT.keep (fun r h1 h2 => by rw [g₂ r (by omega) (by omega), k₁ r (by omega)])
      (fun a ha => by rw [F₂.2.2.1 a (by rw [hA₁]; exact ha), m₁]) (by rw [← hA₁]; exact hA₂)
  -- the record
  obtain ⟨c₃, k₃, e₃, hk₃, f3, sl3, r₃, rr₃, m₃, rm₃, o₃⟩ := recS_exec (P := P) k c₂ w₂
    (by have := hS.hW; unfold hostWords at this; omega)
  have g145 : c₂.nreg 170145 = g₀ := by rw [g₂ _ (by norm_num) (by norm_num), k₁ _ (by norm_num)]; exact hg
  have g146 : c₂.nreg 170146 = u₀ := by rw [g₂ _ (by norm_num) (by norm_num), k₁ _ (by norm_num)]; exact hu₀
  rw [g145, g146] at sl3
  have hslot : SlotOK P c₂.nmem (c₂.nreg ALLOC) (H s.γ) s.e₁
      ((s.e₁ : ℝ) + off - g₀ + (chainModel C).key (Qof P) sa)
      ((s.e₁ : ℝ) + off - g₀ + (chainModel C).key (Qof P) ea) (slotAt c₃ k) := by
    rw [sl3]
    exact ⟨C, ℓ, off, sa, ea, hSt, hoff, rfl, hq1, hLE, h0, hl, hc, ht,
      fun i hi => ⟨(hpp i hi).1, (hpp i hi).2.1, (hpp i hi).2.2.1, (hpp i hi).2.2.2, hkd i hi,
        hk0 i hi, hk1 i hi⟩, hsa, hea, hlt, rfl, rfl⟩
  have T₃ := T₂.add hk r₃ f3 m₃ hslot (by rw [sl3]; exact hqG)
  have C₃ : CEnv P W O s u L h1 h2 c₃ := C₂.keep (fun r hr => r₃ r (Or.inl (by
      unfold CRegs at hr; omega))) (fun a _ => by rw [m₃]) (by
      rw [r₃ _ (Or.inl (by unfold ALLOC; omega))])
  have F₃ : Frame ioBands c₂ c₃ k₃ := frameIO_of_frameB
    (B := fun r => decide (170200 + 5 * k ≤ r ∧ r < 170205 + 5 * k))
    (fun r hr => io_of_band' (Or.inl (by simp at hr; omega)))
    ⟨fun r hr => r₃ r (by simp at hr; omega), fun r _ => by rw [rr₃], m₃, rm₃, o₃⟩ k₃
  have ex : Exec P W (cutR cu k) c c₃ (3 + k₂ + k₃) := .seq (.seq e₁ e₂) e₃
  have hk₂' : k₂ ≤ G s.γ := by
    have := hk₂; simp only [rd, bandReg, bCut] at this; rw [← h9]; exact this
  refine ⟨c₃, _, ex, by omega, T₃, C₃,
    ((F₁.trans (F₂.mono oracleBands_sub_io le_rfl)).trans F₃).mono (by simp) le_rfl,
    fun r h1 h2 hr => ?_⟩
  rw [r₃ r hr, g₂ r h1 h2, k₁ r h1]

end exec

end

end IOrc

end Chazelle.Core
