module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseOracleChR2
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseOracleTop

namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
variable {r : ℕ}
/-- Registers of bands `17`, `14`, `15` and of the kernel are in the adapter's bands. -/
theorem io_of_band' (h : ztnes ∨ ztcko ∨
    (140000 ≤ r ∧ r < 160000)) : bandOf r ∈ ioBands ∧ r ≠ ALLOC := by
  zujfu

  zude
  · zuezj
  · zuezh
  · rcases (show r < 150000 ∨ 150000 ≤ r by omega) with h' | h'
    · zuezi
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
    (.ifLtN 170146 170010 .skip ztnsj)

/-- The registers an arc block of the cutter writes. -/
def BarcC (r : ℕ) : Bool :=
  decide ztnem ||
    decide (r = 170133 ∨ r = 170142 ∨ r = 170143 ∨ r = 170145 ∨ r = 170146)
theorem wr_arcOneC : wr BarcC arcOneC = true := by_decide
theorem wr_arcTwoAC : wr BarcC arcTwoAC = true := by_decide
theorem barcC_io (h : BarcC r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band' (by simp only [BarcC, Bool.or_eq_true, decide_eq_true_eq] at h; omega)

/-- The cutter's inputs other than the arc ends. -/
def cuSetL : List ztw := [ztsrx, ztssd, ztssf]

/-- **One call of the chain cutter.** -/
def cutI (cu : Stmt) : Stmt := .seq ztqdz cu

/-- **Recording slot `k`**: flag, list address, number of pieces, stretch starts. -/
def recS (k : ℕ) : Stmt :=
  block [.constN ztvc 1, .copyN zteko 150010,
    .loadN ztekp 150010, .copyN ztekq 170145,
    .copyN ztekr 170146]

/-- **One call of the chain cutter, recorded as slot `k`.** -/
def cutR (cu : Stmt) (k : ℕ) : Stmt := .seq (cutI cu) ztwcl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
variable (c : Config)
theorem arcOneC_exec (hw : WordsBounded W c) {τ sh ee eh u : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h33 : c.nreg 170033 = u) (hW : 6 + τ + ee ≤ W) :
    ∃ c' k, Exec P W arcOneC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧ c'.nreg 150002 = sh ∧
      c'.nreg 150003 = 6 + τ + ee ∧ c'.nreg 150004 = eh ∧ c'.nreg 170145 = 6 + τ ∧
      c'.nreg 170146 = u ∧ FrameB BarcC c c' := by
  suffices h : ∃ c' k, Exec P W arcOneC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧
      c'.nreg 150002 = sh ∧ c'.nreg 150003 = 6 + τ + ee ∧ c'.nreg 150004 = eh ∧
      c'.nreg 170145 = 6 + τ ∧ c'.nreg 170146 = u by
    zucbe
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7, exec_frameB e wr_arcOneC⟩
  unfold arcOneC
  exec_block
  · omega
  · config_simp; omega
  · simp_all
  simp_all
theorem arcTwoAC_exec (hw : WordsBounded W c) {τ sh L u : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h89 : c.nreg 170089 = 2 * L)
    (h33 : c.nreg 170033 = u) (hW : 2 * L + 6 ≤ W) (hτ : 6 + τ ≤ W) :
    ∃ c' k, Exec P W arcTwoAC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧ c'.nreg 150002 = sh ∧
      c'.nreg 150003 = 2 * L + 6 ∧ c'.nreg 150004 = 0 ∧ c'.nreg 170145 = 6 + τ ∧
      c'.nreg 170146 = u ∧ FrameB BarcC c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoAC c c' k ∧ k = 7 ∧ c'.nreg 150001 = 6 + τ ∧
      c'.nreg 150002 = sh ∧ c'.nreg 150003 = 2 * L + 6 ∧ c'.nreg 150004 = 0 ∧
      c'.nreg 170145 = 6 + τ ∧ c'.nreg 170146 = u by
    zucbe
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, h7, exec_frameB e wr_arcTwoAC⟩
  unfold arcTwoAC
  exec_block
  · omega
  · simp_all
  · simp_all
  · omega
  simp_all
theorem arcTwoBC_exec (hw : WordsBounded W c) {τ ee eh L u n : ℕ}
    (h77 : c.nreg 170077 = τ) (h35 : c.nreg 170035 = ee) (h36 : c.nreg 170036 = eh)
    (h89 : c.nreg 170089 = 2 * L) (h33 : c.nreg 170033 = u) (h10 : c.nreg 170010 = n)
    (hu : u < n) (hL₁ : 2 * L - τ < n) (hW : 6 + ee ≤ W) (hnW : 2 * n ≤ W) :
    ∃ c' k, Exec P W arcTwoBC c c' k ∧ k ≤ 12 ∧ c'.nreg 150001 = 6 ∧ c'.nreg 150002 = 0 ∧
      c'.nreg 150003 = 6 + ztxwk ∧ c'.nreg 150004 = eh ∧ c'.nreg 170145 = 6 ∧
      c'.nreg 170146 = (u + ztdkk) % n ∧ FrameB BarcC c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a1, a2, a3, a4, a45, a46, a10⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 170133 6, .copyN 150001 170133, .constN 150002 0, .subN 170142 170089 170077,
        .subN 170143 170035 170142, .addN 150003 170133 170143, .copyN 150004 170036,
        .copyN 170145 170133, .addN 170146 170033 170142]) c c₁ k₁ ∧ k₁ = 9 ∧
      c₁.nreg 150001 = 6 ∧ c₁.nreg 150002 = 0 ∧ c₁.nreg 150003 = 6 + ztxwk ∧
      c₁.nreg 150004 = eh ∧ c₁.nreg 170145 = 6 ∧ c₁.nreg 170146 = u + ztdkk ∧
      c₁.nreg 170010 = n := by
    exec_block
    · omega
    · omega
    · config_simp; omega
    · config_simp; omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [h77, h35, h36, h89, h33, h10]
  zud
  have hwr : wr BarcC (block [.constN 170133 6, .copyN 150001 170133, .constN 150002 0,
      .subN 170142 170089 170077, .subN 170143 170035 170142, .addN 150003 170133 170143,
      .copyN 150004 170036, .copyN 170145 170133, .addN 170146 170033 170142]) = true := by_decide
  have F₁ := exec_frameB e₁ hwr
  by_cases hlt : c₁.nreg 170146 < c₁.nreg 170010
  · refine ⟨c₁, _, .seq e₁ ztzrx, by_omega, a1, a2, a3, a4, a45, ?_, ?_⟩
    · rw [a46, Nat.mod_eq_of_lt by_omega]
    omega
  · have hwr2 : wr BarcC ztnsj = true := by_decide
    obtain ⟨c₂, k₂, e₂, hk₂, b46, b⟩ : ∃ c₂ k₂, Exec P W (block [.subN 170146 170146 170010]) c₁ c₂ k₂ ∧
        k₂ = 1 ∧ c₂.nreg 170146 = c₁.nreg 170146 - c₁.nreg 170010 ∧
        (∀ r, r ≠ 170146 → c₂.nreg r = c₁.nreg r) := by
      exec_block
      refine by_simp_all
    have F₂ := exec_frameB e₂ hwr2
    refine ⟨c₂, _, .seq e₁ ztsoz, by_omega, by_simp_all,
      by simp_all, by_simp_all,
      by simp_all, by_simp_all, ?_, F₁.trans F₂⟩
    rw [b46, a46, a10]
    rw [a46, a10] at hlt
    zul
theorem cuSet_exec (hw : WordsBounded W c) :
    ∃ c', Exec P W ztqdz c c' 3 ∧ c'.nreg 150000 = c.nreg 170078 ∧
      c'.nreg 150009 = c.nreg 170009 ∧ c'.nreg 150013 = c.nreg 170013 ∧
      (∀ r, r ≠ 150000 → r ≠ 150009 → r ≠ 150013 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) cuSetL c hw
    by_decide
    by_decide
  refine ⟨c', e, h1 ztsrx by_decide, h1 ztssd by_decide,
    h1 ztssf by_decide, fun r r1 r2 r3 => h2 r ?_, h3, h4, h5, h6⟩
  simp only [cuSetL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega
theorem recS_exec (k : ℕ) (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k', Exec P W ztwcl c c' k' ∧ k' = 5 ∧ c'.nreg ztvc = 1 ∧
      slotAt c' k = ⟨c.nreg 150010, c.nmem (c.nreg 150010), c.nreg 170145, c.nreg 170146⟩ ∧
      (∀ r, ztcav → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e1 := Exec.constN (P := P) hw ztvc 1 hW
  zumfs
  have e2 := Exec.copyN (P := P) w1 zteko 150010
  have w2 := e2.wb_right
  have e3 := Exec.loadN (P := P) w2 ztekp 150010
  have w3 := e3.wb_right
  have e4 := Exec.copyN (P := P) w3 ztekq 170145
  have w4 := e4.wb_right
  have e5 := Exec.copyN (P := P) w4 ztekr 170146
  have w5 := e5.wb_right
  have e := Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_cons e4
    (Exec.block_cons e5 (Exec.block_nil w5)))))
  refine ⟨_, _, e, rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp
  · simp only [slotAt, Config.nreg_mk, Config.nmem_mk, upd, Slot.mk.injEq]
    grind
  · zujnm
    grind

/-- **One call of the chain cutter at a chain arc of a stretch, recorded as slot `k`.** -/
theorem cutR_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hC : CEnv P W O s u L h1 h2 c)
    {sa ea : WPos} {Ap : Set Point}
    (ha1 : c.nreg 150001 = sa.edge) (ha2 : c.nreg 150002 = sa.hgt)
    (ha3 : c.nreg 150003 = ea.edge) (ha4 : c.nreg 150004 = ea.hgt)
    (harc : CArc zta ztwls sa ea s.γ Ap)
    {u₀ g₀ ℓ off : ℕ} (hg : c.nreg 170145 = g₀) (hu₀ : c.nreg 170146 = u₀)
    (hSt : Stretch zta ztwls u₀ g₀ ℓ)
    (hoff : u₀ = zttzr % (Qof P).n)
    (hsa : (g₀ : ℝ) ≤ (chainModel ztwls).key zta sa)
    (hea : (chainModel ztwls).key zta ea ≤ g₀ + ℓ)
    (hlt : (chainModel ztwls).key zta sa <
      (chainModel ztwls).key zta ea)
    {k : ℕ} (hk : k < 4) {V0 : ℝ}
    (hT : SlotSt P ztdyn ztffk s.e₁ V0
      ((s.e₁ : ℝ) + off - g₀ + (chainModel ztwls).key zta sa) k c)
    (hroom : c.nreg ALLOC + G s.γ + 10 ≤ W) :
    ∃ c' k', Exec P W zttip c c' k' ∧ k' ≤ G s.γ + 8 ∧
      SlotSt P ztdyn ztffk s.e₁ V0
        ((s.e₁ : ℝ) + off - g₀ + (chainModel ztwls).key zta ea) zts c' ∧
      CEnv P W O s u L h1 h2 c' ∧ Frame ioBands c c' k' ∧
      (∀ r, 170000 ≤ r → r < 180000 → ztcav →
        c'.nreg r = c.nreg r) := by
  zuhxl

  zudq
  zudyq

  -- the inputs
  obtain ⟨c₁, e₁, i0, i9, i13, r₁, rr₁, m₁, rm₁, o₁⟩ := cuSet_exec (P := P) c hw
  zud
  have k₁ : ztkom := by_grind
  have hA₁ : ztdc := r₁ _ by_decide by_decide by_decide
  have F₁ : Frame ioBands c c₁ 3 := by
    refine frameIO_of_frameB (B := fun r => decide ztnem)
      (fun r hr => io_of_band' by_grind) ⟨fun r hr => ?_,
        by simp_all, m₁, rm₁, o₁⟩ 3
    zubzq
    exact r₁ r by_omega by_omega by_omega
  have S₁ : zteeb := hS.keep by_simp_all by_simp_all
    ztjqb
  have D₁ : DescOK P c₁.nmem (c₁.nreg 150000) C ztbmq := by
    rw [i0, m₁, hA₁]; exact hC.desc
  obtain ⟨hMD, hMWF, -⟩ := D₁
  zuicn
  obtain ⟨sP, eP, sE, eE, sI', eI, hwt, -⟩ := harc
  have b1 : c₁.nreg 150001 = sa.edge := by_simp_all
  have b2 : c₁.nreg 150002 = sa.hgt := by_simp_all
  have b3 : c₁.nreg 150003 = ea.edge := by_simp_all
  have b4 : c₁.nreg 150004 = ea.hgt := by_simp_all
  have e1 : rd c₁ bCut 1 = sa.edge := b1
  have e2 : rd c₁ bCut 2 = sa.hgt := b2
  have e3 : rd c₁ bCut 3 = ea.edge := b3
  have e4 : rd c₁ bCut 4 = ea.hgt := b4
  have hsa' : (⟨c₁.nreg 150001, c₁.nreg 150002⟩ : WPos) = sa := by_simp_all
  have hea' : (⟨c₁.nreg 150003, c₁.nreg 150004⟩ : WPos) = ea := by_simp_all
  have h9 : c₁.nreg 150009 = s.γ := by zuoxa; exact hS.r9
  have h13 : c₁.nreg 150013 = s.h := by zuoxb; exact hS.r13
  -- the chain cutter
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hcu P W c₁ w₁ ⟨hG, hW,
    by show (gradeCtx O).holds P c₁.nmem ztvmo _; grind,
    by show c₁.nreg 150009 ≤ (gradeCtx O).cap P c₁.nmem ztvmo; grind,
    hMWF, chainModel C, hMD, okModel_sub hG,
    by grind,
    by grind,
    by omega,
    by omega,
    by grind,
    by grind,
    by show _ ≤ c₁.nreg 150009; grind⟩
    (by show c₁.nreg ALLOC + G (c₁.nreg 150009) ≤ W
        grind)
  have hp := hpost _ hMD
  have e9 : rd c₁ bCut 9 = s.γ := h9
  simp only [e1, e2, e3, e4, e9] at hp
  obtain ⟨-, hLE, hqG, hq1, h0, hl, hc, ht, hk0, hk1, hpp, hkd⟩ := hp
  zue
  -- the registers survive the cutter
  have g₂ : zthph := fun r h1 h2 =>
    F₂.1 r ztggs
      ztu
  zugll
  have C₂ := (hC.keep (fun r hr => by
      zuokd) (fun a _ => by zvmxn)
      ztjqb).keep
    ztyji
    F₂.2.2.1 hA₂
  have T₂ : SlotSt P _ _ s.e₁ V0
      _ k c₂ :=
    hT.keep (fun r h1 h2 => by rw [g₂ r by_omega by_omega, k₁ r by_omega])
      (fun a ha => by zunye) by_omega
  -- the record
  obtain ⟨c₃, k₃, e₃, hk₃, f3, sl3, r₃, rr₃, m₃, rm₃, o₃⟩ := recS_exec (P := P) k c₂ w₂
    by_omega
  have g145 : c₂.nreg 170145 = g₀ := by zunos; exact hg
  have g146 : c₂.nreg 170146 = u₀ := by zunos; omega
  rw [g145, g146] at sl3
  have hslot : SlotOK P c₂.nmem zthwb ztdyn s.e₁
      ((s.e₁ : ℝ) + off - g₀ + (chainModel C).key zta sa)
      ((s.e₁ : ℝ) + off - g₀ + (chainModel C).key zta ea) (slotAt c₃ k) := by
    zuoxc
    exact ⟨C, ℓ, off, sa, ea, hSt, hoff, rfl, hq1, hLE, h0, hl, hc, ht,
      fun i hi => ⟨(hpp i hi).1, (hpp i hi).2.1, (hpp i hi).2.2.1, (hpp i hi).2.2.2, hkd i hi,
        hk0 i hi, hk1 i hi⟩, hsa, hea, hlt, rfl, rfl⟩
  have T₃ := T₂.add hk r₃ f3 m₃ hslot (by zuoxc; exact hqG)
  have C₃ := C₂.keep (fun r hr => r₃ r (Or.inl (by
      unfold CRegs at hr; omega))) (fun a _ => by zumzp) (by
      rw [r₃ _ ztbaex])
  have F₃ := frameIO_of_frameB
    (B := fun r => decide _)
    (fun r hr => io_of_band' (Or.inl ztcyv))
    ⟨fun r hr => r₃ r ztcyv, fun r _ => by zuoek, m₃, rm₃, o₃⟩ k₃
  have ex : Exec P W zttip c c₃ _ := .seq ztyv e₃
  have hk₂' : k₂ ≤ G s.γ := by
    have := hk₂; simp only [rd, bandReg, bCut] at this; zuorp; omega
  refine ⟨c₃, _, ex, by_omega, T₃, C₃,
    ((F₁.trans ztnlc).trans F₃).mono by_simp le_rfl,
    fun r h1 h2 hr => ?_⟩
  rw [r₃ r hr, g₂ r h1 h2, k₁ r h1]
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
section str
variable {Q : Polygon} {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)
  (hD : DistinctHeights Q) (hn : 3 ≤ Q.n)
include hu hD hn in
/-- **The stretch of the one chain arc.** -/
theorem str_one (hs : tau Q u L h1 h2 ≤ L) :
    Stretch Q ztra u ztgcu L := by
  zucvs
  rw [min_eq_left by_omega] at hA
  exact ztfdi
include hu hD hn in
/-- **The stretch of the first of two chain arcs.** -/
theorem str_twoA (hs : L < tau Q u L h1 h2) :
    Stretch Q ztra u ztgcu ztnc := by
  zucvs
  zubas
  rw [min_eq_right by_omega] at hA
  exact ztfdi
include hu hD hn in
/-- **The stretch of the second of two chain arcs.** -/
theorem str_twoB (hs : L < tau Q u L h1 h2) :
    Stretch Q ztra (ztzyi % Q.n) 6
      ztztu := by
  zudyb
  zubas
  zudon
  refine ⟨Nat.mod_lt _ by_omega, le_rfl, by rw [ch_m]; omega, ch_P, hD, hn, by_omega,
    fun d hd => ?_⟩
  rw [hiw, Nat.mod_add_mod, ← hiw]
  tauto
end str

/-- **The slot state with fewer free slots.** -/
theorem SlotSt.mono {P : Polygon} {Hγ Gγ e₁ : ℕ} {V0 V : ℝ} {k k' : ℕ} {c : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hk : k ≤ k') : SlotSt P Hγ Gγ e₁ V0 V k' c :=
  ⟨h.ok, fun j h1 h2 => h.free j by_omega h2, h.bit, h.qG⟩

/-! ## The program -/

/-- **A sub-query of the interior cutter**, recorded as slots `b` (and `b + 1`). -/
def sqC (cu : Stmt) (b : ℕ) : Stmt :=
  .seq chainI (.ifLtN 170037 170077
    (.seq arcTwoAC (.seq zttio (.seq arcTwoBC (cutR cu ztds))))
    (.seq arcOneC zttio))

/-- The registers of band `17` a sub-query of the cutter writes. -/
def BSQC (r : ℕ) : Bool :=
  decide ztekn || decide ztnew ||
    decide (170133 ≤ r ∧ r < 170147) || decide (170200 ≤ r ∧ r < 170220)

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **A sub-query of the interior cutter.** -/
theorem sqC_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) {u L sh₀ ee eh off : ℕ}
    (h33 : c.nreg 170033 = u) (h34 : c.nreg 170034 = sh₀) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h37 : c.nreg 170037 = L)
    (hsub : SubOK zta u L sh₀ ee eh) (hLγ : L ≤ s.γ) (hoff : u = zttzr % (Qof P).n)
    {b : ℕ} (hb : b + 2 ≤ 4) {V0 : ℝ}
    (hT : SlotSt P ztdyn ztffk s.e₁ V0
      ((s.e₁ : ℝ) + off + (interiorModel zta).param zta zthnt) b c)
    (hroom : c.nreg ALLOC + 2 * G s.γ + 1204 * Nat.log 2 ztbtk + 2600 ≤ W) :
    ∃ c' k, Exec P W ztoie c c' k ∧ k ≤ 2 * G s.γ + 1204 * Nat.log 2 ztbtk + 2600 ∧
      SlotSt P ztdyn ztffk s.e₁ V0 ((s.e₁ : ℝ) + off + ee +
        (interiorModel zta).param zta ztbqv) (b + 2) c' ∧
      SEnv P W O s c' ∧ Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → c'.nreg r = c.nreg r) := by
  zudq
  zucg

  zucgd

  have hG := hS.good
  zudyf
  have hn3 : ztcrh := by zvnao; exact Chazelle.Jordan.simple_three_le hG.1
  zufpi
  set t := (interiorModel _).param _ ztbqv with ht
  zullr
  have hx0 := hsub.hs.1
  have hx1 := hsub.hs.2.1
  have ht0 := hsub.he.1
  have hxy := hsub.hxy
  zucqk
  -- the chain
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', C₁, d78, dA, dm, dr, drr, drm, dout⟩ := chainI_exec c hw hS h33 h37
    by_omega h1 h2 hcap by_omega
  zufsu
  zud
  have g₁ : ∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → c₁.nreg r = c.nreg r :=
    fun r r1 r2 hr => dr r (by
      zuggl
      zumzr; omega)
      ztu
  have T₁ : SlotSt P _ _ s.e₁ V0 _ b c₁ :=
    hT.keep (fun r r1 r2 => dr r (by
      zumzr; omega)
      ztu) dm by_omega
  zumd

  -- the arc blocks keep the chain state and the slot state
  have keepArc : ∀ {d d' : Config}, FrameB BarcC d d' → CEnv P W O s u L h1 h2 d →
      CEnv P W O s u L h1 h2 d' := fun F hC => hC.keep (fun r hr => F.1 r (by
        unfold CRegs at hr; zunfc; omega))
      ztbmr zthen
  have keepArcT : ∀ {d d' : Config} {V : ℝ} {k : ℕ}, FrameB BarcC d d' →
      SlotSt P _ _ s.e₁ V0 V k d → SlotSt P ztdyn ztffk s.e₁ V0 V k d' :=
    fun F hT' => hT'.keep (fun r r1 r2 => F.1 r (by
        zunfc; omega))
      ztbmr zthen
  have bandArc : ∀ {d d' : Config}, FrameB BarcC d d' → ∀ r, 170000 ≤ r → r < 180000 →
      BSQC r = false → d'.nreg r = d.nreg r := fun F r r1 r2 hr => F.1 r (by
        zuggl
        zunfc; omega)
  have bandCut : ∀ {d d' : Config} {k : ℕ}, (∀ r, 170000 ≤ r → r < 180000 →
      ztcav → d'.nreg r = d.nreg r) → k < 4 →
      ∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → d'.nreg r = d.nreg r :=
    fun F hk r r1 r2 hr => F r r1 r2 (by
        simp only [BSQC, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega)
  have hps := param_start hu h1 h2 sh₀
  have ks : (chainModel C).key zta ⟨6 + tau _ u L h1 h2, sh₀⟩ =
      ((6 + tau _ u L h1 h2 : ℕ) : ℝ) + x := by rw [key_eq, hps]
  zufrl
  · -- one chain arc
    zugfy
    have hb' : ztrhm := by zunge; omega
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, a45, a46, Fa⟩ := arcOneC_exec c₁ w₁
      C₁.r77 b34 b35 b36 C₁.r33 by_omega
    zudmu
    zuixm
    have hpe := param_end_one hu h1 h2 hs ztwff
    have ke : (chainModel C).key zta ztolt = ((6 + τ + ee : ℕ) : ℝ) + t := by
      zukxg
    have hV : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key zta ztqzy = s.e₁ + off + x := by_grind
    have hV' : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key zta ztolt = s.e₁ + off + ee + t := by
      grind
    obtain ⟨c₃, k₃, e₃, hk₃, T₃, C₃, F₃, g₃⟩ := cutR_exec hcu c₂ e₂.wb_right C₂ a1 a2 a3 a4 harc a45 a46
      (str_one hu h1 h2 hD hn3 hs) hoff
      by_grind
      by_grind
      by_grind (k := b) by_omega
      (by rw [hV]; exact keepArcT Fa T₁) ztjpz
    rw [hV'] at T₃
    have ex : Exec P W ztoie c c₃ _ :=
      .seq e₁ (.ifLtN_false hb' ztcr)
    zuiuo
    refine ⟨c₃, _, ex, by_omega, T₃.mono by_omega, C₃.env,
      ((F₁.trans Fa').trans F₃).mono by_simp by_omega, fun r r1 r2 hr => ?_⟩
    rw [bandCut g₃ by_omega r r1 r2 hr, bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]
  · -- two chain arcs meeting at the top
    zumis
    zugfy
    have hb' : ztsgc := by zunge; exact hs
    zufyd
    zugyf
    zucat
    have hpe := param_end_two hu h1 h2 hs hle ztwff
    have ke : (chainModel C).key zta ztexi = ((2 * L + 6 : ℕ) : ℝ) := by
      simp
    have k6 : (chainModel C).key zta ztbcw = ((6 : ℕ) : ℝ) := by
      simp
    have keB : (chainModel C).key zta ztzia = ((6 + ztfrc : ℕ) : ℝ) + t := by
      zukxg
    have hL₁r : ((L₁ : ℕ) : ℝ) = 2 * L - τ := by rw [hL₁, Nat.cast_sub by_omega]; simp
    have hel : zticx := Nat.cast_sub hle
    -- the first arc
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, a45, a46, Fa⟩ := arcTwoAC_exec c₁ w₁
      C₁.r77 b34 C₁.r89 C₁.r33 by_omega by_omega
    zudmu
    have hVA : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key zta ztqzy = s.e₁ + off + x := by_grind
    have hVA' : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key zta ztexi = s.e₁ + ((off + L₁ : ℕ) : ℝ) := by
      grind
    obtain ⟨c₃, k₃, e₃, hk₃, T₃, C₃, F₃, g₃⟩ := cutR_exec hcu c₂ e₂.wb_right C₂ a1 a2 a3 a4 harcA a45 a46
      (str_twoA hu h1 h2 hD hn3 hs) hoff
      by_grind
      by_grind
      (by rw [ks, ke]; push_cast
          have : (τ : ℝ) + 1 ≤ 2 * L := by exact_mod_cast by_grind
          linarith) (k := b) by_omega
      (by rw [hVA]; exact keepArcT Fa T₁) ztjpz
    rw [hVA'] at T₃
    -- the second arc
    have c35 : zturw := by
      rw [g₃ _ by_norm_num by_norm_num by_omega,
        bandArc Fa _ by_norm_num by_norm_num by_decide]; omega
    have c36 : zturx := by
      rw [g₃ _ by_norm_num by_norm_num by_omega,
        bandArc Fa _ by_norm_num by_norm_num by_decide]; omega
    have c10 : c₃.nreg 170010 = (Qof P).n := by rw [C₃.env.r10, hQ]
    obtain ⟨c₄, k₄, e₄, hk₄, a1', a2', a3', a4', a45', a46', Fb⟩ := arcTwoBC_exec c₃
      e₃.wb_right C₃.r77 c35 c36 C₃.r89 C₃.r33 c10 hu by_omega by_omega by_omega
    zugkr

    have hoff' : (u + L₁) % (Qof P).n = (s.e₁ + (off + L₁)) % (Qof P).n := by
      rw [hoff, Nat.mod_add_mod, Nat.add_assoc]
    have hVB : (s.e₁ : ℝ) + ((off + L₁ : ℕ) : ℝ) - ((6 : ℕ) : ℝ) +
        (chainModel C).key zta ztbcw = s.e₁ + ((off + L₁ : ℕ) : ℝ) := by_simp
    have hVB' : (s.e₁ : ℝ) + ((off + L₁ : ℕ) : ℝ) - ((6 : ℕ) : ℝ) +
        (chainModel C).key zta ztzia = s.e₁ + off + ee + t := by
      grind
    obtain ⟨c₅, k₅, e₅, hk₅, T₅, C₅, F₅, g₅⟩ := cutR_exec hcu c₄ e₄.wb_right C₄ a1' a2' a3' a4' harcB a45' a46'
      (str_twoB hu h1 h2 hD hn3 hs) hoff'
      (by rw [k6])
      (by rw [keB]; push_cast; zuoxd
          have : ztfzw := by exact_mod_cast hle
          have : ((L - L₁ : ℕ) : ℝ) = L - L₁ := Nat.cast_sub by_omega
          zvmwk; linarith)
      (by rw [k6, keB]; push_cast; zuoxd
          have : (L₁ : ℝ) < ee + t := by
            rcases hsub.hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
            · have : ztpgp := by exact_mod_cast by_grind
              linarith
            · zuiuj
              linarith
          linarith) (k := b + 1) by_omega
      (by rw [hVB]; exact keepArcT Fb T₃) (by
        zukpe
        have := Fa.1 ALLOC by_decide
        omega)
    rw [hVB'] at T₅
    have ex : Exec P W ztoie c c₅ _ :=
      .seq e₁ (.ifLtN_true hb' ztbq)
    zuiuo
    have Fb' := frameIO_of_frameB ztiki Fb k₄
    refine ⟨c₅, _, ex, by_omega, T₅, C₅.env,
      ((((F₁.trans Fa').trans F₃).trans Fb').trans F₅).mono by_simp by_omega,
      fun r r1 r2 hr => ?_⟩
    rw [bandCut g₅ by_omega r r1 r2 hr, bandArc Fb r r1 r2 hr, bandCut g₃ by_omega r r1 r2 hr,
      bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
theorem whileLtN_pot2 {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zubu

    · zulfw

/-! ## The programs -/

/-- The translation of the word in `170236` into `170237`. -/
def trI : Stmt :=
  .seq ztirh
    (.ifLtN 170237 170010 .skip (block [.subN 170237 170237 170010]))

/-- Copy one word. -/
def mvW : Stmt :=
  block [.loadN 170236 170234, .storeN 170222 170236, .addN 170234 170234 170011,
    .addN 170222 170222 170011]

/-- Copy one translated word. -/
def mvT : Stmt :=
  .seq (block [.loadN 170236 170234]) (.seq trI
    ztgqy)

/-- Copy one piece record. -/
def cpBody : Stmt :=
  .seq mvT (.seq mvW (.seq mvT (.seq mvW (.seq mvW (.seq mvW (.seq mvW
    ztiqh))))))

/-- **Copy the pieces of a slot.** -/
def cpLoop : Stmt := .whileLtN 170235 170231 cpBody

/-- The registers the copy writes. -/
def Bcp (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170223 ∨ (170234 ≤ r ∧ r < 170238))

/-- The registers one word copy writes. -/
def Bmv (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170234 ∨ r = 170236 ∨ r = 170237)
theorem wrM_mvW : BuildRam.wrM Bmv mvW = true := by_decide
theorem frameM_mono {B B' : ℕ → Bool} {c c' : Config} (h : BuildRam.FrameM B c c')
    (hB : ∀ r, B r = true → B' r = true) : BuildRam.FrameM B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2.1, h.2.2.2⟩
  · cases hb : B r
    · rfl
    · zugdc
  · cases hb : B r
    · rfl
    · zugdc
theorem bmv_bcp (r : ℕ) (h : Bmv r = true) : Bcp r = true := by
  simp only [Bmv, Bcp, decide_eq_true_eq] at h ⊢; omega

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}
theorem trI_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ w : ℕ}
    (h10 : c.nreg 170010 = n) (h32 : c.nreg 170232 = g₀) (h33 : c.nreg 170233 = u₀)
    (h36 : c.nreg 170236 = w) (hW : u₀ + ztudd ≤ W) :
    ∃ c' k, Exec P W trI c c' k ∧ 3 ≤ k ∧ k ≤ 5 ∧ c'.nreg 170237 = trE n u₀ g₀ w ∧
      c'.nmem = c.nmem ∧ BuildRam.FrameM ztfru c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a37, a10, am⟩ : ∃ c₁ k₁, Exec P W
      ztirh c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 170237 = u₀ + ztudd ∧ c₁.nreg 170010 = n ∧ c₁.nmem = c.nmem := by
    exec_block
    · config_simp; rw [h33, h36, h32]; omega
    refine ⟨rfl, ?_, ?_, rfl⟩ <;> config_simp <;> simp only [h33, h36, h32, h10]
  zud
  have F₁ := BuildRam.exec_frameM e₁ (by decide : BuildRam.wrM ztfru
    _ = true)
  by_cases hlt : c₁.nreg 170237 < c₁.nreg 170010
  · have ex : Exec P W trI c c₁ _ := .seq e₁ ztzrx
    refine ⟨c₁, _, ex, by_omega, by_omega, ?_, am, F₁⟩
    rw [a37]; unfold trE; zunab
  · obtain ⟨c₂, k₂, e₂, hk₂, b37, bm⟩ : ∃ c₂ k₂, Exec P W (block [.subN 170237 170237 170010])
        c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg 170237 = c₁.nreg 170237 - c₁.nreg 170010 ∧
        c₂.nmem = c₁.nmem := by
      exec_block
      zufeo
    have F₂ := BuildRam.exec_frameM e₂ (by decide : BuildRam.wrM ztfru
      _ = true)
    have ex : Exec P W trI c c₂ _ := .seq e₁ ztsoz
    refine ⟨c₂, _, ex, by_omega, by_omega, ?_, by rw [bm, am], F₁.trans F₂⟩
    rw [b37, a37, a10]; unfold trE; zvmyd
theorem mvW_exec (c : Config) (hw : WordsBounded W c) {src dst : ℕ}
    (h11 : c.nreg 170011 = 1) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hs : src + 1 ≤ W) (hd : dst + 1 ≤ W) :
    ∃ c' k, Exec P W mvW c c' k ∧ k = 4 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst ztvhd ∧
      BuildRam.FrameM Bmv c c' := by
  suffices h : ∃ c' k, Exec P W mvW c c' k ∧ k = 4 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst _ by
    obtain ⟨c', k, e, h1, h2, h3, h4⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, BuildRam.exec_frameM e wrM_mvW⟩
  unfold mvW
  exec_block
  · config_simp; rw [h34, h11]; omega
  · config_simp; rw [h22, h11]; omega
  refine zthnq <;> config_simp <;> simp only [h34, h22, h11]
theorem mvT_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ src dst : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h32 : c.nreg 170232 = g₀)
    (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hs : src + 1 ≤ W) (hd : dst + 1 ≤ W) (ht : u₀ + ztrli ≤ W) :
    ∃ c' k, Exec P W mvT c c' k ∧ 7 ≤ k ∧ k ≤ 9 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst ztgmp ∧
      BuildRam.FrameM Bmv c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a36, ar, am⟩ : ∃ c₁ k₁, Exec P W (block [.loadN 170236 170234]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170236 = c.nmem src ∧ (∀ r, r ≠ 170236 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, ?_, fun r hr => ?_, rfl⟩
    · config_simp; rw [h34]
    · config_simp; zunaw
  have F₁ := BuildRam.exec_frameM e₁ (by decide : BuildRam.wrM Bmv
    _ = true)
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b37, bm, F₂⟩ := trI_exec (P := P) c₁ e₁.wb_right
    ((ar _ by_decide).trans h10) ((ar _ by_decide).trans h32)
    ((ar _ by_decide).trans h33) a36 ht
  have f₂ : ∀ r, r ≠ 170237 → c₂.nreg r = c₁.nreg r := fun r hr => F₂.1 r (by zumwy)
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, d34, d22, dm⟩ : ∃ c₃ k₃, Exec P W
      ztgqy
      c₂ c₃ k₃ ∧ k₃ = 3 ∧ c₃.nreg 170234 = src + 1 ∧ c₃.nreg 170222 = dst + 1 ∧
      c₃.nmem = upd c₂.nmem dst ztgmp := by
    have g34 : c₂.nreg 170234 = src := by_simp_all
    have g22 : c₂.nreg 170222 = dst := by_simp_all
    have g11 : ztuqy := by_simp_all
    exec_block
    · config_simp; rw [g34, g11]; omega
    · config_simp; rw [g22, g11]; omega
    refine zthnq <;> config_simp <;> simp only [g34, g22, g11, b37]
  have F₃ := BuildRam.exec_frameM e₃ (by decide : BuildRam.wrM Bmv
    _ = true)
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, by_omega, d34, d22, by rw [dm, bm, am],
    (F₁.trans (frameM_mono F₂ (fun r hr => by simp at hr; simp [Bmv, hr]))).trans F₃⟩

/-- Seven consecutive updates, away from them. -/
theorem upd7_lo {m : ℕ → ℕ} {d a v0 v1 v2 v3 v4 v5 v6 : ℕ} (h : a < d) :
    upd (upd (upd ztxow ztnxj v4)
      zttis v5) (d + 6) v6 a = m a := by
  rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
    upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
    upd_other _ _ _ by_omega]

/-- Seven consecutive updates, at them. -/
theorem upd7_at {m : ℕ → ℕ} {d v0 v1 v2 v3 v4 v5 v6 : ℕ} :
    let M := upd (upd (upd ztxow
      ztnxj v4) (d + 5) v5) (d + 6) v6
    M d = v0 ∧ M ztet = v1 ∧ M ztvq = v2 ∧ M ztjte = v3 ∧ M ztnxj = v4 ∧
      M zttis = v5 ∧ M (d + 6) = v6 := by
  intro M
  refine ztuv
  · zubzn
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_same]
  · zubzn
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_same]
  · zubzn
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      upd_other _ _ _ by_omega, upd_same]
  · zubzn
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_other _ _ _ by_omega,
      upd_same]
  · zubzn
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, upd_same]
  · zubzn
    zunsi
  · zubzn
    zunkc

/-- **One piece record copied.** -/
theorem cpBody_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ src dst : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h32 : c.nreg 170232 = g₀)
    (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hsd : src + 7 ≤ dst) (hdW : dst + 7 ≤ W)
    (ht0 : u₀ + ztrli ≤ W) (ht2 : u₀ + (c.nmem zthko - g₀) ≤ W)
    (h35 : c.nreg 170235 + 1 ≤ W) (h23 : c.nreg 170223 + 1 ≤ W) :
    ∃ c' k, Exec P W cpBody c c' k ∧ 36 ≤ k ∧ k ≤ 40 ∧
      c'.nreg 170234 = src + 7 ∧ c'.nreg 170222 = dst + 7 ∧
      c'.nreg 170235 = c.nreg 170235 + 1 ∧ c'.nreg 170223 = c.nreg 170223 + 1 ∧
      (∀ a, a < dst → c'.nmem a = c.nmem a) ∧
      c'.nmem dst = trE n u₀ g₀ ztvhd ∧ c'.nmem (dst + 1) = c.nmem ztoif ∧
      c'.nmem zttjf = trE n u₀ g₀ ztbagc ∧
      c'.nmem (dst + 3) = c.nmem ztoig ∧ c'.nmem zttjg = c.nmem ztkfk ∧
      c'.nmem (dst + 5) = c.nmem ztoih ∧ c'.nmem (dst + 6) = c.nmem ztoii ∧
      BuildRam.FrameM Bcp c c' := by
  -- the registers the steps keep
  have keep : ∀ {d d' : Config}, BuildRam.FrameM Bmv d d' →
      d'.nreg 170010 = d.nreg 170010 ∧ d'.nreg 170011 = d.nreg 170011 ∧
      d'.nreg 170232 = d.nreg 170232 ∧ d'.nreg 170233 = d.nreg 170233 ∧
      d'.nreg 170235 = d.nreg 170235 ∧ d'.nreg 170223 = d.nreg 170223 := fun F =>
    ⟨F.1 _ by_decide, F.1 _ by_decide, F.1 _ by_decide, F.1 _ by_decide,
      F.1 _ by_decide, F.1 _ by_decide⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', a34, a22, am, F₁⟩ := mvT_exec (P := P) c hw h10 h11 h32 h33 h34 h22
    by_omega by_omega ht0
  obtain ⟨q10, q11, q32, q33, q35, q23⟩ := keep F₁
  have m1 : c₁.nmem ztoif = c.nmem ztoif := by rw [am, upd_other _ _ _ by_omega]
  obtain ⟨c₂, k₂, e₂, hk₂, b34, b22, bm, F₂⟩ := mvW_exec (P := P) c₁ e₁.wb_right
    (by rw [q11, h11]) a34 a22 by_omega by_omega
  obtain ⟨p10, p11, p32, p33, p35, p23⟩ := keep F₂
  have m2 : c₂.nmem zthko = c.nmem zthko := by
    rw [bm, upd_other _ _ _ by_omega, am, upd_other _ _ _ by_omega]
  obtain ⟨c₃, k₃, e₃, hk₃, hk₃', d34, d22, dm, F₃⟩ := mvT_exec (P := P) c₂ e₂.wb_right
    (by rw [p10, q10, h10]) (by rw [p11, q11, h11]) (by rw [p32, q32, h32]) (by rw [p33, q33, h33])
    b34 b22 by_omega by_omega (by rw [m2]; exact ht2)
  obtain ⟨s10, s11, s32, s33, s35, s23⟩ := keep F₃
  have m3 : c₃.nmem ztoig = c.nmem ztoig := by
    rw [dm, upd_other _ _ _ by_omega, bm, upd_other _ _ _ by_omega, am,
      upd_other _ _ _ by_omega]
  obtain ⟨c₄, k₄, e₄, hk₄, f34, f22, fm, F₄⟩ := mvW_exec (P := P) c₃ e₃.wb_right
    (by rw [s11, p11, q11, h11]) d34 d22 by_omega by_omega
  obtain ⟨t10, t11, t32, t33, t35, t23⟩ := keep F₄
  have m4 : c₄.nmem ztkfk = c.nmem ztkfk := by
    rw [fm, upd_other _ _ _ by_omega, dm, upd_other _ _ _ by_omega, bm,
      upd_other _ _ _ by_omega, am, upd_other _ _ _ by_omega]
  obtain ⟨c₅, k₅, e₅, hk₅, g34, g22, gm, F₅⟩ := mvW_exec (P := P) c₄ e₄.wb_right
    (by rw [t11, s11, p11, q11, h11]) f34 f22 by_omega by_omega
  obtain ⟨u10, u11, u32, u33, u35, u23⟩ := keep F₅
  have m5 : c₅.nmem ztoih = c.nmem ztoih := by
    rw [gm, upd_other _ _ _ by_omega, fm, upd_other _ _ _ by_omega, dm,
      upd_other _ _ _ by_omega, bm, upd_other _ _ _ by_omega, am, upd_other _ _ _ by_omega]
  obtain ⟨c₆, k₆, e₆, hk₆, i34, i22, im, F₆⟩ := mvW_exec (P := P) c₅ e₅.wb_right
    (by rw [u11, t11, s11, p11, q11, h11]) g34 g22 by_omega by_omega
  obtain ⟨v10, v11, v32, v33, v35, v23⟩ := keep F₆
  have m6 : c₆.nmem ztoii = c.nmem ztoii := by
    rw [im, upd_other _ _ _ by_omega, gm, upd_other _ _ _ by_omega, fm,
      upd_other _ _ _ by_omega, dm, upd_other _ _ _ by_omega, bm, upd_other _ _ _ by_omega,
      am, upd_other _ _ _ by_omega]
  obtain ⟨c₇, k₇, e₇, hk₇, j34, j22, jm, F₇⟩ := mvW_exec (P := P) c₆ e₆.wb_right
    (by rw [v11, u11, t11, s11, p11, q11, h11]) i34 i22 by_omega by_omega
  obtain ⟨w10, w11, w32, w33, w35, w23⟩ := keep F₇
  have r35 : c₇.nreg 170235 = c.nreg 170235 := by rw [w35, v35, u35, t35, s35, p35, q35]
  have r23 : c₇.nreg 170223 = c.nreg 170223 := by rw [w23, v23, u23, t23, s23, p23, q23]
  have r11 : c₇.nreg 170011 = 1 := by rw [w11, v11, u11, t11, s11, p11, q11, h11]
  zubgp
  obtain ⟨c₈, k₈, e₈, hk₈, l35, l23, lr, lm⟩ : ∃ c₈ k₈, Exec P W
      ztiqh c₇ c₈ k₈ ∧ k₈ = 2 ∧
      c₈.nreg 170235 = c.nreg 170235 + 1 ∧ c₈.nreg 170223 = c.nreg 170223 + 1 ∧
      (∀ r, r ≠ 170235 → r ≠ 170223 → c₈.nreg r = c₇.nreg r) ∧ c₈.nmem = c₇.nmem := by
    exec_block
    · config_simp; zuoke; omega
    · config_simp; zuokf; omega
    refine zticq
    · config_simp; zuoke
    · config_simp; zuokf
    · config_simp; zunhr
  have F₈ := BuildRam.exec_frameM e₈ (by decide : BuildRam.wrM Bcp
    _ = true)
  have ex : Exec P W cpBody c c₈ _ :=
    .seq e₁ ztey
  -- the memory
  have mem : ∀ a, c₈.nmem a = upd (upd (upd (upd (upd (upd (upd c.nmem dst
      ztgmp) (dst + 1) (c.nmem (src + 1)))
      zttjf (trE n u₀ g₀ ztbagc)) (dst + 3) (c.nmem (src + 3)))
      zttjg (c.nmem ztkfk)) (dst + 5) (c.nmem (src + 5))) (dst + 6) (c.nmem (src + 6)) a := by
    zumgj
    rw [lm, jm, ← m6, im, ← m5, gm, ← m4, fm, ← m3, dm, ← m2, bm, ← m1, am]
  refine ⟨c₈, _, ex, by_omega, by_omega, by zuoel; exact j34,
    by zuoel; exact j22, l35, l23, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, (frameM_mono (F₁.trans (F₂.trans (F₃.trans (F₄.trans (F₅.trans ztuyw)))))
      bmv_bcp).trans F₈⟩
  · zuoxe; exact upd7_lo ha
  all_goals (zuoxe)
  all_goals first
    | exact upd7_at.1 | exact upd7_at.2.1 | exact upd7_at.2.2.1 | exact upd7_at.2.2.2.1
    | exact upd7_at.2.2.2.2.1 | exact upd7_at.2.2.2.2.2.1 | exact upd7_at.2.2.2.2.2.2

/-- **The pieces of a slot copied**, translated. -/
theorem cpLoop_exec (c : Config) (hw : WordsBounded W c) {n L q g₀ u₀ O : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h31 : c.nreg 170231 = q)
    (h32 : c.nreg 170232 = g₀) (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = L + 1)
    (h35 : c.nreg 170235 = 0)
    (hLO : L + 1 + 7 * q ≤ O) (hOd : O < c.nreg 170222) (hdW : c.nreg 170222 + 7 * q ≤ W)
    (hcnt : c.nreg 170223 + q ≤ W) (hu : u₀ < n) (hnW : 2 * n ≤ W)
    (hed : ∀ i, i < q → c.nmem zthbc - g₀ < n ∧ c.nmem ztclq - g₀ < n) :
    ∃ c' k, Exec P W cpLoop c c' k ∧ k ≤ 42 * q + 2 ∧ 7 * q ≤ k ∧
      c'.nreg 170222 = c.nreg 170222 + 7 * q ∧ c'.nreg 170223 = c.nreg 170223 + q ∧
      (∀ a, a < c.nreg 170222 → c'.nmem a = c.nmem a) ∧
      (∀ j, j < q → ∀ f, f < 7 →
        c'.nmem ztmfw = pcW (trPcR n u₀ g₀ (rdPc c.nmem L j)) f) ∧
      BuildRam.FrameM Bcp c c' := by
  set d₀ := c.nreg 170222 with hd₀
  set n₀ := c.nreg 170223 with hn₀
  zudvs
  let I : Config → Prop := fun d => WordsBounded W d ∧ ∃ i, i ≤ q ∧ d.nreg 170235 = i ∧
    d.nreg 170234 = L + 1 + 7 * i ∧ d.nreg 170222 = d₀ + 7 * i ∧ d.nreg 170223 = n₀ + i ∧
    (∀ a, a < d₀ → d.nmem a = m₀ a) ∧
    (∀ j, j < i → ∀ f, f < 7 → d.nmem (d₀ + 7 * j + f) = pcW (trPcR n u₀ g₀ (rdPc m₀ L j)) f) ∧
    BuildRam.FrameM Bcp c d
  obtain ⟨c', k, e, ⟨w', i, hiq, r35, r34, r22, r23, hlo, hout, F⟩, hex, hk, hψ⟩ :=
    whileLtN_pot2 (P := P) (a := 170235) (b := 170231) (body := cpBody) I
      (fun d => 42 * (q - d.nreg 170235)) (fun d => d.nreg 170222) ztsa
      (fun d ⟨wd, i, hiq, d35, d34, d22, d23, dlo, dout, dF⟩ hlt => by
        have d31 : d.nreg 170231 = q := by rw [dF.1 _ by_decide]; exact h31
        rw [d35, d31] at hlt
        have dsrc : ∀ f, f < 7 → d.nmem _ = m₀ (L + 1 + 7 * i + f) :=
          fun f hf => dlo _ by_omega
        obtain ⟨he0, he2⟩ := hed i hlt
        obtain ⟨d', k', e', hk', hk'', a34, a22, a35, a23, alo, a0, a1, a2, a3, a4, a5, a6, aF⟩ :=
          cpBody_exec (P := P) d wd ((dF.1 _ by_decide).trans h10)
            ((dF.1 _ by_decide).trans h11) ((dF.1 _ by_decide).trans h32)
            ((dF.1 _ by_decide).trans h33) d34 d22 by_omega by_omega
            (by have := dsrc 0 by_omega; zvnhg at this; zvmwk; omega)
            (by rw [dsrc 2 by_omega]; omega)
            (by rw [d35]; have := hw.1 170231; omega) (by rw [d23]; omega)
        refine ⟨d', k', e', ⟨e'.wb_right, i + 1, by_omega, by zuokg,
          by rw [a34]; ring, by rw [a22]; ring, by rw [a23, d23]; ring,
          by grind, fun j hj f hf => ?_, dF.trans aF⟩,
          by zuokg; omega, by rw [a22, d22]; omega⟩
        rcases ztfcl with hj' | rfl
        · rw [alo _ by_omega]; exact by_grind
        · interval_cases f
          · zvnhg; rw [a0]
            have := dsrc 0 by_omega; zvnhg at this; zvmwk; rfl
          · rw [a1, dsrc 1 by_omega]; rfl
          · rw [a2, dsrc 2 by_omega]; rfl
          · rw [a3, dsrc 3 by_omega]; rfl
          · rw [a4, dsrc 4 by_omega]; rfl
          · rw [a5, dsrc 5 by_omega]; rfl
          · rw [a6, dsrc 6 by_omega]; rfl)
      (c := c) ⟨hw, 0, by_omega, h35, by_omega, by_omega, by_omega, fun a _ => rfl,
        fun j hj => absurd hj by_omega, BuildRam.FrameM.refl _ _⟩
  have r31 : c'.nreg 170231 = q := by rw [F.1 _ by_decide]; exact h31
  rw [r35, r31] at hex
  have hi : i = q := by_omega
  zuipx
  refine ⟨c', k, e, by rw [h35] at hk; simpa using hk, by rw [r22] at hψ; omega, r22, r23, hlo,
    hout, F⟩
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
def asmInit : Stmt := block [.copyN 170221 9999, .addN 170222 170221 170011, .constN 170223 0]

/-- The fields of slot `k` and the start of its copy. -/
def asmSet (k : ℕ) : Stmt :=
  block [.copyN 170230 zteko, .copyN 170231 ztekp,
    .copyN 170232 ztekq, .copyN 170233 ztekr, .addN 170234 170230 170011,
    .constN 170235 0]

/-- Copy the pieces of slot `k` if it is recorded. -/
def asmK (k : ℕ) : Stmt := .ifLtN ztvc 170011 .skip (.seq ztqdr cpLoop)

/-- The end: the number of pieces, the answer register, the allocator. -/
def finC : Stmt := block [.storeN 170221 170223, .copyN 150010 170221, .copyN 9999 170222]

/-- **The assembly of the answer.** -/
def asmC : Stmt :=
  .seq asmInit (.seq (asmK 0) (.seq (asmK 1) (.seq (asmK 2) (.seq (asmK 3) finC))))

/-- The registers the copies of the assembly write. -/
def Basm (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170223 ∨ (170230 ≤ r ∧ r < 170238))
theorem wrM_asmSet (k : ℕ) : BuildRam.wrM Basm ztqdr = true := rfl

/-! ## The invariant -/

/-- **The assembly so far**: the pieces of the slots `sls` copied and translated from `O + 1`
on, counted in `170223`, the output pointer in `170222`, the memory up to `O` unchanged. -/
structure AsmSt (m₀ : ℕ → ℕ) (n O : ℕ) (sls : List Slot) (c : Config) : Prop where
  r21 : c.nreg 170221 = O
  r22 : c.nreg 170222 = O + 1 + 7 * (sls.flatMap ztcba).length
  r23 : c.nreg 170223 = (sls.flatMap ztcba).length
  lo : ∀ a, a < O + 1 → c.nmem a = m₀ a
  out : ∀ j (hj : j < (sls.flatMap ztcba).length) f, f < 7 →
    c.nmem (O + 1 + 7 * j + f) = pcW ((sls.flatMap ztcba)[j]'hj) f
theorem slotPcs_length (m : ℕ → ℕ) (n : ℕ) (sl : Slot) : (slotPcs m n sl).length = sl.q := by
  zumpn

/-- **One more slot copied.** -/
theorem AsmSt.step {m₀ : ℕ → ℕ} {n O : ℕ} {sls : List Slot} {sl : Slot} {c c' : Config}
    (h : AsmSt m₀ n O sls c) (r21 : c'.nreg 170221 = O)
    (r22 : c'.nreg 170222 = c.nreg 170222 + 7 * sl.q)
    (r23 : c'.nreg 170223 = c.nreg 170223 + sl.q)
    (hlo : ∀ a, a < c.nreg 170222 → c'.nmem a = c.nmem a)
    (hout : ∀ j, j < sl.q → ∀ f, f < 7 →
      c'.nmem ztmfw = pcW (trPcR n sl.u₀ sl.g₀ (rdPc m₀ sl.L j)) f) :
    AsmSt m₀ n O ztped c' := by
  have e : (sls ++ [sl]).flatMap ztcba = sls.flatMap ztcba ++ slotPcs m₀ n sl := by
    simp
  have hl : ((sls ++ [sl]).flatMap ztcba).length =
      (sls.flatMap ztcba).length + sl.q := by
    rw [e, List.length_append, slotPcs_length]
  have h22 := h.r22
  refine ⟨r21, by_omega, by rw [hl, r23, h.r23], fun a ha => ?_,
    fun j hj f hf => ?_⟩
  · rw [hlo a by_omega]; exact h.lo a ha
  · zumdq
    zvnen at hj'
    have hget : ((sls ++ [sl]).flatMap ztcba)[j]'hj =
        (sls.flatMap ztcba ++ slotPcs m₀ n sl)[j]' by_grind := by
      simp
    zujiy
    by_cases hjl : j < (sls.flatMap ztcba).length
    · rw [List.getElem_append_left hjl, hlo _ by_omega]
      exact h.out j hjl f hf
    · push Not at hjl
      rw [List.getElem_append_right hjl]
      have hi : j - (sls.flatMap ztcba).length < sl.q := by_omega
      have := hout _ hi f hf
      rw [show c.nreg 170222 + 7 * (j - (sls.flatMap ztcba).length) + f =
        O + 1 + 7 * j + f by zuoug; omega] at this
      zubk
      zumpn

/-- The slots recorded among the first `k` are among the first `K ≥ k`. -/
theorem slotsOf_prefix {c : Config} {k : ℕ} : ∀ {K : ℕ}, k ≤ K →
    ∃ l, slotsOf c K = slotsOf c k ++ l
  | 0, hk => ⟨[], by_simp_all⟩
  | K + 1, hk => by
    zukln
    · obtain ⟨l, hl⟩ := slotsOf_prefix (c := c) (k := k) (K := K) by_omega
      exact ⟨l ++ (if c.nreg (170200 + 5 * K) = 1 then [slotAt c K] else []),
        by simp only [slotsOf, hl, List.append_assoc]⟩
    simp_all
variable {c : Config}
theorem flat_le {m : ℕ → ℕ} {n k K : ℕ} (hk : k ≤ K) :
    ((slotsOf c k).flatMap ztkfi).length ≤ ((slotsOf c K).flatMap ztkfi).length := by
  obtain ⟨l, hl⟩ := slotsOf_prefix (c := c) hk
  simp_all
theorem mem_slotsOf_of {k : ℕ} (hf : c.nreg ztvc = 1) :
    ∀ {K : ℕ}, k < K → slotAt c k ∈ slotsOf c K
  | 0, hk => absurd hk by_omega
  | K + 1, hk => by
    simp only [slotsOf, List.mem_append]
    rcases (show k < K ∨ k = K by omega) with h | rfl
    · exact Or.inl (mem_slotsOf_of hf h)
    simp_all
theorem SlotsOK.mem {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} :
    ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      ∀ sl ∈ sls, ∃ Va Vb, SlotOK P m E Hγ e₁ Va Vb sl
  | _, [], _, _, _, h => by_simp_all
  | V, s :: sls, _, ⟨V₁, h1, h2⟩, sl, hsl => by
    rcases List.mem_cons.1 hsl with rfl | hsl
    · grind
    · exact SlotsOK.mem h2 sl hsl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}

/-- **The copy of slot `k`.** -/
theorem asmK_exec (k : ℕ) (hk : k < 4) (c : Config) (hw : WordsBounded W c) {c₀ : Config}
    {n O Hγ e₁ : ℕ} (hA : AsmSt c₀.nmem n O (slotsOf c₀ k) c)
    (hsl : ∀ r, 170200 ≤ r → r < 170220 → c.nreg r = c₀.nreg r)
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1)
    (hbit : c₀.nreg ztvc ≤ 1)
    (hok : c₀.nreg ztvc = 1 → ∃ Va Vb, SlotOK P c₀.nmem O Hγ e₁ Va Vb (slotAt c₀ k))
    (hn : n = (Qof P).n) (hnW : 2 * n ≤ W)
    (hroom : O + 1 + 7 * ((slotsOf c₀ zts).flatMap ztevp).length ≤ W) :
    ∃ c' k', Exec P W ztven c c' k' ∧
      k' + 42 * ((slotsOf c₀ k).flatMap ztevp).length ≤
        42 * ((slotsOf c₀ zts).flatMap ztevp).length + 12 ∧
      7 * ((slotsOf c₀ zts).flatMap ztevp).length ≤
        7 * ((slotsOf c₀ k).flatMap ztevp).length + k' ∧
      AsmSt c₀.nmem n O (slotsOf c₀ zts) c' ∧ BuildRam.FrameM Basm c c' := by
  have hsucc : slotsOf c₀ zts = slotsOf c₀ k ++
      (if c₀.nreg ztvc = 1 then [slotAt c₀ k] else []) := rfl
  have h0 : c.nreg ztvc = c₀.nreg ztvc := hsl _ by_omega by_omega
  by_cases hf : c₀.nreg ztvc = 1
  · -- the slot is recorded: copy it
    have hlt : ¬ c.nreg ztvc < c.nreg 170011 := by_omega
    obtain ⟨Va, Vb, hs⟩ := hok hf
    obtain ⟨hu, hLE, hq, hq1, hed⟩ := slotOK_edges hs
    set sl := slotAt c₀ k with hsld
    have e : slotsOf c₀ zts = slotsOf c₀ k ++ [sl] := by_simp_all
    have hlen : ((slotsOf c₀ zts).flatMap ztevp).length =
        ((slotsOf c₀ k).flatMap ztevp).length + sl.q := by
      rw [e, List.flatMap_append, List.length_append, List.flatMap_singleton, slotPcs_length]
    have f1 : c.nreg zteko = sl.L := hsl _ by_omega by_omega
    have f2 : c.nreg ztekp = sl.q := hsl _ by_omega by_omega
    have f3 : c.nreg ztekq = sl.g₀ := hsl _ by_omega by_omega
    have f4 : c.nreg ztekr = sl.u₀ := hsl _ by_omega by_omega
    have h22 := hA.r22
    have h23 := hA.r23
    -- the fields
    obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a33, a34, a35, ar, am⟩ : ∃ c₁ k₁,
        Exec P W ztqdr c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 170230 = sl.L ∧ c₁.nreg 170231 = sl.q ∧
        c₁.nreg 170232 = sl.g₀ ∧ c₁.nreg 170233 = sl.u₀ ∧ c₁.nreg 170234 = sl.L + 1 ∧
        c₁.nreg 170235 = 0 ∧ (∀ r, (r < 170230 ∨ 170236 ≤ r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem := by
      unfold asmSet
      exec_block
      · config_simp; omega
      · omega
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
      · tauto
      · config_simp; simp only [upd]; grind
      · config_simp; simp only [upd]; grind
      · config_simp; simp only [upd]; grind
      · config_simp; omega
      · config_simp
      · config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
    have F₁ := BuildRam.exec_frameM e₁ (wrM_asmSet k)
    zud
    -- the copy
    obtain ⟨c₂, k₂, e₂, hk₂, hk₂', d22, d23, dlo, dout, F₂⟩ := cpLoop_exec (P := P) c₁ w₁
      (n := n) (L := sl.L) (q := sl.q) (g₀ := sl.g₀) (u₀ := sl.u₀) (O := O)
      ((ar _ by_omega).trans h10) ((ar _ by_omega).trans h11) a31 a32 a33 a34 a35 hLE
      by_grind by_grind
      by_grind by_omega hnW
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hed i hi
        rw [am, hA.lo _ by_omega, hA.lo _ by_omega, hn]
        exact ztomj)
    have F₂' : BuildRam.FrameM Basm c₁ c₂ := frameM_mono F₂ (fun r hr => by
      simp only [Bcp, Basm, decide_eq_true_eq] at hr ⊢; omega)
    have q21 : c₂.nreg 170221 = O := by rw [F₂.1 _ by_decide, ar _ by_omega]; exact hA.r21
    have q22 : c₁.nreg 170222 = c.nreg 170222 := ar _ by_omega
    have q23 : c₁.nreg 170223 = c.nreg 170223 := ar _ by_omega
    have hA' : AsmSt c₀.nmem n O (slotsOf c₀ k ++ [sl]) c₂ := hA.step q21
      by_omega by_omega
      ztxl
      (fun j hj f hf => by
        rw [← q22, dout j hj f hf, rdPc_congr (m := c₀.nmem) (m' := c₁.nmem) (E := O + 1)
          (fun a ha => by zuoem; exact hA.lo a ha) by_omega])
    refine ⟨c₂, _, .ifLtN_false hlt ztyv, by_omega, by_omega,
      by grind, (frameM_mono F₁ (fun r hr => hr)).trans F₂'⟩
  · -- the slot is free
    have hf0 : c₀.nreg ztvc = 0 := by_omega
    have hlt : c.nreg ztvc < c.nreg 170011 := by_omega
    have e : slotsOf c₀ zts = slotsOf c₀ k := by_simp_all
    refine ⟨c, _, .ifLtN_true hlt ztjd, by_grind, by_simp_all,
      by simp_all, BuildRam.FrameM.refl _ _⟩
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
def Basm' (r : ℕ) : Bool := Basm r || decide (r = 170221)
theorem basm_io {r : ℕ} (h : Basm' r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band' (Or.inl (by simp only [Basm', Basm, Bool.or_eq_true, decide_eq_true_eq] at h; omega))
section exec
variable {P : Polygon} {W : ℕ}
variable {k₂ k₃ k₄ k₅ L1 L2 L3 L4 : ℕ}
set_option maxRecDepth 20000 in
theorem asm_cost (h2 : k₂ + 42 * 0 ≤ 42 * L1 + 12)
    (h3 : k₃ + 42 * L1 ≤ 42 * L2 + 12) (h4 : k₄ + 42 * L2 ≤ 42 * L3 + 12)
    (h5 : k₅ + 42 * L3 ≤ 42 * L4 + 12) : 3 + zthil ≤ 42 * L4 + 60 := by
  omega
theorem asm_low (h2 : 7 * L1 ≤ 7 * 0 + k₂)
    (h3 : 7 * L2 ≤ 7 * L1 + k₃) (h4 : 7 * L3 ≤ 7 * L2 + k₄) (h5 : 7 * L4 ≤ 7 * L3 + k₅) :
    1 + 7 * L4 ≤ 3 + zthil := by
  omega

/-- **The assembly of the answer.** -/
theorem asmC_exec (c : Config) (hw : WordsBounded W c) {n Hγ e₁ : ℕ} {V0 V : ℝ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (hn : n = (Qof P).n) (hnW : 2 * n ≤ W)
    (hok : SlotsOK P c.nmem ztm Hγ e₁ V0 ztuap V)
    (hbit : ∀ j, j < 4 → c.nreg ztbln ≤ 1)
    (hroom : c.nreg ALLOC + 42 * ((slotsOf c 4).flatMap ztevo).length + 60 ≤ W) :
    ∃ c' k, Exec P W asmC c c' k ∧
      k ≤ 42 * ((slotsOf c 4).flatMap ztevo).length + 60 ∧
      c'.nreg 150010 = c.nreg ALLOC ∧
      c'.nmem ztm = ((slotsOf c 4).flatMap ztevo).length ∧
      (∀ j (hj : j < ((slotsOf c 4).flatMap ztevo).length) f, f < 7 →
        c'.nmem (c.nreg ALLOC + 1 + 7 * j + f) =
          pcW (((slotsOf c 4).flatMap ztevo)[j]'hj) f) ∧
      c'.nreg ALLOC = c.nreg ALLOC + 1 + 7 * ((slotsOf c 4).flatMap ztevo).length ∧
      Frame ioBands c c' k := by
  set O := c.nreg ALLOC with hO
  set Lf : ℕ → ℕ := fun j => ((slotsOf c j).flatMap ztevo).length with hLf
  have hL0 : Lf 0 = 0 := by_rfl
  have hLle : ∀ j, j ≤ 4 → Lf j ≤ Lf 4 := fun j hj => flat_le hj
  -- the start
  have hA9 : c.nreg 9999 = O := rfl
  obtain ⟨c₁, k₁, x₁, hk₁, a21, a22, a23, ar, am⟩ : ∃ c₁ k₁, Exec P W asmInit c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 170221 = O ∧ c₁.nreg 170222 = O + 1 ∧ c₁.nreg 170223 = 0 ∧
      (∀ r, r ≠ 170221 → r ≠ 170222 → r ≠ 170223 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    unfold asmInit
    exec_block
    · config_simp; omega
    · omega
    simp_all
  have F₁ : BuildRam.FrameM Basm' c c₁ := BuildRam.exec_frameM x₁ by_decide
  have A₁ : AsmSt c.nmem n O (slotsOf c 0) c₁ :=
    ⟨a21, by_simp_all, by_simp_all, fun a _ => by zuoem,
      fun j hj => by_grind⟩
  -- one slot
  have step : ∀ k, k < 4 → ∀ d : Config, WordsBounded W d → AsmSt c.nmem n O (slotsOf c k) d →
      BuildRam.FrameM Basm' c d →
      ∃ d' k', Exec P W ztven d d' k' ∧ k' + 42 * Lf k ≤ 42 * Lf zts + 12 ∧
        7 * Lf zts ≤ 7 * Lf k + k' ∧ AsmSt c.nmem n O (slotsOf c zts) d' ∧
        BuildRam.FrameM Basm' c d' := fun k hk d wd hA hF => by
    have hsl : ∀ r, 170200 ≤ r → r < 170220 → d.nreg r = c.nreg r := by
      intro r r1 r2
      apply hF.1 r
      simp only [Basm', Basm, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega
    obtain ⟨d', k', e', h1, h2, hA', F'⟩ := asmK_exec (P := P) k hk d wd (c₀ := c) (Hγ := Hγ)
      (e₁ := e₁) hA hsl
      ((hF.1 _ by_decide).trans h10) ((hF.1 _ by_decide).trans h11) (hbit k hk)
      (fun hf => SlotsOK.mem hok _ (mem_slotsOf_of hf by_omega)) hn hnW
      by_grind
    exact ⟨d', k', e', h1, h2, hA', hF.trans (frameM_mono F' (fun r hr => by
      simp only [Basm', hr, Bool.true_or]))⟩
  obtain ⟨c₂, k₂, e₂, p2, q2, A₂, F₂⟩ := step 0 by_norm_num c₁ x₁.wb_right A₁ F₁
  obtain ⟨c₃, k₃, e₃, p3, q3, A₃, F₃⟩ := step 1 by_norm_num c₂ e₂.wb_right A₂ F₂
  obtain ⟨c₄, k₄, e₄, p4, q4, A₄, F₄⟩ := step 2 by_norm_num c₃ e₃.wb_right A₃ F₃
  obtain ⟨c₅, k₅, e₅, p5, q5, A₅, F₅⟩ := step 3 by_norm_num c₄ e₄.wb_right A₄ F₄
  rw [hL0] at p2 q2
  zuef
  -- the end
  obtain ⟨c₆, k₆, e₆, hk₆, b10, bA, bm, br, brr, brm, bo⟩ : ∃ c₆ k₆, Exec P W finC c₅ c₆ k₆ ∧
      k₆ = 3 ∧ c₆.nreg 150010 = O ∧ c₆.nreg ALLOC = O + 1 + 7 * Lf 4 ∧
      c₆.nmem = upd c₅.nmem O (Lf 4) ∧ (∀ r, r ≠ 150010 → r ≠ ALLOC → c₆.nreg r = c₅.nreg r) ∧
      c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have g21 := A₅.r21
    have g22 := A₅.r22
    have g23 := A₅.r23
    unfold finC
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp; rw [g22, show (ALLOC : ℕ) = 9999 from rfl, upd_same]
    · grind
    · config_simp; unfold ALLOC at h2; zunhr
  have ex : Exec P W asmC c c₆ (k₁ + zthim) :=
    .seq x₁ ztfv
  have hk := asm_cost p2 p3 p4 p5
  have hl := asm_low q2 q3 q4 q5
  zvmxv at hl hk
  refine ⟨c₆, _, ex, by_grind, b10, by rw [bm, upd_same], fun j hj f hf => ?_,
    bA, ⟨fun r hr ha => ?_, fun r hr => ?_, fun a ha => ?_, fun a _ => ?_, by rw [bo, F₅.2.2.2],
      by omega, by_omega⟩⟩
  · zugud
    exact A₅.out j hj f hf
  · have hb : ztukc := by
      cases hB : Basm' r
      · rfl
      · zuhua
    rw [br r ztwmm ha]
    exact F₅.1 r hb
  · have hb : ztukc := by
      cases hB : Basm' r
      · rfl
      · zuhua
    zuoen; exact F₅.2.1 r hb
  · zugud
    exact A₅.lo a by_omega
  · rw [brm, F₅.2.2.1]
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def setOne : Stmt :=
  block [.copyN 170033 170001, .copyN 170034 170002, .copyN 170035 170031, .copyN 170036 170030,
    .copyN 170037 170032]

/-- The first of two sub-queries: two edges from the start. -/
def setTwoA : Stmt :=
  block [.copyN 170033 170001, .copyN 170034 170002, .constN 170035 2, .constN 170036 0,
    .constN 170037 2]

/-- The second of two sub-queries: from the vertex `(e₁ + 2) mod n` to the end. -/
def setTwoB : Stmt :=
  .seq (block [.addN 170033 170001 170018, .constN 170034 0, .subN 170035 170031 170018,
      .copyN 170036 170030, .subN 170037 170032 170018])
    (.ifLtN 170033 170010 .skip (block [.subN 170033 170033 170010]))

/-- The answer at a vertex. -/
def outV : Stmt :=
  .seq ztoyw
    (.seq ivF (block [.constN 140010 1, .copyN 140011 170096, .constN 140012 0]))

/-- The answer on an edge. -/
def outE : Stmt :=
  .seq ztoyw
    (.seq iEdgeF (block [.constN 140010 1, .copyN 140011 170096, .addN 140012 170073 170011]))

/-- **The answer.** -/
def outI : Stmt :=
  .ifLtN 170070 170011 (block [.constN 140010 0]) (.ifLtN 170071 170011 outV outE)

/-- The registers the parameter blocks write. -/
def Bset (r : ℕ) : Bool := decide (170033 ≤ r ∧ r < 170038)
theorem wr_setOne : wr Bset setOne = true := by_decide
theorem wr_setTwoA : wr Bset setTwoA = true := by_decide
theorem wr_setTwoB : wr Bset setTwoB = true := by_decide

/-- The registers the answer writes. -/
def Bout (r : ℕ) : Bool :=
  decide (140010 ≤ r ∧ r < 140013) || decide (r = 170092 ∨ r = 170095 ∨ r = 170096)
theorem wr_outI : wr Bout outI = true := by_decide

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
variable (c : Config)
theorem setOne_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setOne c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = c.nreg 170031 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 ∧ FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setOne c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = c.nreg 170031 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 by
    zutd
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setOne⟩
  unfold setOne
  exec_block
  simp
theorem setTwoA_exec (hw : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' k, Exec P W setTwoA c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = 2 ∧ c'.nreg 170036 = 0 ∧
      c'.nreg 170037 = 2 ∧ FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setTwoA c c' k ∧ k = 5 ∧ c'.nreg 170033 = c.nreg 170001 ∧
      c'.nreg 170034 = c.nreg 170002 ∧ c'.nreg 170035 = 2 ∧ c'.nreg 170036 = 0 ∧
      c'.nreg 170037 = 2 by
    zutd
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setTwoA⟩
  unfold setTwoA
  exec_block
  all_goals first | omega | skip
  simp
theorem setTwoB_exec (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) :
    ∃ c' k, Exec P W setTwoB c c' k ∧ k ≤ 8 ∧ c'.nreg 170033 = ztful % P.n ∧
      c'.nreg 170034 = 0 ∧ c'.nreg 170035 = c.nreg 170031 - 2 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 - 2 ∧
      FrameB Bset c c' := by
  suffices h : ∃ c' k, Exec P W setTwoB c c' k ∧ k ≤ 8 ∧ c'.nreg 170033 = ztful % P.n ∧
      c'.nreg 170034 = 0 ∧ c'.nreg 170035 = c.nreg 170031 - 2 ∧
      c'.nreg 170036 = c.nreg 170030 ∧ c'.nreg 170037 = c.nreg 170032 - 2 by
    zutd
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameB e wr_setTwoB⟩
  zucg

  zucgt
  unfold setTwoB
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hS.r1, hS.r18]; omega
  · omega
  by_cases h : s.e₁ + 2 < P.n
  · refine spec_ifLtN_true (by config_simp; rw [hS.r1, hS.r18, hS.r10]; exact h) ?_
    refine spec_skip ‹_› ztbfj <;> config_simp
    · rw [hS.r1, hS.r18, Nat.mod_eq_of_lt h]
    · zugur
    · zugur
  · refine spec_ifLtN_false (by config_simp; rw [hS.r1, hS.r18, hS.r10]; exact h) ?_
    exec_block
    refine ztbfj <;> config_simp
    · rw [hS.r1, hS.r18, hS.r10, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
    · zugur
    · zugur

/-- **The answer of the interior shooter.** -/
theorem outI_exec (hw : WordsBounded W c) (hS : SEnv P W O s c) {S : Set Point}
    {z : Point} {σ : ℝ} (hB : BestI P c S z σ) :
    ∃ c' k, Exec P W outI c c' k ∧ k ≤ 20 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit S z σ t ∧
        ProperPos ztwiq zta P.n ztdql ∧
        c'.nreg 140011 < (interiorModel zta).W.n ∧
        (interiorModel zta).pos zta ztdql = rayPt z σ t) ∧
      ztlke ∧ FrameB Bout c c' := by
  zudq
  have hD : ztxpn := (goodShear_epsOf hS.good.2).2.1
  zucgt
  zucg

  suffices h : ∃ c' k, Exec P W outI c c' k ∧ k ≤ 20 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit S z σ t ∧
        ProperPos ztwiq zta P.n ztdql ∧
        c'.nreg 140011 < (interiorModel zta).W.n ∧
        (interiorModel zta).pos zta ztdql = rayPt z σ t) ∧
      ztlke by
    zubgy
    exact ⟨c', k, e, h1, h2, h3, exec_frameB e wr_outI⟩
  zugpi
  unfold outI
  by_cases g : c.nreg 170070 < c.nreg 170011
  · zumjr
    exec_block
    · omega
    refine ⟨by_omega, fun h => by_simp_all, fun _ => hb3 ztlho⟩
  zumjk
  obtain ⟨sb, t, hsb, hbs, hfh, hev⟩ := hb2 ztlho
  have hbsQ := hbs
  zvnoq at hn
  obtain ⟨hpp, hlt, hpos⟩ := iPos_spec hD hn hbsQ
  rw [hev] at hpos
  cases sb with
  | vtx q =>
    obtain ⟨k0, kq⟩ := hsb
    refine spec_ifLtN_true (by rw [k0, hS.r11]; omega) ?_
    unfold outV
    refine spec_seq ?_
    exec_block
    zucsb
    obtain ⟨c₂, k₂, e₂, hk₂, rfl⟩ := ivF_exec (P := P) _ w (by config_simp; exact hS.r11)
    refine spec_seq ⟨_, k₂, e₂, ?_⟩
    zue
    exec_block
    · omega
    · omega
    have hiv : ivV ztjrv ztmft (c.nreg 170072) = iv zta q := by
      rw [kq]; exact hS.ivv q
    refine ⟨by_omega, fun _ => ⟨t, hfh, ?_, ?_, ?_⟩, fun h => (h (by config_simp)).elim⟩
    · config_simp; zuoxm; zvnao at hpp; tauto
    · config_simp; rw [hiv, mi_n]; tauto
    · config_simp; zuoxm; tauto
  | onEdge e h =>
    obtain ⟨k0, ke, kh⟩ := hsb
    zubv
    zumtu
    refine spec_seq ?_
    exec_block
    zucsb
    have he : ztmvo := by have := hbs.1; omega
    have hh : h < P.n := by have := hbs.2.1; omega
    obtain ⟨c₂, k₂, e₂, hk₂, i96, ir, im, irr, irm, io⟩ := iEdgeF_exec (P := P) _ w
      (by config_simp; exact hS.r11) (by config_simp; exact hS.r10) (by config_simp; exact hS.r19)
      (by config_simp; grind)
    zulon
    zue
    have b73 : c₂.nreg 170073 = h := by_simp_all
    have b11 : ztuqy := by rw [ir _ by_decide by_decide]; config_simp; exact hS.r11
    have hie : c₂.nreg 170096 = iEdge zta e := by
      rw [i96]; config_simp; rw [ke, ← hS.iev e]
    exec_block
    · omega
    · config_simp; omega
    refine ⟨by_omega, fun _ => ⟨t, hfh, ?_, ?_, ?_⟩, fun h => (h (by config_simp)).elim⟩
    · config_simp; zunyu; zvnao at hpp; exact hpp
    · config_simp; rw [hie, mi_n]; exact hlt
    · config_simp; zunyu; exact hpos
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def frontI : Stmt := .seq (saveS 140000) (.seq ztncs originI)

/-- The static data of a query of the interior shooter. -/
noncomputable def statOf (P : Polygon) (c : Config) (o : Origin) : Stat :=
  ⟨c.nreg ALLOC, c.nmem, c.nreg 140013, c.nreg 140009, c.nreg 140001, c.nreg 140002,
    c.nreg 140003, c.nreg 140004, c.nreg 140008, oSym zta o⟩
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface}

/-- **The set-up of the interior shooter.** -/
theorem frontI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hX : (gradeCtx O).holds P c.nmem ztvhp ztm)
    (hcap : c.nreg 140009 ≤ (gradeCtx O).cap P c.nmem ztvhp)
    (hwf : c.nreg 140000 + 6 ≤ c.nreg ALLOC)
    (hbit : c.nmem zthuk = 1 ↔ Mountain.LeftInside zta) {o : Origin}
    (ho : OriginIn c 140005 o) (hol : o.Lt P.n ztwiq)
    (hroom : c.nreg ALLOC + 8 ≤ W) :
    ∃ c' k, Exec P W frontI c c' k ∧ k ≤ 52 ∧ SEnv P W O (statOf P c o) c' ∧
      c'.nreg 170070 = 0 ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧ Frame ioBands c c' k := by
  zuers
  zucgn

  -- save
  obtain ⟨c₁, e₁, a10, a13, ar, arr, am, arm, ao⟩ := saveS_exec (P := P) 140000 by_norm_num c hw
  zud
  zuhvo
  have F₁ : ztsbk := frameIO_of_frameB
    (B := fun r => decide ztgxv)
    ztywf
    ⟨fun r hr => ar r by_simp_all, fun r _ => by zuoxf, am, arm, ao⟩ 11
  zulkm
  have a0 : c₁.nreg 170000 = c.nreg 140000 := a10 0 by_norm_num
  have a13' : c₁.nreg 170013 = c.nreg 140013 := a13
  -- the constants and the host record
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b10, b11, b12, b18, b19, b16, b17, b14, b14', b15, bA, b70, bm0,
      bm1, bm2, bm3, bmlo, br, brr, brm, bo⟩ := initI_exec (P := P) c₁ w₁
    by_omega by_omega
    by_omega by_omega by_omega
  zue
  have F₂ : ztmte := by
    refine ⟨fun r hr ha => br r ?_, fun r _ => by zuoen, fun a ha => bmlo a ha,
      fun a _ => by zuoxg, bo, by_omega, by_omega⟩
    zuhgn
    zumqi
    zuhbg
    rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (try (subst h; decide))
    zulxm
  -- the origin
  have hcopy : ∀ r, 170000 ≤ r → r < 170010 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    br r zteqg
  have ho₂ : OriginIn c₂ 170005 o := by
    have e5 : c₂.nreg 170005 = c.nreg 140005 := by_grind
    have e6 : c₂.nreg 170006 = c.nreg 140006 := by_grind
    have e7 : c₂.nreg 170007 = c.nreg 140007 := by_grind
    exact ShotList.originIn_copy ho e5 e6 e7
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃, rr₃, rm₃, o₃⟩ := originI_exec (P := P) c₂ w₂ hn3 b11 b10 b12
    b18 b19 by_grind b14' ho₂ hol by_omega
  have F₃ : ztmtf := frameIO_of_frameB
    (B := fun r => decide (r = 170020 ∨ r = 170021 ∨ r = 170022 ∨ r = 170092 ∨ r = 170095 ∨
      r = 170096))
    ztyex
    ⟨fun r hr => r₃ r (by unfold BorgR; grind), fun r _ => by zuoek, m₃, rm₃, o₃⟩ k₃
  have k3 : ztkoy := r₃
  have g : ∀ r, ¬ BorgR r → ¬ BinitR r → c₃.nreg r = c₁.nreg r := fun r h1 h2 => by
    grind
  have gs : ∀ i, i < 10 → c₃.nreg ztner = c.nreg ztsrd := fun i hi => by
    zuoet; grind
  have q : ztkoy := k3
  have ex : Exec P W frontI c c₃ ztzsn := .seq e₁ ztcr
  have cA : ztpno := by
    rw [q _ (by unfold BorgR ALLOC; omega), bA, aA]
  refine ⟨c₃, _, ex, by_omega, ⟨hG, hHW, gs 1 by_norm_num, gs 2 by_norm_num,
    gs 3 by_norm_num, gs 4 by_norm_num, gs 8 by_norm_num, gs 9 by_norm_num,
    by zuoet; exact a13',
    by zumzs; omega, by zumzs; omega,
    by zumzs; omega, by zumzs; omega,
    by zumzs; omega,
    by rw [q _ ztbeh, b14, a0, am]; omega,
    by zumzs; omega,
    by rw [q _ ztbeh, b15, aA]; rfl,
    by rw [q _ ztbeh, b16, a13', am]; rfl,
    by rw [q _ ztbeh, b17, a13', am]; rfl, s₃,
    fun a ha => by rw [m₃, bmlo a ztmcx, am]; rfl,
    by zumzp; show c₂.nmem ztm = 1; grind,
    by zumzp; show c₂.nmem ztccv = 0; grind,
    by zumzp; show c₂.nmem zteep = 0; grind,
    by zumzp; show c₂.nmem zteeq = P.n - 1; grind,
    by zuoxh; rfl, hX, hcap⟩,
    by zumzs; omega, cA,
    ((F₁.trans F₂).trans F₃).mono by_simp by_omega⟩
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def branchI (sh : Stmt) : Stmt :=
  .ifLtN 170032 170010 (.seq setOne ztibb)
    (.seq setTwoA (.seq ztibb (.seq setTwoB ztibb)))

/-- **The query of the interior shooter.** -/
def queryI (sh : Stmt) : Stmt := .seq normI (.seq ztvfu outI)

/-- The logarithm of a stretch within a weight bound. -/
theorem log_le_clog_succ {L γ : ℕ} (h1 : 1 ≤ L) (h2 : L ≤ γ) :
    Nat.log 2 ztbtk ≤ Nat.clog 2 γ + 1 := by
  have e : Nat.log 2 ztbtk = Nat.log 2 L + 1 := by
    zuhnb
  zui
  have := Nat.log_mono_right (b := 2) h2
  have := Nat.log_le_clog 2 γ
  omega
set_option maxRecDepth 20000 in
theorem room_one {A lg Fg cl W : ℕ} (h : A + ztydo ≤ W)
    (hl : lg ≤ cl + 1) : A + 2 * Fg + 1204 * lg + 4500 ≤ W := by_omega
set_option maxRecDepth 20000 in
theorem room_two {A k lg lg₁ Fg cl W : ℕ} (h : A + ztydo ≤ W)
    (hk : k ≤ 2 * Fg + 1204 * lg₁ + 4500) (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    A + k + 2 * Fg + 1204 * lg + 4500 ≤ W := by_omega
set_option maxRecDepth 20000 in
theorem cost_one {k₂ k₃ lg Fg cl : ℕ} (h2 : k₂ = 5) (h3 : k₃ ≤ 2 * Fg + 1204 * lg + 4500)
    (hl : lg ≤ cl + 1) : k₂ + k₃ + 1 ≤ 4 * Fg + 3000 * ztbcp + 18000 := by_omega
set_option maxRecDepth 20000 in
theorem cost_two {k₂ k₃ k₄ k₅ lg lg₁ Fg cl : ℕ} (h2 : k₂ = 5)
    (h3 : k₃ ≤ 2 * Fg + 1204 * lg₁ + 4500) (h4 : k₄ ≤ 8) (h5 : k₅ ≤ 2 * Fg + 1204 * lg + 4500)
    (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    k₂ + ztlg + 2 ≤ 4 * Fg + 3000 * ztbcp + 18000 := by_omega
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The frame of the parameter blocks. -/
theorem bset_io {r : ℕ} (h : Bset r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band (Or.inl (by simp only [Bset, decide_eq_true_eq] at h; omega))

/-- **The query of the interior shooter.** -/
theorem queryI_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (h70 : c.nreg 170070 = 0) (q : QFacts zta s.e₁ s.h₁ s.e₂ s.h₂)
    (hwt : (interiorModel zta).arcWt ztwoo
      ztwop ≤ s.γ)
    (ho1 : |(s.o.eval zta).1| ≤ Jordan.coordBound zta)
    (ho2 : |(s.o.eval zta).2| ≤ Jordan.coordBound zta) (hol : s.o.Lt P.n)
    (hoA : s.o.eval zta ∉ (interiorModel zta).arcSet
      ztwoo
      ztwop)
    (hroom : c.nreg ALLOC + (4 * F s.γ + 3000 * ztdle + 19000) ≤ W) :
    ∃ c' k, Exec P W ztwcf c c' k ∧
      k ≤ 4 * F s.γ + 3000 * ztdle + 19000 ∧
      (c'.nreg 140010 = 1 → ∃ t, FirstHit ((interiorModel zta).arcSet
          ztwoo
          ztwop) (s.o.eval (Qof P)) (dirOf s.dir) t ∧
        ProperPos ztwiq zta P.n ztdql ∧
        c'.nreg 140011 < (interiorModel zta).W.n ∧
        (interiorModel zta).pos zta ztdql =
          rayPt ztxah ztfhd t) ∧
      (c'.nreg 140010 ≠ 1 → NoHit ((interiorModel zta).arcSet
          ztwoo
          ztwop) (s.o.eval (Qof P)) (dirOf s.dir)) ∧
      Frame ioBands c c' k := by
  zudq
  zucgt
  zucg

  zudo

  -- the normalized query

  zud
  zuiuw
  have S₁ := hS.keep (fun r h1 h2 => f₁ r (by
    zunot; omega))
    ztdnp ztnti
  have Fr₁ := frameIO_of_frameB (fun r hr => io_of_band (by
    simp only [Bnorm, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₁ k₁
  have hB₁ : BestI P c₁ ∅ ztxah ztfhd :=
    bestI_empty (by zuokj; omega)
  set A := (interiorModel _).arcSet _
    _ with hAd
  set z := s.o.eval zta with hzd
  set σ := dirOf s.dir with hσd
  have bandSet : ∀ {d d' : Config}, FrameB Bset d d' → ∀ r, ztofj →
      d'.nreg r = d.nreg r := fun F r hr => F.1 r (by
        zuoep; omega)
  have keepSet : zteec :=
    fun F hS' => hS'.keep by_grind ztbmr
      ztgfp
  have bestSet : ∀ {d d' : Config} {S' : Set Point}, FrameB Bset d d' → BestI P d S' z σ →
      BestI P d' S' z σ := fun F hb => hb.keep by_grind
  -- the branch
  have hbr : ∃ c₂ k₂, Exec P W ztvfu c₁ c₂ k₂ ∧
      k₂ ≤ 4 * F s.γ + 3000 * ztdle + 18000 ∧ BestI P c₂ (∅ ∪ A) z σ ∧
      SEnv P W O s c₂ ∧ Frame ioBands c₁ c₂ k₂ := by
    zucnv
    unfold branchI
    by_cases hL : spanL ztbakl
        ztwla + 1 ≤ (Qof P).n
    · -- one sub-query
      zubki

      zubff

      have hLγ : spanL _
          _ ≤ s.γ := hwL ▸ hwt
      zukde
      have hA₂ : ztbae := by
        zugcl
      obtain ⟨c₃, k₃, e₃, hk₃, hB₃, S₃, F₃, g₃⟩ := sqS_exec hsh c₂ e₂.wb_right S₂
        ztntc ztntd by_omega by_omega by_omega
        hsub hLγ ho1 ho2 hol by_grind zttgt
        by_grind
      refine ⟨c₃, _, .ifLtN_true hcond ztcr, by_omega,
        by grind, S₃,
        ((frameIO_of_frameB ztczn Fs k₂).trans F₃).mono by_simp by_omega⟩
    · -- two sub-queries
      zucon

      obtain ⟨hsubA, hsubB, hset, hwn⟩ := plan_two q by_omega
      zuhzm
      -- the first sub-query
      zubdy

      have hA₂ : ztbae := by
        zugcl
      zudop
      have hsA : (interiorModel zta).arcSet ztwoo
          ztwop ⊇ oset ztwsc s.e₁
          ((interiorModel zta).param zta ztbra)
          ((2 : ℕ) + (interiorModel zta).param zta ztcjp) := by
        zukwf
      obtain ⟨c₃, k₃, e₃, hk₃, hB₃, S₃, F₃, g₃⟩ := sqS_exec hsh c₂ e₂.wb_right S₂
        ztntc ztntd b35 b36 b37
        hsubA by_omega ho1 ho2 hol (fun h => hoA (hsA h)) zttgt
        by_grind
      -- the second sub-query
      have c31 : c₃.nreg 170031 = eeOf zta s.e₁ s.h₁ s.e₂ ztwla := by
        zugo
      have c30 : ztyyq := by
        zugo
      have c32 : c₃.nreg 170032 = spanL ztbakl
          ztwla := by
        zugo
      obtain ⟨c₄, k₄, e₄, hk₄, d33, d34, d35, d36, d37, Ft⟩ := setTwoB_exec c₃
        e₃.wb_right S₃ he1
      zujwg
      have hA₄ : ztpnu := by
        zujhp
        have := F₃.2.2.2.2.2.2; omega
      have hLB : spanL ztbakl
          ztwla - 2 ≤ s.γ := by
        omega
      zukdg
      have hsB : (interiorModel zta).arcSet ztwoo
          ztwop ⊇ oset ztwsc
          (ztful % (Qof P).n) ((interiorModel zta).param zta ztcjp)
          ((eeOf zta s.e₁ s.h₁ s.e₂ ztwla - 2 : ℕ) +
            (interiorModel zta).param zta ⟨(ztful % (Qof P).n +
              (eeOf zta s.e₁ s.h₁ s.e₂ ztwla - 2)) % (Qof P).n,
              nh zta s.e₂ s.h₂⟩) := by
        zukwf
      obtain ⟨c₅, k₅, e₅, hk₅, hB₅, S₅, F₅, g₅⟩ := sqS_exec hsh c₄ e₄.wb_right S₄
        by_grind d34 by_omega by_omega by_omega
        hsubB hLB ho1 ho2 hol (fun h => hoA (hsB h)) (bestSet Ft hB₃)
        by_grind
      refine ⟨c₅, _, .ifLtN_false hcond ztbq,
        by omega, ?_, S₅,
        ((((frameIO_of_frameB ztczn Fs k₂).trans F₃).trans
          ztzlv).trans F₅).mono by_simp by_omega⟩
      grind
  obtain ⟨c₂, k₂, e₂, hk₂, hB₂, S₂, F₂⟩ := hbr
  -- the answer
  obtain ⟨c₃, k₃, e₃, hk₃, hhit, hno, F₃⟩ := outI_exec c₂ e₂.wb_right S₂ hB₂
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, fun h => ?_, fun h => ?_,
    ((Fr₁.trans F₂).trans (frameIO_of_frameB (fun r hr => io_of_band (by
      simp only [Bout, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₃ k₃)).mono
      by_simp by_omega⟩
  · simp_all
  simp_all
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def OkI (P : Polygon) (M : Model) : Prop := OkModel P M ∨ M = interiorModel zta

/-- **The interior shooter.** -/
def shI (sh : Stmt) : Stmt :=
  .seq ztdcc
    (.ifLtN 170099 170098 sh (.seq frontI ztwcf))

/-- The cost of the interior shooter. -/
def FI (F : ℕ → ℕ) (γ : ℕ) : ℕ := 4 * F γ + 3000 * ztxd + 20000
theorem chainModel_ne_interior'' (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  zuq
  have := congrArg (fun M : Model => M.counted 0) h
  zuckl

/-- An `OkI` model with a chain descriptor is an `OkModel`. -/
theorem okModel_of_okI {P : Polygon} {m : ℕ → ℕ} {B : ℕ} {M : Model}
    (hMD : ModelDescAt m B zta M) (h0 : m B = 0) (hOk : OkI P M) : OkModel P M := by
  rcases hOk with h | h
  · zubh
  · rcases hMD with ⟨-, H, C, -, hM⟩ | ⟨h1, -, -⟩
    · exact absurd (hM.symm.trans h) (chainModel_ne_interior'' C _)
    omega
theorem room_q {A F' cl W : ℕ} (h : A + (4 * F' + 3000 * ztbcp + 20000) ≤ W) :
    A + 8 + (4 * F' + 3000 * ztbcp + 19000) ≤ W := by_linarith
theorem cost_q {k₁ k₂ k₃ F' cl : ℕ} (h1 : k₁ = 2) (h2 : k₂ ≤ 52)
    (h3 : k₃ ≤ 4 * F' + 3000 * ztbcp + 19000) :
    k₁ + ztjzq ≤ 4 * F' + 3000 * ztbcp + 20000 := by_linarith
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface}
theorem load_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W ztdcc c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem ztqhn ∧ c'.nreg 170098 = 1 ∧
      FrameB ztcib c c' := by
  have hwr : wr ztcib
      ztdcc = true := by_decide
  suffices h : ∃ c' k, Exec P W ztdcc c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem ztqhn ∧ c'.nreg 170098 = 1 by
    zubgy
    exact zthmm
  exec_block
  · omega
  simp
theorem load_io {r : ℕ} (h : decide (r = 170098 ∨ r = 170099) = true) :
    bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band ztzz

/-- **The interior shooter.** -/
theorem interiorShooter_of {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F ztsy OkModel) :
    ShooterOK (shI sh) ioBands (FI F) ztsy OkI := by
  zulq
  obtain ⟨hG, hHW, hX, hcap, hMDWF, hreg, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt, o,
    hol, ho, hof, hoA⟩ := hpre
  zucgn

  zuiqz
  zudq
  obtain ⟨c₁, k₁, e₁, hk₁, a99, a98, F₁⟩ := load_exec (P := P) c hw by_omega
  zud
  have f₁ : zthpo := fun r h1 h2 =>
    F₁.1 r by_simp_all
  zuhdq
  have rk : ∀ i, i < 20 → rd c₁ bShoot i = rd c bShoot i := fun i hi =>
    f₁ _ ztozm ztozm
  zurt

  have r8 := rk 8 by_norm_num
  zufhr

  have ho₁ : ztyyi := ShotList.originIn_copy ho
    ztefd ztefd ztefd
  by_cases hk : c.nmem ztqhn = 0
  · -- a chain descriptor: the chain shooter itself
    zuerg

    obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hsh P W c₁ w₁ (by
      grind) (by
      zuiqx

      have : F ztcdr ≤ FI F ztcdr := by unfold FI; omega
      omega)
    refine ⟨c₂, _, .seq e₁ ztnaj, ?_, fun M' o' hM' ho' => ?_,
      (Fr₁.trans ztnlc).mono by_simp by_omega⟩
    · zugjd

      have : F ztcdr + 3 ≤ FI F ztcdr := by unfold FI; omega
      omega
    · have hp := hpost M' o' by_grind (ShotList.originIn_copy ho'
        ztefd ztefd
        ztefd)
      grind
  · -- the interior model
    zukcf
    obtain ⟨hk1, hbit, hMI⟩ : c.nmem (rd c bShoot 0) = 1 ∧
        (c.nmem ztfih = 1 ↔ Mountain.LeftInside zta) ∧
        M = interiorModel zta := by
      zugrq
      · tauto
      omega
    zubfk

    have hol' : o.Lt (Qof P).n ztwiq := by_grind
    obtain ⟨hoL, hoE, hb1, hb2⟩ := oSym_spec hD hn3 hol' by_grind
    -- the set-up
    obtain ⟨c₂, k₂, e₂, hk₂, S₂, h70, hA₂, F₂⟩ := frontI_exec (O := O) c₁ w₁ hG hHW
      (by show (gradeCtx O).holds P c₁.nmem ztrwi ztbmq
          grind)
      (by show rd c₁ bShoot 9 ≤ (gradeCtx O).cap P c₁.nmem ztrwi
          grind)
      (by show rd c₁ bShoot 0 + 6 ≤ c₁.nreg ALLOC
          zuojz; exact hMDWF.1)
      (by show c₁.nmem (rd c₁ bShoot 0 + 1) = 1 ↔ _
          grind) ho₁ hol (by
        rw [hA₁]; have : 8 ≤ FI F ztcdr := by unfold FI; omega
        omega)
    zue
    have se1 : (statOf P c₁ o).e₁ = rd c bShoot 1 := r1
    have sh1 : (statOf P c₁ o).h₁ = rd c bShoot 2 := r2
    have se2 : (statOf P c₁ o).e₂ = rd c bShoot 3 := r3
    have sh2 : (statOf P c₁ o).h₂ = rd c bShoot 4 := r4
    have sγ : (statOf P c₁ o).γ = rd c bShoot 9 := r9
    have sdir : (statOf P c₁ o).dir = rd c bShoot 8 := r8
    have so : (statOf P c₁ o).o = oSym zta o := rfl
    have q : QFacts zta (statOf P c₁ o).e₁ (statOf P c₁ o).h₁ (statOf P c₁ o).e₂
        (statOf P c₁ o).h₂ := by
      zugxc
      exact ⟨hn3, hD, by_omega, by_omega,
        by grind, by_grind⟩
    obtain ⟨c₃, k₃, e₃, hk₃, hhit, hno, F₃⟩ := queryI_exec hsh c₂ w₂ S₂ h70 q
      by_grind by_grind
      by_grind by_grind
      by_grind (by
        zuiio
        unfold FI at hcost
        grind)
    refine ⟨c₃, _, .seq e₁ ztzrq, ?_, fun M' o' hM' ho' => ?_,
      ((Fr₁.trans F₂).trans F₃).mono by_simp by_omega⟩
    · zuiqy

      unfold FI
      omega
    · have hM'I : ztbabz := by
        zudrz
        · omega
        omega
      subst hM'I
      have hoo : o' = o := ShotList.originIn_unique ho' ho
      subst hoo
      rw [so, hoE, se1, sh1, se2, sh2, sdir] at hhit hno
      exact ⟨hhit, hno⟩
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open ShootCut (Pc KPath)
@[expose] public section
def clrC : Stmt :=
  block [.constN 170020 0, .constN 170021 0, .constN 170200 0, .constN 170205 0,
    .constN 170210 0, .constN 170215 0]

/-- **The set-up of the interior cutter.** -/
def frontC : Stmt := .seq (saveS 150000) (.seq ztncs clrC)

/-- The static data of a query of the interior cutter. -/
noncomputable def statC (c : Config) : Stat :=
  ⟨c.nreg ALLOC, c.nmem, c.nreg 150013, c.nreg 150009, c.nreg 150001, c.nreg 150002,
    c.nreg 150003, c.nreg 150004, c.nreg 150008, .vtx 0⟩

/-- One or two sub-queries of the cutter. -/
def branchC (cu : Stmt) : Stmt :=
  .ifLtN 170032 170010 (.seq setOne ztuav)
    (.seq setTwoA (.seq ztuav (.seq setTwoB (sqC cu 2))))

/-- **The query of the interior cutter.** -/
def queryC (cu : Stmt) : Stmt := .seq normI (.seq ztvft asmC)

/-! ## Lemmas -/
theorem flat_len_le {m : ℕ → ℕ} {n Gγ : ℕ} :
    ∀ {sls : List Slot}, (∀ sl ∈ sls, sl.q ≤ Gγ) →
      (sls.flatMap ztkfi).length ≤ sls.length * Gγ
  | [], _ => by_simp
  | sl :: sls, h => by
    have ih := flat_len_le (m := m) (n := n) (sls := sls) (fun s hs => h s by_simp_all)
    have h1 := h sl by_simp
    rw [List.flatMap_cons, List.length_append, slotPcs_length, List.length_cons]
    nlinarith
variable {m : ℕ → ℕ}
theorem slotPcs_fields {n : ℕ} {sls : List Slot} {pc : Pc}
    (h : pc ∈ sls.flatMap ztkfi) : pc.dir = 0 ∧ pc.pw = 0 := by
  obtain ⟨sl, -, hpc⟩ := List.mem_flatMap.1 h
  unfold slotPcs at hpc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hpc
  tauto

/-- A piece record read back. -/
theorem rdPc_of_words {A j : ℕ} {pc : Pc}
    (h : ∀ f, f < 7 → m (A + 1 + 7 * j + f) = pcW pc f) (hd : pc.dir = 0) (hp : pc.pw = 0) :
    rdPc m A j = pc := by
  obtain ⟨⟨a, b⟩, ⟨d, e⟩, k, en, x, dir, pw⟩ := pc
  simp only at hd hp
  subst hd hp
  zujxz
  have h1 := h 1 by_norm_num
  have h2 := h 2 by_norm_num
  have h3 := h 3 by_norm_num
  have h4 := h 4 by_norm_num
  have h5 := h 5 by_norm_num
  have h6 := h 6 by_norm_num
  simp only [Nat.add_zero, pcW] at h0 h1 h2 h3 h4 h5 h6
  unfold rdPc
  simp_all
theorem slotsOf_nil {c : Config} (h : ∀ j, j < 4 → c.nreg ztbln = 0) :
    slotsOf c 4 = [] := by
  rw [slotsOf_free (k := 0) by_norm_num (fun j _ hj => h j hj)]; rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface}

/-- **The set-up of the interior cutter.** -/
theorem frontC_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hX : (gradeCtx O).holds P c.nmem ztvhq ztm)
    (hcap : c.nreg 150009 ≤ (gradeCtx O).cap P c.nmem ztvhq)
    (hwf : c.nreg 150000 + 6 ≤ c.nreg ALLOC)
    (hbit : c.nmem (c.nreg 150000 + 1) = 1 ↔ Mountain.LeftInside zta)
    (hroom : c.nreg ALLOC + 8 ≤ W) :
    ∃ c' k, Exec P W frontC c c' k ∧ k ≤ 50 ∧ SEnv P W O (statC c) c' ∧
      (∀ j, j < 4 → c'.nreg ztbln = 0) ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧
      Frame ioBands c c' k := by
  zuers
  zucgn

  -- save
  obtain ⟨c₁, e₁, a10, a13, ar, arr, am, arm, ao⟩ := saveS_exec (P := P) 150000 by_norm_num c hw
  zud
  zuhvo
  have F₁ : ztsbk := frameIO_of_frameB
    (B := fun r => decide ztgxv)
    ztywf
    ⟨fun r hr => ar r by_simp_all, fun r _ => by zuoxf, am, arm, ao⟩ 11
  zulkm
  have a0 : c₁.nreg 170000 = c.nreg 150000 := a10 0 by_norm_num
  have a13' : c₁.nreg 170013 = c.nreg 150013 := a13
  -- the constants and the host record
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b10, b11, b12, b18, b19, b16, b17, b14, b14', b15, bA, b70, bm0,
      bm1, bm2, bm3, bmlo, br, brr, brm, bo⟩ := initI_exec (P := P) c₁ w₁
    by_omega by_omega
    by_omega by_omega by_omega
  zue
  have F₂ : ztmte := by
    refine ⟨fun r hr ha => br r ?_, fun r _ => by zuoen, fun a ha => bmlo a ha,
      fun a _ => by zuoxg, bo, by_omega, by_omega⟩
    zuhgn
    zumqi
    zuhbg
    rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (try (subst h; decide))
    zulxm
  -- the dummy origin and the free slots
  obtain ⟨c₃, k₃, e₃, hk₃, d20, d21, d200, d205, d210, d215, dr, drr, dm, drm, dout⟩ :
      ∃ c₃ k₃, Exec P W clrC c₂ c₃ k₃ ∧ k₃ = 6 ∧ c₃.nreg 170020 = 0 ∧ c₃.nreg 170021 = 0 ∧
      c₃.nreg 170200 = 0 ∧ c₃.nreg 170205 = 0 ∧ c₃.nreg 170210 = 0 ∧ c₃.nreg 170215 = 0 ∧
      (∀ r, r ≠ 170020 → r ≠ 170021 → r ≠ 170200 → r ≠ 170205 → r ≠ 170210 → r ≠ 170215 →
        c₃.nreg r = c₂.nreg r) ∧ c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧ c₃.rmem = c₂.rmem ∧
      c₃.output = c₂.output := by
    unfold clrC
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp
    simp [upd, h1, h2, h3, h4, h5, h6]
  have F₃ : ztmtf := frameIO_of_frameB
    (B := fun r => decide (r = 170020 ∨ r = 170021 ∨ r = 170200 ∨ r = 170205 ∨ r = 170210 ∨
      r = 170215))
    ztyex
    ⟨fun r hr => dr r by_grind by_grind by_grind
      by_grind by_grind by_grind,
      fun r _ => by rw [drr], dm, drm, dout⟩ k₃
  have q : ∀ r, r < 170020 ∨ ztneu → c₃.nreg r = c₂.nreg r := fun r hr =>
    dr r by_omega by_omega by_omega by_omega by_omega by_omega
  have g : ∀ r, r < 170020 ∨ ztneu → ¬ BinitR r → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 => by_grind
  have gs : ∀ i, i < 10 → c₃.nreg ztner = c.nreg (150000 + i) := fun i hi => by
    zuoeo; grind
  have ex : Exec P W frontC c c₃ ztzsn := .seq e₁ ztcr
  have cA : ztpno := by
    rw [q _ by_decide, bA, aA]
  refine ⟨c₃, _, ex, by_omega, ⟨hG, hHW, gs 1 by_norm_num, gs 2 by_norm_num,
    gs 3 by_norm_num, gs 4 by_norm_num, gs 8 by_norm_num, gs 9 by_norm_num,
    by zuoeo; exact a13',
    by grind, by_grind,
    by grind, by_grind,
    by grind,
    by grind,
    by grind,
    by rw [q _ by_omega, b15, aA]; rfl,
    by rw [q _ by_omega, b16, a13', am]; rfl,
    by rw [q _ by_omega, b17, a13', am]; rfl, ⟨d20, d21⟩,
    fun a ha => by rw [dm, bmlo a ztmcx, am]; rfl,
    by zunsj; show c₂.nmem ztm = 1; grind,
    by zunsj; show c₂.nmem ztccv = 0; grind,
    by zunsj; show c₂.nmem zteep = 0; grind,
    by zunsj; show c₂.nmem zteeq = P.n - 1; grind,
    by zuoxh; rfl, hX, hcap⟩,
    fun j hj => ?_, cA, ((F₁.trans F₂).trans F₃).mono by_simp by_omega⟩
  interval_cases j
  · omega
  · omega
  · omega
  omega
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open ShootCut (Pc KPath)
@[expose] public section
set_option maxRecDepth 20000 in
theorem roomC_one {A lg Gg cl W : ℕ} (h : A + ztxdk ≤ W)
    (hl : lg ≤ cl + 1) : A + 2 * Gg + 1204 * lg + 2600 ≤ W := by_omega
set_option maxRecDepth 20000 in
theorem roomC_two {A A' k₃ lg lg₁ Gg cl W : ℕ}
    (h : A + ztxdk ≤ W) (hA : A' ≤ A + k₃)
    (hk : k₃ ≤ 2 * Gg + 1204 * lg₁ + 2600) (hl₁ : lg₁ ≤ cl + 1)
    (hl : lg ≤ cl + 1) : A' + 2 * Gg + 1204 * lg + 2600 ≤ W := by_omega
set_option maxRecDepth 20000 in
theorem costC_one {k₂ k₃ lg Gg cl : ℕ} (h2 : k₂ = 5) (h3 : k₃ ≤ 2 * Gg + 1204 * lg + 2600)
    (hl : lg ≤ cl + 1) : k₂ + k₃ + 1 ≤ 4 * Gg + 2408 * ztbcp + 5300 := by_omega
set_option maxRecDepth 20000 in
theorem costC_two {k₂ k₃ k₄ k₅ lg lg₁ Gg cl : ℕ} (h2 : k₂ = 5)
    (h3 : k₃ ≤ 2 * Gg + 1204 * lg₁ + 2600) (h4 : k₄ ≤ 8) (h5 : k₅ ≤ 2 * Gg + 1204 * lg + 2600)
    (hl₁ : lg₁ ≤ cl + 1) (hl : lg ≤ cl + 1) :
    k₂ + ztlg + 2 ≤ 4 * Gg + 2408 * ztbcp + 5300 := by_omega
set_option maxRecDepth 20000 in
theorem roomC_asm {A k₁ k₂ len Gg cl W : ℕ} (h : A + ztxdk ≤ W)
    (hk₁ : k₁ ≤ 900) (hk₂ : k₂ ≤ 4 * Gg + 2408 * ztbcp + 5300) (hl : len ≤ 4 * Gg) :
    A + k₁ + k₂ + 42 * len + 60 ≤ W := by_omega
set_option maxRecDepth 20000 in
theorem costC_q {k₁ k₂ k₃ len Gg cl : ℕ} (hk₁ : k₁ ≤ 900)
    (hk₂ : k₂ ≤ 4 * Gg + 2408 * ztbcp + 5300) (hk₃ : k₃ ≤ 42 * len + 60) (hl : len ≤ 4 * Gg) :
    k₁ + zttl ≤ 172 * Gg + 2408 * ztbcp + 6300 := by_omega
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **The query of the interior cutter.** -/
theorem queryC_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (hfree : ∀ j, j < 4 → c.nreg ztbln = 0)
    (q : QFacts zta s.e₁ s.h₁ s.e₂ s.h₂)
    (hwt : (interiorModel zta).arcWt ztwoo
      ztwop ≤ s.γ)
    (hroom : c.nreg ALLOC + (172 * G s.γ + 2408 * ztdle + 6300) ≤ W) :
    ∃ (c' : Config) (k : ℕ) (ps : List Pc), Exec P W ztwce c c' k ∧
      k ≤ 172 * G s.γ + 2408 * ztdle + 6300 ∧
      ps ≠ [] ∧ ps.length ≤ 4 * G s.γ ∧
      c.nreg ALLOC ≤ c'.nreg 150010 ∧ c'.nmem ztvge = ps.length ∧
      c'.nreg 150010 + 1 + 7 * ps.length ≤ c'.nreg ALLOC ∧
      (∀ j (hj : j < ps.length), rdPc c'.nmem ztvge j = ps[j]'hj) ∧
      KPath ztwiq zta (Qof P).n
        ((s.e₁ : ℝ) + (interiorModel zta).param zta ztbra) ps
        ((s.e₁ : ℝ) + eeOf zta s.e₁ s.h₁ s.e₂ ztwla +
          (interiorModel zta).param zta ztdjh) ∧
      (∀ pc ∈ ps, PcV P ztwiq c'.nmem ztdo ztdyn pc) ∧
      Frame ioBands c c' k := by
  zudq
  zucgt
  zucg

  zudo

  -- the normalized query

  zucnv
  set x := (interiorModel zta).param zta ztbra with hx
  set ee := eeOf zta s.e₁ s.h₁ s.e₂ ztwla with heed
  set t₂ := (interiorModel _).param _ ztdjh with ht₂
  set V0 : ℝ := (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + x with hV0
  set V1 : ℝ := (s.e₁ : ℝ) + ee + t₂ with hV1
  zud
  zuiuw
  have S₁ := hS.keep (fun r h1 h2 => f₁ r (by
    zunot; omega))
    ztdnp ztnti
  have Fr₁ := frameIO_of_frameB (fun r hr => io_of_band (by
    simp only [Bnorm, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₁ k₁
  zuhwj
  have fs : ∀ j, j < 4 → c₁.nreg ztbln = 0 := fun j hj => by
    rw [f₁ _ (by simp only [Bnorm, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
    simp_all
  have T₁ : SlotSt P ztdyn ztffk s.e₁ V0 V0 0 c₁ := by
    refine ⟨?_, by_simp_all, by_simp_all, fun sl hsl => ?_⟩
    · rw [slotsOf_nil fs]; rfl
    · rw [slotsOf_nil fs] at hsl; simp_all
  have bandSet : ∀ {d d' : Config}, FrameB Bset d d' → ∀ r, ztofj →
      d'.nreg r = d.nreg r := fun F r hr => F.1 r (by
        zuoep; omega)
  have keepSet : zteec :=
    fun F hS' => hS'.keep by_grind ztbmr
      ztgfp
  have keepSetT : ∀ {d d' : Config} {V : ℝ} {k : ℕ}, FrameB Bset d d' →
      SlotSt P _ _ s.e₁ V0 V k d → SlotSt P ztdyn ztffk s.e₁ V0 V k d' :=
    fun F hT => hT.keep by_grind ztbmr
      ztgfp
  -- the branch
  have hbr : ∃ c₂ k₂, Exec P W ztvft c₁ c₂ k₂ ∧
      k₂ ≤ 4 * G s.γ + 2408 * ztdle + 5300 ∧
      SlotSt P ztdyn ztffk s.e₁ V0 V1 4 c₂ ∧ SEnv P W O s c₂ ∧ Frame ioBands c₁ c₂ k₂ := by
    unfold branchC
    by_cases hL : spanL ee ztwla + 1 ≤ (Qof P).n
    · -- one sub-query
      zubki

      rw [← heed] at hsub hwL
      zubff

      zujwh
      have hLγ : spanL ee _ ≤ s.γ := hwL ▸ hwt
      zukde
      have hA₂ : ztbae := by
        zuhkq
      obtain ⟨c₃, k₃, e₃, hk₃, T₃, S₃, F₃, g₃⟩ := sqC_exec hcu c₂ e₂.wb_right S₂
        ztveo ztvep (b35.trans a31) (b36.trans a30) (b37.trans a32)
        hsub hLγ ztmcv by_norm_num
        T₂ by_grind
      have hV : (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + (ee : ℝ) + (interiorModel zta).param zta
          ⟨(s.e₁ + ee) % (Qof P).n, nh zta s.e₂ s.h₂⟩ = V1 := by
        rw [hmod, param_nh q.he₂]; grind
      rw [hV] at T₃
      refine ⟨c₃, _, .ifLtN_true hcond ztcr, by_omega, T₃.mono by_norm_num,
        S₃, ((frameIO_of_frameB ztczn Fs k₂).trans F₃).mono by_simp by_omega⟩
    · -- two sub-queries
      zucon

      obtain ⟨hsubA, hsubB, hset, hwn⟩ := plan_two q by_grind
      rw [← heed] at hsubB
      zuhzm
      zuhym
      have hmod2 : ztyfy % (Qof P).n = s.e₂ := by
        rw [Nat.mod_add_mod, show s.e₁ + 2 + ztjur = s.e₁ + ee by omega, hmod]
      -- the first sub-query
      zubdy

      zujwh
      have hA₂ : ztbae := by
        zuhkq
      zudop
      obtain ⟨c₃, k₃, e₃, hk₃, T₃, S₃, F₃, g₃⟩ := sqC_exec hcu c₂ e₂.wb_right S₂
        ztveo ztvep b35 b36 b37
        hsubA by_omega ztmcv
        by_norm_num T₂ by_grind
      -- the second sub-query
      have c31 : c₃.nreg 170031 = ee := by
        zugo
      have c30 : ztyyq := by
        zugo
      have c32 : c₃.nreg 170032 = spanL ee ztwla := by
        zugo
      obtain ⟨c₄, k₄, e₄, hk₄, d33, d34, d35, d36, d37, Ft⟩ := setTwoB_exec c₃
        e₃.wb_right S₃ he1
      zujwg
      have hA₄ : ztpnu := by
        zujhp
        have := F₃.2.2.2.2.2.2; omega
      have hLB : spanL ee ztwla - 2 ≤ s.γ := by
        omega
      zukdg
      have hV2 : (s.e₁ : ℝ) + ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + (interiorModel zta).param
          zta ztcjp = (s.e₁ : ℝ) + ((2 : ℕ) : ℝ) +
          (interiorModel zta).param zta ztcjp := by
        simp
      rw [hV2] at T₃
      obtain ⟨c₅, k₅, e₅, hk₅, T₅, S₅, F₅, g₅⟩ := sqC_exec hcu c₄ e₄.wb_right S₄
        by_grind d34 by_omega by_omega by_omega
        hsubB hLB rfl by_norm_num (keepSetT Ft T₃)
        by_grind
      have hV : (s.e₁ : ℝ) + ((2 : ℕ) : ℝ) + ((ee - 2 : ℕ) : ℝ) + (interiorModel zta).param
          zta ⟨ztyfy % (Qof P).n, nh zta s.e₂ s.h₂⟩ = V1 := by
        rw [hmod2, param_nh q.he₂, Nat.cast_sub hee2]; grind
      rw [hV] at T₅
      refine ⟨c₅, _, .ifLtN_false hcond ztbq,
        by omega, T₅, S₅,
        ((((frameIO_of_frameB ztczn Fs k₂).trans F₃).trans
          ztzlv).trans F₅).mono by_simp by_omega⟩
  obtain ⟨c₂, k₂, e₂, hk₂, T₂, S₂, F₂⟩ := hbr
  -- the assembly
  have hlen : ((slotsOf c₂ 4).flatMap ztohz).length ≤ 4 * G s.γ := by
    have h1 := flat_len_le (m := c₂.nmem) (n := (Qof P).n) T₂.qG
    have h2 := slotsOf_length (c := c₂) (k := 4)
    have : (slotsOf c₂ 4).length * G s.γ ≤ 4 * G s.γ := Nat.mul_le_mul_right _ h2
    omega
  have hA₂ : c₂.nreg ALLOC ≤ c.nreg ALLOC + k₁ + k₂ := by
    have := F₂.2.2.2.2.2.2; grind
  obtain ⟨c₃, k₃, e₃, hk₃, d10, dO, dout, dA, F₃⟩ := asmC_exec (P := P) c₂ e₂.wb_right
    (n := (Qof P).n) (by rw [S₂.r10, hQ]) S₂.r11 rfl by_omega T₂.ok T₂.bit
    by_omega
  set ps := (slotsOf c₂ 4).flatMap ztohz with hps
  obtain ⟨hkp, hv, hne⟩ := slotsOK_out T₂.ok
  have hlt : V0 < V1 := by
    rw [param_nh q.he₂] at hxy
    grind
  have hsne : slotsOf c₂ 4 ≠ [] := by
    zuq
    have hok := T₂.ok
    zvmwc at hok
    exact absurd hok hlt.ne
  have hpne := hne hsne
  have hF₃m := F₃.2.2.1
  have hA₃ := F₃.2.2.2.2.2.1
  refine ⟨c₃, _, ps, .seq e₁ ztcr, by_omega, hpne, hlen,
    by zuoxi; have := Fr₁.2.2.2.2.2.1; have := F₂.2.2.2.2.2.1; omega, by_grind,
    by omega, fun j hj => ?_, ?_, fun pc hpc => (hv pc hpc).keep hF₃m hA₃,
    ((Fr₁.trans F₂).trans F₃).mono by_simp by_omega⟩
  · zuoxi
    obtain ⟨h1, h2⟩ := slotPcs_fields ztuzm
    exact rdPc_of_words (dout j hj) h1 h2
  grind
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)
@[expose] public section
def cuI (cu : Stmt) : Stmt :=
  .seq ztdcd
    (.ifLtN 170099 170098 cu (.seq frontC ztwce))

/-- The piece bound and cost of the interior cutter. -/
def GI (G : ℕ → ℕ) (γ : ℕ) : ℕ := 172 * G γ + 2408 * ztxd + 6400
theorem roomC_q {A G' cl W : ℕ} (h : A + (172 * G' + 2408 * ztbcp + 6400) ≤ W) :
    A + 8 + (172 * G' + 2408 * ztbcp + 6300) ≤ W := by_linarith
theorem costC_q' {k₁ k₂ k₃ G' cl : ℕ} (h1 : k₁ = 2) (h2 : k₂ ≤ 50)
    (h3 : k₃ ≤ 172 * G' + 2408 * ztbcp + 6300) :
    k₁ + ztjzq ≤ 172 * G' + 2408 * ztbcp + 6400 := by_linarith
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface}
theorem loadC_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W ztdcd c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem ztqho ∧ c'.nreg 170098 = 1 ∧
      FrameB ztcib c c' := by
  have hwr : wr ztcib
      ztdcd = true := by_decide
  suffices h : ∃ c' k, Exec P W ztdcd c c' k ∧ k = 2 ∧
      c'.nreg 170099 = c.nmem ztqho ∧ c'.nreg 170098 = 1 by
    zubgy
    exact zthmm
  exec_block
  · omega
  simp

/-- **The interior cutter.** -/
theorem interiorCutter_of {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H ztsy OkModel) :
    CutterOK (cuI cu) ioBands (GI G) H ztsy OkI := by
  zulq
  obtain ⟨hG, hHW, hX, hcap, hMDWF, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt⟩ := hpre
  zucgn

  zuiqz
  zudq
  obtain ⟨c₁, k₁, e₁, hk₁, a99, a98, F₁⟩ := loadC_exec (P := P) c hw by_omega
  zud
  have f₁ : zthpo := fun r h1 h2 =>
    F₁.1 r by_simp_all
  zuhdq
  have rk : ∀ i, i < 20 → rd c₁ bCut i = rd c bCut i := fun i hi =>
    f₁ _ ztozl ztozl
  zurt

  zufhr

  by_cases hk : c.nmem ztqho = 0
  · -- a chain descriptor: the chain cutter itself
    zuerg

    obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hcu P W c₁ w₁ (by
      grind) (by
      zuiqx

      zuhdo
      omega)
    refine ⟨c₂, _, .seq e₁ ztnaj, ?_, fun M' hM' => ?_,
      (Fr₁.trans ztnlc).mono by_simp by_omega⟩
    · zugjd

      have : G ztbit + 3 ≤ GI G ztbit := by unfold GI; omega
      omega
    · have hp := hpost M' (by rw [r0, hm₁]; omega)
      simp only [r1, r2, r3, r4, r9, hA₁] at hp
      obtain ⟨p1, p2, p3, prest⟩ := hp
      zuhdo
      exact ⟨p1, p2, p3.trans this, prest⟩
  · -- the interior model
    zukcf
    obtain ⟨hk1, hbit, hMI⟩ : c.nmem (rd c bCut 0) = 1 ∧
        (c.nmem (rd c bCut 0 + 1) = 1 ↔ Mountain.LeftInside zta) ∧
        M = interiorModel zta := by
      zugrq
      · tauto
      omega
    zubfk

    -- the set-up
    obtain ⟨c₂, k₂, e₂, hk₂, S₂, hfree, hA₂, F₂⟩ := frontC_exec (O := O) c₁ w₁ hG hHW
      (by show (gradeCtx O).holds P c₁.nmem ztrwg ztbmq
          simp_all)
      (by show rd c₁ bCut 9 ≤ (gradeCtx O).cap P c₁.nmem ztrwg
          simp_all)
      (by show rd c₁ bCut 0 + 6 ≤ c₁.nreg ALLOC
          zuojz; exact hMDWF.1)
      (by show c₁.nmem (rd c₁ bCut 0 + 1) = 1 ↔ _
          simp_all) (by
        rw [hA₁]; have : 8 ≤ GI G ztbit := by unfold GI; omega
        omega)
    zue
    have se1 : (statC c₁).e₁ = rd c bCut 1 := r1
    have sh1 : (statC c₁).h₁ = rd c bCut 2 := r2
    have se2 : (statC c₁).e₂ = rd c bCut 3 := r3
    have sh2 : (statC c₁).h₂ = rd c bCut 4 := r4
    have sγ : (statC c₁).γ = rd c bCut 9 := r9
    have q : QFacts zta (statC c₁).e₁ (statC c₁).h₁ (statC c₁).e₂ (statC c₁).h₂ := by
      zugxc
      exact ⟨hn3, hD, by_omega, by_omega,
        by simp_all, by_simp_all⟩
    obtain ⟨c₃, k₃, ps, e₃, hk₃, hne, hlen, hAL, hq, hLE, hr, hkp, hv, F₃⟩ :=
      queryC_exec (H := H) hcu c₂ w₂ S₂ hfree q by_simp_all (by
        zuiio
        unfold GI at hcost
        grind)
    rw [se1, sh1, se2, sh2] at hkp
    rw [sγ] at hlen hv
    refine ⟨c₃, _, .seq e₁ ztzrq, ?_, fun M' hM' => ?_,
      ((Fr₁.trans F₂).trans F₃).mono by_simp by_omega⟩
    · zuiqy

      unfold GI
      omega
    · have hM'I : ztbabz := by
        zudrz
        · omega
        omega
      subst hM'I
      set K := (interiorModel zta).key zta with hK
      set A := c₃.nreg 150010 with hAd
      have hn0 : (0 : ℝ) < (Qof P).n := by_positivity
      -- the order facts of the list
      have hsb := pkey_bd (N := P.n) hsP hs1
      have heb := pkey_bd (N := P.n) heP he1
      rw [hmn] at hsb heb
      obtain ⟨-, -, hmod, -, -, -, -, -⟩ := qplan q
      rw [se1, sh1, se2, sh2] at hmod
      have hy1 : (interiorModel zta).param zta ztxu < 1 := heP.2.1
      have hle := ee_bound (Q := Qof P) (e₁ := rd c bCut 1) (h₁ := rd c bCut 2) (e₂ := rd c bCut 3)
        (h₂ := nh zta ztcog ztefp) by_omega hsP.1
        (by rw [param_nh by_omega]; omega)
      rw [param_nh by_omega] at hle
      obtain ⟨o1, o2, o3, o4⟩ := cut_out (s := ztbgi)
        (e := ztxu) hkp hv hne by_rfl (by
          refine ⟨(((rd c bCut 1 + eeOf zta zthzt zthzv ztcog
            ztyfj) / (Qof P).n : ℕ) : ℤ), ?_⟩
          rw [key_eq]
          set a := rd c bCut 1 + eeOf zta zthzt zthzv ztcog
            ztyfj with ha
          have e1 := Nat.mod_add_div a (Qof P).n
          rw [hmod] at e1
          have e2 : ((rd c bCut 3 : ℕ) : ℝ) + (Qof P).n * ((a / (Qof P).n : ℕ) : ℝ) = a := by
            exact_mod_cast e1
          have e3 : (a : ℝ) = rd c bCut 1 + eeOf zta zthzt zthzv ztcog
              ztyfj := by_grind
          zulrp
          linarith) hsb heb by_linarith
      -- the list in memory
      have hlenq : c₃.nmem ztdpj = ps.length := hq
      have hpne := List.length_pos_iff.2 hne
      have hvi : ∀ i (hi : i < ps.length), PcV P ztwiq c₃.nmem zterl
          (H ztbit) (rdPc c₃.nmem A i) := fun i hi => by
        zuoka; exact hv _ ztdyp
      have hri : ∀ i (hi : i < ps.length), rdPc c₃.nmem A i = ps[i]'hi := hr
      zubvt
      refine ⟨by rw [hA₁] at hA₂; show c.nreg ALLOC ≤ A; omega,
        by show A + 1 + 7 * c₃.nmem A ≤ c₃.nreg ALLOC; omega,
        by show c₃.nmem A ≤ GI G ztbit; zvnck; unfold GI; omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show K (rdPc c₃.nmem A 0).s = K ztbgi
        grind
      · show K (rdPc c₃.nmem A (c₃.nmem A - 1)).e = K ztxu
        grind
      · zug
        zuld
        show K (rdPc c₃.nmem A i).e = K (rdPc c₃.nmem A ztg).s
        rw [hri i by_omega, hri ztg hi]; exact o3 i hi
      · zug
        zuld
        show sideInArc (K (rdPc c₃.nmem A i).s) (K ztxu)
          (K (rdPc c₃.nmem A i).e)
        rw [hri i by_omega]; exact o4 i hi
      · zug
        zuld
        exact (hvi i hi).2.2.2.2.2.1
      · zug
        zuld
        exact (hvi i hi).2.2.2.2.2.2
      · zug
        zuld
        have h := hvi i hi
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · zug
        zuld
        exact (hvi i hi).2.2.2.2.1
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine
@[expose] public section
theorem shooterOK_weaken {sh : Stmt} {B : Finset ℕ} {F F' : ℕ → ℕ} {X : MemCtx}
    {Ok Ok' : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok)
    (hOk : ∀ P M, Ok' P M → Ok P M) (hF : ∀ γ, F γ ≤ F' γ) : ShooterOK sh B F' X Ok' := by
  zulq
  obtain ⟨hG, hHW, hX, hcap, hwf, hreg, M, hMD, hOk', rest⟩ := hpre
  zuiqz
  obtain ⟨c', k, e, hk, hpost, F₁⟩ := h P W c hw
    ⟨hG, hHW, hX, hcap, hwf, hreg, M, hMD, hOk P M hOk', rest⟩
    by_grind
  grind

/-- **A cutter serves fewer models at a larger cost and piece bound.** -/
theorem cutterOK_weaken {cu : Stmt} {B : Finset ℕ} {G G' H : ℕ → ℕ} {X : MemCtx}
    {Ok Ok' : Polygon → Model → Prop} (h : CutterOK cu B G H X Ok)
    (hOk : ∀ P M, Ok' P M → Ok P M) (hG : ∀ γ, G γ ≤ G' γ) : CutterOK cu B G' H X Ok' := by
  zulq
  obtain ⟨hGE, hHW, hX, hcap, hwf, M, hMD, hOk', rest⟩ := hpre
  zuiqz
  obtain ⟨c', k, e, hk, hpost, F₁⟩ := h P W c hw
    ⟨hGE, hHW, hX, hcap, hwf, M, hMD, hOk P M hOk', rest⟩
    by_grind
  refine ⟨c', k, e, ?_, fun M' hM' => ?_, F₁⟩
  · beta_reduce at hk ⊢
    exact hk.trans ztmkr
  · obtain ⟨p1, p2, p3, prest⟩ := hpost M' hM'
    exact ⟨p1, p2, p3.trans ztmkr, prest⟩
theorem one_le_rpowCeil' (γ : ℕ) : 1 ≤ rpowCeil ztwku ztby := by
  have h1 : ztujx := by
    zumsg

  have h2 : ztytw := Nat.mul_le_mul h1 (Nat.one_le_pow _ _ by_omega)
  zuluv
variable (κ γ : ℕ)
theorem shCost_ge :
    FI ztbalu γ ≤
      DrvR.shCost ztptj γ := by
  unfold FI DrvR.shCost
  beta_reduce
  have hR := one_le_rpowCeil' γ
  set R := rpowCeil ztwku ztby
  set a := Nat.clog 2 γ + 1
  have ha : 1 ≤ a := by_omega
  have h1 : a ≤ a * R := Nat.le_mul_of_pos_right _ by_omega
  grind
theorem cuCost_ge :
    GI ztywh γ ≤ DrvR.cuCost ztptj γ := by
  unfold GI DrvR.cuCost
  grind

/-- **The interior oracles** (finding E7-B): from the oracles of `ShootCutSpec O`, a shooter and a
cutter serving the interior model of `Qof P` on `gradeCtx O`, writing `insert bUp oracleBands`,
with the cost shape of `ShootCutSpec O`. -/
theorem interiorOracles_of {O : OracleIface} (hSC : ShootCutSpec O) : DrvR.IntOraclesSpec O := by
  obtain ⟨sh, cu, κ, hsh, hcu⟩ := hSC
  refine ⟨shI sh, cuI cu, 172 * κ + 23000, ?_, ?_⟩
  · exact shooterOK_weaken (interiorShooter_of hsh) ztnyj (shCost_ge κ)
  · exact cutterOK_weaken (interiorCutter_of hcu) ztnyj (cuCost_ge κ)
end
end IOrc
namespace SweepIo
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK
variable {P : Polygon} {W : ℕ} {c : Config}

/-- **Only the registers `L` change** (and nothing else of the configuration). -/
def Out (c c' : Config) (L : List ℕ) : Prop :=
  ztiuv ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
    c'.rmem = c.rmem ∧ c'.output = c.output
theorem Out.refl (c : Config) (L : List ℕ) : Out c c L :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem Out.trans {c c₁ c₂ : Config} {L₁ L₂ : List ℕ} (h₁ : Out c c₁ L₁) (h₂ : Out c₁ c₂ L₂) :
    Out c c₂ zthrg :=
  ⟨fun r hr => by
    zuhpi
    zunto, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
theorem Out.mono {c c' : Config} {L L' : List ℕ} (h : Out c c' L) (hL : ∀ r ∈ L, r ∈ L') :
    Out c c' L' := ztfwj

/-- One register instruction. -/
theorem out_instr {i : Instr} {r v : ℕ}
    (hex : Exec P W ztbgj c { c with nreg := upd c.nreg r v } 1) :
    ∃ c', Exec P W ztbgj c c' 1 ∧ c'.nreg r = v ∧ Out c c' [r] :=
  ⟨_, hex, by_simp, fun q hq => by_simp_all,
    rfl, rfl, rfl, rfl⟩

/-! ## A conditional subtraction -/

/-- `dst := a < b ? a : a - b`. -/
def condSub (dst a b : ℕ) : Stmt := .ifLtN a b ztigo ztgwx
theorem condSub_exec (hw : WordsBounded W c) (dst a b : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W ztlme c c' k ∧
      c'.nreg dst = ztdhq ∧
      Out c c' [dst] := by
  unfold condSub
  zubjy
  · zucsl

  · zucsk

/-! ## The tour step of a tour position -/

/-- `dst := candIdx m S j` for `j` in `jr`, `S` in `sr`, `2m` in `mr` (`t` scratch). -/
def candS (dst jr sr mr : ℕ) : Stmt :=
  .ifLtN jr sr ztfmj
    ztncg
theorem candS_exec (hw : WordsBounded W c) {dst jr sr mr : ℕ} (hd1 : dst ≠ jr) (_hd2 : dst ≠ sr)
    (_hd3 : dst ≠ mr) {m S j : ℕ} (hj : c.nreg jr = j) (hs : c.nreg sr = S)
    (hm : c.nreg mr = 2 * m) (hS : S ≤ 2 * m) (hW : 2 * m ≤ W) (_hjm : j ≤ 2 * m) :
    ∃ c', ∃ k ≤ 4, Exec P W ztqjo c c' k ∧ c'.nreg dst = candIdx m S j ∧
      Out c c' [dst] := by
  zuhaj

  · zudee
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right dst dst jr
      ztgga)
    zubjo

  · zuwo

/-! ## Wrapping a walk index -/

/-- `r := r < n ? r : 0` (`n` in `nr`). -/
def nxtS (r nr : ℕ) : Stmt := .ifLtN r nr .skip ztdsd
theorem nxtS_exec (hw : WordsBounded W c) (r nr : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W zttup c c' k ∧
      c'.nreg r = ztjyr ∧ Out c c' [r] := by
  unfold nxtS
  zucfj
  · exact ztxmb
  · zucsm

/-- The wrap of `q + 1` below `n` is `(q + 1) % n`. -/
theorem wrap_succ {q n : ℕ} (hq : q < n) : ztitb = ztfo % n := by
  zus
  · zuclg
  · zubac
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE)
variable {P : Polygon} {W : ℕ} {c : Config}

/-- The descriptor words and the tour step `i = e - 6`. -/
def chainPre : Stmt := block [.constN 243096 2, .addN 243095 243020 243096, .loadN 243097 243095,
  .addN 243095 243095 243023, .loadN 243098 243095, .addN 243095 243095 243023, .loadN 243099 243095,
  .addN 243100 243097 243097, .constN 243101 7, .addN 243090 243100 243101, .constN 243103 6,
  .subN 243104 243005 243103]

/-- The start `S` of the tour (`sideS`). -/
def sS : Stmt := .ifLtN 243099 243023 ztnbr
  (.ifLtN 243023 243099 ztnbr (.instr (.copyN 243102 243098)))

/-- The tour position `j = (S + i) mod 2m` (without sums above `2m`). -/
def jS : Stmt := .seq (.instr (.subN 243105 243100 243102))
  (.ifLtN 243104 243105 (.instr (.addN 243106 243102 243104))
    (.seq (.instr (.subN 243106 243104 243105)) (condSub 243106 243106 243100)))

/-- The holes of a point inside a tour edge. -/
def edgeH : Stmt := .seq (.instr (.subN 243107 243100 243023)) (.seq (.instr (.subN 243107 243107 243106))
  (.seq (candS 243108 243107 243102 243100) (.seq ztoty
    (.seq (.instr (.copyN 241310 243005)) (.seq (.instr (.addN 241311 243005 243023))
      (.seq (.instr (.addN 241312 243108 243103)) (.instr (.addN 241313 241312 243023))))))))

/-- The third hole, at the last tour vertex, for the top. -/
def topH : Stmt := .ifLtN 243109 243098 .skip (.ifLtN 243098 243109 .skip
  (.seq (.instr (.constN 241309 3)) (.seq (.instr (.addN 241314 243100 243101))
    (.seq (.instr (.subN 241314 241314 243096)) (.instr (.constN 241315 0))))))

/-- The holes of a chain vertex. -/
def vtxH : Stmt :=
  .seq (.ifLtN 243097 243106 ztnbs ztovh)
  (.seq (candS 243110 243109 243102 243100) (.seq (.instr (.subN 243111 243100 243109))
  (.seq (candS 243112 243111 243102 243100) (.seq (.instr (.addN 243113 243110 243103))
  (.seq (.instr (.addN 243114 243112 243103)) (.seq ztoty
  (.seq (.instr (.subN 241310 243113 243023)) (.seq (.instr (.addN 241311 243113 243023))
  (.seq (nxtS 241311 243090) (.seq (.instr (.subN 241312 243114 243023))
  (.seq (.instr (.addN 241313 243114 243023)) (.seq (nxtS 241313 243090) topH))))))))))))

/-- **The holes of the candidate in a chain model.** -/
def chainH : Stmt := .seq chainPre (.seq sS (.seq jS (.ifLtN 243022 243006 edgeH vtxH)))

/-- The scratch registers of `chainH`. -/
def chainHL : List ℕ := [243090, 243095, 243096, 243097, 243098, 243099, 243100, 243101, 243102, 243103,
  243104, 243105, 243106, 243107, 243108, 243109, 243110, 243111, 243112, 243113, 243114, 241309, 241310,
  241311, 241312, 241313, 241314, 241315]

/-- The start of the tour from the descriptor words. -/
def sOf (m top bit : ℕ) : ℕ := if bit = 1 then top else 2 * m - top
theorem chainPre_exec (hw : WordsBounded W c) {B m top bit : ℕ} (hB : c.nreg 243020 = B)
    (h23 : c.nreg 243023 = 1) (hm : c.nmem zthb = m) (ht : c.nmem ztkh = top)
    (hb : c.nmem ztow = bit) (hBW : B + 4 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W chainPre c c' k ∧ c'.nreg 243097 = m ∧ c'.nreg 243098 = top ∧
      c'.nreg 243099 = bit ∧ c'.nreg 243100 = 2 * m ∧ c'.nreg 243101 = 7 ∧
      c'.nreg 243090 = 2 * m + 7 ∧ c'.nreg 243096 = 2 ∧ c'.nreg 243103 = 6 ∧
      c'.nreg 243104 = c.nreg 243005 - 6 ∧ Out c c' chainHL := by
  zulbk

  obtain ⟨c', k, ex, hk, q97, q98, q99, q100, q101, q90, q96, q103, q104, hr, rr, mm, rm, oo⟩ :
      ∃ c' k, Exec P W (block [.constN 243096 2, .addN 243095 243020 243096, .loadN 243097 243095,
        .addN 243095 243095 243023, .loadN 243098 243095, .addN 243095 243095 243023,
        .loadN 243099 243095, .addN 243100 243097 243097, .constN 243101 7,
        .addN 243090 243100 243101, .constN 243103 6, .subN 243104 243005 243103]) c c' k ∧ k = 12 ∧
        c'.nreg 243097 = m ∧ c'.nreg 243098 = top ∧ c'.nreg 243099 = bit ∧
        c'.nreg 243100 = 2 * m ∧ c'.nreg 243101 = 7 ∧ c'.nreg 243090 = 2 * m + 7 ∧
        c'.nreg 243096 = 2 ∧ c'.nreg 243103 = 6 ∧ c'.nreg 243104 = c.nreg 243005 - 6 ∧
        ztiuw ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
    have ht' : ztunm := ht
    have hb' : ztlxo := by_omega
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hB', h23]; omega)
    zubqj
    refine ztdbj
    · simp_all
    · simp_all
    · simp_all
    · zugu
    · simp
    · zugu
    · simp
    · simp
    · simp
    · zudwa

  exact ⟨c', k, by_omega, ex, q97, q98, q99, q100, q101, q90, q96, q103, q104,
    ⟨hr, rr, mm, rm, oo⟩⟩
theorem sS_exec (hw : WordsBounded W c) {m top bit : ℕ} (h99 : c.nreg 243099 = bit)
    (h100 : c.nreg 243100 = 2 * m) (h98 : c.nreg 243098 = top) (h23 : c.nreg 243023 = 1) :
    ∃ c', ∃ k ≤ 5, Exec P W sS c c' k ∧ c'.nreg 243102 = sOf m top bit ∧ Out c c' [243102] := by
  unfold sS sOf
  by_cases g1 : c.nreg 243099 < c.nreg 243023
  · zuett
    refine ztinu
    simp_all
  by_cases g2 : c.nreg 243023 < c.nreg 243099
  · zuett
    refine ztgok
    grind
  · obtain ⟨c', e, v, o⟩ := out_instr (Exec.copyN hw 243102 243098)
    refine ztgoj
    grind
theorem jS_exec (hw : WordsBounded W c) {m S i : ℕ} (_hm : 0 < m) (h102 : c.nreg 243102 = S)
    (h104 : c.nreg 243104 = i) (h100 : c.nreg 243100 = 2 * m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m)
    (hW : 2 * m ≤ W) :
    ∃ c', ∃ k ≤ 8, Exec P W jS c c' k ∧ c'.nreg 243106 = ztbat % ztdk ∧
      Out c c' [243105, 243106] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 243105 243100 243102)
  have g : ∀ r, r ≠ 243105 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r by_simp_all
  have u : c₁.nreg 243105 = 2 * m - S := by_omega
  by_cases hlt : c₁.nreg 243104 < c₁.nreg 243105
  · zubcz
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (Exec.addN e₁.wb_right 243106 243102 243104
      by_grind)
    refine ⟨c₂, _, by_omega, .seq e₁ ztspg,
      ?_, (o₁.trans o₂).mono by_simp⟩
    zudaw
  · zubcz
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (Exec.subN e₁.wb_right 243106 243104 243105)
    obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec e₂.wb_right 243106 243106 243100
    refine ⟨c₃, _, by_omega, .seq e₁ (.ifLtN_false by_simp_all
      ztcr), ?_, ((o₁.trans o₂).trans o₃).mono by_simp⟩
    have w6 : c₂.nreg 243106 = S + i - 2 * m := by
      grind
    have w100 : c₂.nreg 243100 = 2 * m := by zunmr
    zuckc

    · zucpz
    · zubyu
theorem edgeH_exec (hw : WordsBounded W c) {m S j e : ℕ} (h100 : c.nreg 243100 = 2 * m)
    (h106 : c.nreg 243106 = j) (h102 : c.nreg 243102 = S) (h103 : c.nreg 243103 = 6)
    (h23 : c.nreg 243023 = 1) (h05 : c.nreg 243005 = e) (hj : j < 2 * m) (hS : S ≤ 2 * m)
    (heW : e + 1 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W edgeH c c' k ∧ c'.nreg 241309 = 2 ∧ c'.nreg 241310 = e ∧
      c'.nreg 241311 = e + 1 ∧ c'.nreg 241312 = candIdx m S ztbdt + 6 ∧
      c'.nreg 241313 = candIdx m S ztbdt + 7 ∧
      Out c c' [243107, 243108, 241309, 241310, 241311, 241312, 241313] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 243107 243100 243023)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 243107 243107 243106)
  have g : ∀ r, r ≠ 243107 → c₂.nreg r = c.nreg r := fun r hr => by
    zugwv
  have q107 : c₂.nreg 243107 = 2 * m - 1 - j := by
    zudvl
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := candS_exec (P := P) e₂.wb_right (dst := 243108) (jr := 243107)
    (sr := 243102) (mr := 243100) by_omega by_omega by_omega q107
    by_simp_all by_simp_all hS by_omega by_omega
  have g3 : ∀ r, r ≠ 243107 → r ≠ 243108 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    zugww
  obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (P := P) (Exec.constN e₃.wb_right 241309 2 by_omega)
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.copyN e₄.wb_right 241310 243005)
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 241311 243005 243023
    (by rw [o₅.1 _ by_simp, o₄.1 _ by_simp, o₅.1 _ by_simp, o₄.1 _ by_simp,
      g3 _ by_omega by_omega, g3 _ by_omega by_omega, h05, h23]; omega))
  have c1 : ∀ r, r ≠ 241309 → r ≠ 241310 → r ≠ 241311 → c₆.nreg r = c₃.nreg r := fun r a b d => by
    zuemm
  zugly
  have a108 : c₆.nreg 243108 = candIdx m S ztbdt := by
    grind
  have a103 : c₆.nreg 243103 = 6 := by_grind
  have a23 : c₆.nreg 243023 = 1 := by_grind
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.addN e₆.wb_right 241312 243108 243103
    by_omega)
  have b12 : c₇.nreg 241312 = candIdx m S ztbdt + 6 := by_omega
  have b23 : c₇.nreg 243023 = 1 := by zuoam
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.addN e₇.wb_right 241313 241312 243023
    by_omega)
  have ex : ztpjn :=
    .seq e₁ ztey
  have a05 : c₄.nreg 243005 = e := by zunku
  have a23' : c₅.nreg 243023 = 1 := by rw [o₅.1 _ by_simp, o₄.1 _ by_simp,
    g3 _ by_omega by_omega, h23]
  have a05' : c₅.nreg 243005 = e := by zuoan
  refine ztfwf
  · zuctu
  · zudfy
  · zudvc
  · zuilz
  · omega
  · exact (((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).mono
      by_simp
theorem candIdx_le {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j ≤ 2 * m) : candIdx m S j ≤ 2 * m := by
  zumsb
theorem vtxH_exec (hw : WordsBounded W c) {m top S j : ℕ} (h97 : c.nreg 243097 = m)
    (h98 : c.nreg 243098 = top) (h100 : c.nreg 243100 = 2 * m) (h101 : c.nreg 243101 = 7)
    (h96 : c.nreg 243096 = 2) (h90 : c.nreg 243090 = 2 * m + 7) (h103 : c.nreg 243103 = 6)
    (h102 : c.nreg 243102 = S) (h106 : c.nreg 243106 = j) (h23 : c.nreg 243023 = 1)
    (hS : S ≤ 2 * m) (hj : j < 2 * m) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 60, Exec P W vtxH c c' k ∧
      c'.nreg 241309 = ztkwr ∧
      c'.nreg 241310 = candIdx m S ztkfd + 5 ∧
      c'.nreg 241311 = ztyvs % ztfk ∧
      c'.nreg 241312 = candIdx m S ztela + 5 ∧
      c'.nreg 241313 = ztyvr % ztfk ∧
      (sideE m j = top → c'.nreg 241314 = 2 * m + 5 ∧ c'.nreg 241315 = 0) ∧
      Out c c' chainHL := by
  zubzf

  -- the chain vertex
  obtain ⟨c₁, k₁, hk₁, e₁, v₁, o₁⟩ : ∃ c₁, ∃ k₁ ≤ 3, Exec P W (.ifLtN 243097 243106
      ztnbs ztovh) c c₁ k₁ ∧
      c₁.nreg 243109 = k ∧ Out c c₁ [243109] := by
    by_cases g : c.nreg 243097 < c.nreg 243106
    · obtain ⟨c', e, v, o⟩ := out_instr (Exec.subN hw 243109 243100 243106)
      zubpt

    · obtain ⟨c', e, v, o⟩ := out_instr (Exec.copyN hw 243109 243106)
      zubum

  have i1 : ∀ r, r ≠ 243109 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r by_simp_all
  obtain ⟨c₂, k₂, hk₂, e₂, v₂, o₂⟩ := candS_exec (P := P) e₁.wb_right (dst := 243110)
    (jr := 243109) (sr := 243102) (mr := 243100) by_omega by_omega by_omega v₁
    by_simp_all by_simp_all hS by_omega by_omega
  zulma
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.subN e₂.wb_right 243111 243100 243109)
  have q111 : c₃.nreg 243111 = 2 * m - k := by
    zudvm
  zulmb
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ := candS_exec (P := P) e₃.wb_right (dst := 243112)
    (jr := 243111) (sr := 243102) (mr := 243100) by_omega by_omega by_omega q111
    ztlif ztlie hS by_omega by_omega
  zubgo

  have a110 : c₄.nreg 243110 = candIdx m S k := by zunms
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.addN e₄.wb_right 243113 243110 243103
    ztiie)
  zulmc
  have a112 : c₅.nreg 243112 = candIdx m S ztbhk := by zuoao
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 243114 243112 243103
    ztiif)
  zulmd
  have q113 : c₆.nreg 243113 = candIdx m S k + 6 := by
    zudvb
  have q114 : c₆.nreg 243114 = candIdx m S ztbhk + 6 := by
    zufoq
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.constN e₆.wb_right 241309 2 by_omega)
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.subN e₇.wb_right 241310 243113 243023)
  zuhgb
  obtain ⟨c₉, e₉, v₉, o₉⟩ := out_instr (P := P) (Exec.addN e₈.wb_right 241311 243113 243023
    ztfbo)
  obtain ⟨c₁₀, k₁₀, hk₁₀, e₁₀, v₁₀, o₁₀⟩ := nxtS_exec (P := P) e₉.wb_right 241311 243090
  zuhga
  have g113 : c₉.nreg 243113 = candIdx m S k + 6 := by
    zudvd
  have g23 : ∀ {cc : Config} {L : List ℕ}, Out c cc L → 243023 ∉ L → cc.nreg 243023 = 1 :=
    fun o h => by zuoap
  obtain ⟨c₁₁, e₁₁, v₁₁, o₁₁⟩ := out_instr (P := P) (Exec.subN e₁₀.wb_right 241312 243114 243023)
  obtain ⟨c₁₂, e₁₂, v₁₂, o₁₂⟩ := out_instr (P := P) (Exec.addN e₁₁.wb_right 241313 243114 243023
    (by rw [o₁₁.1 _ by_simp, o₁₀.1 _ by_simp, o₉.1 _ by_simp, o₈.1 _ by_simp,
      o₇.1 _ by_simp, q114, g23 ztmms by_simp]; omega))
  obtain ⟨c₁₃, k₁₃, hk₁₃, e₁₃, v₁₃, o₁₃⟩ := nxtS_exec (P := P) e₁₂.wb_right 241313 243090
  zuesv
  have g114 : c₁₀.nreg 243114 = candIdx m S ztbhk + 6 := by
    zucts
  -- the values of the two vertex holes
  have a9_11 : c₉.nreg 241311 = candIdx m S k + 7 := by
    zudge
  have a9_90 : c₉.nreg 243090 = 2 * m + 7 := by zunmt
  have a12_13 : c₁₂.nreg 241313 = candIdx m S ztbhk + 7 := by
    zuems
  have a12_90 : c₁₂.nreg 243090 = 2 * m + 7 := by
    zudtf
  have w10 : c₁₃.nreg 241310 = candIdx m S k + 5 := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, o₁₀.1 _ by_simp,
      o₉.1 _ by_simp, v₈, o₇.1 _ by_simp, q113, g23 ztwaw by_simp]; omega
  have w11 : c₁₃.nreg 241311 = ztpac % ztfk := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, v₁₀, a9_11, a9_90,
      show candIdx m S k + 7 = candIdx m S k + 6 + 1 by ring]
    zuitx
  have w12 : c₁₃.nreg 241312 = candIdx m S ztbhk + 5 := by
    zuctt
  have w13 : c₁₃.nreg 241313 = ztyvq % ztfk := by
    rw [v₁₃, a12_13, a12_90, show candIdx m S _ + 7 = candIdx m S _ + 6 + 1
      by ring]
    zuitx
  have w09 : c₁₃.nreg 241309 = 2 := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, o₁₀.1 _ by_simp,
      o₉.1 _ by_simp, o₈.1 _ by_simp, v₇]
  -- the third hole
  have b109 : c₁₃.nreg 243109 = k := by
    rw [(o₂.trans (((((((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans
      o₁₀).trans o₁₁).trans o₁₂).trans o₁₃))).1 _ by_simp, v₁]
  have b98 : c₁₃.nreg 243098 = top := by zuoaq
  zumcr
  have b100 : c₁₃.nreg 243100 = 2 * m := by zuoar
  have b101 : c₁₃.nreg 243101 = 7 := by zuoas
  have b96 : c₁₃.nreg 243096 = 2 := by zuoat
  obtain ⟨cT, kT, hkT, eT, t09, t1415, oT⟩ : ∃ cT, ∃ kT ≤ 8, Exec P W topH c₁₃ cT kT ∧
      cT.nreg 241309 = ztmlr ∧
      (k = top → cT.nreg 241314 = 2 * m + 5 ∧ cT.nreg 241315 = 0) ∧
      Out c₁₃ cT [241309, 241314, 241315] := by
    unfold topH
    by_cases g1 : c₁₃.nreg 243109 < c₁₃.nreg 243098
    · refine zteye
      · zudax
      omega
    by_cases g2 : c₁₃.nreg 243098 < c₁₃.nreg 243109
    · refine ⟨c₁₃, _, by_omega, .ifLtN_false g1 ztotb, ?_,
        fun h => ?_, Out.refl _ _⟩
      · zudax
      omega
    zuhyx
    obtain ⟨d₁, f₁, u₁, p₁⟩ := out_instr (P := P) (Exec.constN hW13 241309 3 by_omega)
    obtain ⟨d₂, f₂, u₂, p₂⟩ := out_instr (P := P) (Exec.addN f₁.wb_right 241314 243100 243101
      ztgfy)
    obtain ⟨d₃, f₃, u₃, p₃⟩ := out_instr (P := P) (Exec.subN f₂.wb_right 241314 241314 243096)
    obtain ⟨d₄, f₄, u₄, p₄⟩ := out_instr (P := P) (Exec.constN f₃.wb_right 241315 0 ztbg)
    refine ⟨d₄, _, by_omega, .ifLtN_false g1 ztgwq,
      ?_, fun _ => ztcp, (((p₁.trans p₂).trans p₃).trans p₄).mono by_simp⟩
    · zudan
    · rw [p₄.1 _ by_simp, u₃, u₂, p₂.1 _ by_simp, p₁.1 _ by_simp, p₁.1 _ by_simp,
        b100, b101, p₁.1 _ by_simp, b96]; omega
    omega
  have ex : ztpjx :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      ztgxb))))))))
  refine zteba
  · zuilv
  · zuilw
  · zuilx
  · zuily
  decide
