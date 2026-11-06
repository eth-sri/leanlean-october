module

public import Chazelle.MacT
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.GranRamBody

namespace Chazelle.Core
namespace Brute
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
variable {P : Polygon} {W : ℕ} {C : Chain}
theorem bitS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW8 : 8 ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config)
    (hw : WordsBounded W c) (h0 : c.nreg 180000 = C.s) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) (h28 : c.nreg 180028 = 0) :
    ∃ c' k, Exec P W bitS c c' k ∧ k ≤ 1602 ∧ FrameB Bbit c c' ∧ c'.nreg 180014 ≤ 1 ∧
      ztmfd := by
  by_cases hT : 0 < C.topIdx
  · obtain ⟨c', k, e, hk, F, b, hb⟩ := bitGen_exec hG hW hW8 hC hsn hT c hw h0 h10 h11 h13
    exact ⟨c', _, .ifLtN_true by_omega e, by_omega, F, b, hb⟩
  · have e := Exec.constN (P := P) hw 180014 0 by_omega
    refine ⟨_, _, .ifLtN_false by_omega e, by_omega,
      ⟨fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩, by_simp, ?_⟩
    · unfold Bbit at hr
      simp_all
    · rw [sideBeta_of_top_zero by_omega]; simp

/-- The tour start: `S = T` if the bit is set, else `2m - T`. -/
def sS : Stmt := .ifLtN 180014 180011 (.instr (.subN 180015 180012 180013))
  (.instr (.copyN 180015 180013))
theorem sS_exec (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (h12 : c.nreg 180012 = 2 * C.m) (h13 : c.nreg 180013 = C.topIdx)
    (hb : c.nreg 180014 ≤ 1) (hbit : c.nreg 180014 = 1 ↔ C.sideBeta = true) :
    ∃ c' k, Exec P W sS c c' k ∧ k ≤ 3 ∧ c'.nreg 180015 = tS C ∧
      FrameB ztloo c c' := by
  have fr : ∀ v, FrameB ztloo c
      { c with nreg := upd c.nreg 180015 v } := fun v =>
    ⟨by_simp_all, by_simp_all, rfl,
      rfl, rfl⟩
  by_cases h : c.nreg 180014 < 1
  · have hf : ztidl := by
      simp_all
    refine ⟨_, _, .ifLtN_true by_omega (Exec.subN hw 180015 180012 180013),
      by omega, ?_, fr _⟩
    zubzl
    rw [h12, h13]; unfold tS Chain.sideS; simp_all
  · have ht : ztpiw := by_grind
    refine ⟨_, _, .ifLtN_false by_omega (Exec.copyN hw 180015 180013),
      by omega, ?_, fr _⟩
    zubzl
    rw [h13]; unfold tS Chain.sideS; simp_all

/-! ## Stores -/

/-- Store the value register `v` at the pointer `p`, then advance the pointer. -/
def putS (p v : ℕ) : Stmt := block [.storeN p v, .addN p p 180011]
theorem putS_exec (c : Config) (hw : WordsBounded W c) {p v : ℕ}
    (_hp : p ≠ 180011) (h11 : c.nreg 180011 = 1) (hroom : c.nreg p + 1 ≤ W) :
    ∃ c' k, Exec P W (putS p v) c c' k ∧ k = 2 ∧ c'.nreg p = c.nreg p + 1 ∧
      c'.nmem = upd c.nmem ztfgw ztjsn ∧ (∀ r, r ≠ p → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold putS
  exec_block
  · simp_all
  simp_all

/-- The host and the descriptor. -/
def descS : Stmt :=
  .seq ztjpl
  (.seq (putS 180045 180011) (.seq ztoer (.seq ztoer
  (.seq (putS 180045 180046) (.seq (.instr (.copyN 180017 180045))
  (.seq ztoer (.seq (putS 180045 180016) (.seq (putS 180045 180000)
  (.seq (putS 180045 180001) (.seq (putS 180045 180013) (.seq (putS 180045 180014)
    zthsy)))))))))))

/-- The memory words of the host and the descriptor at `A₀`. -/
def DescMem (P : Polygon) (C : Chain) (m : ℕ → ℕ) (A₀ : ℕ) : Prop :=
  m A₀ = 1 ∧ m ztfnc = 0 ∧ m (A₀ + 2) = 0 ∧ m (A₀ + 3) = P.n - 1 ∧ m ztnjb = 0 ∧
    m (A₀ + 5) = A₀ ∧ m ztsux = C.s ∧ m ztsuy = C.m ∧ m (A₀ + 8) = C.topIdx ∧
    (m (A₀ + 9) = 1 ↔ C.sideBeta = true)
theorem descMem_agree {m m' : ℕ → ℕ} {A₀ : ℕ} (h : DescMem P C m A₀)
    (hm : ∀ a, a < A₀ + 10 → m' a = m a) : DescMem P C m' A₀ := by
  zucbh
  refine ztbbh
  all_goals first
    | (rwa [hm _ by_omega])
    | skip

/-- **The descriptor words describe the chain model**, and are well formed below `E`. -/
theorem descMem_model (hC : C.P = Qof P) (hn1 : 1 ≤ P.n)
    (hsn : C.s < P.n) {m : ℕ → ℕ} {A₀ : ℕ} (h : DescMem P C m A₀) {E : ℕ} (hE : A₀ + 10 ≤ E) :
    ModelDescAt m ztnjb zta ztc ∧ ModelDescWF P E m ztnjb := by
  zucbh
  zuc
  have hH : HostAt m A₀ ztoxa := by
    refine ztomy
    have hi0 : ztfla := by simpa [Host.whole] using hi
    zufpy
    zuiow

  have hCD : ChainDescAt m ztpvu _ ztoxa C :=
    ⟨by_simp_all,
      by rw [hC, poly_whole _ by_omega],
      by omega,
      by omega,
      by omega,
      by omega⟩
  refine ⟨Or.inl ⟨h4, _, _, hCD, rfl⟩, by_omega, fun _ => ztmqi⟩
  have hHH : H = Host.whole (Qof P).n := by
    have e5 : m ztpvu = A₀ := by_omega
    have := hC'.1
    rw [e5] at this
    exact NFLoc.hostAt_unique this hH
  zular
  refine ⟨by zvohn, ?_, ?_, ?_⟩
  · zujbe
    simp only [Host.whole, List.mem_cons, List.not_mem_nil, or_false] at hit
    grind
  · rw [show A₀ + 4 + 1 = A₀ + 5 by ring, h5]; zvohn; omega
  · have e1 : ztidk := by
      have := hC'.2.2.1; simp_all
    have e2 : ztpiu := by rw [hC'.2.1, poly_whole _ by_omega]
    simp_all

/-- The memory after the ten stores of `descS`. -/
def descMemory (m : ℕ → ℕ) (A₀ n s mm T b : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m A₀ 1)
      ztfnc 0) (A₀ + 2) 0) (A₀ + 3) (n - 1)) (A₀ + 4) 0) (A₀ + 5) A₀) (A₀ + 6) s)
      ztsuy mm) (A₀ + 8) T) (A₀ + 9) b
theorem descMemory_desc (m : ℕ → ℕ) (A₀ b : ℕ)
    (hbit : b = 1 ↔ C.sideBeta = true) :
    DescMem P C (descMemory m A₀ P.n C.s C.m C.topIdx b) A₀ := by
  unfold descMemory
  refine ztbbh <;>
    zusb
  omega
theorem descMemory_below (m : ℕ → ℕ) (A₀ n s mm T b : ℕ) {a : ℕ} (ha : a < A₀) :
    descMemory m A₀ n s mm T b a = m a := by
  unfold descMemory
  zup
set_option maxHeartbeats 2000000 in
/-- **The host and the descriptor** at `A₀`. -/
theorem descS_exec (c : Config) (hw : WordsBounded W c)
    {A₀ : ℕ} (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) (h16 : c.nreg 180016 = A₀)
    (h28 : c.nreg 180028 = 0) (hbit : c.nreg 180014 = 1 ↔ C.sideBeta = true)
    (hroom : A₀ + 10 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 26 ∧ DescMem P C c'.nmem A₀ ∧
      ztpt ∧ c'.nreg 180017 = A₀ + 4 ∧
      c'.nreg 180018 = A₀ + 10 ∧ c'.nreg 180024 = A₀ + 10 ∧ c'.nreg 180019 = 0 ∧
      (∀ r, r ≠ 180017 → r ≠ 180018 → r ≠ 180024 → r ≠ 180019 → r ≠ 180045 → r ≠ 180046 →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d0, k0, e0, hk0, p0, q0, R0, rr0, m0, rm0, o0⟩ : ∃ d k, Exec P W
      ztjpl c d k ∧ k = 2 ∧
      d.nreg 180045 = A₀ ∧ d.nreg 180046 = P.n - 1 ∧
      (∀ r, r ≠ 180045 → r ≠ 180046 → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧
      d.nmem = c.nmem ∧ d.rmem = c.rmem ∧ d.output = c.output := by
    exec_block
    simp_all
  have K0 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d0.nreg r = c.nreg r :=
    by simp_all
  have Q0 := q0
  have u1 : d0.nreg 180011 = 1 := by_simp_all
  have w1 : d0.nreg 180011 = c.nreg 180011 := by_omega
  obtain ⟨d1, k1, e1, hk1, p1, m1, R1, rr1, rm1, o1⟩ := putS_exec (P := P) d0 e0.wb_right
    (p := 180045) (v := 180011) by_decide u1 by_omega
  rw [p0, w1] at m1
  rw [p0] at p1
  have K1 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d1.nreg r = c.nreg r :=
    by simp_all
  have Q1 : d1.nreg 180046 = P.n - 1 := by_simp_all
  have u2 : d1.nreg 180011 = 1 := by_simp_all
  have w2 : d1.nreg 180028 = c.nreg 180028 := by_simp_all
  obtain ⟨d2, k2, e2, hk2, p2, m2, R2, rr2, rm2, o2⟩ := putS_exec (P := P) d1 e1.wb_right
    (p := 180045) (v := 180028) by_decide u2 by_omega
  rw [p1, w2] at m2
  rw [p1] at p2
  have K2 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d2.nreg r = c.nreg r :=
    by simp_all
  have Q2 : d2.nreg 180046 = P.n - 1 := by_simp_all
  have u3 : d2.nreg 180011 = 1 := by_simp_all
  have w3 : d2.nreg 180028 = c.nreg 180028 := by_simp_all
  obtain ⟨d3, k3, e3, hk3, p3, m3, R3, rr3, rm3, o3⟩ := putS_exec (P := P) d2 e2.wb_right
    (p := 180045) (v := 180028) by_decide u3 by_omega
  rw [p2, w3] at m3
  rw [p2] at p3
  have K3 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d3.nreg r = c.nreg r :=
    by grind
  have Q3 : d3.nreg 180046 = P.n - 1 := by_grind
  have u4 : d3.nreg 180011 = 1 := by_grind
  have w4 := Q3
  obtain ⟨d4, k4, e4, hk4, p4, m4, R4, rr4, rm4, o4⟩ := putS_exec (P := P) d3 e3.wb_right
    (p := 180045) (v := 180046) by_decide u4 by_omega
  rw [p3, w4] at m4
  rw [p3] at p4
  have K4 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d4.nreg r = c.nreg r :=
    by grind
  have Q4 : d4.nreg 180046 = P.n - 1 := by_grind
  have eD := Exec.copyN (P := P) e4.wb_right 180017 180045
  set dD : Config := { d4 with nreg := upd d4.nreg 180017 _ } with hdD
  have pD : dD.nreg 180045 = A₀ + 4 := by
    zunrg; zumzy; zunbw; zuotv
  have qD : dD.nreg 180017 = A₀ + 4 := by
    zunrg; zuocj; zuotv
  have KD : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → dD.nreg r = c.nreg r := fun r h1 h2 h3 => by
    zunrg; zumzy; rw [upd_other _ _ _ h3]; grind
  have QD : dD.nreg 180046 = P.n - 1 := by
    zunrg; zumzy; zunbw; exact Q4
  have mD : dD.nmem = d4.nmem := rfl
  have u5 : dD.nreg 180011 = 1 := by_grind
  have w5 : dD.nreg 180028 = c.nreg 180028 := by_grind
  obtain ⟨d5, k5, e5, hk5, p5, m5, R5, rr5, rm5, o5⟩ := putS_exec (P := P) dD eD.wb_right
    (p := 180045) (v := 180028) by_decide u5 by_omega
  rw [pD, w5] at m5
  rw [pD] at p5
  have K5 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d5.nreg r = c.nreg r :=
    by grind
  have Q5 : d5.nreg 180046 = P.n - 1 := by_grind
  have u6 : d5.nreg 180011 = 1 := by_grind
  have w6 : d5.nreg 180016 = c.nreg 180016 := by_grind
  obtain ⟨d6, k6, e6, hk6, p6, m6, R6, rr6, rm6, o6⟩ := putS_exec (P := P) d5 e5.wb_right
    (p := 180045) (v := 180016) by_decide u6 by_grind
  rw [p5, w6] at m6
  rw [p5] at p6
  have K6 :=
    fun r h1 h2 h3 => (R6 r h1).trans (K5 r h1 h2 h3)
  have Q6 := (R6 _ by_decide).trans Q5
  have u7 : d6.nreg 180011 = 1 := by rw [K6 _ by_decide by_decide by_decide, h11]
  have w7 : d6.nreg 180000 = c.nreg 180000 := K6 _ by_decide by_decide by_decide
  obtain ⟨d7, k7, e7, hk7, p7, m7, R7, rr7, rm7, o7⟩ := putS_exec (P := P) d6 e6.wb_right
    (p := 180045) (v := 180000) by_decide u7 by_grind
  rw [p6, w7] at m7
  rw [p6] at p7
  have K7 :=
    fun r h1 h2 h3 => (R7 r h1).trans (K6 r h1 h2 h3)
  have Q7 := (R7 _ by_decide).trans Q6
  have u8 : d7.nreg 180011 = 1 := by rw [K7 _ by_decide by_decide by_decide, h11]
  have w8 : d7.nreg 180001 = c.nreg 180001 := K7 _ by_decide by_decide by_decide
  obtain ⟨d8, k8, e8, hk8, p8, m8, R8, rr8, rm8, o8⟩ := putS_exec (P := P) d7 e7.wb_right
    (p := 180045) (v := 180001) by_decide u8 by_grind
  rw [p7, w8] at m8
  rw [p7] at p8
  have K8 :=
    fun r h1 h2 h3 => (R8 r h1).trans (K7 r h1 h2 h3)
  have Q8 := (R8 _ by_decide).trans Q7
  have u9 : d8.nreg 180011 = 1 := by rw [K8 _ by_decide by_decide by_decide, h11]
  have w9 : d8.nreg 180013 = c.nreg 180013 := K8 _ by_decide by_decide by_decide
  obtain ⟨d9, k9, e9, hk9, p9, m9, R9, rr9, rm9, o9⟩ := putS_exec (P := P) d8 e8.wb_right
    (p := 180045) (v := 180013) by_decide u9 by_grind
  rw [p8, w9] at m9
  rw [p8] at p9
  have K9 :=
    fun r h1 h2 h3 => (R9 r h1).trans (K8 r h1 h2 h3)
  have Q9 := (R9 _ by_decide).trans Q8
  have u10 : d9.nreg 180011 = 1 := by rw [K9 _ by_decide by_decide by_decide, h11]
  have w10 : d9.nreg 180014 = c.nreg 180014 := K9 _ by_decide by_decide by_decide
  obtain ⟨d10, k10, e10, hk10, p10, m10, R10, rr10, rm10, o10⟩ := putS_exec (P := P) d9 e9.wb_right
    (p := 180045) (v := 180014) by_decide u10 by_grind
  rw [p9, w10] at m10
  rw [p9] at p10
  have K10 :=
    fun r h1 h2 h3 => (R10 r h1).trans (K9 r h1 h2 h3)
  have Q10 := (R10 _ by_decide).trans Q9
  have q17 : d10.nreg 180017 = A₀ + 4 := by
    rw [R10 _ by_decide, R9 _ by_decide, R8 _ by_decide, R7 _ by_decide,
      R6 _ by_decide, R5 _ by_decide, qD]
  obtain ⟨d11, k11, e11, hk11, s18, s24, s19, R11, rr11, m11, rm11, o11⟩ : ∃ d k, Exec P W
      zthsy d10 d k ∧ k = 3 ∧
      d.nreg 180018 = A₀ + 10 ∧ d.nreg 180024 = A₀ + 10 ∧ d.nreg 180019 = 0 ∧
      (∀ r, r ≠ 180018 → r ≠ 180024 → r ≠ 180019 → d.nreg r = d10.nreg r) ∧ d.rreg = d10.rreg ∧
      d.nmem = d10.nmem ∧ d.rmem = d10.rmem ∧ d.output = d10.output := by
    have w := e10.wb_right
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩ <;>
        zubs
      · rw [p10]
      omega
  have ex : Exec P W descS c d11 _ :=
    .seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq eD (.seq e5 (.seq e6 (.seq e7 (.seq e8
      (.seq e9 ztspx))))))))))
  have hmem : d11.nmem = descMemory c.nmem A₀ P.n C.s C.m C.topIdx (c.nreg 180014) := by
    rw [m11, m10, m9, m8, m7, m6, m5, mD, m4, m3, m2, m1, m0, h11, h28, h16, h0, h1, h13]; rfl
  refine ⟨d11, _, ex, by_grind, ?_, fun a ha => ?_, by rw [R11 _ by_decide by_decide
    by_decide, q17], s18, s24, s19, fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_⟩
  · rw [hmem]; exact descMemory_desc _ _ _ hbit
  · rw [hmem]; exact descMemory_below _ _ _ _ _ _ _ ha
  · rw [R11 r h2 h3 h4]; exact K10 r h5 h6 h1
  · grind
  · grind
  grind

/-! ## The set-up phase -/

/-- The register context after the set-up (see the table in `BruteRam1`). -/
def Ctx (P : Polygon) (C : Chain) (γ A₀ : ℕ) (c : Config) : Prop :=
  c.nreg 180000 = C.s ∧ c.nreg 180001 = C.m ∧ c.nreg 180002 = γ ∧ c.nreg 180010 = P.n ∧
    c.nreg 180011 = 1 ∧ c.nreg 180012 = 2 * C.m ∧ c.nreg 180013 = C.topIdx ∧
    c.nreg 180015 = tS C ∧ c.nreg 180016 = A₀ ∧ c.nreg 180017 = A₀ + 4 ∧
    c.nreg 180018 = A₀ + 10 ∧ c.nreg 180023 = C.m + 1 ∧ c.nreg 180025 = 2 * C.m + 1 ∧
    c.nreg 180026 = 3 ∧ c.nreg 180027 = 6 ∧ c.nreg 180028 = 0

/-- The registers of the context. -/
def CtxReg (r : ℕ) : Prop :=
  ztnez ∨ (180010 ≤ r ∧ r < 180014) ∨ (180015 ≤ r ∧ r < 180019) ∨
    r = 180023 ∨ (180025 ≤ r ∧ r < 180029)

/-- The context survives when its registers do. -/
theorem Ctx.keep {γ A₀ : ℕ} {c c' : Config} (h : Ctx P C γ A₀ c)
    (hk : ∀ r, CtxReg r → c'.nreg r = c.nreg r) : Ctx P C γ A₀ c' := by
  obtain ⟨h0, h1, h2, h10, h11, h12, h13, h15, h16, h17, h18, h23, h25, h26, h27, h28⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hk _ by_tauto]; assumption)

/-- The set-up phase. -/
def setupS : Stmt := .seq initS (.seq topS (.seq bitS (.seq sS descS)))
set_option maxHeartbeats 1000000 in
/-- **The set-up phase**. -/
theorem setup_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hW2 : P.n + 2 * C.m + 7 ≤ W)
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (hroom : c.nreg ALLOC + 2 * C.m + 10 ≤ W) :
    ∃ c' k, Exec P W setupS c c' k ∧ k ≤ 260 * C.m + 1900 ∧ 10 ≤ k ∧
      Ctx P C (c.nreg 180002) ztm c' ∧ DescMem P C c'.nmem ztm ∧
      zth ∧ c'.nreg 180019 = 0 ∧
      c'.nreg 180024 = c.nreg ALLOC + 10 ∧ (∀ r, Bm r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, Bm r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zudzi
  zudhf
  zuce
  -- constants
  obtain ⟨c₁, k₁, e₁, hk₁, i10, i11, i12, i16, i26, i27, i28, i23, i25, F₁⟩ :=
    initS_exec (P := P) c hw by_omega
  have g : ∀ r, (r < 180010 ∨ 180030 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    F₁.1 r by_grind
  have j0 : c₁.nreg 180000 = C.s := by_simp_all
  have j1 : c₁.nreg 180001 = C.m := by_simp_all
  zvmwp at i12 i23 i25
  replace i16 : c₁.nreg 180016 = A₀ := i16
  -- top index
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, t13, tmax⟩ := topS_exec (P := P) hG by_omega c₁ e₁.wb_right
    j0 i11 i23 by_omega
  have hT : c₂.nreg 180013 = C.topIdx := by
    refine (topIdx_eq_of_max hDH t13 fun i hi => ?_).symm
    have e1 := vertex_eq (C := C) (k := i) by_omega
    have e2 := vertex_eq (C := C) (k := c₂.nreg 180013) by_omega
    simp_all
  have kk2 := F₂.1
  -- the bit
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b14, t14⟩ := bitS_exec (P := P) hG by_omega by_omega hC hsn c₂
    e₂.wb_right (by rw [kk2 _ by_decide, j0]) (by rw [kk2 _ by_decide, i10])
    (by rw [kk2 _ by_decide, i11]) hT (by rw [kk2 _ by_decide, i28])
  have kk3 := F₃.1
  -- the tour start
  obtain ⟨c₄, k₄, e₄, hk₄, s15, F₄⟩ := sS_exec (P := P) (C := C) c₃ e₃.wb_right
    (by rw [kk3 _ by_decide, kk2 _ by_decide, i11])
    (by rw [kk3 _ by_decide, kk2 _ by_decide, i12])
    (by rw [kk3 _ by_decide, hT]) b14 t14
  have kk4 : ∀ r, r ≠ 180015 → c₄.nreg r = c₃.nreg r := fun r hr =>
    F₄.1 r by_simp_all
  -- a register untouched since `c₁`
  have up : ∀ r, Btop r = false → Bbit r = false → r ≠ 180015 → c₄.nreg r = c₁.nreg r :=
    by simp_all
  -- the descriptor
  obtain ⟨c₅, k₅, e₅, hk₅, hD, hlow, q17, q18, q24, q19, R₅, rr₅, rm₅, o₅⟩ :=
    descS_exec (P := P) (C := C) (A₀ := A₀) c₄ e₄.wb_right
    (by rw [up _ by_decide by_decide by_decide, j0])
    (by rw [up _ by_decide by_decide by_decide, j1])
    (by rw [up _ by_decide by_decide by_decide, i10])
    (by rw [up _ by_decide by_decide by_decide, i11])
    (by rw [kk4 _ by_decide, kk3 _ by_decide, hT])
    (by rw [up _ by_decide by_decide by_decide, i16])
    (by rw [up _ by_decide by_decide by_decide, i28])
    by_simp_all by_omega
  have ex : Exec P W setupS c c₅ _ :=
    .seq e₁ ztbq
  -- the memory is unchanged before `descS`
  have m4 : zteid := by rw [F₄.2.2.1, F₃.2.2.1, F₂.2.2.1, F₁.2.2.1]
  have all5 : ∀ r, Bm r = false → c₅.nreg r = c.nreg r := by
    zuz
    have hr' : ztguq := by
      zulax

    rw [R₅ r by_omega by_omega by_omega by_omega by_omega by_omega, kk4 r by_omega,
      kk3 r (by unfold Bbit Bk; zvnam; omega),
      kk2 r (by unfold Btop Bk; zvnam; omega),
      g r by_omega]
  refine ⟨c₅, _, ex, by_omega, by_omega, ?_, hD, fun a ha => by_grind, q19,
    q24, all5, fun r hr => ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q17, q18, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [R₅ _ by_decide by_decide by_decide by_decide by_decide by_decide,
          up _ by_decide by_decide by_decide]; first | assumption | rfl |
          (rw [g _ by_omega]))
      | (rw [R₅ _ by_decide by_decide by_decide by_decide by_decide by_decide,
          kk4 _ by_decide, kk3 _ by_decide]; exact hT)
      | (rw [R₅ _ by_decide by_decide by_decide by_decide by_decide by_decide];
          exact s15)
  · have hr' : ztguq := by
      zulax

    have x4 : (fun q => decide (q = 180015)) r = false := by
      grind
    have x3 : Bbit r = false := by
      unfold Bbit Bk; zvnam; omega
    have x2 : Btop r = false := by
      unfold Btop Bk; zvnam; omega
    have x1 : (fun q => decide (180010 ≤ q ∧ q < 180030)) r = false := by
      grind
    rw [rr₅, F₄.2.1 r x4, F₃.2.1 r x3, F₂.2.1 r x2, F₁.2.1 r x1]
  · rw [rm₅, F₄.2.2.2.1, F₃.2.2.2.1, F₂.2.2.2.1, F₁.2.2.2.1]
  · rw [o₅, F₄.2.2.2.2, F₃.2.2.2.2, F₂.2.2.2.2, F₁.2.2.2.2]
variable {d : ℕ} {k : ℕ} {σ : ℝ} {j : ℕ}
theorem vtxQ {C : Chain} (hC : C.P = Qof P) (_hsn : C.s + C.m + 1 ≤ P.n) {j : ℕ}
    (_hj : j ≤ C.m + 1) (hjn : C.s + j < P.n) : (Qof P).vtx ztjhj = C.vertex j := by
  zudzi
  rw [vertex_eq by_omega, hC]
theorem edgeXQ (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {j k : ℕ}
    (hj : j < C.m) (hk : k ≤ C.m) :
    edgeXAt zta ztjhj zttw = edgeXk C j k := by
  zuc
  unfold edgeXAt edgeXk Visibility.edgeX
  rw [Nat.mod_eq_of_lt by_omega, vtxQ hC hsn by_omega by_omega,
    show C.s + j + 1 = C.s + ztl by ring, vtxQ hC hsn by_omega by_omega,
    vtxQ hC hsn by_omega by_omega]

/-- The encoding of the scan state: `found = 0`, or `found = 1` and `best`. -/
def Enc (found best : ℕ) : Option ℕ → Prop
  | none => found = 0
  | some b => found = 1 ∧ best = b

/-! ## The statements -/

/-- The side test of candidate `j` (into `180077`). -/
def sideS (d : ℕ) : Stmt :=
  if d = 0 then testS 0 ztdbr ztjcv ztdye 180077
  else testS 0 ztjcv ztdbr ztdye 180077

/-- The nearer test (into `180078`). -/
def nearS (d : ℕ) : Stmt :=
  if d = 0 then testS 0 ztjcv ztsov ztdye 180078
  else testS 0 ztsov ztjcv ztdye 180078

/-- A candidate: take it if none was found, else if it is nearer. -/
def candS (d : ℕ) : Stmt :=
  .ifLtN 180051 180011 ztkrx
    (.seq (.instr (.addN 180055 180000 180052))
      (.seq ztvzr (.ifLtN 180078 180011 .skip (.instr (.copyN 180052 180050)))))

/-- One step of the scan. -/
def scanBody (d : ℕ) : Stmt :=
  .seq ztiqj
  (.seq (testS 1 ztdye ztdbr ztdye 180056)
  (.seq (testS 1 ztdbr ztuvv ztdye 180057)
  (.seq (testS 1 ztuvv ztdbr ztdye 180058)
  (.seq (testS 1 ztdbr ztdye ztdye 180059)
  (.seq (andS 180056 180056 180057) (.seq (andS 180058 180058 180059)
  (.seq (orS 180076 180056 180058 180079) (.seq ztweb (.seq (andS 180076 180076 180077)
  (.seq ztlzx (.instr (.addN 180050 180050 180011))))))))))))

/-- The scan. -/
def scanS (d : ℕ) : Stmt :=
  .seq zthsl
    (.whileLtN 180050 180001 ztwdg)

/-- The write set of the scan: the kernel and `180050 … 180089`. -/
def Bsc (r : ℕ) : Bool := Bk r || decide (180050 ≤ r ∧ r < 180090)

/-- The registers the scan reads. -/
def SI (C : Chain) (qk : ℕ) (c : Config) : Prop :=
  c.nreg 180000 = C.s ∧ c.nreg 180001 = C.m ∧ c.nreg 180011 = 1 ∧ c.nreg 180035 = qk
theorem SI.keep {qk : ℕ} {c c' : Config} (h : SI C qk c) (F : FrameB Bsc c c') :
    SI C qk c' := by
  obtain ⟨h0, h1, h11, h35⟩ := h
  exact ⟨by rw [F.1 _ by_decide, h0], by rw [F.1 _ by_decide, h1],
    by rw [F.1 _ by_decide, h11], by rw [F.1 _ by_decide, h35]⟩
theorem sc_of_bt (hd : 180050 ≤ d ∧ d < 180090) {c c' : Config} (F : FrameB ztjhb c c') :
    FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    unfold Bsc at hr; unfold Bt
    grind
theorem sc_of_one (hd : 180050 ≤ d ∧ d < 180090) {c c' : Config}
    (F : FrameB ztbaz c c') : FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    zultn
theorem sc_of_two {d t : ℕ} (hd : 180050 ≤ d ∧ d < 180090) (ht : 180050 ≤ t ∧ t < 180090)
    {c c' : Config} (F : FrameB ztbqe c c') : FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    zultn

/-! ## The tests of a scan step -/
theorem sig_zero : sig 0 = 1 := rfl
theorem sig_one (hd : d ≠ 0) : sig d = -1 := by unfold sig; simp_all
theorem sideS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (h35 : c.nreg 180035 = C.s + k)
    (h53 : c.nreg 180053 = C.s + j) :
    ∃ c' k', Exec P W ztweb c c' k' ∧ k' ≤ 245 ∧ FrameB (Bt 180077) c c' ∧
      c'.nreg 180077 ≤ 1 ∧
      (c'.nreg 180077 = 1 ↔ 0 < sig d * ztkvv) := by
  zukig
  zukif
  zuclb
  · subst hd
    obtain ⟨c', k', e, hk', F, b, hb⟩ := testS_exec hG hW (op := 0) by_omega
      (x := .v 180035) (y := .e 180053 180035) (z := .v 180053) ztbh
      ⟨by_omega, by_omega⟩ ztbh c hw
      ztig ztig
      ztig
    zubir

    refine ⟨c', k', e, hk', F, b, ?_⟩
    rw [hb, sig_zero, one_mul, sub_pos]
  · obtain ⟨c', k', e, hk', F, b, hb⟩ := testS_exec hG hW (op := 0) by_omega
      (x := .e 180053 180035) (y := .v 180035) (z := .v 180053)
      ⟨by_omega, by_omega⟩ ztbh ztbh c hw
      ztig ztig
      ztig
    zubir

    refine ⟨c', k', by unfold sideS; simp_all, hk', F, b, ?_⟩
    rw [hb, sig_one hd]
    simp
theorem nearS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j b k : ℕ} (hj : j < C.m) (hb : b < C.m)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (h35 : c.nreg 180035 = C.s + k)
    (h53 : c.nreg 180053 = C.s + j) (h55 : c.nreg 180055 = C.s + b) :
    ∃ c' k', Exec P W ztvzr c c' k' ∧ k' ≤ 245 ∧ FrameB (Bt 180078) c c' ∧
      c'.nreg 180078 ≤ 1 ∧
      (c'.nreg 180078 = 1 ↔ sig d * edgeXk C j k < sig d * edgeXk C b k) := by
  zuclb
  · subst hd
    obtain ⟨c', k', e, hk', F, b', hb'⟩ := testS_exec hG hW (op := 0) by_omega
      (x := .e 180053 180035) (y := .e 180055 180035) (z := .v 180053)
      ⟨by_omega, by_omega⟩ ⟨by_omega, by_omega⟩
      ztbh c hw
      ztig ztig
      ztig
    zubeq

    refine ⟨c', k', e, hk', F, b', ?_⟩
    rw [hb', sig_zero, one_mul, one_mul]
  · obtain ⟨c', k', e, hk', F, b', hb'⟩ := testS_exec hG hW (op := 0) by_omega
      (x := .e 180055 180035) (y := .e 180053 180035) (z := .v 180053)
      ⟨by_omega, by_omega⟩ ⟨by_omega, by_omega⟩
      ztbh c hw
      ztig ztig
      ztig
    zubeq

    refine ⟨c', k', by unfold nearS; simp_all, hk', F, b', ?_⟩
    rw [hb', sig_one hd]
    simp

/-! ## A candidate -/

/-- The update of the scan state by a candidate `j`. -/
noncomputable def upd1 (C : Chain) (k : ℕ) (σ : ℝ) (j : ℕ) : Option ℕ → Option ℕ := by
  classical
  exact fun o => match o with
    | none => some j
    | some b => if σ * edgeXk C j k < σ * edgeXk C b k then some j else some b
theorem scan_succ_cand (h : Cand C k σ j) :
    scan C k σ ztl = upd1 C k σ j (scan C k σ j) := by
  classical
  show ztkwl = _
  zueyn
  unfold upd1
  rcases scan C k σ j with _ | b <;> rfl
theorem scan_succ_not (h : ¬ Cand C k σ j) :
    scan C k σ ztl = scan C k σ j := by
  classical
  show ztkwl = _
  zubme
theorem candS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C zttw c) (h50 : c.nreg 180050 = j)
    (h53 : c.nreg 180053 = C.s + j) (hE : Enc ztqhp ztqhq ztxxy)
    (hsc : ∀ b, scan C k ztbgm j = some b → b < C.m) :
    ∃ c' k', Exec P W (candS d) c c' k' ∧ k' ≤ 260 ∧ FrameB Bsc c c' ∧ c'.nreg 180050 = j ∧
      Enc ztqgy ztqgz (upd1 C k ztbgm j ztxxy) := by
  zucdv
  rcases hsj : scan C k _ j with _ | b
  · zukwg
    zudbu
    obtain ⟨c', k', e, hk', q52, q51, R⟩ : ∃ c' k', Exec P W
        ztkrx c c' k' ∧ k' = 2 ∧
        c'.nreg 180052 = j ∧ c'.nreg 180051 = 1 ∧
        FrameB (fun r => decide (r = 180052 ∨ r = 180051)) c c' := by
      exec_block
      · omega
      · refine ztxmh
        · simp_all
        · simp
        simp_all
    refine ⟨c', _, .ifLtN_true by_omega e, by_omega, sc_of_two by_omega
      by_omega R, by rw [R.1 _ by_decide, h50], ?_⟩
    tauto
  · zukwg
    zudbu
    zuicp
    have hbm := hsc b hsj
    have e₁ := Exec.addN (P := P) hw 180055 180000 180052 by_omega
    set c₁ : Config := { c with nreg := upd c.nreg 180055 _ }
      with hc₁
    have R₁ : ∀ r, r ≠ 180055 → c₁.nreg r = c.nreg r := by_simp_all
    have q55 : c₁.nreg 180055 = C.s + b := by_simp_all
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, bit₂, t₂⟩ := nearS_exec hG hW hC hsn hj hbm hk
      c₁ e₁.wb_right by_simp_all by_simp_all q55
    have k11 : ztpnd := by rw [F₂.1 _ by_decide, R₁ _ by_decide, h11]
    have k50 : c₂.nreg 180050 = j := by rw [F₂.1 _ by_decide, R₁ _ by_decide, h50]
    have k52 : ztura := by rw [F₂.1 _ by_decide, R₁ _ by_decide, hb]
    have k51 : c₂.nreg 180051 = 1 := by rw [F₂.1 _ by_decide, R₁ _ by_decide, hf]
    zue
    have F₁ : FrameB Bsc c c₁ := ⟨fun r hr => R₁ r (by
      unfold Bsc at hr; grind),
      by simp_all, rfl, rfl, rfl⟩
    by_cases hn : sig d * edgeXk C j k < sig d * edgeXk C b k
    · have e₃ := Exec.copyN (P := P) w₂ 180052 180050
      refine ⟨_, _, .ifLtN_false by_omega (.seq e₁ (.seq e₂
        (.ifLtN_false by_simp_all e₃))), by_omega,
        (F₁.trans ztker).trans ztgq,
        ?_, ?_⟩
      · have : r ≠ 180052 := by
          zudwe
        simp_all
      · simp_all
      · simp only [upd1, Enc, ite_eq_left hn]
        simp_all
    · have h0' : c₂.nreg 180078 = 0 := by_grind
      refine ⟨_, _, .ifLtN_false by_omega (.seq e₁ (.seq e₂
        ztzru)), by_omega,
        F₁.trans ztker, k50, ?_⟩
      simp only [upd1, Enc, ite_eq_right hn]
      omega

/-! ## One step of the scan -/
set_option maxHeartbeats 1000000 in
theorem scanBody_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C zttw c) (h50 : c.nreg 180050 = j)
    (hE : Enc ztqhp ztqhq ztxxy)
    (hsc : ∀ b, scan C k ztbgm j = some b → b < C.m) :
    ∃ c' k', Exec P W ztwdg c c' k' ∧ k' ≤ 1600 ∧ FrameB Bsc c c' ∧
      c'.nreg 180050 = j + 1 ∧
      Enc ztqgy ztqgz ztzgy := by
  have hS0 := hS
  zucdv
  zukif
  have lj1 : C.s + j + 1 < P.n := by_omega
  zukig
  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, q53, q54, R₁⟩ : ∃ c₁ k₁, Exec P W
      ztiqj c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180053 = C.s + j ∧ c₁.nreg 180054 = C.s + j + 1 ∧
      FrameB (fun r => decide (r = 180053 ∨ r = 180054)) c c₁ := by
    exec_block
    · omega
    · config_simp; omega
    · refine ztxmh
      · simp_all
      · simp_all
      simp_all
  zuiuq
  have S₁ := hS0.keep G₁
  -- the four height tests
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b56, t56⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180053) (r₂ := 180035) (r₃ := 180053) (d := 180056) ztbh
    ztbh ztbh c₁ e₁.wb_right q53 S₁.2.2.2 q53 lj lk lj
  have S₂ := S₁.keep ztker
  have q53₂ : c₂.nreg 180053 = C.s + j := by rw [F₂.1 _ by_decide, q53]
  have q54₂ : c₂.nreg 180054 = C.s + j + 1 := by rw [F₂.1 _ by_decide, q54]
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b57, t57⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180035) (r₂ := 180054) (r₃ := 180053) (d := 180057) ztbh
    ztbh ztbh c₂ e₂.wb_right S₂.2.2.2 q54₂ q53₂ lk lj1 lj
  have S₃ := S₂.keep zttzw
  have q53₃ : c₃.nreg 180053 = C.s + j := by rw [F₃.1 _ by_decide, q53₂]
  have q54₃ : c₃.nreg 180054 = C.s + j + 1 := by rw [F₃.1 _ by_decide, q54₂]
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b58, t58⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180054) (r₂ := 180035) (r₃ := 180053) (d := 180058) ztbh
    ztbh ztbh c₃ e₃.wb_right q54₃ S₃.2.2.2 q53₃ lj1 lk lj
  have S₄ := S₃.keep zttzx
  have q53₄ : c₄.nreg 180053 = C.s + j := by rw [F₄.1 _ by_decide, q53₃]
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, b59, t59⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180035) (r₂ := 180053) (r₃ := 180053) (d := 180059) ztbh
    ztbh ztbh c₄ e₄.wb_right S₄.2.2.2 q53₄ q53₄ lk lj lj
  have S₅ := S₄.keep (sc_of_bt by_omega F₅)
  zvnhd at t56 t57 t58 t59
  rw [vtxQ hC hsn by_omega lj, vtxQ hC hsn by_omega lk] at t56 t59
  rw [vtxQ hC hsn by_omega lk, show C.s + j + 1 = C.s + ztl by ring,
    vtxQ hC hsn by_omega by_omega] at t57 t58
  -- the bits in `c₅`
  have r56 : c₅.nreg 180056 = c₂.nreg 180056 := by
    rw [F₅.1 _ by_decide, F₄.1 _ by_decide, F₃.1 _ by_decide]
  have r57 : c₅.nreg 180057 = c₃.nreg 180057 := by rw [F₅.1 _ by_decide, F₄.1 _ by_decide]
  have r58 : c₅.nreg 180058 = c₄.nreg 180058 := F₅.1 _ by_decide
  rw [← r56] at b56 t56
  rw [← r57] at b57 t57
  rw [← r58] at b58 t58
  zufsv
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, F₆⟩ := andS_exec (P := P) W2 c₅ e₅.wb_right (d := 180056)
    (x := 180056) (y := 180057) by_decide S₅.2.2.1 b56 b57
  have A₆ := and_bit b56 b57
  rw [← v₆, t56, t57] at A₆
  have S₆ := S₅.keep (sc_of_one by_omega F₆)
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, F₇⟩ := andS_exec (P := P) W2 c₆ e₆.wb_right (d := 180058)
    (x := 180058) (y := 180059) by_decide S₆.2.2.1 ztlgz
    ztlgz
  have A₇ := and_bit (show c₆.nreg 180058 ≤ 1 by zuoho; exact b58)
    (show c₆.nreg 180059 ≤ 1 by zuoho; exact b59)
  rw [← v₇, fr1 F₆ by_decide, fr1 F₆ by_decide, t58, t59] at A₇
  have S₇ := S₆.keep zttzz
  have x56 : c₇.nreg 180056 = c₆.nreg 180056 := fr1 F₇ by_decide
  obtain ⟨c₈, k₈, e₈, hk₈, v₈, F₈⟩ := orS_exec (P := P) W2 c₇ e₇.wb_right (d := 180076)
    (x := 180056) (y := 180058) (t := 180079) by_decide by_decide by_decide S₇.2.2.1
    by_omega A₇.1
  have A₈ := or_bit (show c₇.nreg 180056 ≤ 1 by rw [x56]; exact A₆.1) A₇.1
  rw [← v₈, x56, A₆.2, A₇.2] at A₈
  have S₈ := S₇.keep (sc_of_two by_omega by_omega F₈)
  have q53₈ : c₈.nreg 180053 = C.s + j := by
    rw [fr2 F₈ by_decide by_decide, fr1 F₇ by_decide, fr1 F₆ by_decide,
      F₅.1 _ by_decide, q53₄]
  -- the side test
  obtain ⟨c₉, k₉, e₉, hk₉, F₉, b77, t77⟩ := sideS_exec (P := P) (d := d) hG by_omega hC hsn hj
    hk c₈ e₈.wb_right S₈.2.2.2 q53₈
  have S₉ := S₈.keep zttzy
  have x76 : c₉.nreg 180076 = c₈.nreg 180076 := F₉.1 _ by_decide
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, v₁₀, F₁₀⟩ := andS_exec (P := P) W2 c₉ e₉.wb_right (d := 180076)
    (x := 180076) (y := 180077) by_decide S₉.2.2.1 by_omega b77
  have A₁₀ := and_bit (show c₉.nreg 180076 ≤ 1 by rw [x76]; exact A₈.1) b77
  rw [← v₁₀, x76, A₈.2, t77] at A₁₀
  have S₁₀ := S₉.keep (sc_of_one by_omega F₁₀)
  have hcand : c₁₀.nreg 180076 = 1 ↔ Cand C k ztbgm j := by
    rw [A₁₀.2]; unfold Cand Strad
    grind
  -- the scan registers are unchanged so far
  have G₁₀ := (((((((((sc_of_bt by_omega F₂).trans zttzw).trans
    zttzx).trans (sc_of_bt by_omega F₅)).trans (sc_of_one by_omega F₆)).trans
    zttzz).trans (sc_of_two by_omega by_omega F₈)).trans
    zttzy).trans (sc_of_one by_omega F₁₀))
  have keepS : ∀ r, r = 180050 ∨ r = 180051 ∨ r = 180052 ∨ r = 180053 → c₁₀.nreg r = c₁.nreg r := by
    rintro r (rfl | rfl | rfl | rfl) <;>
    rw [fr1 F₁₀ by_decide, F₉.1 _ by_decide, fr2 F₈ by_decide by_decide,
      fr1 F₇ by_decide, fr1 F₆ by_decide, F₅.1 _ by_decide, F₄.1 _ by_decide,
      F₃.1 _ by_decide, F₂.1 _ by_decide]
  have p50 : c₁₀.nreg 180050 = j := by rw [keepS _ ztp, R₁.1 _ by_decide, h50]
  have p51 : c₁₀.nreg 180051 = c.nreg 180051 := by
    zugvz
  have p52 : c₁₀.nreg 180052 = c.nreg 180052 := by
    zugvz
  have p53 : c₁₀.nreg 180053 = C.s + j := by
    grind
  zumfw
  -- the branch
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, F₁₁, p50', hE'⟩ : ∃ c₁₁ k₁₁, Exec P W
      ztlzx c₁₀ c₁₁ k₁₁ ∧ k₁₁ ≤ 262 ∧ FrameB Bsc c₁₀ c₁₁ ∧
      c₁₁.nreg 180050 = j ∧
      Enc (c₁₁.nreg 180051) (c₁₁.nreg 180052) ztzgy := by
    by_cases hc : Cand C k ztbgm j
    · obtain ⟨c', k', e', hk', F', q50', hE''⟩ := candS_exec hG by_omega hC
        hsn hj hk c₁₀ w₁₀ S₁₀ p50 p53 by_grind hsc
      refine ⟨c', _, .ifLtN_false (by rw [hcand.2 hc, S₁₀.2.2.1]; omega) e', by_omega, F', q50',
        ?_⟩
      rw [scan_succ_cand hc]; omega
    · have h0' : c₁₀.nreg 180076 = 0 := by_grind
      refine ⟨c₁₀, _, .ifLtN_true (by rw [h0', S₁₀.2.2.1]; omega) (.skip w₁₀), by_omega,
        FrameB.refl _ _, p50, ?_⟩
      rw [scan_succ_not hc, p51, p52]; exact hE
  have S₁₁ := S₁₀.keep F₁₁
  have e₁₂ := Exec.addN (P := P) e₁₁.wb_right 180050 180050 180011 (by
    zuohp; grind)
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
    (.seq e₁₀ (.seq e₁₁ e₁₂)))))))))), by_omega, ?_, ?_, ?_⟩
  · refine ((G₁.trans G₁₀).trans F₁₁).trans ⟨fun r hr => ?_, by_grind, rfl, rfl, rfl⟩
    have : r ≠ 180050 := by
      zudwe
    zuotw
  · zuock; zuohp
  · zulro
    rw [upd_other _ _ _ by_decide, upd_other _ _ _ by_decide]
    omega

/-- **The scan**: registers `180051, 180052` encode `scan C k σ m` (at most `1602 m + 5`
steps). -/
theorem scanS_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C zttw c) :
    ∃ c' k', Exec P W ztwdi c c' k' ∧ k' ≤ 1602 * C.m + 5 ∧ FrameB Bsc c c' ∧
      Enc ztqgy ztqgz ztzgx := by
  obtain ⟨c₁, k₁, e₁, hk₁, q50, q51, q52, R₁⟩ : ∃ c₁ k₁, Exec P W
      zthsl c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180050 = 0 ∧ c₁.nreg 180051 = 0 ∧ c₁.nreg 180052 = 0 ∧ FrameB Bsc c c₁ := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp,
        ⟨fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩⟩
      unfold Bsc at hr; zvnam at hr
      zudw
  let I : Config → Prop := fun e => WordsBounded W e ∧ FrameB Bsc c e ∧ SI C zttw e ∧
    e.nreg 180050 ≤ C.m ∧ Enc (e.nreg 180051) (e.nreg 180052) (scan C k ztbgm (e.nreg 180050))
  have hI : ztkzz := ⟨e₁.wb_right, R₁, hS.keep R₁, by_omega, by rw [q50, q51]; rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, F₂, S₂, l₂, E₂⟩, hex, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 180050) (b := 180001) (body := scanBody d) I
      (fun e => C.m - e.nreg 180050) 1600 ztchu
      (by
        intro e ⟨we, Fe, Se, le, Ee⟩ hlt
        rw [Se.2.1] at hlt
        obtain ⟨e', k', ex, hk', F', q50', E'⟩ := scanBody_exec (P := P) (d := d) hG hW hC hsn
          hlt hk e we Se rfl Ee (fun b hb => by
            have := (scan_some hb).1; omega)
        refine ⟨e', k', ex, ⟨ex.wb_right, Fe.trans F', Se.keep F', by_omega, by_simp_all⟩,
          hk', by_omega⟩)
      hI
  rw [S₂.2.1] at hex
  have hm : c₂.nreg 180050 = C.m := by_omega
  zvmwi at E₂
  refine ⟨c₂, _, .seq e₁ e₂, ?_, F₂, E₂⟩
  omega
def modS : Stmt := .ifLtN 180083 180012 (.instr (.copyN 180082 180083))
  (.instr (.subN 180082 180083 180012))
theorem mod_small {x M : ℕ} (_hM : 0 < M) (hx : x < 2 * M) : x % M = if x < M then x else x - M := by
  zus
  · zubql
  · zul
variable {P : Polygon} {W : ℕ} {C : Chain} {k : ℕ} {σ : ℝ}
theorem modS_exec (c : Config) (hw : WordsBounded W c) {M : ℕ}
    (hM : 0 < M) (h12 : c.nreg 180012 = M) (hx : c.nreg 180083 < 2 * M) :
    ∃ c' k', Exec P W modS c c' k' ∧ k' ≤ 3 ∧ c'.nreg 180082 = c.nreg 180083 % M ∧
      FrameB ztlop c c' := by
  have fr : ∀ v, FrameB ztlop c
      { c with nreg := upd c.nreg 180082 v } := fun v =>
    ⟨by_simp_all, by_simp_all, rfl,
      rfl, rfl⟩
  rw [mod_small hM hx]
  by_cases h : c.nreg 180083 < M
  · exact ⟨_, _, .ifLtN_true by_omega (Exec.copyN hw 180082 180083), by_omega,
      by zumxk, fr _⟩
  · exact ⟨_, _, .ifLtN_false by_omega (Exec.subN hw 180082 180083 180012),
      by omega, by_simp_all, fr _⟩

/-- The forward tour position of the chain edge `best`. -/
def fwdS : Stmt := .seq ztiql modS

/-- The backward tour position. -/
def bwdS : Stmt := .seq (block [.subN 180083 180012 180011, .subN 180083 180083 180052,
  .addN 180083 180083 180012, .subN 180083 180083 180015]) modS

/-- The far walk edge. -/
def farS (d : ℕ) : Stmt :=
  .ifLtN 180051 180011 (.instr (.constN 180082 ztmln))
    (.seq ztiqk
      (.seq (testS 2 (.v 180055) (.v 180080) ztdbr 180081)
        (.seq (.ifLtN 180081 180011 bwdS fwdS) (.instr (.addN 180082 180082 180027)))))

/-- The registers the far edge reads (beyond `SI`). -/
def FI (C : Chain) (c : Config) : Prop :=
  c.nreg 180012 = 2 * C.m ∧ c.nreg 180015 = tS C ∧ c.nreg 180027 = 6
theorem FI.keep {c c' : Config} (h : FI C c) (F : FrameB Bsc c c') : FI C c' :=
  ⟨by rw [F.1 _ by_decide, h.1], by rw [F.1 _ by_decide, h.2.1], by rw [F.1 _ by_decide, h.2.2]⟩
theorem fwdS_exec (c : Config) (hw : WordsBounded W c)
    (hF : FI C c) {b : ℕ} (hb : c.nreg 180052 = b) (hbm : b < C.m) (hW : 4 * C.m ≤ W) :
    ∃ c' k', Exec P W fwdS c c' k' ∧ k' ≤ 5 ∧ c'.nreg 180082 = fwdIdx C.m ztbkt b ∧
      FrameB Bsc c c' := by
  zugpd
  zuec
  zubt
  obtain ⟨c₁, k₁, e₁, hk₁, q83, R₁⟩ : ∃ c₁ k₁, Exec P W
      ztiql c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180083 = b + 2 * C.m - tS C ∧ FrameB ztloq c c₁ := by
    exec_block
    · omega
    · zulox
      · simp_all
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, q82, R₂⟩ := modS_exec (P := P) c₁ e₁.wb_right (M := 2 * C.m)
    by_omega ztlha by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by zuohq; rfl,
    (sc_of_one by_omega R₁).trans ztuaa⟩
theorem bwdS_exec (c : Config) (hw : WordsBounded W c)
    (hF : FI C c) (h11 : c.nreg 180011 = 1) {b : ℕ} (hb : c.nreg 180052 = b) (hbm : b < C.m)
    (hW : 4 * C.m ≤ W) :
    ∃ c' k', Exec P W bwdS c c' k' ∧ k' ≤ 7 ∧ c'.nreg 180082 = bwdIdx C.m ztbkt b ∧
      FrameB Bsc c c' := by
  zugpd
  zuec
  zubt
  obtain ⟨c₁, k₁, e₁, hk₁, q83, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 180083 180012 180011, .subN 180083 180083 180052,
        .addN 180083 180083 180012, .subN 180083 180083 180015]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 180083 = 2 * C.m - 1 - b + 2 * C.m - tS C ∧
      FrameB ztloq c c₁ := by
    exec_block
    · config_simp; omega
    · zulox
      · zubs
        omega
      · zubzq
        zudw
  obtain ⟨c₂, k₂, e₂, hk₂, q82, R₂⟩ := modS_exec (P := P) c₁ e₁.wb_right (M := 2 * C.m)
    by_omega ztlha by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by zuohq; rfl,
    (sc_of_one by_omega R₁).trans ztuaa⟩
theorem farEdge_none (h : scan C k σ C.m = none) :
    farEdge C k σ = if σ = 1 then 3 else 1 := by
  zufdh
theorem farEdge_some {b : ℕ} (h : scan C k σ C.m = some b) :
    farEdge C k σ = (if 0 < det ztgdi ztxmt ztib then
      fwdIdx C.m ztbkt b else bwdIdx C.m ztbkt b) + 6 := by
  zufdh
set_option maxHeartbeats 1000000 in
theorem farS_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hd : d ≤ 1)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (hS : SI C zttw c) (hF : FI C c)
    (hE : Enc ztqhp ztqhq ztzgx) :
    ∃ c' k', Exec P W ztvqk c c' k' ∧ k' ≤ 270 ∧ FrameB Bsc c c' ∧
      c'.nreg 180082 = farEdge C k ztbgm := by
  zucdv
  rcases hsc : scan C k ztbgm C.m with _ | b
  · zukwc
    zudbu
    have e := Exec.constN (P := P) hw 180082 ztmln by_grind
    refine ⟨_, _, .ifLtN_true by_omega e, by_omega,
      ⟨fun r hr => ?_, by_simp_all, rfl, rfl, rfl⟩, ?_⟩
    · have : r ≠ 180082 := by
        zudwe
      simp_all
    · rw [farEdge_none hsc]
      zubzl
      zuckz
      · subst h0; rw [sig_zero]; simp
      · rw [ite_eq_right h0, sig_one h0, ite_eq_right by_norm_num]
  · zukwc
    zudbu
    zuicp
    have hbm := (scan_some hsc).1
    obtain ⟨c₁, k₁, e₁, hk₁, q55, q80, R₁⟩ : ∃ c₁ k₁, Exec P W
        ztiqk c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 180055 = C.s + b ∧ c₁.nreg 180080 = C.s + b + 1 ∧
        FrameB (fun r => decide (r = 180055 ∨ r = 180080)) c c₁ := by
      exec_block
      · omega
      · config_simp; omega
      · refine ztxmh
        · simp_all
        · simp_all
        simp_all
    zuiuq
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, b81, t81⟩ := testV_exec hG by_omega (op := 2)
      by_omega (r₃ := 180035) (d := 180081) by_omega
      by_omega by_omega c₁ e₁.wb_right q55 q80
      (by rw [G₁.1 _ by_decide, h35]) by_omega by_omega by_omega
    zvnhd at t81
    rw [vtxQ hC hsn by_omega by_omega, show C.s + b + 1 = C.s + ztds by ring,
      vtxQ hC hsn by_omega by_omega, vtxQ hC hsn by_omega by_omega] at t81
    have G₂ := G₁.trans ztker
    have F₂' := hF.keep G₂
    have k11 : ztpnd := by rw [G₂.1 _ by_decide, h11]
    have k52 : ztura := by rw [F₂.1 _ by_decide, fr2 R₁ by_decide by_decide, hb]
    have hWm : 4 * C.m ≤ W := by_omega
    zue
    obtain ⟨c₃, k₃, e₃, hk₃, q82, G₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 180081 180011 bwdS fwdS) c₂ c₃ k₃ ∧
        k₃ ≤ 9 ∧ c₃.nreg 180082 = (if 0 < det ztgdi ztxmt ztib then
          fwdIdx C.m ztbkt b else bwdIdx C.m ztbkt b) ∧ FrameB Bsc c₂ c₃ := by
      by_cases hdt : 0 < det ztgdi ztxmt ztib
      · obtain ⟨c', k', e', hk', q', G'⟩ := fwdS_exec c₂ w₂ F₂' k52 hbm hWm
        exact ⟨c', _, .ifLtN_false by_simp_all e', by_omega,
          by simp_all, G'⟩
      · have h0' : c₂.nreg 180081 = 0 := by_grind
        obtain ⟨c', k', e', hk', q', G'⟩ := bwdS_exec c₂ w₂ F₂' k11 k52 hbm hWm
        exact ⟨c', _, .ifLtN_true by_omega e', by_omega,
          by simp_all, G'⟩
    have F₃' := F₂'.keep G₃
    have e₄ := Exec.addN (P := P) e₃.wb_right 180082 180082 180027 (by
      zukyj
      have h1 := (fwdIdx_spec hbm).1
      have h2 := (bwdIdx_spec hbm).1
      grind)
    refine ⟨_, _, .ifLtN_false by_omega ztwri,
      by omega, (G₂.trans G₃).trans ztgq, ?_⟩
    · have : r ≠ 180082 := by
        zudwe
      simp_all
    · rw [farEdge_some hsc]
      zubzl
      zukyj

/-! ## Writing the triple -/

/-- Store the triple of direction `d`. -/
def writeS (d : ℕ) : Stmt :=
  .seq (putS 180024 180035) (.seq (putS 180024 ztgkk)
    (.seq (putS 180024 ztgkl) (.instr (.addN 180019 180019 180011))))

/-- The write set of an emission. -/
def Bem (r : ℕ) : Bool := Bsc r || decide (r = 180024 ∨ r = 180019)
theorem writeS_exec {d : ℕ} (c : Config) (hw : WordsBounded W c) {A len : ℕ}
    (h24 : c.nreg 180024 = A) (h19 : c.nreg 180019 = len) (h11 : c.nreg 180011 = 1)
    (hA : A + 3 ≤ W) (hl : len + 1 ≤ W) :
    ∃ c' k', Exec P W ztwhx c c' k' ∧ k' = 7 ∧ c'.nreg 180024 = A + 3 ∧
      c'.nreg 180019 = len + 1 ∧
      c'.nmem = upd (upd (upd c.nmem A (c.nreg 180035)) ztbo
        (c.nreg ztgkk)) (A + 2)
        (c.nreg ztgkl) ∧
      (∀ r, r ≠ 180024 → r ≠ 180019 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hv1 : ztgkk ≠ 180024 := by_grind
  have hv2 : ztgkl ≠ 180024 := by_grind
  obtain ⟨c₁, k₁, e₁, hk₁, p₁, m₁, R₁, rr₁, rm₁, o₁⟩ := putS_exec (P := P) c hw (p := 180024)
    (v := 180035) by_decide h11 by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, p₂, m₂, R₂, rr₂, rm₂, o₂⟩ := putS_exec (P := P) c₁ e₁.wb_right
    (p := 180024) (v := if d = 0 then 180044 else 180082) by_decide
    by_simp_all by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, m₃, R₃, rr₃, rm₃, o₃⟩ := putS_exec (P := P) c₂ e₂.wb_right
    (p := 180024) (v := if d = 0 then 180082 else 180044) by_decide
    by_simp_all by_omega
  have e₄ := Exec.addN (P := P) e₃.wb_right 180019 180019 180011 (by
    simp_all)
  refine ⟨_, _, .seq e₁ ztcb, by_omega, ?_, ?_, ?_, fun r h1 h2 => ?_,
    by simp_all, by_simp_all,
    by simp_all⟩
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **Emit the chord of `v_k` in direction `d`.** -/
def emitS (d : ℕ) : Stmt := .seq ztwdi (.seq ztvqk ztwhx)
set_option maxHeartbeats 1000000 in
theorem emitS_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hd : d ≤ 1)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (hS : SI C zttw c) (hF : FI C c)
    {A len p : ℕ} (h24 : c.nreg 180024 = A) (h19 : c.nreg 180019 = len) (h44 : c.nreg 180044 = p)
    (hA : A + 3 ≤ W) (hl : len + 1 ≤ W) :
    ∃ c' k', Exec P W ztvpv c c' k' ∧ k' ≤ 1602 * C.m + 282 ∧ 7 ≤ k' ∧ c'.nreg 180024 = A + 3 ∧
      c'.nreg 180019 = len + 1 ∧
      c'.nmem = upd (upd (upd c.nmem A zttw) ztbo
        (if d = 0 then p else farEdge C k ztbgm)) (A + 2)
        (if d = 0 then farEdge C k ztbgm else p) ∧
      ztimr ∧ ztims ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, E₁⟩ := scanS_exec (P := P) (d := d) hG hW hC hsn hk c hw hS
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, q82⟩ := farS_exec (P := P) (d := d) hG hW hW4 hC hsn hd hk c₁
    e₁.wb_right (hS.keep F₁) (hF.keep F₁) E₁
  have G := F₁.trans F₂
  obtain ⟨c₃, k₃, e₃, hk₃, p24, p19, m₃, R₃, rr₃, rm₃, o₃⟩ := writeS_exec (P := P) (d := d) c₂
    e₂.wb_right (A := A) (len := len) (by rw [G.1 _ by_decide, h24])
    (by rw [G.1 _ by_decide, h19]) (by rw [G.1 _ by_decide, hS.2.2.1]) hA hl
  have k35 : c₂.nreg 180035 = C.s + k := by rw [G.1 _ by_decide, hS.2.2.2]
  have k44 : c₂.nreg 180044 = p := by rw [G.1 _ by_decide, h44]
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, by_omega, p24, p19, ?_, fun r hr => ?_,
    fun r hr => by rw [rr₃, G.2.1 r hr], by rw [rm₃, G.2.2.2.1], by rw [o₃, G.2.2.2.2]⟩
  · rw [m₃, G.2.2.1, k35]
    grind
  · unfold Bem at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hr
    rw [R₃ r hr.2.1 hr.2.2, G.1 r hr.1]
def logicE : Stmt :=
  .seq (andS 180043 180038 180039) (.seq (orS 180047 180038 180039 180048)
  (.seq (notS 180047 180047) (.seq (.instr (.addN 180043 180043 180047))
  (.seq (notS 180040 180040) (.seq (andS 180049 180043 180040) (.seq (notS 180047 180043)
  (.seq (notS 180048 180039) (.seq (andS 180041 180047 180048)
  (.seq (orS 180041 180049 180041 180043) (.seq (andS 180042 180047 180039)
    (orS 180042 180049 180042 180043)))))))))))

/-- The write set of the corner decision: the kernel, `180038 … 180043` and `180047 … 180049`. -/
def Bco (r : ℕ) : Bool :=
  Bk r || decide ((180038 ≤ r ∧ r < 180044) ∨ (180047 ≤ r ∧ r < 180050))
variable {d : ℕ} {P : Polygon} {W : ℕ}
theorem co_one (hd : ztgya ∨ ztgyb) {c c' : Config}
    (F : FrameB ztbaz c c') : FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    zultm
theorem co_two {d t : ℕ} (hd : ztgya ∨ ztgyb) (ht : (180038 ≤ t ∧ t < 180044) ∨ (180047 ≤ t ∧ t < 180050))
    {c c' : Config} (F : FrameB ztbqe c c') : FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    zultm
theorem co_bt (hd : ztgya ∨ ztgyb) {c c' : Config} (F : FrameB ztjhb c c') :
    FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    unfold Bco at hr; unfold Bt
    grind
set_option maxHeartbeats 1000000 in
theorem logicE_exec (hW : 8 ≤ W) (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (b38 : c.nreg 180038 ≤ 1) (b39 : c.nreg 180039 ≤ 1)
    (b40 : c.nreg 180040 ≤ 1) :
    ∃ c' k, Exec P W logicE c c' k ∧ k ≤ 30 ∧ FrameB Bco c c' ∧
      c'.nreg 180041 ≤ 1 ∧ c'.nreg 180042 ≤ 1 ∧
      (c'.nreg 180041 = 1 ↔ ztyxl ∨
        (¬ ztcmq ∧ c.nreg 180039 = 0)) ∧
      (c'.nreg 180042 = 1 ↔ ztyxl ∨
        (¬ ztcmq ∧ c.nreg 180039 = 1)) := by
  zufsv
  obtain ⟨c1, k1, e1, hk1, v1, F1⟩ := andS_exec (P := P) W2 c hw (d := 180043) (x := 180038)
    (y := 180039) by_decide h11 b38 b39
  zuehr
  have a38 : c1.nreg 180038 = c.nreg 180038 := fr1 F1 by_decide
  have a39 : c1.nreg 180039 = c.nreg 180039 := fr1 F1 by_decide
  obtain ⟨c2, k2, e2, hk2, v2, F2⟩ := orS_exec (P := P) W2 c1 e1.wb_right (d := 180047)
    (x := 180038) (y := 180039) (t := 180048) by_decide by_decide by_decide o1
    by_omega by_omega
  have o2 : ztuph := by rw [fr2 F2 by_decide by_decide, o1]
  obtain ⟨c3, k3, e3, hk3, v3, F3⟩ := notS_exec (P := P) c2 e2.wb_right (d := 180047)
    (x := 180047) by_decide o2
  have x43 : c3.nreg 180043 = c.nreg 180038 + c.nreg 180039 - 1 := by
    rw [fr1 F3 by_decide, fr2 F2 by_decide by_decide, v1]
  have x47 : c3.nreg 180047 = 1 - ((c.nreg 180038 + c.nreg 180039) -
      (c.nreg 180038 + c.nreg 180039 - 1)) := by_grind
  have e4 := Exec.addN (P := P) e3.wb_right 180043 180043 180047 by_omega
  set c4 : Config := { c3 with nreg := upd c3.nreg 180043 _ }
    with hc4
  have F4 : FrameB (fun r => decide (r = 180043)) c3 c4 :=
    ⟨fun r hr => by zvnan at hr; simp [hc4, hr], by_grind,
      rfl, rfl, rfl⟩
  have EQ : c4.nreg 180043 ≤ 1 ∧ (c4.nreg 180043 = 1 ↔ ztcmq) := by
    have : c4.nreg 180043 = c3.nreg 180043 + c3.nreg 180047 := by_rfl
    grind
  have o4 : ztupo := by rw [fr1 F4 by_decide, fr1 F3 by_decide, o2]
  have y40 : c4.nreg 180040 = c.nreg 180040 := by
    rw [fr1 F4 by_decide, fr1 F3 by_decide, fr2 F2 by_decide by_decide, fr1 F1 by_decide]
  obtain ⟨c5, k5, e5, hk5, v5, F5⟩ := notS_exec (P := P) c4 (by simpa [hc4] using e4.wb_right)
    (d := 180040) (x := 180040) by_decide o4
  have N5 := not_bit (show c4.nreg 180040 ≤ 1 by rw [y40]; exact b40)
  rw [← v5, y40] at N5
  zuehs
  have z43 : c5.nreg 180043 = c4.nreg 180043 := fr1 F5 by_decide
  obtain ⟨c6, k6, e6, hk6, v6, F6⟩ := andS_exec (P := P) W2 c5 e5.wb_right (d := 180049)
    (x := 180043) (y := 180040) by_decide o5 by_omega N5.1
  have A6 := and_bit (show c5.nreg 180043 ≤ 1 by rw [z43]; exact EQ.1) N5.1
  rw [← v6, z43, EQ.2, N5.2] at A6
  have o6 : ztupr := by rw [fr1 F6 by_decide, o5]
  have z43' : c6.nreg 180043 = c4.nreg 180043 := by rw [fr1 F6 by_decide, z43]
  obtain ⟨c7, k7, e7, hk7, v7, F7⟩ := notS_exec (P := P) c6 e6.wb_right (d := 180047)
    (x := 180043) by_decide o6
  have N7 := not_bit (show c6.nreg 180043 ≤ 1 by rw [z43']; exact EQ.1)
  rw [← v7, z43', bit_of EQ.1 EQ.2] at N7
  zueht
  have y39 : c7.nreg 180039 = c.nreg 180039 := by
    rw [fr1 F7 by_decide, fr1 F6 by_decide, fr1 F5 by_decide, fr1 F4 by_decide,
      fr1 F3 by_decide, fr2 F2 by_decide by_decide, a39]
  obtain ⟨c8, k8, e8, hk8, v8, F8⟩ := notS_exec (P := P) c7 e7.wb_right (d := 180048)
    (x := 180039) by_decide o7
  have N8 := not_bit (show c7.nreg 180039 ≤ 1 by rw [y39]; exact b39)
  rw [← v8, y39] at N8
  zuehu
  have z47 : c8.nreg 180047 = c7.nreg 180047 := fr1 F8 by_decide
  obtain ⟨c9, k9, e9, hk9, v9, F9⟩ := andS_exec (P := P) W2 c8 e8.wb_right (d := 180041)
    (x := 180047) (y := 180048) by_decide o8 by_omega N8.1
  have A9 := and_bit (show c8.nreg 180047 ≤ 1 by rw [z47]; exact N7.1) N8.1
  rw [← v9, z47, N7.2, N8.2] at A9
  zuehv
  have z49 : c9.nreg 180049 = c6.nreg 180049 := by
    rw [fr1 F9 by_decide, fr1 F8 by_decide, fr1 F7 by_decide]
  obtain ⟨c10, k10, e10, hk10, v10, F10⟩ := orS_exec (P := P) W2 c9 e9.wb_right (d := 180041)
    (x := 180049) (y := 180041) (t := 180043) by_decide by_decide by_decide o9
    by_omega A9.1
  have O10 := or_bit (show c9.nreg 180049 ≤ 1 by rw [z49]; exact A6.1) A9.1
  rw [← v10, z49, A6.2, A9.2] at O10
  have o10 : ztupd := by rw [fr2 F10 by_decide by_decide, o9]
  have z47' : c10.nreg 180047 = c7.nreg 180047 := by
    rw [fr2 F10 by_decide by_decide, fr1 F9 by_decide, z47]
  have y39' : c10.nreg 180039 = c.nreg 180039 := by
    rw [fr2 F10 by_decide by_decide, fr1 F9 by_decide, fr1 F8 by_decide, y39]
  obtain ⟨c11, k11, e11, hk11, v11, F11⟩ := andS_exec (P := P) W2 c10 e10.wb_right (d := 180042)
    (x := 180047) (y := 180039) by_decide o10 by_omega
    by_omega
  have A11 := and_bit (show c10.nreg 180047 ≤ 1 by rw [z47']; exact N7.1)
    (show c10.nreg 180039 ≤ 1 by rw [y39']; exact b39)
  rw [← v11, z47', y39', N7.2] at A11
  have o11 : ztupe := by rw [fr1 F11 by_decide, o10]
  have z49' : c11.nreg 180049 = c6.nreg 180049 := by
    rw [fr1 F11 by_decide, fr2 F10 by_decide by_decide, z49]
  obtain ⟨c12, k12, e12, hk12, v12, F12⟩ := orS_exec (P := P) W2 c11 e11.wb_right (d := 180042)
    (x := 180049) (y := 180042) (t := 180043) by_decide by_decide by_decide o11
    by_omega A11.1
  have O12 := or_bit (show c11.nreg 180049 ≤ 1 by rw [z49']; exact A6.1) A11.1
  rw [← v12, z49', A6.2, A11.2] at O12
  have g41 : c12.nreg 180041 = c10.nreg 180041 := by
    rw [fr2 F12 by_decide by_decide, fr1 F11 by_decide]
  have ex : Exec P W logicE c c12 _ :=
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9 (.seq e10
      (.seq e11 e12))))))))))
  refine ⟨c12, _, ex, by_omega, ?_, by_omega, O12.1, by_grind,
    by grind⟩
  have G1 := co_one by_omega F1
  have G2 := co_two by_omega by_omega F2
  have G3 := co_one by_omega F3
  have G4 := co_one by_omega F4
  have G5 := co_one by_omega F5
  have G6 := co_one by_omega F6
  have G7 := co_one by_omega F7
  have G8 := co_one by_omega F8
  have G9 := co_one by_omega F9
  have G10 := co_two by_omega by_omega F10
  have G11 := co_one by_omega F11
  have G12 := co_two by_omega by_omega F12
  exact ((((((((((G1.trans G2).trans G3).trans G4).trans G5).trans G6).trans G7).trans G8).trans
    G9).trans G10).trans G11).trans G12

/-! ## The corner decision -/

/-- The three tests and the combination. -/
def generalS : Stmt :=
  .seq (testS 1 ztdbr ztuvt ztdbr 180038)
    (.seq (testS 1 ztdbr ztuvu ztdbr 180039)
      (.seq (testS 2 ztuvt ztdbr ztuvu 180040) logicE))

/-- The corner decision: east only at position `0`, west only at position `2m`. -/
def cornerS : Stmt :=
  .ifLtN 180028 180030
    (.ifLtN 180030 180012 generalS ztkqz)
    ztkra
theorem emit_general {C : Chain} (hDH : DistinctHeights C.P) {i d : ℕ} (_hi0 : 0 < i)
    (hi : i < 2 * C.m) {t1 t2 t3 : Prop} (h1 : t1 ↔ (vPt C i).2 < (prevPt C i).2)
    (h2 : t2 ↔ (vPt C i).2 < (nextPt C i).2)
    (h3 : t3 ↔ 0 < det zthjh ztfve zthiu) :
    (Emit C i d ↔ (ztubx ∧ ¬ t3) ∨ (¬ ztubx ∧ (if d = 0 then ¬ t2 else t2))) := by
  have hne := nextPt_ne hDH hi.le
  unfold Emit emitR
  simp only [h1, h2, h3]
  by_cases hp : ((vPt C i).2 < (prevPt C i).2 ↔ (vPt C i).2 < (nextPt C i).2)
  · simp_all
  · zuhmq
    simp only [hp, false_and, false_or, not_false_eq_true, true_and]
    zuclb
    · subst hd; rw [sig_zero, ite_eq_left rfl]
      grind
    · rw [sig_one hd, ite_eq_right hd]
      grind
set_option maxHeartbeats 1000000 in
/-- **The corner decision** at tour position `i ≤ 2m`. -/
theorem cornerS_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {i : ℕ} (hi : i ≤ 2 * C.m) (c : Config)
    (hw : WordsBounded W c) (h11 : c.nreg 180011 = 1) (h12 : c.nreg 180012 = 2 * C.m)
    (h28 : c.nreg 180028 = 0) (h30 : c.nreg 180030 = i)
    (h35 : c.nreg 180035 = C.s + C.sideIdx C.sideBeta i)
    (h36 : 0 < i → c.nreg 180036 = C.s + C.sideIdx C.sideBeta ztei)
    (h37 : i < 2 * C.m → c.nreg 180037 = C.s + C.sideIdx C.sideBeta ztg) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 800 ∧ FrameB Bco c c' ∧ c'.nreg 180041 ≤ 1 ∧
      c'.nreg 180042 ≤ 1 ∧ (c'.nreg 180041 = 1 ↔ Emit C i 0) ∧
      (c'.nreg 180042 = 1 ↔ Emit C i 1) := by
  zudhf
  zumdt
  have frc : ∀ (v1 v2 : ℕ), FrameB Bco c
      { c with nreg := upd (upd c.nreg 180041 v1) 180042 v2 } := fun v1 v2 =>
    ⟨fun r hr => by
      unfold Bco at hr; zvnam at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other], by_simp_all, rfl, rfl, rfl⟩
  zuclc
  · zufpy
    obtain ⟨c', k, e, hk, q41, q42, R⟩ : ∃ c' k, Exec P W
        ztkra c c' k ∧ k = 2 ∧ c'.nreg 180041 = 1 ∧
        c'.nreg 180042 = 0 ∧ FrameB Bco c c' := by
      exec_block
      · omega
      · omega
      simp_all
    refine ⟨c', _, .ifLtN_false by_omega e, by_omega, R, by_omega, by_omega,
      ?_, ?_⟩
    · zuotx; unfold Emit; rw [emitR_zero hDH, sig_zero]; simp
    · zuoty; unfold Emit; rw [emitR_zero hDH, sig_one by_omega]; norm_num
  by_cases hil : i = 2 * C.m
  · subst hil
    obtain ⟨c', k, e, hk, q41, q42, R⟩ : ∃ c' k, Exec P W
        ztkqz c c' k ∧ k = 2 ∧ c'.nreg 180041 = 0 ∧
        c'.nreg 180042 = 1 ∧ FrameB Bco c c' := by
      exec_block
      · omega
      · omega
      simp_all
    refine ⟨c', _, .ifLtN_true by_omega
      ztejp, by_omega, R, by_omega, by_omega, ?_, ?_⟩
    · zuotx; unfold Emit; rw [emitR_two_m hDH (sig_cases 0), sig_zero]; norm_num
    · zuoty; unfold Emit; rw [emitR_two_m hDH (sig_cases 1), sig_one by_omega]; simp
  -- the general case
  have lk : C.s + C.sideIdx C.sideBeta i < P.n := by_grind
  have lp : C.s + C.sideIdx C.sideBeta ztei < P.n := by_grind
  have ln : C.s + C.sideIdx C.sideBeta ztg < P.n := by_grind
  have e36 := h36 by_omega
  have e37 := h37 by_omega
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, b38, t38⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180035) (r₂ := 180036) (r₃ := 180035) (d := 180038) ztbh
    ztbh ztbh c hw h35 e36 h35 lk lp lk
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b39, t39⟩ := testV_exec (P := P) hG by_omega (op := 1) by_omega
    (r₁ := 180035) (r₂ := 180037) (r₃ := 180035) (d := 180039) ztbh
    ztbh ztbh c₁ e₁.wb_right ztlgo
    (by rw [F₁.1 _ by_decide, e37]) ztlgo lk ln lk
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b40, t40⟩ := testV_exec (P := P) hG by_omega (op := 2) by_omega
    (r₁ := 180036) (r₂ := 180035) (r₃ := 180037) (d := 180040) ztbh
    ztbh ztbh c₂ e₂.wb_right
    (by rw [F₂.1 _ by_decide, F₁.1 _ by_decide, e36])
    (by rw [F₂.1 _ by_decide, F₁.1 _ by_decide, h35])
    (by rw [F₂.1 _ by_decide, F₁.1 _ by_decide, e37]) lp lk ln
  have r38 : c₃.nreg 180038 = c₁.nreg 180038 := by rw [F₃.1 _ by_decide, F₂.1 _ by_decide]
  have r39 : c₃.nreg 180039 = c₂.nreg 180039 := F₃.1 _ by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b41, b42, t41, t42⟩ := logicE_exec (P := P) by_omega c₃
    e₃.wb_right (by rw [F₃.1 _ by_decide, F₂.1 _ by_decide, F₁.1 _ by_decide, h11])
    by_omega by_omega b40
  rw [r38, r39] at t41 t42
  zvnhd at t38 t39 t40
  -- geometric points
  have ev : (Qof P).vtx _ = vPt C i :=
    vtxQ hC hsn by_grind lk
  have ep : (Qof P).vtx (C.s + C.sideIdx C.sideBeta ztei) = prevPt C i := by
    rw [vtxQ hC hsn by_grind lp]; unfold prevPt; simp_all
  have en : (Qof P).vtx ztxfx = nextPt C i := by
    rw [vtxQ hC hsn by_grind ln]; unfold nextPt; simp_all
  rw [ev, ep] at t38
  rw [ev, en] at t39
  rw [ev, ep, en] at t40
  have n39 := bit_of b39 t39
  have n40 := bit_of b40 t40
  have ex : Exec P W cornerS c c₄ _ :=
    .ifLtN_true by_grind (.ifLtN_true by_grind
      ztwri)
  refine ⟨c₄, _, ex, by_omega, (((co_bt by_omega F₁).trans (co_bt by_omega F₂)).trans
    (co_bt by_omega F₃)).trans F₄, b41, b42, ?_, ?_⟩
  · zujxm
    have e39 : c₂.nreg 180039 = 0 ↔ ¬ c₂.nreg 180039 = 1 := by_omega
    rw [t41, emit_general hDH by_omega by_omega t38 t39 t40, ite_eq_left rfl, e40, e39]
  · zujxm
    rw [t42, emit_general hDH by_omega by_omega t38 t39 t40, ite_eq_right by_omega, e40]
open Classical

/-! ## The list written so far -/

/-- The entries of the tour positions `< i`. -/
noncomputable def pre (C : Chain) (i : ℕ) : List zte :=
  (List.range i).flatMap fun i' =>
    (if Emit C i' 0 then [trip C i' 0] else []) ++ (if Emit C i' 1 then [trip C i' 1] else [])
variable (C : Chain) (i : ℕ) {P : Polygon} {W : ℕ}
theorem pre_succ :
    pre C ztg = pre C i ++ (zthht ++
      zthhu) := by
  classical
  unfold pre; zunno; simp
theorem pre_length_le : (pre C i).length ≤ 2 * i := by
  induction i with
  | zero => zuotz
  | succ i ih =>
    rw [pre_succ, List.length_append, List.length_append]
    have h1 : ztfxd := by_grind
    have h2 : (if Emit C i 1 then [trip C i 1] else []).length ≤ 1 := by_grind
    omega
theorem pre_full : pre C ztyw = bruteList C := by
  classical
  unfold pre bruteList entries
  rw [List.filter_flatMap, List.map_flatMap]
  zucr
  funext i
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  zujpm

/-- Appending a triple to a chord list in memory. -/
theorem chordList_snoc {m m' : ℕ → ℕ} {L : ℕ} {l : List zte} (h : ChordListAt m L l)
    (x : ℕ × ℕ × ℕ)
    (hm : m' = upd (upd (upd m (L + 3 * l.length) x.1) (L + 3 * l.length + 1) x.2.1)
      (L + 3 * l.length + 2) x.2.2) : ChordListAt m' L (l ++ [x]) := by
  zug
  zucjh
  zucjq
  zucyp
  · have e : (l ++ [x]).getD i ztt = l.getD i ztt := by
      simp_all
    zui
    zufjc
    refine ztcg <;>
      simp (disch := omega) only [Machine.upd_other] <;> assumption
  simp

/-- The value of `trip`. -/
theorem trip_eq {C : Chain} {i d : ℕ} (hsn : C.s + C.m + 1 ≤ C.P.n) :
    trip C i d = (C.s + C.sideIdx C.sideBeta i,
      if d = 0 then i + 6 else farEdge C ztlx ztbgm,
      if d = 0 then farEdge C ztlx ztbgm else i + 6) := by
  zufuz
  unfold trip
  rw [edgeIdx_eq by_omega]
  zuclb
  · subst hd; rfl
  · simp [hd, sig_one hd]

/-! ## Emitting in one direction -/

/-- Emit the chord of direction `d` if its bit (`180041 + d`) is set. -/
def emitB (d : ℕ) : Stmt := .ifLtN ztjen 180011 .skip ztvpv
set_option maxHeartbeats 1000000 in
theorem emitB_exec (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d i : ℕ} (hd : d ≤ 1)
    (_hi : i ≤ 2 * C.m) (c : Config) (hw : WordsBounded W c)
    (hS : SI C ztema c) (hF : FI C c)
    (hb : c.nreg ztjen ≤ 1) (he : c.nreg ztjen = 1 ↔ Emit C i d)
    (h44 : c.nreg 180044 = i + 6) {L : ℕ} {l : List zte} {M : ℕ → ℕ}
    (h24 : c.nreg 180024 = L + 3 * l.length) (h19 : c.nreg 180019 = l.length)
    (hl : ChordListAt c.nmem L l) (hM : ∀ x, x < L → c.nmem x = M x)
    (hroom : L + 3 * l.length + 3 ≤ W) :
    ∃ c' k, Exec P W (emitB d) c c' k ∧ k ≤ 1602 * C.m + 290 ∧
      3 * (l ++ ztcaf).length ≤ 3 * l.length + k ∧
      c'.nreg 180024 = L + 3 * (l ++ ztcaf).length ∧
      c'.nreg 180019 = (l ++ ztcaf).length ∧
      ChordListAt c'.nmem L (l ++ ztcaf) ∧
      (∀ x, x < L → c'.nmem x = M x) ∧
      ztimr ∧ ztims ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zufuz
  by_cases hE : Emit C i d
  · simp only [hE, ite_true]
    obtain ⟨c', k, e, hk', hk7, p24, p19, pm, R, rr, rm, o⟩ := emitS_exec hG hW hW4 hC
      hsn hd hk c hw hS hF h24 h19 h44
      by_omega by_omega
    refine ⟨c', _, .ifLtN_false (by rw [he.2 hE, hS.2.2.1]; omega) e, by_omega,
      by grind, ?_, ?_, ?_, ?_, R, rr, rm, o⟩
    · grind
    · simp_all
    · refine chordList_snoc hl _ ?_
      rw [pm, trip_eq (by rw [hC, show (Qof P).n = P.n from shear_n _ _]; omega)]
    · intro x hx; rw [pm]; simp (disch := omega) only [Machine.upd_other]; simp_all
  · simp only [hE, ite_false, List.append_nil]
    have h0 : c.nreg ztjen = 0 := by_grind
    exact ⟨c, _, .ifLtN_true (by rw [h0, hS.2.2.1]; omega) ztjd, by_omega, by_omega, h24, h19,
      hl, hM,
      by omega, by_simp_all, rfl, rfl⟩

/-! ## Indices and advancing -/

/-- `d := sideE m x`. -/
def sideES (d x : ℕ) : Stmt :=
  .ifLtN 180001 x (.instr (.subN d 180012 x)) ztign
theorem sideES_exec (c : Config) (hw : WordsBounded W c) {d x m : ℕ}
    (h1 : c.nreg 180001 = m) (h12 : c.nreg 180012 = 2 * m) :
    ∃ c' k, Exec P W (sideES d x) c c' k ∧ k ≤ 3 ∧ c'.nreg d = Chain.sideE m ztmhf ∧
      FrameB ztbaz c c' := by
  have fr : ∀ v, FrameB ztbaz c { c with nreg := upd c.nreg d v } := fun v =>
    ⟨by_simp_all, by_simp_all, rfl,
      rfl, rfl⟩
  have hse : Chain.sideE m ztmhf = if m < c.nreg x then 2 * m - c.nreg x else c.nreg x := by
    unfold Chain.sideE; grind
  rw [hse]
  by_cases h : m < c.nreg x
  · exact ⟨_, _, .ifLtN_true by_omega (Exec.subN hw d 180012 x), by_omega,
      by simp_all, fr _⟩
  · exact ⟨_, _, .ifLtN_false by_omega (Exec.copyN hw d x), by_omega,
      by zumxk, fr _⟩

/-- The indices of tour position `i`. -/
def idxS : Stmt :=
  .seq (sideES 180032 180031) (.seq (.instr (.addN 180043 180031 180011))
    (.seq (sideES 180034 180043) (block [.addN 180035 180000 180032, .addN 180036 180000 180033,
      .addN 180037 180000 180034, .addN 180044 180030 180027])))

/-- The write set of the loop body's own registers: `180030 … 180049`. -/
def Blp (r : ℕ) : Bool := decide (180030 ≤ r ∧ r < 180050)
theorem lp_one {d : ℕ} (hd : 180030 ≤ d ∧ d < 180050) {c c' : Config}
    (F : FrameB ztbaz c c') : FrameB Blp c c' :=
  frameB_mono F fun r hr => by unfold Blp at hr; grind
theorem idxS_exec {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hsn : C.s + C.m + 1 ≤ P.n) (hW : P.n + 2 * C.m + 8 ≤ W) {i kp : ℕ} (hi : i ≤ 2 * C.m)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (h11 : c.nreg 180011 = 1)
    (h12 : c.nreg 180012 = 2 * C.m) (h27 : c.nreg 180027 = 6) (h30 : c.nreg 180030 = i)
    (h31 : c.nreg 180031 = ztbwj % ztbb) (h33 : c.nreg 180033 = kp) (hkp : kp ≤ C.m) :
    ∃ c' k, Exec P W idxS c c' k ∧ k ≤ 12 ∧ FrameB Blp c c' ∧
      c'.nreg 180032 = C.sideIdx C.sideBeta i ∧ c'.nreg 180033 = kp ∧
      c'.nreg 180035 = C.s + C.sideIdx C.sideBeta i ∧ c'.nreg 180036 = C.s + kp ∧
      c'.nreg 180037 = C.s + C.sideIdx C.sideBeta ztg ∧ c'.nreg 180044 = i + 6 ∧
      c'.nreg 180030 = i ∧ c'.nreg 180031 = c.nreg 180031 := by
  zubco
  zumdt
  obtain ⟨c₁, k₁, e₁, hk₁, q32, F₁⟩ := sideES_exec (P := P) (d := 180032) (x := 180031) c hw h1 h12
  rw [h31] at q32
  have e32 : c₁.nreg 180032 = C.sideIdx C.sideBeta i := by_tauto
  have r : ∀ q, q ≠ 180032 → c₁.nreg q = c.nreg q := fun q hq => fr1 F₁ hq
  have e₂ := Exec.addN (P := P) e₁.wb_right 180043 180031 180011 (by
    rw [r _ by_decide, r _ by_decide, h31, h11]; have := Nat.mod_lt ztbwj hm; omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 180043 _ }
    with hc₂
  have q43 : c₂.nreg 180043 = ztbwj % ztbb + 1 := by
    simp_all
  have r₂ : ∀ q, q ≠ 180043 → c₂.nreg q = c₁.nreg q := by_simp_all
  obtain ⟨c₃, k₃, e₃, hk₃, q34, F₃⟩ := sideES_exec (P := P) (d := 180034) (x := 180043) c₂
    e₂.wb_right (m := C.m) by_simp_all
    by_simp_all
  rw [q43] at q34
  have e34 : c₃.nreg 180034 = C.sideIdx C.sideBeta ztg := by
    rw [q34, Chain.sideIdx_succ]; rfl
  have r₃ : ∀ q, q ≠ 180034 → q ≠ 180043 → q ≠ 180032 → c₃.nreg q = c.nreg q := fun q h1 h2 h3 =>
    by rw [fr1 F₃ h1, r₂ q h2, r q h3]
  have k32 : c₃.nreg 180032 = C.sideIdx C.sideBeta i := by
    rw [fr1 F₃ by_decide, r₂ _ by_decide, e32]
  obtain ⟨c₄, k₄, e₄, hk₄, q35, q36, q37, q44, R₄⟩ : ∃ c₄ k₄, Exec P W
      (block [.addN 180035 180000 180032, .addN 180036 180000 180033,
        .addN 180037 180000 180034, .addN 180044 180030 180027]) c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg 180035 = C.s + C.sideIdx C.sideBeta i ∧ c₄.nreg 180036 = C.s + kp ∧
      c₄.nreg 180037 = C.s + C.sideIdx C.sideBeta ztg ∧ c₄.nreg 180044 = i + 6 ∧
      FrameB (fun r => decide (r = 180035 ∨ r = 180036 ∨ r = 180037 ∨ r = 180044)) c₃ c₄ := by
    have w := e₃.wb_right
    have a0 : c₃.nreg 180000 = C.s := by_simp_all
    have a33 : c₃.nreg 180033 = kp := by_simp_all
    have a30 : c₃.nreg 180030 = i := by_simp_all
    have a27 : c₃.nreg 180027 = 6 := by_simp_all
    have hk1 := hl i
    have hk2 := hl ztg
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ⟨fun q hq => ?_, by_grind, rfl, rfl, rfl⟩⟩
      · zubs
        omega
      · zubs
        omega
      · zubs
        omega
      · zubs
        omega
      · simp only [decide_eq_false_iff_not, not_or] at hq
        zudw
  have F₂ : FrameB Blp c₁ c₂ := lp_one (d := 180043) by_omega
    ⟨by_simp_all, by_simp_all, rfl, rfl, rfl⟩
  have F₄ : FrameB Blp c₃ c₄ := frameB_mono R₄ fun q hq => by
    unfold Blp at hq; zvnan at hq ⊢; omega
  refine ⟨c₄, _, .seq e₁ ztcb, by_omega,
    (((lp_one by_omega F₁).trans F₂).trans (lp_one by_omega F₃)).trans F₄, ?_, ?_, q35, q36,
    q37, q44, ?_, ?_⟩
  · rw [R₄.1 _ by_decide, k32]
  · rw [R₄.1 _ by_decide, r₃ _ by_decide by_decide by_decide, h33]
  · rw [R₄.1 _ by_decide, r₃ _ by_decide by_decide by_decide, h30]
  · rw [R₄.1 _ by_decide, r₃ _ by_decide by_decide by_decide]

/-- Advance to the next tour position. -/
def advS : Stmt :=
  .seq ztgqw
    ztebq
theorem advS_exec {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hW : 2 * C.m + 2 ≤ W) {i : ℕ} (hi : i ≤ 2 * C.m) (h11 : c.nreg 180011 = 1)
    (h12 : c.nreg 180012 = 2 * C.m) (h30 : c.nreg 180030 = i)
    (h31 : c.nreg 180031 = ztbwj % ztbb) :
    ∃ c' k, Exec P W advS c c' k ∧ k ≤ 6 ∧ FrameB Blp c c' ∧
      c'.nreg 180033 = c.nreg 180032 ∧ c'.nreg 180030 = i + 1 ∧
      (i + 1 ≤ 2 * C.m → c'.nreg 180031 = ztzny % ztbb) := by
  zubco
  have hj := Nat.mod_lt ztbwj hm
  obtain ⟨c₁, k₁, e₁, hk₁, q33, q30, q31, R₁⟩ : ∃ c₁ k₁, Exec P W
      ztgqw c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 180033 = c.nreg 180032 ∧ c₁.nreg 180030 = i + 1 ∧
      c₁.nreg 180031 = ztbwj % ztbb + 1 ∧
      FrameB (fun r => decide (r = 180033 ∨ r = 180030 ∨ r = 180031)) c c₁ := by
    exec_block
    · config_simp; omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ⟨fun q hq => ?_, by_simp_all, rfl, rfl, rfl⟩⟩
      · simp
      · simp_all
      · simp_all
      simp_all
  have G₁ : FrameB Blp c c₁ := frameB_mono R₁ fun q hq => by
    unfold Blp at hq; grind
  have k12 : c₁.nreg 180012 = 2 * C.m := by rw [R₁.1 _ by_decide, h12]
  zud
  have hnext : ztzny % ztbb =
      if ztbwj % ztbb + 1 < 2 * C.m then ztbwj % ztbb + 1 else 0 := by
    have h1 : (1 : ℕ) % ztbb = 1 := Nat.mod_eq_of_lt by_omega
    rw [← Nat.add_assoc, Nat.add_mod _ 1, h1]
    zus
    · zubql
    · rw [show ztbwj % ztbb + 1 = 2 * C.m by omega, Nat.mod_self]
  by_cases hlt : ztbwj % ztbb + 1 < 2 * C.m
  · refine ⟨c₁, _, .seq e₁ ztxdi, by_omega, G₁,
      q33, q30, by_simp_all⟩
  · have e₂ := Exec.constN (P := P) w₁ 180031 0 by_omega
    refine ⟨_, _, .seq e₁ ztcry, by_omega,
      G₁.trans (lp_one (d := 180031) by_omega ⟨by_simp_all,
        by simp_all, rfl, rfl, rfl⟩), by_simp_all, by_simp_all,
      by simp_all⟩
def bodyS : Stmt := .seq idxS (.seq cornerS (.seq (emitB 0) (.seq (emitB 1) advS)))

/-- The loop. -/
def loopS : Stmt :=
  .seq zthsk
    (.seq ztebq
      (.whileLtN 180030 180025 bodyS))

/-- The write set of the body: the kernel, `180030 … 180089`, `180019`, `180024`. -/
def Bbd (r : ℕ) : Bool := Bk r || decide (180030 ≤ r ∧ r < 180090) || decide (r = 180019 ∨ r = 180024)
variable {P : Polygon} {c c' : Config} {W : ℕ}
theorem ctx_of_bbd {C : Chain} {γ A₀ : ℕ} {c c' : Config} (h : Ctx P C γ A₀ c)
    (hk : ∀ r, Bbd r = false → c'.nreg r = c.nreg r) : Ctx P C γ A₀ c' :=
  h.keep fun r hr => hk r (by
    unfold CtxReg at hr; unfold Bbd Bk
    grind)

/-- **The loop invariant** at the head of the loop. -/
def LI (P : Polygon) (C : Chain) (γ A₀ : ℕ) (M : ℕ → ℕ) (c₀ d : Config) : Prop :=
  Ctx P C γ A₀ d ∧ d.nreg 180030 ≤ 2 * C.m + 1 ∧
    (d.nreg 180030 ≤ 2 * C.m → d.nreg 180031 = (tS C + d.nreg 180030) % ztbb) ∧
    d.nreg 180033 ≤ C.m ∧
    (0 < d.nreg 180030 → d.nreg 180033 = C.sideIdx C.sideBeta (d.nreg 180030 - 1)) ∧
    d.nreg 180019 = (pre C ztmij).length ∧
    d.nreg 180024 = A₀ + 10 + 3 * (pre C ztmij).length ∧
    ChordListAt d.nmem ztsuw (pre C ztmij) ∧
    (∀ x, x < A₀ + 10 → d.nmem x = M x) ∧
    (∀ r, Bbd r = false → d.nreg r = c₀.nreg r) ∧ (∀ r, Bbd r = false → d.rreg r = c₀.rreg r) ∧
    d.rmem = c₀.rmem ∧ d.output = c₀.output
theorem bbd_of_lp (F : FrameB Blp c c') : ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => F.1 r (by
    unfold Bbd Bk at hr; unfold Blp
    grind)
theorem bbd_of_co (F : FrameB Bco c c') : ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => F.1 r (by
    zujps
    grind)
theorem bbd_of_em {c c' : Config} (h : ∀ r, Bem r = false → c'.nreg r = c.nreg r) :
    ∀ r, Bbd r = false → c'.nreg r = c.nreg r :=
  fun r hr => h r (by
    unfold Bbd at hr; unfold Bem Bsc
    grind)
set_option maxHeartbeats 4000000 in
/-- **One iteration of the loop.** -/
theorem bodyS_exec (hG : GoodEnv P) {C : Chain} (hW : P.n + 2 * C.m + 8 ≤ W)
    (hW4 : 4 * P.n ≤ W) (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n)
    {γ A₀ : ℕ} {M : ℕ → ℕ} (hroom : A₀ + 10 + 6 * ztyw + 3 ≤ W) {c₀ : Config}
    (c : Config) (hw : WordsBounded W c) (hI : LI P C γ A₀ M c₀ c) (hlt : c.nreg 180030 < 2 * C.m + 1) :
    ∃ c' k, Exec P W bodyS c c' k ∧ k ≤ 3300 * C.m + 1400 ∧
      3 * (pre C (c.nreg 180030 + 1)).length ≤ 3 * (pre C (c.nreg 180030)).length + k ∧
      LI P C γ A₀ M c₀ c' ∧
      c'.nreg 180030 = c.nreg 180030 + 1 := by
  obtain ⟨hX, -, h31, h33b, h33, h19, h24, hL, hM, hR, hRR, hRM, hO⟩ := hI
  obtain ⟨x0, x1, x2, x10, x11, x12, x13, x15, x16, x17, x18, x23, x25, x26, x27, x28⟩ := hX
  set i := c.nreg 180030 with hid
  zukcn
  zufuz
  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, q32, q33, q35, q36, q37, q44, q30, q31⟩ := idxS_exec (P := P) (C := C) c hw
    hsn hW hi x0 x1 x11 x12 x27 rfl (h31 hi) rfl h33b
  have K₁ := bbd_of_lp F₁
  have X₁ := ctx_of_bbd ⟨x0, x1, x2, x10, x11, x12, x13, x15, x16, x17, x18, x23,
    x25, x26, x27, x28⟩ K₁
  -- the corner
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b41, b42, t41, t42⟩ := cornerS_exec (P := P) hG by_omega hC hsn hi
    c₁ e₁.wb_right X₁.2.2.2.2.1 X₁.2.2.2.2.2.1 X₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 q30 q35
    ztczk (fun _ => q37)
  have K₂ := bbd_of_co F₂
  zujwj
  have c35 : c₂.nreg 180035 = C.s + C.sideIdx C.sideBeta i := by rw [F₂.1 _ by_decide, q35]
  have c44 : c₂.nreg 180044 = i + 6 := by rw [F₂.1 _ by_decide, q44]
  have c24 : c₂.nreg 180024 = A₀ + 10 + 3 * (pre C i).length := by
    rw [F₂.1 _ by_decide, F₁.1 _ by_decide, h24]
  have c19 : c₂.nreg 180019 = (pre C i).length := by rw [F₂.1 _ by_decide, F₁.1 _ by_decide, h19]
  have m₂ : ztckc := by rw [F₂.2.2.1, F₁.2.2.1]
  have hlen := pre_length_le C i
  -- east
  obtain ⟨c₃, k₃, e₃, hk₃, lb₃, p24, p19, pL, pM, R₃, RR₃, RM₃, O₃⟩ := emitB_exec (P := P) (d := 0) hG
    by_omega hW4 hC hsn by_omega hi c₂ e₂.wb_right
    ⟨X₂.1, X₂.2.1, X₂.2.2.2.2.1, c35⟩ ⟨X₂.2.2.2.2.2.1, X₂.2.2.2.2.2.2.2.1, X₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    b41 t41 c44 (L := A₀ + 10) (l := pre C i) (M := M) c24 c19 by_grind by_grind
    by_omega
  have K₃ := bbd_of_em R₃
  have X₃ := ctx_of_bbd X₂ K₃
  have d35 : c₃.nreg 180035 = C.s + C.sideIdx C.sideBeta i := by rw [R₃ _ by_decide, c35]
  have d44 : c₃.nreg 180044 = i + 6 := by rw [R₃ _ by_decide, c44]
  have d42 : c₃.nreg 180042 = c₂.nreg 180042 := R₃ _ by_decide
  set l₁ := pre C i ++ zthht with hl₁
  have hl₁len : l₁.length ≤ 2 * i + 1 := by
    rw [hl₁, List.length_append]; have : ztfxd := by
      zujpm
    omega
  -- west
  obtain ⟨c₄, k₄, e₄, hk₄, lb₄, r24, r19, rL, rM, R₄, RR₄, RM₄, O₄⟩ := emitB_exec (P := P) (d := 1) hG
    by_omega hW4 hC hsn by_omega hi c₃ e₃.wb_right
    ⟨X₃.1, X₃.2.1, X₃.2.2.2.2.1, d35⟩ ⟨X₃.2.2.2.2.2.1, X₃.2.2.2.2.2.2.2.1, X₃.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    by_grind by_grind d44 (l := l₁) (L := A₀ + 10) (M := M) p24 p19
    pL pM by_omega
  have K₄ := bbd_of_em R₄
  have X₄ := ctx_of_bbd X₃ K₄
  -- advance
  have e30 : c₄.nreg 180030 = i := by
    rw [R₄ _ by_decide, R₃ _ by_decide, F₂.1 _ by_decide, q30]
  have e31 : c₄.nreg 180031 = ztbwj % ztbb := by
    rw [R₄ _ by_decide, R₃ _ by_decide, F₂.1 _ by_decide, q31]
    grind
  have e32 : c₄.nreg 180032 = C.sideIdx C.sideBeta i := by
    rw [R₄ _ by_decide, R₃ _ by_decide, F₂.1 _ by_decide, q32]
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, s33, s30, s31⟩ := advS_exec (P := P) (C := C) c₄ e₄.wb_right
    by_omega hi X₄.2.2.2.2.1 X₄.2.2.2.2.2.1 e30 e31
  have K₅ := bbd_of_lp F₅
  have X₅ := ctx_of_bbd X₄ K₅
  have ex : Exec P W bodyS c c₅ _ :=
    .seq e₁ ztbq
  have hpre : pre C ztg = l₁ ++ zthhu := by
    rw [pre_succ, hl₁, List.append_assoc]
  have hlb : 3 * (pre C ztg).length ≤ 3 * (pre C i).length + ztbamf := by
    grind
  refine ⟨c₅, _, ex, by_omega, hlb, ⟨X₅, by_omega, fun h => by zuoua; grind,
    by omega, fun _ => by rw [s33, e32, s30]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    s30⟩
  · rw [F₅.1 _ by_decide, r19, s30, hpre]
  · rw [F₅.1 _ by_decide, r24, s30, hpre]
  · rw [F₅.2.2.1, s30, hpre]; exact rL
  · intro x hx; rw [F₅.2.2.1]; exact rM x hx
  · intro r hr; rw [K₅ r hr, K₄ r hr, K₃ r hr, K₂ r hr, K₁ r hr, hR r hr]
  · zuz
    have hb : Bsc r = false := by
      unfold Bbd at hr; unfold Bsc
      grind
    have hc : Bco r = false := by
      zujps
      zvnam at hr ⊢; exact ⟨hr.1.1, by_omega⟩
    have hl : Blp r = false := by
      unfold Bbd at hr; unfold Blp
      grind
    rw [F₅.2.1 r hl, RR₄ r hb, RR₃ r hb, F₂.2.1 r hc, F₁.2.1 r hl, hRR r hr]
  · rw [F₅.2.2.2.1, RM₄, RM₃, F₂.2.2.2.1, F₁.2.2.2.1, hRM]
  · rw [F₅.2.2.2.2, O₄, O₃, F₂.2.2.2.2, F₁.2.2.2.2, hO]

/-- A loop rule with a bounded body, a decreasing measure and a lower bound on the cost in
terms of a potential `g` (each iteration costs at least the growth of `g`). -/
theorem whileLtN_lb {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (μ : Config → ℕ) (B : ℕ) (g : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c ∧ g c' ≤ g c + k) :
    ∀ n c, μ c = n → I c → ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ k ≤ zthb * μ c + 2 ∧ g c' ≤ g c + k := by
  zugok
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    zumgk
    zudm
    · obtain ⟨c₁, k₁, e₁, hI₁, hk₁, hμ, hg⟩ := hbody c hc ht
      obtain ⟨c', k₂, e₂, hI', hex, hk₂, hg'⟩ := ih ztgne by_omega c₁ rfl hI₁
      refine ⟨c', _, .whileLtN_true ht e₁ e₂, hI', hex, ?_, by_omega⟩
      zuhvi

    · zulfw
set_option maxHeartbeats 1000000 in
/-- **The main loop**: from the set-up state, the list `bruteList C` is written at `A₀ + 10`. -/
theorem loopS_exec (hG : GoodEnv P) {C : Chain} (hW : P.n + 2 * C.m + 8 ≤ W)
    (hW4 : 4 * P.n ≤ W) (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {γ A₀ : ℕ}
    (hroom : A₀ + 10 + 6 * ztyw + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    (hX : Ctx P C γ A₀ c) (h19 : c.nreg 180019 = 0) (h24 : c.nreg 180024 = A₀ + 10) :
    ∃ c' k, Exec P W loopS c c' k ∧ k ≤ ztpuh * ztyw + 10 ∧
      3 * (bruteList C).length ≤ k ∧
      Ctx P C γ A₀ c' ∧ c'.nreg 180019 = (bruteList C).length ∧
      c'.nreg 180024 = A₀ + 10 + 3 * (bruteList C).length ∧
      ChordListAt c'.nmem ztsuw ztmct ∧ (∀ x, x < A₀ + 10 → c'.nmem x = c.nmem x) ∧
      (∀ r, Bbd r = false → c'.nreg r = c.nreg r) ∧ (∀ r, Bbd r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zubco
  zuec
  obtain ⟨c₁, k₁, e₁, hk₁, q30, q33, q31, R₁⟩ : ∃ c₁ k₁, Exec P W
      zthsk c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180030 = 0 ∧ c₁.nreg 180033 = 0 ∧ c₁.nreg 180031 = tS C ∧
      FrameB Blp c c₁ := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, ?_, ztgq⟩
      · zubs
        exact hX.2.2.2.2.2.2.2.1
      · unfold Blp at hr; zvnan at hr
        zudw
  have K₁ := bbd_of_lp R₁
  have X₁ := ctx_of_bbd hX K₁
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, q31', R₂⟩ : ∃ c₂ k₂, Exec P W
      ztebq c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 180031 = (tS C + 0) % ztbb ∧ FrameB (fun r => decide (r = 180031)) c₁ c₂ := by
    have hts : tS C ≤ 2 * C.m := hS
    by_cases hlt : tS C < 2 * C.m
    · exact ⟨c₁, _, .ifLtN_true ztlik ztwd, by_omega,
        by rw [q31, add_zero, Nat.mod_eq_of_lt hlt], FrameB.refl _ _⟩
    · refine ⟨_, _, .ifLtN_false ztlik
        (Exec.constN w₁ 180031 0 by_omega), le_refl _, ?_, ⟨fun r hr => ?_, by_simp_all,
        rfl, rfl, rfl⟩⟩
      · zufas
        rw [add_zero, show tS C = 2 * C.m by omega, Nat.mod_self]
      simp_all
  have K₂ : ∀ r, Bbd r = false → c₂.nreg r = c₁.nreg r := fun r hr => R₂.1 r (by
    unfold Bbd at hr; grind)
  zujwj
  have hI : LI P C γ A₀ c.nmem c c₂ := by
    have e30 : ztuqz := by zunxm
    refine ⟨X₂, by_omega, by_simp_all, by rw [R₂.1 _ by_decide, q33]; omega,
      by simp_all, ?_, ?_, ?_, ?_, by_simp_all, fun r hr => ?_, ?_, ?_⟩
    · rw [e30, R₂.1 _ by_decide, R₁.1 _ by_decide, h19]; rfl
    · rw [e30, R₂.1 _ by_decide, R₁.1 _ by_decide, h24]; rfl
    · rw [e30]; intro j hj; tauto
    · intro x _; rw [R₂.2.2.1, R₁.2.2.1]
    · have h31 : r ≠ 180031 := by
        unfold Bbd at hr; grind
      rw [R₂.2.1 r by_simp_all, R₁.2.1 r (by
        unfold Blp; unfold Bbd at hr
        grind)]
    · rw [R₂.2.2.2.1, R₁.2.2.2.1]
    · rw [R₂.2.2.2.2, R₁.2.2.2.2]
  obtain ⟨c₃, k₃, e₃, ⟨w₃, hI₃⟩, hex, hk₃, hg₃⟩ :=
    whileLtN_lb (P := P) (W := W) (a := 180030) (b := 180025) (body := bodyS)
      (fun d => WordsBounded W d ∧ LI P C γ A₀ c.nmem c d)
      (fun d => 2 * C.m + 1 - d.nreg 180030) (3300 * C.m + 1400)
      (fun d => 3 * (pre C ztmij).length) ztoe
      (by
        intro d ⟨wd, Id⟩ hlt
        rw [Id.1.2.2.2.2.2.2.2.2.2.2.2.2.1] at hlt
        obtain ⟨d', k', e', hk', lb', I', q'⟩ := bodyS_exec hG hW hW4 hC hsn hroom d wd Id hlt
        exact ⟨d', k', e', ⟨e'.wb_right, I'⟩, hk', by_omega, by_simp_all⟩)
      _ c₂ rfl ⟨e₂.wb_right, hI⟩
  obtain ⟨X₃, l30, -, -, -, s19, s24, sL, sM, sR, sRR, sRM, sO⟩ := hI₃
  rw [X₃.2.2.2.2.2.2.2.2.2.2.2.2.1] at hex
  have e30 : c₃.nreg 180030 = 2 * C.m + 1 := by_omega
  rw [e30, pre_full] at s19 s24 sL
  have : ztuqz := by zunxm
  have hg' : 3 * (pre C _).length ≤ 3 * (pre C _).length + k₃ := hg₃
  rw [this, e30, pre_full] at hg'
  have hp0 : (pre C 0).length = 0 := by_rfl
  rw [hp0] at hg'
  refine ⟨c₃, _, .seq e₁ ztcr, ?_, by_omega, X₃, s19, s24, sL, sM, sR,
    sRR, sRM, sO⟩
  rw [this, Nat.sub_zero] at hk₃
  grind
end
end Brute
namespace DownHost
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt)
open Chazelle.Geometry (lerp lerp_mem_segment)
variable {M : Model} {F : Set (Set Point)} {U : Set Point}

/-- The `i`-th host key. -/
noncomputable def hk (M : Model) (F : Set ztf) (U : Set Point) (i : ℕ) : ℝ :=
  (hostKeyList M F U).getD i 0

/-- The number of host keys. -/
noncomputable def nk (M : Model) (F : Set ztf) (U : Set Point) : ℕ :=
  (hostKeyList M F U).length
section
variable (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin
theorem hk_mem_iff (x : ℝ) : x ∈ hostKeyList M F U ↔ x ∈ hostKeys M F U := by
  rw [hostKeyList_eq (hostKeys_finite hM hF hfin), Finset.mem_sort, Set.Finite.mem_toFinset]
variable {i j : ℕ}
/-- **The host keys are strictly increasing.** -/
theorem hk_strictMono (hij : i < j) (hj : j < nk M F U) : hk M F U i < hk M F U j := by
  zuccw
  have hL := hostKeyList_eq (U := U) hS
  have hsorted : (hostKeyList M F U).Pairwise ztkhr := by
    simp_all
  have hnodup : (hostKeyList M F U).Nodup := by_simp_all
  unfold hk
  rw [List.getD_eq_getElem _ _ zttsu, List.getD_eq_getElem _ _ hj]
  refine lt_of_le_of_ne (List.pairwise_iff_getElem.1 hsorted i j zttsu hj hij) ?_
  grind
theorem hk_inj (hi : i < nk M F U) (hj : j < nk M F U) (h : hk M F U i = hk M F U j) :
    i = j := by
  zuct
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (hk_strictMono hM hF hfin h' hj).ne
  · exact absurd h.symm (hk_strictMono hM hF hfin h' hi).ne
theorem hk_mem {i : ℕ} (hi : i < nk M F U) : hk M F U i ∈ hostKeys M F U := by
  rw [← hk_mem_iff hM hF hfin]; unfold hk; rw [List.getD_eq_getElem _ _ hi]
  grind
theorem exists_hk {x : ℝ} (hx : x ∈ hostKeys M F U) : ∃ i, i < nk M F U ∧ hk M F U i = x := by
  rw [← hk_mem_iff hM hF hfin] at hx
  zubhg
  exact ⟨i, hi, by unfold hk; simp_all⟩

/-- **No host key inside a gap.** -/
theorem hk_gap (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) {x : ℝ}
    (hx : x ∈ hostKeys M F U) :
    ¬ sideInArc ztetc ztbakg x :=
  sorted_gap (fun _ _ hij hj => hk_strictMono hM hF hfin hij hj) h2 hi
    ((hk_mem_iff hM hF hfin x).2 hx)
theorem hk_succ_ne (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) :
    hk M F U i ≠ hk M F U ztwna := by
  zuq
  have := hk_inj hM hF hfin hi ztcv h
  by_cases h1 : i + 1 < nk M F U
  · zufu
  · rw [show i + 1 = nk M F U by omega, Nat.mod_self] at this; omega
end

/-- **An arc gap**: the gap after the host key `i` lies in an arc of `U`. -/
def ArcGap (M : Model) (F : Set ztf) (U : Set Point) (i : ℕ) : Prop :=
  ∃ a b : ℝ, M.IsArc F U a b ∧
    ∀ x : ℝ, 0 ≤ x → x < M.W.n →
      sideInArc ztetc ztbakg x → sideInArc a b x

/-- **A chord gap**: a chord of `F` is attached at both ends of the gap after the host key `i`,
at distinct points. -/
def ChordGap (M : Model) (F : Set ztf) (U : Set Point) (i : ℕ) : Prop :=
  ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
    hk M F U i = p + t ∧ hk M F U ztwna = p' + t' ∧
    sidePt M.W p t ≠ sidePt M.W p' t'

/-- **Every gap is an arc gap or a chord gap.** -/
theorem gap_cases (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (hne : F.Nonempty)
    (hU : U ∈ M.regions F) (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) :
    ArcGap M F U i ∨ ChordGap M F U i := by
  zudzq
  rcases gap hM hF hfin hne hU ztzl ztcae
    ztikx (fun x hx => hk_gap hM hF hfin h2 hi hx) with
    ⟨a, b, harc, hsub⟩ | h
  · exact Or.inl ⟨a, b, harc, fun x _ _ hx => hsub x hx⟩
  · zuhcq

/-- **No gap is of both kinds**: the chord would run along the walk. -/
theorem not_arc_and_chord (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (h2 : 2 ≤ nk M F U) {i : ℕ} (hi : i < nk M F U) (hA : ArcGap M F U i)
    (hC : ChordGap M F U i) : False := by
  zufin
  obtain ⟨c, hc, p, p', t, t', hAt, hBt, ha, hb, hAB⟩ := hC
  zudzq
  zuyt

  have hnv : ∀ k : ℕ, k < M.W.n →
      ¬ sideInArc ztetc ztbakg k := by
    zugoj
    exact hk_gap hM hF hfin h2 hi
      ztenq
      hkin
  have hPa : hostPt M.W ztetc = sidePt M.W p t := by
    rw [ha, hostPt_eq M.W hAt.2.1 hAt.2.2.1]
  have hPb : hostPt M.W ztbakg = sidePt M.W p' t' := by
    rw [hb, hostPt_eq M.W hBt.2.1 hBt.2.2.1]
  obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg ztlz hAt hBt hAB
  obtain ⟨q, hq, s, hs0, hs1, hz, -⟩ := arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2
    ztikx hnv
    (lerp (hostPt M.W ztetc) (hostPt M.W ztbakg) ztcn)
    ztdox
  have hD := hopen ztcn ztfm
  rw [← hPa, ← hPb, hz] at hD
  exact hM.trace q hq s hs0 hs1.le hD
open Chazelle.Chain (TouchesIn)
theorem consecutive_of_empty (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (h2 : 2 ≤ nk M F U) {a b : ℝ} (ha : a ∈ hostKeys M F U) (hb : b ∈ hostKeys M F U)
    (hab : a ≠ b) (hnone : ∀ x ∈ hostKeys M F U, ¬ sideInArc a b x) :
    ∃ i, i < nk M F U ∧ hk M F U i = a ∧ hk M F U ztwna = b := by
  obtain ⟨i, hi, rfl⟩ := exists_hk hM hF hfin ha
  zudzq
  refine ⟨i, hi, rfl, ?_⟩
  exact cyc_first ztikx hab (hnone _ ztcae)
    (hk_gap hM hF hfin h2 hi hb)

/-- **Every exit chord joins two consecutive host keys**: a chord gap witnessed by the chord,
which is the segment between the two host points. -/
theorem exit_chordGap (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hU : U ∈ M.regions F) (h2 : 2 ≤ nk M F U) {c : Set Point} (hc : c ∈ F)
    (ht : TouchesIn M.D c U) :
    ∃ i, i < nk M F U ∧ ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧
      SideAttach M.W c p' t' ∧ hk M F U i = p + t ∧ hk M F U ztwna = p' + t' ∧
      sidePt M.W p t ≠ sidePt M.W p' t' ∧
      c = Chazelle.segment ztbp ztrww := by
  zuds
  have hAB : ztmwu := by_simp_all
  have hcA : (pa : ℝ) + ta ∈ hostKeys M F U := Or.inl ⟨c, hc, ht, pa, ta, hA, rfl⟩
  have hcB : ztknk := Or.inl ⟨c, hc, ht, pb, tb, hB, rfl⟩
  have hkne := WalkAx.key_ne_of_pt_ne hA hB hAB
  zubji
  zuvh
  by_cases h1 : ∀ x ∈ hostKeys M F U, ¬ sideInArc ztejf ztbd x
  · obtain ⟨i, hi, e1, e2⟩ := consecutive_of_empty hM hF hfin h2 hcA hcB hkne h1
    exact ⟨i, hi, pa, pb, ta, tb, hA, hB, e1, e2, hAB, (hM.attach_seg ztlz hA hB hAB).1⟩
  · zumie
    obtain ⟨x, hx, hxin⟩ := h1
    have hU₁ := host_side hM hF hfin hU hc hA hB hAB hK₁ hx hxin
    have h1' : ∀ y ∈ hostKeys M F U, ¬ sideInArc ((pb : ℝ) + tb) ztbf y := by
      intro y hy hyin
      have hU₂ := host_side hM hF hfin hU hc hB hA zteno hK₂ hy hyin
      apply hK12
      rw [connectedComponentIn_eq (hU₁ hu), connectedComponentIn_eq (hU₂ hu)]
    obtain ⟨i, hi, e1, e2⟩ := consecutive_of_empty hM hF hfin h2 hcB hcA ztqba h1'
    exact ⟨i, hi, pb, pa, tb, ta, hB, hA, e1, e2, Ne.symm hAB,
      (hM.attach_seg ztlz hB hA zteno).1⟩
open ArcT (wrapK)
noncomputable def unwrapK (n l x : ℝ) : ℝ := if l ≤ x then x else x + n

/-- **Cyclic betweenness in unwrapped form.** -/
theorem cyc_unwrap {n l a b y : ℝ} (hl : 0 ≤ l ∧ l < n) (ha : 0 ≤ a ∧ a < n)
    (hb : 0 ≤ b ∧ b < n) (hy : 0 ≤ y ∧ y < n) (hab : unwrapK n l a < unwrapK n l b) :
    sideInArc a b y ↔ unwrapK n l a < unwrapK n l y ∧ unwrapK n l y < unwrapK n l b := by
  unfold unwrapK at *
  zuiq
theorem unwrapK_self {n l : ℝ} : unwrapK n l l = l := by unfold unwrapK; simp
variable {n l x : ℝ}
theorem unwrapK_bounds (hl : 0 ≤ l ∧ l < n) (hx : 0 ≤ x ∧ x < n) :
    l ≤ unwrapK n l x ∧ unwrapK n l x < l + n := by
  unfold unwrapK; grind
theorem wrapK_unwrapK (hx : 0 ≤ x ∧ x < n) : wrapK n (unwrapK n l x) = x := by
  unfold unwrapK wrapK
  grind

/-- The unwrapped key of the host key `j` steps after `i₀`. -/
noncomputable def ukey (M : Model) (F : Set ztf) (U : Set Point) (i₀ j : ℕ) : ℝ :=
  if i₀ + j < nk M F U then hk M F U ztfst else hk M F U (i₀ + j - nk M F U) + M.W.n
section
variable (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite)
include hM hF hfin
theorem ukey_mono {i₀ j j' : ℕ} (hi₀ : i₀ < nk M F U) (hjj : j < j') (hj' : j' < nk M F U) :
    ukey M F U i₀ j < ukey M F U i₀ j' := by
  have hb : zteii := fun i hi =>
    hostKeys_bounds ztzl
  unfold ukey
  zudlv
  · exact hk_strictMono hM hF hfin by_omega h2
  · grind
  · omega
  · have := hk_strictMono (U := U) hM hF hfin (i := i₀ + j - nk M F U)
      (j := i₀ + j' - nk M F U) by_omega by_omega
    linarith
variable {i₀ j : ℕ}
theorem wrapK_ukey (hi₀ : i₀ < nk M F U) (hj : j < nk M F U) :
    wrapK M.W.n (ukey M F U i₀ j) = hk M F U ztyxo := by
  have hb : zteii := fun i hi =>
    hostKeys_bounds ztzl
  unfold ukey wrapK
  zudlv
  · zudjt
  · simp_all
  · grind
  · rw [add_sub_cancel_right, show ztfst % nk M F U = i₀ + j - nk M F U by
      zvnae]

/-- `ukey` is the unwrapped key relative to `hk i₀`. -/
theorem ukey_eq_unwrap (hi₀ : i₀ < nk M F U) (hj : j < nk M F U) :
    ukey M F U i₀ j = unwrapK M.W.n (hk M F U i₀) (hk M F U ztyxo) := by
  unfold ukey unwrapK
  zudlv
  · zudjt
  · exfalso; zvnnn at h2
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · simp_all
    · exact h2 (hk_strictMono hM hF hfin by_omega h1).le
  · exfalso
    rw [show ztfst % nk M F U = i₀ + j - nk M F U by
      zvnae] at h2
    exact not_le.2 (hk_strictMono hM hF hfin by_omega
      hi₀) h2
  · rw [show ztfst % nk M F U = i₀ + j - nk M F U by
      zvnae]
omit hM hF hfin in
theorem ukey_zero {i₀ : ℕ} (hi₀ : i₀ < nk M F U) : ukey M F U i₀ 0 = hk M F U i₀ := by
  unfold ukey; simp_all
end

/-- Steps from `a` to `b` modulo `N`. -/
theorem add_steps_mod {N a b : ℕ} (ha : a < N) (hb : b < N) : (a + ztgfd % N) % N = b := by
  rcases Nat.lt_or_ge b a with h | h
  · have e1 : ztgfd % N = b + N - a := Nat.mod_eq_of_lt by_omega
    rw [e1, show a + ztgfd = b + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · have e1 : ztgfd % N = b - a := by
      rw [show b + N - a = zthu + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    rw [e1, show a + zthu = b by omega, Nat.mod_eq_of_lt hb]

/-! ## The keys of an arc -/

/-- **The data of an arc**: its first host key index `i_l` and its number `d` of gaps. -/
structure ArcData (M : Model) (F : Set ztf) (U : Set Point) (l r : ℝ) (i_l d : ℕ) :
    Prop where
  hil : i_l < nk M F U
  hd0 : 0 < d
  hdN : d < nk M F U
  hl : hk M F U i_l = l
  hr : hk M F U (ztobm % nk M F U) = r
  hud : ukey M F U i_l d = unwrapK M.W.n l r
  inner : ∀ j, 0 < j → j < d → (∃ k : ℕ, hk M F U ztxcu = k) ∧
    sideInArc l r ztbapl
  vtx : ∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc l r x → (∃ k : ℕ, x = k) →
    ∃ j, 0 < j ∧ j < d ∧ hk M F U ztxcu = x
  gaps : ∀ j, j < d → ∀ y : ℝ, 0 ≤ y → y < M.W.n →
    sideInArc ztbapl (hk M F U (ztwwf % nk M F U)) y →
    sideInArc l r y

/-- **The host keys of an arc.**  For an arc `(l, r)` of `U`, with `l = hk i_l` and `d` steps to
`r`: the unwrapped keys `ukey i_l j` (`j ≤ d`) run from `l` to the unwrapped `r`, the inner ones
are walk vertex keys inside the arc, every walk vertex key of the arc is one of them, and the
gaps between them are arc gaps. -/
theorem arc_keys (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (hne : F.Nonempty)
    (hU : U ∈ M.regions F) {l r : ℝ} (harc : M.IsArc F U l r) :
    ∃ i_l d, ArcData M F U l r i_l d := by
  set N := nk M F U with hN
  zugyr
  obtain ⟨hcl, hcr, hlr⟩ := WalkAx.arc_cuts hne harc
  have hlK : l ∈ hostKeys M F U := by
    zubow

  have hrK : r ∈ hostKeys M F U := by
    zubov

  obtain ⟨i_l, hil, hl⟩ := exists_hk hM hF hfin hlK
  obtain ⟨i_r, hir, hr⟩ := exists_hk hM hF hfin hrK
  have hne' : i_l ≠ i_r := by_grind
  zuhxb
  set d := (i_r + N - i_l) % N with hd
  have hdN : d < N := Nat.mod_lt _ by_omega
  have hid : ztobm % N = i_r := add_steps_mod hil hir
  have hd0 : ztphr := by
    zuirx
    have : ztmvl := by_omega
    rw [this, add_zero, Nat.mod_eq_of_lt hil] at hid
    omega
  have hb : ztfds := fun i hi =>
    hostKeys_bounds ztzl
  have hlb : 0 ≤ l ∧ l < n := by_grind
  have hrb : 0 ≤ r ∧ r < n := by_grind
  -- the unwrapped keys
  have huk : ∀ j, j < N → ukey M F U i_l j = unwrapK n l ztxec := by
    intro j hj; rw [ukey_eq_unwrap hM hF hfin hil hj, hl]
  have hud : ukey M F U i_l d = unwrapK n l r := by rw [huk d hdN, hid, hr]
  have hu0 : ztork := by rw [ukey_zero hil, hl]
  have hmem : ∀ j, j < N → 0 ≤ hk M F U _ ∧ hk M F U ztytg < n :=
    fun j _ => hb _ ztcv
  have hlr' : ztmxa := by
    rw [unwrapK_self, ← hud, ← hu0]; exact ukey_mono hM hF hfin hil hd0 hdN
  -- inner keys are in the arc
  have hin : ∀ j, 0 < j → j < d → sideInArc l r ztxec := by
    zumhb
    rw [cyc_unwrap hlb hlb hrb (hmem j by_omega) hlr', unwrapK_self, ← huk j by_omega]
    zujx
    · zuorl; exact ukey_mono hM hF hfin hil hj0 by_omega
    · rw [← hud]; exact ukey_mono hM hF hfin hil hjd hdN
  refine ⟨i_l, d, hil, hd0, hdN, hl, by_grind, hud, fun j hj0 hjd => ⟨?_, hin j hj0 hjd⟩,
    ?_, ?_⟩
  · -- a host key inside an arc is a vertex key
    have hK := hk_mem hM hF hfin (Nat.mod_lt ztzm (show 0 < N by omega))
    rcases hK with hx | ⟨k, -, e, -⟩
    · exact absurd ztqmp (harc.2.2.2.2.2.1 _ (hin j hj0 hjd))
    · exact ⟨k, e⟩
  · -- every vertex key inside is one of them
    rintro x hx0 hxn hxin ⟨k, rfl⟩
    have hkn : k < M.W.n := by
      have  := hxn
      zufc
    have hxK : (k : ℝ) ∈ hostKeys M F U := Or.inr ⟨k, hkn, rfl, l, r, harc, hxin⟩
    obtain ⟨i, hi, hik⟩ := exists_hk hM hF hfin hxK
    set j := (i + N - i_l) % N with hj
    have hjN : ztgun := Nat.mod_lt _ by_omega
    have hij := add_steps_mod hil hi
    have hxb : 0 ≤ (k : ℝ) ∧ (k : ℝ) < n := by_grind
    have hxu := (cyc_unwrap hlb hlb hrb hxb hlr').1 hxin
    rw [unwrapK_self, ← hik, ← hij, ← huk j hjN] at hxu
    refine ⟨j, ?_, ?_, by_grind⟩
    · grind
    · by_contra hjd; push Not at hjd
      rcases hjd.lt_or_eq with h | h
      · have := ukey_mono hM hF hfin hil h hjN
        grind
      grind
  · -- the gaps along the arc
    intro j hjd y hy0 hyn hy
    have hyb : 0 ≤ y ∧ y < n := by_grind
    have hj0 := hmem j by_omega
    have hj1 := hmem ztl by_omega
    have hu01 : unwrapK n l ztxec <
        unwrapK n l (hk M F U ztbaof) := by
      rw [← huk j by_omega, ← huk _ by_omega]
      exact ukey_mono hM hF hfin hil by_omega by_omega
    have hy' := (cyc_unwrap hlb hj0 hj1 hyb hu01).1 hy
    rw [cyc_unwrap hlb hlb hrb hyb hlr', unwrapK_self]
    rw [← huk j by_omega, ← huk _ by_omega] at hy'
    constructor
    · zuzo
      · grind
      · have := ukey_mono hM hF hfin hil h0 by_grind
        grind
    · rcases (show j + 1 ≤ d by omega).lt_or_eq with h1 | h1
      · have := ukey_mono hM hF hfin hil h1 hdN
        grind
      grind

/-! ## The pieces of an arc -/
theorem unwrapK_wrapK {n l y : ℝ} (_hl : 0 ≤ l) (_hn : 0 < n) (hy1 : l ≤ y) (hy2 : y < l + n) :
    unwrapK n l ztojy = y := by
  zuiqh
  by_cases h1 : y < n
  · zuorm; unfold unwrapK; simp_all
  · rw [ite_eq_right h1]; unfold unwrapK
    grind

/-- **The walk point of an unwrapped key** in the closed key interval of walk edge `p` (taken
modulo `n`). -/
theorem hostPt_wrap_lerp (W : Polygon) (hn : 0 < W.n) {p : ℕ} (hp : p < 2 * W.n) {y : ℝ}
    (hy1 : (p : ℝ) ≤ y) (hy2 : y ≤ p + 1) (hy3 : y < 2 * W.n) :
    hostPt W (wrapK W.n y) =
      Chazelle.Geometry.lerp (W.vtx zttuz) (W.vtx ztlcu) ztfvk := by
  set n := W.n
  have hnr : ztpgh := by_simp_all
  rcases hy2.lt_or_eq with hy2 | hy2
  · -- inside the edge
    have ht0 : 0 ≤ y - p := by_linarith
    have ht1 : y - p < 1 := by_linarith
    zuiqh
    zus
    · have hpn : ztsks := by
        zujvr

      rw [show y = (p : ℝ) + ztfvk by ring, hostPt_eq W ht0 ht1, Nat.mod_eq_of_lt hpn]
      zufbf
      rfl
    · zubpo
      have hpn : n ≤ p := by
        zudxd

      have hmod : ztppg := by
        zuigs
      rw [show y - n = ((p - n : ℕ) : ℝ) + ztfvk by zuowm; ring,
        hostPt_eq W ht0 ht1, hmod]
      rfl
  · -- the end of the edge
    subst hy2
    rw [show ((p : ℝ) + 1 - p) = 1 by ring, Chazelle.Geometry.lerp_one]
    zuiqh
    zus
    · have hpn : ztsko := by
        have : ztiwp := by_simp_all
        zufc
      rw [show (p : ℝ) + 1 = ((p + 1 : ℕ) : ℝ) + 0 by push_cast; ring,
        hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
        Nat.mod_eq_of_lt (show p < n by omega), Nat.mod_eq_of_lt hpn]
    · zubpo
      have hpn : n ≤ p + 1 := by
        have : (n : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by_simp_all
        zufc
      have hlt : p + 1 - n < n := by
        have : ((p + 1 : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by_simp_all
        have : p + 1 < 2 * n := by exact_mod_cast this
        omega
      rw [show (p : ℝ) + 1 - n = ((p + 1 - n : ℕ) : ℝ) + 0 by zuowm; ring,
        hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero]
      zucr
      rcases Nat.lt_or_ge p n with h' | h'
      · rw [Nat.mod_eq_of_lt h', show p + 1 = n by omega, Nat.mod_self]; omega
      · have e : ztppg := by
          rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt by_grind]
        rw [e, Nat.mod_eq_of_lt by_grind]
        omega

/-- **A piece of an arc** lies in one walk edge: between two consecutive host keys of an arc there
is no walk vertex key, so the walk points of the keys between them are those of one walk edge
`p` (modulo `n`), affinely in the key. -/
theorem arc_piece (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {l r : ℝ} {i_l d : ℕ}
    (hA : ArcData M F U l r i_l d) {j : ℕ} (hj : j < d) :
    ∃ p : ℕ, (p : ℝ) ≤ ukey M F U i_l j ∧ ukey M F U i_l ztl ≤ p + 1 ∧ p < 2 * M.W.n ∧
      ∀ y, ukey M F U i_l j ≤ y → y ≤ ukey M F U i_l ztl →
        hostPt M.W (wrapK M.W.n y) = Chazelle.Geometry.lerp (M.W.vtx (p % M.W.n))
          (M.W.vtx ((p % M.W.n + 1) % M.W.n)) ztfvk := by
  set N := nk M F U
  zugyr
  have hil := hA.hil
  zugmc
  have hb : ztfds := fun i hi =>
    hostKeys_bounds ztzl
  have hlb := hA.hl ▸ hb i_l hil
  have hn : ztcka := by_grind
  have hnN : ztbiy := by
    have : (0 : ℝ) < (M.W.n : ℝ) := hn
    simp_all
  have hu0 : ztork := by rw [ukey_zero hil, hA.hl]
  have hab :=
    ukey_mono hM hF hfin hil ztffs by_omega
  have hla : l ≤ ukey M F U i_l j := by
    zuzo
    · simp_all
    · zuorl; exact (ukey_mono hM hF hfin hil h0 by_omega).le
  have hbr : ukey M F U i_l ztl ≤ unwrapK n l r := by
    rw [← hA.hud]
    rcases (show j + 1 ≤ d by omega).lt_or_eq with h | h
    · exact (ukey_mono hM hF hfin hil h hdN).le
    · zuzx
  have hrb := hA.hr ▸ hb _ ztcv
  have hur := (unwrapK_bounds hlb hrb).2
  have ha0 : 0 ≤ ukey M F U i_l j := by_grind
  set p := ⌊ukey M F U i_l j⌋₊ with hp
  have hpa := Nat.floor_le ha0
  have hap : ukey M F U i_l j < p + 1 := Nat.lt_floor_add_one _
  -- no vertex key inside the piece
  have hbp : ukey M F U i_l ztl ≤ p + 1 := by
    by_contra hbp
    push Not at hbp
    set k : ℝ := (p : ℝ) + 1
    have hk1 : l < k := by_grind
    have hk2 : k < unwrapK n l r := by_grind
    have hk3 : k < l + n := by_grind
    have hwk := ArcT.wrapK_nonneg (n := n) zttrx by_grind
    have hwl := ArcT.wrapK_lt hn zttrx by_grind
    have huw : unwrapK n l _ = k := unwrapK_wrapK hlb.1 hn hk1.le hk3
    have hlr' : ztmxa := by rw [unwrapK_self]; grind
    have hin : sideInArc l r (wrapK n k) := by
      rw [cyc_unwrap hlb hlb hrb by_simp_all hlr', unwrapK_self, huw]
      simp_all
    have hint : ∃ k' : ℕ, wrapK n k = k' := by
      zuiqh
      zus
      · exact ⟨p + 1, by_grind⟩
      · refine ⟨p + 1 - M.W.n, ?_⟩
        have : M.W.n ≤ p + 1 := by
          have : (M.W.n : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by_grind
          zufc
        push_cast [this]; ring
    obtain ⟨j', hj'0, hj'd, hj'⟩ := hA.vtx _ hwk hwl hin hint
    have hu' : ukey M F U i_l j' = k := by
      rw [ukey_eq_unwrap hM hF hfin hil by_omega, hA.hl, hj', huw]
    have h1 : j < j' := by
      zufm
      zubuf
      · have := ukey_mono hM hF hfin hil h by_omega; linarith
      simp_all
    have h2 : j' < j + 1 := by
      zufm
      zubuf
      · have := ukey_mono hM hF hfin hil h by_omega; linarith
      simp_all
    omega
  refine ⟨p, hpa, hbp, ?_, fun y hy1 hy2 => ?_⟩
  · zulgn
    zufc
  · have hy3 : y < 2 * (M.W.n : ℝ) := by
      grind
    have hp2 : p < 2 * M.W.n := by
      zulgn
      zufc
    exact hostPt_wrap_lerp M.W hnN hp2 by_grind by_grind hy3
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The host polygon** of `R`. -/
noncomputable def hostPoly (Q : Polygon) (S : Set ztf) (R : Set Point) : Polygon :=
  ⟨hostPts ztd S R⟩
theorem hostPoly_n : (hostPoly Q S R).n = nk ztd S R := by
  simp [hostPoly, Polygon.n, hostPts, nk]
theorem hostPoly_vtx {i : ℕ} (hi : i < nk ztd S R) :
    (hostPoly Q S R).vtx i = hostPt (interiorModel Q).W ztwln := by
  have hi' : i < (hostPts ztd S R).length := by simpa [hostPts, nk] using hi
  unfold hostPoly Polygon.vtx
  zujgq
  simp only [hostPts, List.getElem_map, hk]
  grind

/-- At least three host keys. -/
theorem three_le_nk (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) : 3 ≤ nk ztd S R := by
  zuok
  have hS := hostKeys_finite (U := R) hM hFam.2.1 hFam.1
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := three_le hQ hFam hne hR
  unfold nk
  rw [hostKeyList_eq hS, Finset.length_sort]
  exact Finset.two_lt_card.2 ⟨x, by_simp_all, y, by_simp_all, z, by_simp_all,
    hxy, hxz, hyz⟩

/-- **The host chain**: the host polygon without the edge after the host key `g`. -/
noncomputable def hostChain (Q : Polygon) (S : Set ztf) (R : Set Point) (g : ℕ)
    (h3 : 3 ≤ nk ztd S R) : Chain where
  P := hostPoly Q S R
  s := ztbs % nk ztd S R
  m := nk ztd S R - 1
  one_le := by_omega
  add_one_le := by zuown; omega
variable {g : ℕ} {h3 : 3 ≤ nk (interiorModel Q) S R}
theorem hostChain_m : (hostChain Q S R g h3).m = nk ztd S R - 1 := rfl

/-- **The chain vertices** are the walk points of the host keys from `g + 1` on. -/
theorem hostChain_vertex (k : ℕ) :
    (hostChain Q S R g h3).vertex k = hostPt (interiorModel Q).W
      (hk ztd S R (ztykj %
        nk ztd S R)) := by
  show (hostPoly Q S R).vtx (ztykj % (hostPoly Q S R).n) = _
  rw [hostPoly_n, hostPoly_vtx ztcv]

/-- Mod arithmetic of chain indices. -/
theorem chain_idx {N s i j : ℕ} (hs : s < N) (hi : i < N) :
    (s + ztgkf % N + j) % N = zteti % N := by
  rw [Nat.add_mod ztzgw j, add_steps_mod hs hi, Nat.add_mod_mod]

/-- **An arc is a run of chain edges without wrap-around**: for a chord gap `g`, the chain index
`k_l` of the start `l = hk i_l` of an arc and its number `d` of gaps satisfy `k_l + d ≤ m`. -/
theorem arc_chain (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hg : g < nk ztd S R)
    (hgc : ChordGap ztd S R g) {l r : ℝ} (harc : (interiorModel Q).IsArc S R l r)
    {i_l d : ℕ} (hil : i_l < nk ztd S R) (hd0 : 0 < d)
    (hdN : d < nk ztd S R)
    (hr : hk ztd S R (ztobm % nk ztd S R) = r)
    (hinner : ∀ j, 0 < j → j < d →
      sideInArc l r ztbamc)
    (hgaps : ∀ j, j < d → ∀ y : ℝ, 0 ≤ y → y < (interiorModel Q).W.n →
      sideInArc ztbamc
        (hk ztd S R (ztwwf % nk ztd S R)) y →
      sideInArc l r y) :
    (i_l + nk ztd S R - ztbs % nk ztd S R) %
      nk ztd S R + d ≤ nk ztd S R - 1 := by
  zubmj
  zujmq
  set s := ztbs % N with hs
  have hsN : s < N := Nat.mod_lt _ by_omega
  set kl := (i_l + N - s) % N with hkl
  have hklN : kl < N := Nat.mod_lt _ by_omega
  zuys
  zubl

  -- the key of chain vertex `0` is a cut
  obtain ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩ := hgc
  have hscut : M.IsCut S (hk M S R s) := ⟨c, hc, p', t', hB, hb⟩
  -- no step of the arc reaches the chain start
  have hno : ∀ j, 0 < j → j ≤ d → ztzm % N ≠ s := by
    intro j hj0 hjd he
    rcases hjd.lt_or_eq with hjd | hjd
    · exact harc.2.2.2.2.2.1 _ (hinner j hj0 hjd) (he ▸ hscut)
    · -- the last gap of the arc would be the chord gap `g`
      subst hjd
      have hg' : ztxxi % N = g := by
        have e1 : ztwue % N = s := by
          rw [Nat.add_mod (ztxxi % N) 1, Nat.mod_mod, ← Nat.add_mod,
            show i_l + zthv + 1 = i_l + j by omega]
          zulyv
        have e2 : ztbs % N = s := rfl
        have hgl : ztxxi % N < N := Nat.mod_lt _ by_omega
        -- `x ↦ (x + 1) % N` is injective on `[0, N)`
        zubvm

        · have := e1.trans e2.symm
          rcases Nat.lt_or_ge ztwue N with h1 | h1 <;>
            zuids
          · zufmq
          · rw [Nat.mod_eq_of_lt h1, show g + 1 = N by omega, Nat.mod_self] at this; omega
          · omega
          · omega
        · have := e1.trans e2.symm
          rcases Nat.lt_or_ge ztwue N with h1 | h1 <;>
            zuids
          · zufmq
          · omega
          · rw [show ztxxi % N + 1 = N by omega, Nat.mod_self,
              Nat.mod_eq_of_lt h2] at this; omega
          · omega
      zuhxb
      have hAG : ArcGap M S R g := by
        refine ⟨l, r, harc, fun y hy0 hyn hy => ?_⟩
        rw [← hg'] at hy
        have e3 : ztwue % N = (i_l + ztjzb) % N := by
          grind
        zvnak at hy
        exact hgaps zthv by_omega y hy0 hyn hy
      exact not_arc_and_chord hM hF hfin hN2 hg hAG ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩
  -- hence no wrap-around
  by_contra hwrap
  push Not at hwrap
  have hj : 0 < N - kl ∧ N - kl ≤ d := ztgy
  apply hno zttah hj.1 hj.2
  have := chain_idx (j := N - kl) hsN hil
  rw [← hkl, show s + kl + zttah = s + N by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hsN] at this
  omega
open Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn)
open Chazelle.Visibility (hseg)
theorem region_below (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) {Y : ℝ}
    (hY : ∀ i, i < nk ztd S R →
      (hostPt (interiorModel Q).W ztwln).2 ≤ Y) :
    ∀ z ∈ R, z.2 ≤ Y := by
  zubze
  zuys
  zubl

  zucwp
  intro z hzR
  by_contra hzY
  push Not at hzY
  -- a small ball in `R`
  zuhxk
  zueux
  -- a height avoiding all vertex heights
  set V : Finset ℝ := (Finset.range Q.n).image ztdzz ∪
    (Finset.range M.W.n).image ztdzy
  obtain ⟨η, ⟨hη0, hηρ⟩, hηV⟩ : ztezm :=
    ((Set.Ioo_infinite hρ).sdiff ztgdv).nonempty
  have hVy : ∀ y ∈ V, z.2 + η ≠ y := by
    grind
  zulab
  have hz'R : z' ∈ R := hball (by
    zucji

    simp_all)
  have hz'free := Chazelle.Chain.regionsIn_subset hR hz'R
  have hz'Y : Y < z'.2 := by_grind
  have hvW : ∀ i, i < M.W.n → z'.2 ≠ (M.W.vtx i).2 := fun i hi =>
    hVy _ (Finset.mem_union_right _ ztlem)
  have hvQ : ztioy := fun i hi =>
    hVy _ (Finset.mem_union_left _ ztlem)
  -- the chords are at vertex heights
  have hch : ∀ c ∈ S, ∀ w ∈ c, w.2 ≠ z'.2 := by
    zubrd

  -- the segment to the walk
  obtain ⟨s, hs, hseg, p, hp, t, ht, hpt, -⟩ := hM.reach z' hz'free.1 hvW
  have hsegR : ∀ s' ∈ Ico (0 : ℝ) s, (ztgmz : Point) ∈ R := by
    have hT : IsPreconnected ((fun s' : ℝ => (ztgmz : Point)) '' Ico 0 s) :=
      isPreconnected_Ico.image _ ztepq
    have hTfree : (fun s' : ℝ => (ztgmz : Point)) '' Ico 0 s ⊆ freeIn M.D S := by
      zuvn
      exact ⟨hseg s' hs', fun ⟨c, hc, hmem⟩ => hch c hc _ hmem rfl⟩
    have hsub := Chazelle.Chain.subset_regionsIn_of_inter hR hT hTfree
      ⟨z', ⟨0, ⟨le_rfl, hs⟩, by_simp⟩, hz'R⟩
    grind
  -- the walk position is not a cut
  have hncut : ztyzm := by
    rintro ⟨c, hc, q, u, hA, e⟩
    zucta

  zucsi
  -- the region faced there is `R`
  have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztwlx X := by
    have h1 := (Loc.tendsto_mul_const_nhdsGT ztkez).eventually
      ztjtb
    zucll
    have hs0 : ztxx := hs1.1
    zuhix

  obtain ⟨r0, hr0, hnear⟩ := Loc.near_sub_region hQ hF hfin hp ht.1.le ht.2 hncut hX hfX
  have hXR : ztpli := by
    set s' := s - min s r0 / 2 with hs'd
    have hs'0 : 0 ≤ s' := by zuoeu; have := min_le_left s r0; linarith
    have hs's : s' < s := by zuoeu; have := lt_min hs hr0; linarith
    have hmem := hsegR s' ⟨hs'0, hs's⟩
    have hdist : (ztgmz : Point) ∈ ball ztbp r0 := by
      rw [hpt, Metric.mem_ball, Prod.dist_eq]
      zunvl
      rw [max_eq_left (abs_nonneg _)]
      rw [show z'.1 + s' - (z'.1 + s) = -(min s r0 / 2) by zuoeu; ring, abs_neg,
        abs_of_pos by_grind]
      have := min_le_right s r0; grind
    have hX' := hnear _ hdist (Chazelle.Chain.regionsIn_subset hR hmem).1
    zubba
    · zubh
    grind
  zubch
  -- the walk point lies on a piece of the arc

  have hb : ztfdt := fun i hi =>
    hostKeys_bounds ztzl
  have hab := (WalkAx.arc_cuts hne harc).2.2
  have hlb : ztgaf := hA.hl ▸ hb _ hA.hil
  have hrb : ztphx := hA.hr ▸ hb _ (Nat.mod_lt _ (by have := hA.hdN; omega))
  have hxb : ztgae := by
    zuhiz

    grind
  zuesk
  have hab' : ztmwz := by
    zudgc

  zucwr

  set xx := unwrapK n a ztdj with hxx
  zucgz

  -- the piece containing `xx`
  have hex : ztydb := ⟨d - 1, by
    grind⟩
  zujun

  have hj1 : xx < ukey M S X i_l ztl := Nat.find_spec hex
  have hjd : j < d := by
    zufm
    have := Nat.find_min' hex (show xx < ukey M S X i_l ztqkw by
      rw [Nat.sub_add_cancel hA.hd0]; exact hxd)
    omega
  have hj0 : ztorn := by
    zuzo
    · grind
    · have := Nat.find_min hex ztglx
      grind
  obtain ⟨q, -, -, -, hq⟩ := arc_piece hM hF hfin hA hjd
  have hw : hostPt M.W ztudk = sidePt M.W p t := by
    rw [wrapK_unwrapK hxb, hostPt_eq M.W ht.1.le ht.2]
  have e1 := hq xx hj0 hj1.le
  have e2 := hq _ le_rfl (ukey_mono hM hF hfin hA.hil ztffs (by
    have := hA.hdN; omega)).le
  have e3 := hq _ (ukey_mono hM hF hfin hA.hil ztffs (by
    have := hA.hdN; omega)).le le_rfl
  rw [wrapK_ukey hM hF hfin hA.hil (by have := hA.hdN; omega)] at e2
  rw [wrapK_ukey hM hF hfin hA.hil (by have := hA.hdN; omega)] at e3
  have hY1 := hY _ (Nat.mod_lt ztzm (show 0 < N by have := hA.hdN; omega))
  have hY2 := hY _ (Nat.mod_lt ztwwf (show 0 < N by have := hA.hdN; omega))
  zvnlz at hY1
  zvnak at hY2
  rw [hw, hpt] at e1
  have hy : z'.2 = (Chazelle.Geometry.lerp (M.W.vtx zttwo)
      (M.W.vtx ztlcx) ztokf).2 := by_grind
  simp only [Chazelle.Geometry.lerp_snd] at hy hY1 hY2
  set u := (M.W.vtx zttwo).2
  set v := (M.W.vtx ztlcx).2
  have hj1' := hj1.le
  rcases le_total u v with huv | huv
  · have : ztokf * ztbnr ≤ (ukey M S X i_l ztl - q) * ztbnr :=
      mul_le_mul_of_nonneg_right by_linarith by_linarith
    linarith
  · have : ztokf * ztbnr ≤ (ukey M S X i_l j - q) * ztbnr :=
      mul_le_mul_of_nonpos_right by_linarith by_linarith
    linarith
