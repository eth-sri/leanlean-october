module

public import Chazelle.MacT
public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.DownPhaseDrvXRamH
public import Chazelle.Core.ShootCutLoop2

namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey Brute SweepPrim
@[expose] public section
def nbrI : Stmt :=
  .seq (block [.addN 170080 170079 170019, .addN 170081 170079 170011])
    (.seq (.ifLtN 170080 170010 .skip (block [.subN 170080 170080 170010]))
      (.ifLtN 170081 170010 .skip (block [.constN 170081 0])))

/-- The six sign tests. -/
def testsI : Stmt :=
  .seq (testS 2 ztmad ztffd zthqk 170082)
  (.seq (testS 3 ztmad ztffd zthqk 170083)
  (.seq (testS 0 ztffd zthqk ztffd 170085)
  (.seq (testS 0 ztmad ztffd ztmad 170086)
  (.seq (testS 1 ztffd zthqk ztffd 170087)
  (testS 1 zthqk ztffd zthqk 170088)))))

/-- `170075 := v`. -/
def setB (v : ℕ) : Stmt := block [.constN 170075 v]

/-- The decision tree of `BetaF`. -/
def logI : Stmt :=
  .ifLtN 170012 170083
    (.ifLtN 170012 170088 ztkev
      (.ifLtN 170012 170087 (.ifLtN 170012 170085 ztkev ztiap) ztiap))
    (.ifLtN 170012 170082
      (.ifLtN 170012 170085 ztyzu ztiap)
      (.ifLtN 170012 170085 ztkev ztyzu))

/-- **The orientation bit.** -/
def betaI : Stmt := .ifLtN 170012 170074 (.seq nbrI (.seq testsI logI)) ztiap

/-- The registers `betaI` writes. -/
def Bbeta (r : ℕ) : Bool := decide (r = 170075) || decide (170080 ≤ r ∧ r < 170089) || Bk r
theorem wr_betaI : wr Bbeta betaI = true := by
  rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
theorem setB_exec (c : Config) (hw : WordsBounded W c) (v : ℕ) (hv : v ≤ 1) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (setB v) c c' k ∧ k = 1 ∧
      c' = { c with nreg := upd c.nreg 170075 v } := by
  unfold setB
  exec_block
  · omega
  simp

/-- **The decision tree** of `BetaF` on six bits. -/
theorem logI_exec (c : Config) (hw : WordsBounded W c) (h12 : c.nreg 170012 = 0) (hW : 1 ≤ W)
    {pp p0 bx ax by' by'' : Prop} (hpp : BitIs c 170082 pp) (hp0 : BitIs c 170083 p0)
    (hbx : BitIs c 170085 bx) (hax : BitIs c 170086 ax) (hby : BitIs c 170087 by')
    (hby' : BitIs c 170088 by'') (hcons : p0 → ¬ pp) :
    ∃ c' k, Exec P W logI c c' k ∧ k ≤ 12 ∧ ∃ b, b ≤ 1 ∧
      c' = { c with nreg := upd c.nreg 170075 b } ∧
      (b = 1 ↔ (pp ∧ bx ∧ ax) ∨ (¬ pp ∧ ¬ p0 ∧ (bx ∨ ax)) ∨ (p0 ∧ by' ∧ bx) ∨
        (p0 ∧ by'')) := by
  obtain ⟨hpp1, hpp2⟩ := hpp
  obtain ⟨hp01, hp02⟩ := hp0
  obtain ⟨hbx1, hbx2⟩ := hbx
  obtain ⟨hax1, hax2⟩ := hax
  obtain ⟨hby1, hby2⟩ := hby
  obtain ⟨hby'1, hby'2⟩ := hby'
  have t : ∀ r, c.nreg r ≤ 1 → (c.nreg 170012 < c.nreg r ↔ c.nreg r = 1) := by_grind
  have one : ∀ {Φ : Prop}, Φ → ((1 : ℕ) = 1 ↔ Φ) := by_simp_all
  have zero : ∀ {Φ : Prop}, ¬ Φ → ((0 : ℕ) = 1 ↔ Φ) := by_simp_all
  unfold logI
  by_cases g0 : c.nreg 170012 < c.nreg 170083
  · have q0 : p0 := by_simp_all
    have q0' := hcons q0
    refine spec_ifLtN_true g0 ?_
    by_cases g1 : c.nreg 170012 < c.nreg 170088
    · have q1 : by'' := by_simp_all
      zumjs
      zuen

    · have q1 : ¬ by'' := by_simp_all
      zumjl
      by_cases g2 : c.nreg 170012 < c.nreg 170087
      · have q2 : by' := by_simp_all
        zumjt
        by_cases g3 : c.nreg 170012 < c.nreg 170085
        · have q3 : bx := by_simp_all
          refine spec_ifLtN_true g3 ?_
          zuen

        · have q3 : ¬ bx := by_simp_all
          refine spec_ifLtN_false g3 ?_
          zueg

      · have q2 : ¬ by' := by_simp_all
        refine spec_ifLtN_false g2 ?_
        zueg

  · have q0 : ¬ p0 := by_simp_all
    refine spec_ifLtN_false g0 ?_
    by_cases g1 : c.nreg 170012 < c.nreg 170082
    · have q1 : pp := by_simp_all
      zumjs
      zuhse
      · zugns

        zuhsg
        · zugnt

          zuen

        · zufxe

          zueg

      · zufxd

        zueg

    · have q1 : ¬ pp := by_simp_all
      zumjl
      zuhse
      · zugns

        zuen

      · zufxd

        zuhsg
        · zugnt

          zuen

        · zufxe

          zueg

/-- **The neighbours of the top.** -/
theorem nbrI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {v : ℕ}
    (hv : c.nreg 170079 = v) (hvn : v < P.n) :
    ∃ c' k, Exec P W nbrI c c' k ∧ k ≤ 8 ∧ c'.nreg 170080 = ztqxz % P.n ∧
      c'.nreg 170081 = ztsp % P.n ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170080 → r ≠ 170081 → c'.nreg r = c.nreg r) := by
  zucg

  zucgt
  unfold nbrI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hv, hS.r19]; omega
  · config_simp; rw [hv, hS.r11]; omega
  zujl
  have hA : (v + ztch) % P.n = ztqxz % P.n := by_grind
  by_cases h1 : v + ztch < P.n
  · refine spec_ifLtN_true (by config_simp; rw [hv, hS.r19, hS.r10]; exact h1) ?_
    zurc
    zuhss
    · refine spec_ifLtN_true (by config_simp; rw [hv, hS.r11, hS.r10]; exact h2) ?_
      refine spec_skip ‹_› ztdqj
      · config_simp; rw [hv, hS.r19, ← hA, Nat.mod_eq_of_lt h1]
      · config_simp; rw [hv, hS.r11, Nat.mod_eq_of_lt h2]
      simp_all
    omega
  · refine spec_ifLtN_false (by config_simp; rw [hv, hS.r19, hS.r10]; exact h1) ?_
    exec_block
    zuhss
    · refine spec_ifLtN_true (by config_simp; rw [hv, hS.r11, hS.r10]; exact h2) ?_
      refine spec_skip ‹_› ztdqj
      · config_simp; rw [hv, hS.r19, hS.r10, ← hA, Nat.mod_eq_sub_mod by_omega,
          Nat.mod_eq_of_lt by_omega]
      · config_simp; rw [hv, hS.r11, Nat.mod_eq_of_lt h2]
      simp_all
    · refine spec_ifLtN_false (by config_simp; rw [hv, hS.r11, hS.r10]; exact h2) ?_
      exec_block
      · omega
      refine ztdqj
      · config_simp; rw [hv, hS.r19, hS.r10, ← hA, Nat.mod_eq_sub_mod by_omega,
          Nat.mod_eq_of_lt by_omega]
      · config_simp; rw [show v + 1 = P.n by omega, Nat.mod_self]
      simp_all

/-- One test of `testsI`: the bit, and the other registers outside the kernel. -/
theorem test1 {op : ℕ} (hop : op ≤ 3) (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {a b d dst : ℕ}
    (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hd : 10500 ≤ d) (hdst : 10500 ≤ dst) (c : Config)
    (hw : WordsBounded W c) (hla : c.nreg a < P.n) (hlb : c.nreg b < P.n) (hld : c.nreg d < P.n) :
    ∃ c' k, Exec P W (testS op (.v a) (.v b) (.v d) dst) c c' k ∧ k ≤ 245 ∧
      BitIs c' dst (SignTest op ((Qof P).vtx ztcux) ((Qof P).vtx ztfgv)
        ((Qof P).vtx ztqir)) ∧
      (∀ r, r ≠ dst → ztcu → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, F, b1, b2⟩ := testS_exec hG hW hop (x := .v a) (y := .v b) (z := .v d)
    (d := dst) by_tauto by_tauto
    by_tauto c hw hla hlb hld
  refine ⟨c', k, e, hk, ztomj, fun r h1 h2 => F.1 r ?_, F.2.2.1⟩
  unfold Bt Bk; grind

/-- **The six sign tests.** -/
theorem testsI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    {A v B : ℕ} (hA : c.nreg 170080 = A) (hv : c.nreg 170079 = v) (hB : c.nreg 170081 = B)
    (hAn : A < P.n) (hvn : v < P.n) (hBn : B < P.n) :
    ∃ c' k, Exec P W testsI c c' k ∧ k ≤ 1470 ∧
      BitIs c' 170082 (0 < det ztosf ztosh ztosg) ∧
      BitIs c' 170083 (det ztosf ztosh ztosg = 0) ∧
      BitIs c' 170085 (((Qof P).vtx v).1 < ((Qof P).vtx B).1) ∧
      BitIs c' 170086 (((Qof P).vtx A).1 < ((Qof P).vtx v).1) ∧
      BitIs c' 170087 (((Qof P).vtx v).2 < ((Qof P).vtx B).2) ∧
      BitIs c' 170088 (((Qof P).vtx B).2 < ((Qof P).vtx v).2) ∧
      (∀ r, ztbqm → ztcu → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁, m₁⟩ := test1 (op := 2) by_norm_num hG hW (a := 170080)
    (b := 170079) (d := 170081) (dst := 170082) by_norm_num by_norm_num by_norm_num
    by_norm_num c hw by_omega by_omega by_omega
  rw [hA, hv, hB] at b₁
  have f₁ : ∀ r, (r < 170082 ∨ 170082 < r) → ztcu → c₁.nreg r = c.nreg r :=
    by simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, r₂, m₂⟩ := test1 (op := 3) by_norm_num hG hW (a := 170080)
    (b := 170079) (d := 170081) (dst := 170083) by_norm_num by_norm_num by_norm_num
    by_norm_num c₁ e₁.wb_right by_simp_all
    by_simp_all
    by_simp_all
  rw [f₁ _ by_omega by_omega, f₁ _ by_omega by_omega, f₁ _ by_omega by_omega, hA, hv,
    hB] at b₂
  have f₂ : ∀ r, (r < 170082 ∨ 170083 < r) → ztcu → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃, m₃⟩ := test1 (op := 0) by_norm_num hG hW (a := 170079)
    (b := 170081) (d := 170079) (dst := 170085) by_norm_num by_norm_num by_norm_num
    by_norm_num c₂ e₂.wb_right by_simp_all
    by_simp_all
    by_simp_all
  rw [f₂ _ by_omega by_omega, f₂ _ by_omega by_omega, hv, hB] at b₃
  have f₃ : ∀ r, (r < 170082 ∨ 170085 < r) → ztcu → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => by_grind
  obtain ⟨c₄, k₄, e₄, hk₄, b₄, r₄, m₄⟩ := test1 (op := 0) by_norm_num hG hW (a := 170080)
    (b := 170079) (d := 170080) (dst := 170086) by_norm_num by_norm_num by_norm_num
    by_norm_num c₃ e₃.wb_right by_simp_all
    by_simp_all
    by_simp_all
  rw [f₃ _ by_omega by_omega, f₃ _ by_omega by_omega, hv, hA] at b₄
  have f₄ : ∀ r, (r < 170082 ∨ 170086 < r) → ztcu → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by_grind
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, r₅, m₅⟩ := test1 (op := 1) by_norm_num hG hW (a := 170079)
    (b := 170081) (d := 170079) (dst := 170087) by_norm_num by_norm_num by_norm_num
    by_norm_num c₄ e₄.wb_right by_grind
    by_grind
    by_grind
  rw [f₄ _ by_omega by_omega, f₄ _ by_omega by_omega, hv, hB] at b₅
  have f₅ : ∀ r, (r < 170082 ∨ 170087 < r) → ztcu → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => by_grind
  obtain ⟨c₆, k₆, e₆, hk₆, b₆, r₆, m₆⟩ := test1 (op := 1) by_norm_num hG hW (a := 170081)
    (b := 170079) (d := 170081) (dst := 170088) by_norm_num by_norm_num by_norm_num
    by_norm_num c₅ e₅.wb_right by_grind
    by_grind
    by_grind
  rw [f₅ _ by_omega by_omega, f₅ _ by_omega by_omega, hv, hB] at b₆
  have ex : Exec P W testsI c c₆ _ :=
    .seq e₁ ztfv
  have pr : ∀ {c c' : Config} {r : ℕ}, (∀ q, q ≠ r → (q < 10000 ∨ 10500 ≤ q) →
      c'.nreg q = c.nreg q) → ∀ {r' : ℕ} {p : Prop}, BitIs c r' p → r' ≠ r → 10500 ≤ r' →
      BitIs c' r' p := fun h _ _ hb hne h2 => hb.of_eq by_grind
  refine ⟨c₆, _, ex, by_omega, ?_, ?_, ?_, ?_, ?_, b₆, fun r h1 h2 => ?_, by
    grind⟩
  · exact pr r₆ (pr r₅ (pr r₄ (pr r₃ (pr r₂ b₁ by_norm_num by_norm_num) by_norm_num
      by_norm_num) by_norm_num by_norm_num) by_norm_num by_norm_num) by_norm_num
      by_norm_num
  · exact pr r₆ (pr r₅ (pr r₄ (pr r₃ b₂ by_norm_num by_norm_num) by_norm_num
      by_norm_num) by_norm_num by_norm_num) by_norm_num by_norm_num
  · exact pr r₆ (pr r₅ (pr r₄ b₃ by_norm_num by_norm_num) by_norm_num by_norm_num)
      by_norm_num by_norm_num
  · exact pr r₆ (pr r₅ b₄ by_norm_num by_norm_num) by_norm_num by_norm_num
  · exact pr r₆ b₅ by_norm_num by_norm_num
  grind

/-- **The orientation bit of the chain of a stretch.** -/
theorem betaI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {C : Chain}
    (hC : C.P = Qof P) (hT : c.nreg 170074 = C.topIdx) (hv : c.nreg 170079 = ztwi % (Qof P).n) :
    ∃ c' k, Exec P W betaI c c' k ∧ k ≤ 1500 ∧ c'.nreg 170075 ≤ 1 ∧
      (c'.nreg 170075 = 1 ↔ C.sideBeta = true) ∧ c'.nmem = c.nmem ∧ FrameB Bbeta c c' := by
  zudq
  zuhwq
  zucwc
  unfold betaI
  have hwr := wr_betaI
  by_cases h0 : c.nreg 170012 < c.nreg 170074
  · have hT0 : ztphp := by_omega
    set v := ztwi % (Qof P).n with hvd
    have hvn : v < P.n := by zvnoq; exact Nat.mod_lt _ (by zvnao; have := hS.n3; omega)
    obtain ⟨c₁, k₁, e₁, hk₁, a80, a81, m₁, r₁⟩ := nbrI_exec c hw hS hv hvn
    obtain ⟨c₂, k₂, e₂, hk₂, b82, b83, b85, b86, b87, b88, r₂, m₂⟩ := testsI_exec c₁ e₁.wb_right
      hS.good hW a80 by_simp_all a81
      ztcv hvn ztcv
    have c12 : ztlxz := by
      rw [r₂ _ by_decide by_decide, r₁ _ by_decide by_decide]; exact hS.r12
    have hcons : ∀ x : ℝ, x = 0 → ¬ 0 < x := fun x h => by_grind
    obtain ⟨c₃, k₃, e₃, hk₃, b, b75, rfl, i75⟩ := logI_exec c₂ e₂.wb_right c12 by_omega b82 b83
      b85 b86 b87 b88 (hcons _)
    have ex := Exec.ifLtN_true (e := setB 0) h0 ztwrj
    refine ⟨_, _, ex, by_omega, by simpa using b75, ?_, by_grind, exec_frameB ex hwr⟩
    zufb
    rw [i75, sideBeta_ch hC hD hT0 hvd]
    unfold BetaF
    zuext
  · have hT0 : C.topIdx = 0 := by rw [← hT]; rw [hS.r12] at h0; omega
    obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := setB_exec c hw 0 by_norm_num by_omega
    have ex := Exec.ifLtN_false (t := nbrI.seq (testsI.seq logI)) h0 e₁
    refine ⟨_, _, ex, by_omega, by_simp, ?_, rfl, exec_frameB ex hwr⟩
    rw [sideBeta_of_top_zero hT0]; simp
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
@[expose] public section
def sI : Stmt :=
  .seq (block [.addN 170089 170037 170037])
    (.ifLtN 170075 170011 (block [.subN 170076 170089 170074]) (block [.copyN 170076 170074]))

/-- `170077 := τ = (J + 2 L - S) mod 2 L` (`J = 0` if `LeftInside`, else `L`). -/
def tauI : Stmt :=
  .seq ztfme
    (.seq ztiqg
      ztifg)

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
  ModelDescAt m B zta ztc ∧ ModelDescWF P E m B ∧ ShotListG.HReg P m B

/-- **The descriptor survives** memory changes at or above its bound. -/
theorem DescOK.keep {P : Polygon} {m m' : ℕ → ℕ} {B E E' : ℕ} {C : Chain} (h : DescOK P m B C E)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') : DescOK P m' B C E' := by
  obtain ⟨hMD, hwf, hreg⟩ := h
  obtain ⟨hwf', hMD'⟩ := ShotListG.modelDescG_keep hwf hMD he hE
  exact ⟨hMD', hwf', ShotListG.hreg_keep hwf hMD hreg he⟩

/-- **The descriptor of the chain of a stretch**, from its six words. -/
theorem descOK_of {P : Polygon} (hG : GoodEnv P) {m : ℕ → ℕ} {A₀ B E : ℕ} {u L : ℕ}
    {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hu : u < (Qof P).n) (hH : HostAt m A₀ ztqg)
    (hA : A₀ + 8 ≤ B) (hBE : B + 6 ≤ E) (m0 : m B = 0) (m1 : m ztvf = A₀)
    (m2 : m zthb = cStart zta u L) (m3 : m ztkh = L)
    (m4 : m ztow = (ch zta u L h1 h2).topIdx)
    (m5 : m zter = 1 ↔ (ch zta u L h1 h2).sideBeta = true) :
    DescOK P m B ztwls E := by
  zudq
  zudos
  have hpoly : ztyks := by
    have := L41.poly_whole zta by_omega; simp_all
  have hCD : ChainDescAt m _ _ ztqg _ :=
    ⟨by_simp_all, by_tauto, m2, m3, m4, m5⟩
  have huniq : ∀ H C, ChainDescAt m ztvf zta H C → H = Host.whole P.n := fun H C hC =>
    NFLoc.hostAt_unique hC.1 by_simp_all
  refine ⟨Or.inl ⟨m0, _, _, hCD, rfl⟩, ⟨by_omega, fun _ => ⟨by_omega, fun H C hC => ?_⟩⟩,
    fun _ H C hC => ?_⟩
  · have e := huniq H C hC
    zugig
    refine ⟨by zvohn, L41.hostWF_whole hn, by zvnmf; zvohn; omega, ?_⟩
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
  zucg

  unfold sI
  refine spec_seq ?_
  exec_block
  · omega
  by_cases h : c.nreg 170075 < c.nreg 170011
  · have hf : ztidl := by
      cases hc : C.sideBeta
      · rfl
      · have := hb.2 hc; zvnem at h; omega
    zuek
    exec_block
    refine ⟨by_omega, by config_simp; omega, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hL, hT]; unfold Chain.sideS; grind
    simp_all
  · have ht := hb.1 (by zvnem at h; omega)
    zudx
    exec_block
    refine ⟨by_omega, by config_simp; omega, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; zvncs; unfold Chain.sideS; simp_all
    simp_all

/-- **The tour offset** of the interior walk's pass. -/
theorem tauI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hL : c.nreg 170037 = L) (h89 : c.nreg 170089 = 2 * L)
    (h76 : c.nreg 170076 = (ch zta u L h1 h2).sideS (ch zta u L h1 h2).sideBeta) :
    ∃ c' k, Exec P W tauI c c' k ∧ k ≤ 8 ∧ c'.nreg 170077 = tau zta u L h1 h2 ∧
      c'.nmem = c.nmem ∧ (∀ r, r ≠ 170077 → c'.nreg r = c.nreg r) := by
  zucg

  zudq
  have hSle := (ch _ u L h1 h2).sideS_lt (ch _ u L h1 h2).sideBeta
  rw [ch_m] at hSle
  -- the start of the tour position
  obtain ⟨c₁, k₁, e₁, hk₁, a77, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztfme c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 170077 = jStart zta L ∧ (∀ r, r ≠ 170077 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    zudwv
    · have hL' : ¬ Mountain.LeftInside _ := fun h' => by
        have := hS.lb.2 h'; zvnem at h; omega
      zugss
      exec_block
      refine ztcxm
      · config_simp; zvnlm; unfold jStart; simp_all
      simp_all
    · have hL' : Mountain.LeftInside _ := hS.lb.1 (by
        zvnem at h; have := hS.lb1; omega)
      zumjm
      exec_block
      · omega
      refine ztcxm
      · config_simp; unfold jStart; simp_all
      simp_all
  have hJ : jStart zta L ≤ L := by unfold jStart; grind
  zud
  have b89 : c₁.nreg 170089 = 2 * L := by_simp_all
  have b76 : c₁.nreg 170076 = (ch _ u L h1 h2).sideS (ch _ u L h1 h2).sideBeta := by
    simp_all
  have htau : tau _ u L h1 h2 = (jStart _ L + 2 * L -
      (ch _ u L h1 h2).sideS (ch _ u L h1 h2).sideBeta) % (2 * L) := rfl
  obtain ⟨c₂, k₂, e₂, hk₂, hτ, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W
      (.seq ztiqg
        ztifg) c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
      c₂.nreg 170077 = tau zta u L h1 h2 ∧ (∀ r, r ≠ 170077 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem := by
    refine spec_seq ?_
    exec_block
    · omega
    by_cases h : jStart zta L + 2 * L -
        (ch _ u L h1 h2).sideS (ch _ u L h1 h2).sideBeta < 2 * L
    · zuek
      refine spec_skip ‹_› ztcxm
      · config_simp; rw [a77, b89, b76, htau, Nat.mod_eq_of_lt h]
      simp_all
    · zudx
      exec_block
      refine ztcxm
      · config_simp; rw [a77, b89, b76, htau, Nat.mod_eq_sub_mod by_omega,
          Nat.mod_eq_of_lt by_omega]
      · simp only [Config.nreg_mk, upd, ite_eq_right hr]
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, hτ, by_simp_all, fun r hr => ?_⟩
  simp_all

/-- **The descriptor.** -/
theorem descI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hAW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W descI c c' k ∧ k = 14 ∧ c'.nreg 170078 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      c'.nmem ztm = 0 ∧ c'.nmem ztccv = s.A₀ ∧
      c'.nmem zteep = c.nreg 170038 ∧ c'.nmem zteeq = c.nreg 170037 ∧
      c'.nmem ztllf = c.nreg 170074 ∧ c'.nmem ztllg = c.nreg 170075 ∧
      zth ∧
      (∀ r, r ≠ 170078 → r ≠ 170090 → r ≠ 170091 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
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
  decide ztekn || decide ztgxy ||
    decide (170074 ≤ r ∧ r < 170092) || Bk r
theorem wr_chain4 : wr Bchain (.seq topCh (.seq betaI (.seq sI tauI))) = true := by
  rfl

/-- The registers the state of a chain consists of. -/
def CRegs (r : ℕ) : Prop :=
  ztekm ∨ (170033 ≤ r ∧ r < 170039) ∨ (170074 ≤ r ∧ r < 170080) ∨
    r = 170089

/-- **The state after `chainI`** for the stretch of `L` edges of the interior walk from `u`. -/
structure CEnv (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (u L : ℕ) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (c : Config) : Prop where
  env : SEnv P W O s c
  hu : u < P.n
  r33 : c.nreg 170033 = u
  r37 : c.nreg 170037 = L
  r38 : c.nreg 170038 = cStart zta u L
  r74 : c.nreg 170074 = (ch zta u L h1 h2).topIdx
  r75 : c.nreg 170075 = 1 ↔ (ch zta u L h1 h2).sideBeta = true
  r75' : c.nreg 170075 ≤ 1
  r76 : c.nreg 170076 = (ch zta u L h1 h2).sideS (ch zta u L h1 h2).sideBeta
  r77 : c.nreg 170077 = tau zta u L h1 h2
  r79 : c.nreg 170079 = ztxnm % (Qof P).n
  r89 : c.nreg 170089 = 2 * L
  desc : DescOK P c.nmem (c.nreg 170078) ztwls ztm
  dlo : s.A₀ + 8 ≤ c.nreg 170078

/-- **The state of a chain survives** steps that keep its registers, the memory below the
allocator, and do not lower the allocator. -/
theorem CEnv.keep {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} {c c' : Config}
    (h : CEnv P W O s u L h1 h2 c) (hr : ∀ r, CRegs r → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    CEnv P W O s u L h1 h2 c' := by
  zumfi
  refine ⟨h.env.keep (fun r h1 h2 => k r ztec) hm ha, h.hu, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · zumyb; exact h.r33
  · zumyb; exact h.r37
  · zumyb; exact h.r38
  · zumyb; exact h.r74
  · zumyb; exact h.r75
  · zumyb; exact h.r75'
  · zumyb; exact h.r76
  · zumyb; exact h.r77
  · zumyb; exact h.r79
  · zumyb; exact h.r89
  · zumyb; exact h.desc.keep hm ha
  · zumyb; exact h.dlo

/-- **The chain of a stretch and its descriptor.** -/
theorem chainI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (hcap : L ≤ 2 ^ ztbwe) (hAW : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W chainI c c' k ∧ k ≤ 1204 * Nat.log 2 ztbtk + 2500 ∧ 14 ≤ k ∧
      CEnv P W O s u L h1 h2 c' ∧ c'.nreg 170078 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧ zth ∧
      (∀ r, Bchain r = false → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, Bchain r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zudq
  zujyn
  zucqk
  obtain ⟨c₁, k₁, e₁, hk₁, S₁, a38, a79n, a74, a79, F₁⟩ := topCh_exec c hw hS hu hL hun h1 h2 hcap
  zuiuw
  obtain ⟨c₂, k₂, e₂, hk₂, b75', b75, m₂, F₂⟩ := betaI_exec c₁ e₁.wb_right S₁ (C := C) rfl a74
    (by rw [← a79]; rfl)
  have f₂ := F₂.1
  have S₂ := S₁.keep (fun r r1 r2 => f₂ r (by
    unfold Bbeta Bk; grind))
    by_simp_all (by zuojv)
  have b37 : c₂.nreg 170037 = C.m := by
    rw [f₂ _ by_decide, f₁ _ by_decide]; exact hL
  have b74 : c₂.nreg 170074 = C.topIdx := by zuojv; omega
  obtain ⟨c₃, k₃, e₃, hk₃, d89, d76, m₃, r₃⟩ := sI_exec c₂ e₂.wb_right S₂ b37 b74 b75' b75
    ztnte
  have S₃ : ztlai := S₂.keep by_grind
    by_simp_all ztmdz
  obtain ⟨c₄, k₄, e₄, hk₄, d77, m₄, r₄⟩ := tauI_exec c₃ e₃.wb_right S₃ (h1 := h1) (h2 := h2)
    (by rw [r₃ _ by_decide by_decide]; exact b37) (by rw [d89, ch_m]) d76
  have S₄ : ztrfu := S₃.keep by_grind
    by_simp_all (by zuojw)
  have ex4 : ztiyf :=
    .seq e₁ ztcb
  have F₄ := exec_frameB ex4 wr_chain4
  have hA4 : ztgul := F₄.1 _ by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, g78, gA, g0, g1, g2, g3, g4, g5, gm, gr, grr, grm, go⟩ :=
    descI_exec c₄ e₄.wb_right S₄ by_omega
  -- register values at `c₄`
  have v := F₄.1
  have q38 : c₄.nreg 170038 = cStart zta u L := by
    zunhq; omega
  have q37 : c₄.nreg 170037 = L := by zuojx; exact hL
  have q33 : c₄.nreg 170033 = u := by zuojx; exact hu
  have q74 : c₄.nreg 170074 = C.topIdx := by
    zunor; omega
  have q75 : c₄.nreg 170075 = c₂.nreg 170075 := by
    zunor
  have q79 : c₄.nreg 170079 = c₁.nreg 170079 := by
    zunhq
  have q89 : c₄.nreg 170089 = 2 * L := by rw [r₄ _ by_decide, d89, ch_m]
  have q76 : c₄.nreg 170076 = C.sideS C.sideBeta := by zuojw; omega
  have hm4 := F₄.2.2.1
  have S₅ := S₄.keep (fun r r1 r2 => gr r by_omega by_omega by_omega
    ztu) gm by_omega
  have hal := S₄.alloc
  have ex : Exec P W chainI c c₅ _ :=
    .seq e₁ ztbq
  have keep5 := gr
  have hlog : Nat.log 2 ztbtk ≥ 0 := Nat.zero_le _
  refine ⟨c₅, _, ex, by_omega, by_omega, ⟨S₅, hun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by omega, by_omega, fun a ha => ?_, fun r hr hra => ?_, fun r hr => ?_,
    by rw [grm, F₄.2.2.2.1], by rw [go, F₄.2.2.2.2]⟩
  · zujo
  · zujo
  · zujo
  · zujo
  · zueyv
  · zueyv
  · zujo
  · zujo
  · rw [keep5 _ by_decide by_decide by_decide by_decide, q79]; omega
  · zujo
  · rw [g78, gA]
    refine descOK_of S₄.good by_omega
      (S₅.hostAt) hal by_omega g0 g1 ?_ ?_ ?_ ?_
    · omega
    · omega
    · grind
    · rw [g5, q75]; omega
  · omega
  · rw [gm a by_omega, hm4]
  · have h78 : r ≠ 170078 := fun h => by subst h; revert hr; decide
    have h90 : r ≠ 170090 := fun h => by subst h; revert hr; decide
    have h91 : r ≠ 170091 := fun h => by subst h; revert hr; decide
    rw [gr r h78 h90 h91 hra, v r hr]
  · rw [grr, F₄.2.1 r hr]
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Chain (sideE)
@[expose] public section
def cvI : Stmt :=
  .seq (block [.addN 170136 170076 170134])
  (.seq ztifh
  (.seq ztifh
  (.seq (.ifLtN 170037 170136 (block [.subN 170136 170089 170136]) .skip)
  (.seq (block [.addN 170136 170038 170136])
    (.ifLtN 170136 170010 .skip (block [.subN 170136 170136 170010]))))))

/-- The vertex `v` (the top): kind `0`. -/
def vtxV : Stmt := block [.constN 170130 0, .copyN 170131 170079]

/-- The vertex `a` (`170137`): kind `0`. -/
def vtxA : Stmt := block [.constN 170130 0, .copyN 170131 170137]

/-- The edge point: the edge `edgeOf n a a'` and the height vertex `h - 1` (`170139`). -/
def onE : Stmt :=
  .seq (block [.addN 170140 170137 170011])
  (.seq (.ifLtN 170140 170010 .skip (block [.constN 170140 0]))
  (.seq (.ifLtN 170140 170138 ztffz
      ztyzv)
    ztkqx))

/-- The general case `6 ≤ e < 2 L + 6`. -/
def genI : Stmt :=
  .seq (block [.subN 170134 140011 170133]) (.seq cvI
  (.seq ztjpk (.seq cvI
  (.seq (block [.copyN 170138 170136])
    (.ifLtN 170012 140012
      (.seq ztheb
        ztejn)
      vtxA)))))

/-- **The boundary symbolic point of the hit** `⟨140011, 140012⟩` into `170130 …`. -/
def hsI : Stmt :=
  .seq ztjpd
    (.ifLtN 140011 170133 vtxV (.ifLtN 140011 170135 genI vtxV))

/-- The registers `hsI` writes. -/
def Bhs (r : ℕ) : Bool := decide (170130 ≤ r ∧ r < 170141)
theorem wr_hsI : wr Bhs hsI = true := by_decide

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}

/-- The register facts `cvI` and `hsI` read. -/
structure HRegs (P : Polygon) (W : ℕ) (c : Config) (cs L S v : ℕ) : Prop where
  r10 : c.nreg 170010 = P.n
  r11 : c.nreg 170011 = 1
  r12 : c.nreg 170012 = 0
  r37 : c.nreg 170037 = L
  r38 : c.nreg 170038 = cs
  r76 : c.nreg 170076 = S
  r79 : c.nreg 170079 = v
  r89 : c.nreg 170089 = 2 * L
  hcs : cs < P.n
  hS : S ≤ 2 * L
  hL : 1 ≤ L
  hLn : L + 1 ≤ P.n
  hW : 256 * P.n + 16 ≤ W
theorem HRegs.keep {c c' : Config} {cs L S v : ℕ} (h : HRegs P W c cs L S v)
    (hk : ∀ r, Bhs r = false → c'.nreg r = c.nreg r) : HRegs P W c' cs L S v :=
  ⟨by zumzg; exact h.r10, by zumzg; exact h.r11,
    by zumzg; exact h.r12, by zumzg; exact h.r37,
    by zumzg; exact h.r38, by zumzg; exact h.r76,
    by zumzg; exact h.r79, by zumzg; exact h.r89, h.hcs, h.hS,
    h.hL, h.hLn, h.hW⟩
variable {c : Config}
/-- A conditional subtraction `r := r - b` if `b ≤ r`. -/
theorem condSub_exec (hw : WordsBounded W c) (r b : ℕ) :
    ∃ k, Exec P W (.ifLtN r b .skip (block [.subN r r b])) c
      { c with nreg := upd c.nreg r (if c.nreg r < c.nreg b then c.nreg r else c.nreg r - c.nreg b) }
      k ∧ k ≤ 3 :=
  exec_ite_upd c ztisj
    (fun _ => ⟨1, exec_subN_upd hw r r b, le_rfl⟩)

/-- A conditional reflection `r := b - r` if `a < r`. -/
theorem condRef_exec (hw : WordsBounded W c) (r a b : ℕ) :
    ∃ k, Exec P W (.ifLtN a r (block [.subN r b r]) .skip) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg r then c.nreg b - c.nreg r else c.nreg r) }
      k ∧ k ≤ 3 :=
  exec_ite_upd c (fun _ => ⟨1, exec_subN_upd hw r b r, by_omega⟩)
    ztisj

/-- **The vertex of `Q` at a walk vertex of the double boundary.** -/
theorem cvI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {i : ℕ} (hi : c.nreg 170134 = i) (hi2 : i ≤ 2 * L) :
    ∃ k, Exec P W cvI c { c with nreg := upd c.nreg 170136 (cVtxV P.n cs L S i) } k ∧ k ≤ 18 := by
  zuglv
  zumdf
  have hS := hR.hS
  zuiwm
  zuiwj
  have e₀ := exec_addN_upd (P := P) hw 170136 170076 170134 (by rw [hR.r76, hi]; omega)
  obtain ⟨k₁, e₁, hk₁⟩ := condSub_exec (P := P) e₀.wb_right 170136 170089
  obtain ⟨k₂, e₂, hk₂⟩ := condSub_exec (P := P) e₁.wb_right 170136 170089
  obtain ⟨k₃, e₃, hk₃⟩ := condRef_exec (P := P) e₂.wb_right 170136 170037 170089
  config_simp at e₀
  config_simp at e₁
  config_simp at e₂
  config_simp at e₃
  simp only [hR.r76, hi, hR.r89, hR.r37] at e₀ e₁ e₂ e₃
  set j := if ztcio < 2 * L then
      ztcio else
      ztcio - 2 * L with hj
  have hjm : j = mod2 L ztbat := by
    unfold mod2; grind
  have hjL : (if L < j then 2 * L - j else j) = sideE L j := by
    zumu
  have hj2 : j < 2 * L := by_grind
  have hjE : sideE L j ≤ L := by_grind
  have e₄ := exec_addN_upd (P := P) e₃.wb_right 170136 170038 170136 (by
    config_simp; rw [hR.r38, hjL]; omega)
  config_simp at e₄
  rw [hR.r38, hjL] at e₄
  rw [hjL] at e₃
  obtain ⟨k₅, e₅, hk₅⟩ := condSub_exec (P := P) e₄.wb_right 170136 170010
  config_simp at e₅
  rw [hR.r10] at e₅
  have hval : (if cs + sideE L j < P.n then cs + sideE L j else cs + sideE L j - P.n) =
      cVtxV P.n cs L S i := by
    unfold cVtxV; rw [← hjm]
    zus
    · zukp
    · zul
  rw [hval] at e₅
  refine ⟨_, .seq e₀ ztyoe, by_omega⟩

/-- The vertex `v`. -/
theorem vtxV_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W vtxV c c' k ∧ k = 2 ∧ SymPtIn c' 170130 (.vtx (c.nreg 170079)) := by
  unfold vtxV
  exec_block
  · omega
  tauto

/-- The vertex `a`. -/
theorem vtxA_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W vtxA c c' k ∧ k = 2 ∧ SymPtIn c' 170130 (.vtx (c.nreg 170137)) := by
  unfold vtxA
  exec_block
  · omega
  tauto

/-- The choice of the edge of the edge point. -/
theorem onETail_exec (c : Config) (hw : WordsBounded W c) {a a' : ℕ} (h37 : c.nreg 170137 = a)
    (h38 : c.nreg 170138 = a') (h40 : c.nreg 170140 = ztdf % P.n) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (.seq (.ifLtN 170140 170138 ztffz
      ztyzv)
      ztkqx) c c' k ∧ k ≤ 7 ∧
      SymPtIn c' 170130 ztzrz := by
  zujl
  set q := ztdf % P.n with hq
  by_cases hne : q = a'
  · have h1 : ¬ q < a' := by_omega
    have h2 : ¬ a' < q := by_omega
    zubv
    zubv
    exec_block
    · omega
    refine ⟨by_omega, by config_simp, ?_, ?_⟩
    · config_simp; rw [h37]; simp only [ShootCut.edgeOf]; simp_all
    simp
  · by_cases h1 : q < a'
    · zudd
      exec_block
      · omega
      refine ⟨by_omega, by config_simp, ?_, ?_⟩
      · config_simp; rw [h38]; simp only [ShootCut.edgeOf]; grind
      simp
    · have h2 : a' < q := by_omega
      zubv
      zudd
      exec_block
      · omega
      refine ⟨by_omega, by config_simp, ?_, ?_⟩
      · config_simp; rw [h38]; simp only [ShootCut.edgeOf]; grind
      simp

/-- **The edge point.** -/
theorem onE_exec (c : Config) (hw : WordsBounded W c) {a a' : ℕ} (h37 : c.nreg 170137 = a)
    (h38 : c.nreg 170138 = a') (h10 : c.nreg 170010 = P.n) (h11 : c.nreg 170011 = 1)
    (ha : a < P.n) (hW : P.n + 1 ≤ W) :
    ∃ c' k, Exec P W onE c c' k ∧ k ≤ 12 ∧
      SymPtIn c' 170130 ztzrz := by
  unfold onE
  refine spec_seq ?_
  exec_block
  · omega
  zujl
  by_cases hq1 : a + 1 < P.n
  · zuek
    zurc
    obtain ⟨c', k, e, hk, s'⟩ := onETail_exec (a := a) (a' := a') _ ‹_›
      by_simp_all by_simp_all
      (by config_simp; rw [h37, h11, Nat.mod_eq_of_lt hq1]) by_omega
    exact ztlvm
  · zudx
    exec_block
    · omega
    obtain ⟨c', k, e, hk, s'⟩ := onETail_exec (a := a) (a' := a') _ ‹_›
      by_simp_all by_simp_all
      (by config_simp; rw [show a + 1 = P.n by omega, Nat.mod_self]) by_omega
    exact ztlvm

/-- The general case, without the frame. -/
theorem genI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {e h : ℕ} (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (h33 : c.nreg 170133 = 6)
    (h6 : 6 ≤ e) (he2 : e < 2 * L + 6) :
    ∃ c' k, Exec P W genI c c' k ∧ k ≤ 70 ∧
      SymPtIn c' 170130 (if h = 0 ∨ h - 1 = cVtxV P.n cs L S ztbcs then
        .vtx ztyvn
        else .onEdge (ShootCut.edgeOf P.n (.vtx ztyvn)
          (.vtx (cVtxV P.n cs L S zterq))) (h - 1)) := by
  zuglv
  zuiwj
  zumdf
  zuiwm
  have kR : ∀ {c c' : Config}, HRegs P W c cs L S v →
      (∀ r, ztofk → c'.nreg r = c.nreg r) → HRegs P W c' cs L S v :=
    fun h hk => h.keep (fun r hr => hk r (by
      unfold Bhs at hr; grind))
  set a := cVtxV P.n cs L S _ with had
  set a' := cVtxV P.n cs L S _ with had'
  have ha : a < P.n := by rw [had]; unfold cVtxV; exact Nat.mod_lt _ by_omega
  -- `170134 := e - 6`
  obtain ⟨c₁, k₁, e₁, hk₁, b34, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 170134 140011 170133]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170134 = e - 6 ∧ (∀ r, r ≠ 170134 → c₁.nreg r = c.nreg r) := by
    exec_block
    simp_all
  have R₁ := kR hR (fun r hr => r₁ r by_omega)
  obtain ⟨k₂, e₂, hk₂⟩ := cvI_exec (P := P) c₁ e₁.wb_right R₁ b34 by_omega
  zue
  -- `170137 := a`, `170134 := e - 6 + 1`
  obtain ⟨c₃, k₃, e₃, hk₃, b37, b34', r₃⟩ : ∃ c₃ k₃, Exec P W
      ztjpk
      { c₁ with nreg := upd c₁.nreg 170136 a } c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 170137 = a ∧
      c₃.nreg 170134 = e - 6 + 1 ∧ (∀ r, r ≠ 170137 → r ≠ 170134 → r ≠ 170136 →
        c₃.nreg r = c₁.nreg r) := by
    exec_block
    · config_simp; zuoki; omega
    refine ⟨rfl, by config_simp, by config_simp; zuoki, fun r h1 h2 h3 => ?_⟩
    simp_all
  have R₃ := kR R₁ (fun r hr => r₃ r by_omega by_omega by_omega)
  obtain ⟨k₄, e₄, hk₄⟩ := cvI_exec (P := P) c₃ e₃.wb_right R₃ b34' by_omega
  zucc
  -- `170138 := a'`
  obtain ⟨c₅, k₅, e₅, hk₅, b38, b37', r₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 170138 170136])
      { c₃ with nreg := upd c₃.nreg 170136 a' } c₅ k₅ ∧ k₅ = 1 ∧ c₅.nreg 170138 = a' ∧
      c₅.nreg 170137 = a ∧ (∀ r, r ≠ 170138 → r ≠ 170136 → c₅.nreg r = c₃.nreg r) := by
    exec_block
    refine ⟨rfl, by config_simp, by config_simp; omega, fun r h1 h2 => ?_⟩
    simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
  have R₅ := kR R₃ (fun r hr => r₅ r by_omega by_omega)
  zuef
  have k₅' : ∀ r, ztofk → c₅.nreg r = c.nreg r := fun r hr => by
    grind
  have h12' := R₅.r12
  have hh' : c₅.nreg 140012 = h := by_grind
  -- the decision
  by_cases hv : h = 0 ∨ h - 1 = a
  · rw [ite_eq_left hv]
    -- `vtxA` (possibly after the two comparisons)
    have hA : ∃ c' k, Exec P W (.ifLtN 170012 140012
        (.seq ztheb
          ztejn) vtxA) c₅ c' k ∧ k ≤ 9 ∧
        SymPtIn c' 170130 ztpsg := by
      rcases hv with h0 | h0
      · zubv
        zucdp

      · zujue
        · zubv
          zucdp

        zudd
        refine spec_seq ?_
        exec_block
        refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        obtain ⟨c', k, e', hk, s'⟩ := vtxA_exec _ ‹_› by_omega
        refine ⟨c', k, e', by_omega, ?_⟩
        config_simp at s'; grind
    obtain ⟨c', k, e', hk, s'⟩ := hA
    exact ztdxd
  · zulql
    zugrj
    have hB : ∃ c' k, Exec P W (.ifLtN 170012 140012
        (.seq ztheb
          ztejn) vtxA) c₅ c' k ∧ k ≤ 18 ∧
        SymPtIn c' 170130 (.onEdge ztfbf zthhn) := by
      zudd
      refine spec_seq ?_
      exec_block
      have w := by_omega
      have o := onE_exec { c₅ with nreg := upd c₅.nreg 170139 _ }
        w (by config_simp; omega) (by config_simp; omega)
        (by config_simp; exact R₅.r10) (by config_simp; exact R₅.r11) ha by_omega
      obtain ⟨c', k, e', hk, s'⟩ := o
      config_simp at s'
      rw [hh', R₅.r11] at s'
      by_cases hlt : h - 1 < a
      · refine spec_ifLtN_true (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        grind
      · refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        refine spec_ifLtN_true (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        grind
    obtain ⟨c', k, e', hk, s'⟩ := hB
    exact ztdxd

/-- **The boundary symbolic point of a hit.** -/
theorem hsI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {e h : ℕ} (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (he2 : e < 2 * L + 7) :
    ∃ c' k, Exec P W hsI c c' k ∧ k ≤ 90 ∧ SymPtIn c' 170130 (hitSymV P.n cs L S v e h) ∧
      FrameB Bhs c c' := by
  zuglv
  zuiwj
  zuiwm
  obtain ⟨c₁, k₁, e₁, hk₁, a33, a35, R₁, f₁⟩ : ∃ c₁ k₁, Exec P W
      ztjpd c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 170133 = 6 ∧ c₁.nreg 170135 = 2 * L + 6 ∧ HRegs P W c₁ cs L S v ∧
      (∀ r, r ≠ 170133 → r ≠ 170135 → c₁.nreg r = c.nreg r) := by
    exec_block
    · omega
    · config_simp; zuoxk; omega
    refine ⟨rfl, by config_simp, by config_simp; zuoxk, hR.keep ztez,
      fun r h1 h2 => ?_⟩
    · unfold Bhs at hr; zvnan at hr
      zufx
    simp_all
  zud
  have b11 : c₁.nreg 140011 = e := by_simp_all
  have b12 : c₁.nreg 140012 = h := by_simp_all
  suffices hX : ∃ c' k, Exec P W hsI c c' k ∧ k ≤ 90 ∧
      SymPtIn c' 170130 _ by
    obtain ⟨c', k, ex, hk, s'⟩ := hX
    exact ⟨c', k, ex, hk, s', exec_frameB ex wr_hsI⟩
  unfold hsI hitSymV
  zugar
  zujsu
  · zudd
    zucxm

    rw [ite_eq_left ztqbd]
    zuigt

  zubv
  by_cases h7 : e < 2 * L + 6
  · zudd
    obtain ⟨c₂, k₂, e₂, hk₂, s₂⟩ := genI_exec c₁ w₁ R₁ b11 b12 a33 by_omega h7
    grind
  · zubv
    zucxm

    zubek
    zuigt
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def takeI : Stmt :=
  block [.constN 170070 1, .copyN 170071 170130, .copyN 170072 170131, .copyN 170073 170132]

/-- `170141 := 1` iff the new hit (`170130`) is nearer than the best one (`170071`) in the
direction of the ray. -/
def cmpI : Stmt :=
  .ifLtN 170008 170011 ztpcm
    (.ifLtN 170011 170008 ztpcm
      (kbit 170130 170071 170130 0 170141))

/-- **The update of the running best hit** after a shot. -/
def updI : Stmt :=
  .ifLtN 140010 170011 .skip
    (.ifLtN 170011 140010 .skip
      (.seq hsI
        (.ifLtN 170070 170011 takeI
          (.seq cmpI (.ifLtN 170012 170141 takeI .skip)))))

/-- The registers `updI` writes. -/
def Bupd (r : ℕ) : Bool :=
  decide ztnex || decide (170130 ≤ r ∧ r < 170142) || Bk r
theorem wr_updI : wr Bupd updI = true := by
  rfl

/-! ## The running best hit -/

/-- **The running best hit** describes the first hit of the ray from `z` in direction `σ` on
`S`. -/
def BestI (P : Polygon) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) : Prop :=
  c.nreg 170070 ≤ 1 ∧
    (c.nreg 170070 = 1 → ∃ sb t, SymPtIn c 170071 sb ∧ BSym zta sb ∧ FirstHit S z σ t ∧
      sb.eval zta = rayPt z σ t) ∧
    (c.nreg 170070 ≠ 1 → NoHit S z σ)
theorem BestI.keep {P : Polygon} {c c' : Config} {S : Set Point} {z : Point} {σ : ℝ}
    (h : BestI P c S z σ) (hk : ∀ r, 170070 ≤ r → r < 170074 → c'.nreg r = c.nreg r) :
    BestI P c' S z σ := by
  zuboy
  have k0 : c'.nreg 170070 = c.nreg 170070 := hk _ le_rfl by_norm_num
  refine ztiwf
  obtain ⟨sb, t, hs, hb, hfh, hev⟩ := h1 by_omega
  exact ⟨sb, t, symPtIn_of_eq hs (fun j h1 h2 => hk j by_omega by_omega), hb, hfh, hev⟩

/-- The empty best: no hit on the empty set. -/
theorem bestI_empty {P : Polygon} {c : Config} {z : Point} {σ : ℝ} (h : c.nreg 170070 = 0) :
    BestI P c ∅ z σ :=
  ⟨by_omega, fun hf => by_omega, fun _ t _ hm => hm⟩

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
/-- **Taking the new hit.** -/
theorem takeI_exec (hw : WordsBounded W c) (hW : 1 ≤ W) {sn : SymPt}
    (hs : SymPtIn c 170130 sn) :
    ∃ c' k, Exec P W takeI c c' k ∧ k = 4 ∧ c'.nreg 170070 = 1 ∧ SymPtIn c' 170071 sn ∧
      FrameB (fun r => decide ztnex) c c' := by
  unfold takeI
  exec_block
  · omega
  refine ⟨rfl, by config_simp, NFLoc.symPtIn_copy hs (by config_simp) (by config_simp)
    (by config_simp), ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
  zubzq
  zufx

/-- **The comparison of two hits on one ray.** -/
theorem cmpI_exec (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (h11 : c.nreg 170011 = 1) {sn sb : SymPt} (hsn : SymPtIn c 170130 sn)
    (hsb : SymPtIn c 170071 sb) (hln : sn.Lt P.n) (hlb : sb.Lt P.n) {z : Point} {t₁ t₂ : ℝ}
    (hen : sn.eval zta = rayPt z ztbahp t₂)
    (heb : sb.eval zta = rayPt z ztbahp t₁) :
    ∃ c' k, Exec P W cmpI c c' k ∧ k ≤ 245 ∧ c'.nreg 170141 ≤ 1 ∧
      (c'.nreg 170141 = 1 ↔ t₂ < t₁) ∧ FrameB (SweepPrim.Bkb 170141) c c' := by
  unfold cmpI
  by_cases h1 : c.nreg 170008 < c.nreg 170011
  · have hd : ztzqe := by unfold dirOf; simp_all
    obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170071) (b := 170130)
      (d := 170071) (op := 0) (dst := 170141) by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num hlb hln hlb hsb hsn hsb
    refine ⟨c', _, .ifLtN_true h1 e, by_omega, b1, ?_, F⟩
    zuczp

  · by_cases h2 : c.nreg 170011 < c.nreg 170008
    · have hd : ztzqe := by unfold dirOf; grind
      obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170071) (b := 170130)
        (d := 170071) (op := 0) (dst := 170141) by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num hlb hln hlb hsb hsn hsb
      refine ⟨c', _, .ifLtN_false h1 ztnai, by_omega, b1, ?_, F⟩
      zuczp

    · have hd : dirOf zthul = 1 := by unfold dirOf; grind
      obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170130) (b := 170071)
        (d := 170130) (op := 0) (dst := 170141) by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num hln hlb hln hsn hsb hsn
      refine ⟨c', _, .ifLtN_false h1 ztjdj, by_omega, b1, ?_, F⟩
      rw [b2, SignTest, heb, hen, hd]; simp

/-- **The update of the running best hit** after a shot at a chain arc `A` of the chain `C`
(the shooter's answer in `140010 … 140012`). -/
theorem updI_exec (hw : WordsBounded W c) (hG : GoodEnv P) {cs L S v : ℕ}
    (hR : HRegs P W c cs L S v) {C : Chain} (hC : C.P = Qof P) (hCs : C.s = cs) (hCm : C.m = L)
    (hCS : C.sideS C.sideBeta = S) (hv : v = ztwi % (Qof P).n) {e h : ℕ}
    (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (he2 : c.nreg 140010 = 1 → e < 2 * L + 7)
    {A Sp : Set Point} {z : Point} {σ : ℝ} (hσ : σ = dirOf zthul) (hAC : A ⊆ C.set)
    (hhit : c.nreg 140010 = 1 → ∃ t, FirstHit A z σ t ∧
      ProperPos ztc zta P.n ztcq ∧ (chainModel C).pos zta ztcq = rayPt z σ t)
    (hno : c.nreg 140010 ≠ 1 → NoHit A z σ) (hB : BestI P c Sp z σ) :
    ∃ c' k, Exec P W updI c c' k ∧ k ≤ 600 ∧ BestI P c' ztjmx z σ ∧ FrameB Bupd c c' := by
  zuglv
  zudq
  have hD : ztxpn := (goodShear_epsOf hG.2).2.1
  suffices hX : ∃ c' k, Exec P W updI c c' k ∧ k ≤ 600 ∧ BestI P c' ztjmx z σ by
    obtain ⟨c', k, ex, hk, b⟩ := hX
    exact ⟨c', k, ex, hk, b, exec_frameB ex wr_updI⟩
  zugpi
  -- no hit
  have nohit : c.nreg 140010 ≠ 1 → BestI P c ztjmx z σ := fun hf => by
    have hn := hno hf
    refine ⟨hb1, fun h1 => ?_, fun h1 => noHit_union (hb3 h1) hn⟩
    obtain ⟨sb, t, hs, hbs, hfh, hev⟩ := hb2 h1
    exact ⟨sb, t, hs, hbs, firstHit_noHit hfh hn, hev⟩
  unfold updI
  by_cases f1 : c.nreg 140010 < c.nreg 170011
  · refine spec_ifLtN_true f1 (spec_skip hw ⟨by_omega, nohit (by rw [hR.r11] at f1; omega)⟩)
  refine spec_ifLtN_false f1 ?_
  by_cases f2 : c.nreg 170011 < c.nreg 140010
  · refine spec_ifLtN_true f2 (spec_skip hw ⟨by_omega, nohit (by rw [hR.r11] at f2; omega)⟩)
  refine spec_ifLtN_false f2 ?_
  have hf : c.nreg 140010 = 1 := by rw [hR.r11] at f1 f2; omega
  replace he2 := he2 hf
  obtain ⟨t₂, hA, hp, hpos⟩ := hhit hf
  -- the symbolic point of the hit
  obtain ⟨c₁, k₁, e₁, hk₁, s₁, F₁⟩ := hsI_exec (P := P) c hw hR he hh he2
  have hv' : v = ztwi % C.P.n := by_simp_all
  have hcm : ztdh := chainModel_n C
  have hsym := hitSym_ch (C := C) hv' (e := e) (h := h) by_omega
  rw [hCs, hCm, show sSV C.sideBeta C.topIdx L = S by rw [← hCS]; unfold sSV Chain.sideS; rw [hCm],
    hC, hQ] at hsym
  have hmem : (chainModel C).pos C.P ztcq ∈ C.set := by
    rw [hC, hpos]; exact hAC hA.2.1
  have hDC : ztrfm := by_simp_all
  have hpC : ProperPos ztc C.P C.P.n ztcq := by
    simp_all
  obtain ⟨hbsym, hev⟩ := hitSym_spec C hDC hpC by_omega hmem
  rw [hsym, hC] at hbsym hev
  zvnbl at hev
  set sn := hitSymV P.n cs L S v e h with hsn
  have hlt : sn.Lt P.n := by have := hbsym.lt; simp_all
  zud
  have f₁ : ∀ r, Bhs r = false → c₁.nreg r = c.nreg r := F₁.1
  zugar
  have b70 : c₁.nreg 170070 = c.nreg 170070 := f₁ _ by_decide
  have b11 : ztupz := by zuokj; omega
  by_cases g : c₁.nreg 170070 < c₁.nreg 170011
  · -- no best yet: take the new hit
    have hb0 : c.nreg 170070 ≠ 1 := by_omega
    zumjr
    obtain ⟨c₂, k₂, e₂, hk₂, a70, s₂, -⟩ := takeI_exec (P := P) c₁ w₁ by_omega s₁
    refine ⟨c₂, k₂, e₂, by_omega, by_omega, fun _ => ⟨sn, t₂, s₂, hbsym, ?_, hev⟩,
      fun h => absurd a70 h⟩
    exact noHit_firstHit (hb3 hb0) hA
  zumjk
  have hb1' : c.nreg 170070 = 1 := by_omega
  obtain ⟨sb, t₁, hsb, hbsb, hfh, hevb⟩ := hb2 hb1'
  have hsb₁ : SymPtIn c₁ 170071 sb := symPtIn_of_eq hsb (fun j h1 h2 => f₁ j (by
    unfold Bhs; grind))
  have hltb : sb.Lt P.n := by have := hbsb.lt; simp_all
  have d8 : c₁.nreg 170008 = c.nreg 170008 := f₁ _ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, b41, i41, F₂⟩ := cmpI_exec (P := P) c₁ w₁ hG by_omega b11 s₁ hsb₁
    hlt hltb (z := z) (t₁ := t₁) (t₂ := t₂) by_simp_all
    by_simp_all
  have f₂ : ∀ r, 10500 ≤ r → r ≠ 170141 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega)
  zue
  zulon
  have c12 : ztlxz := by
    rw [f₂ _ by_norm_num by_norm_num, f₁ _ by_decide]; exact hR.r12
  by_cases g2 : c₂.nreg 170012 < c₂.nreg 170141
  · have ht : t₂ < t₁ := i41.1 by_omega
    zumjt
    have s₂ : SymPtIn c₂ 170130 sn := symPtIn_of_eq s₁ (fun j h1 h2 => f₂ j by_omega by_omega)
    obtain ⟨c₃, k₃, e₃, hk₃, a70, s₃, -⟩ := takeI_exec (P := P) c₂ w₂ by_omega s₂
    refine ⟨c₃, k₃, e₃, by_omega, by_omega, fun _ => ⟨sn, t₂, s₃, hbsym, ?_, hev⟩,
      fun h => absurd a70 h⟩
    zuoes
    exact firstHit_min hA hfh ht.le
  · have ht : ¬ t₂ < t₁ := fun h => g2 by_grind
    refine spec_ifLtN_false g2 (spec_skip w₂ ?_)
    have k70 : ∀ r, 170070 ≤ r → r < 170074 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
      have hb : Bhs r = false := by unfold Bhs; grind
      rw [f₂ r by_omega by_omega, f₁ r hb]
    zubsc
    have hB' : BestI P c ztjmx z σ := ⟨hb1, fun _ => ⟨sb, t₁, hsb, hbsb,
      firstHit_min hfh hA ztwak, hevb⟩,
      fun h => absurd hb1' h⟩
    exact hB'.keep k70
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
theorem frameIO_of_frameB {B : ℕ → Bool} (hB : ∀ r, B r = true → bandOf r ∈ ioBands ∧ r ≠ ALLOC)
    {c c' : Config} (h : FrameB B c c') (k : ℕ) : Frame ioBands c c' k := by
  have hA : ztble := h.1 _ (by
    grind)
  refine ⟨fun r hr _ => h.1 r ?_, fun r hr => h.2.1 r ?_, fun a _ => by zunrv,
    fun a _ => by zuoxl, h.2.2.2.2, by zvmze, by_omega⟩
  · grind
  grind

/-- Registers of band `17` or of the kernel are in the adapter's bands. -/
theorem io_of_band {r : ℕ} (h : ztnes ∨ ztcko ∨
    (140000 ≤ r ∧ r < 150000)) : bandOf r ∈ ioBands ∧ r ≠ ALLOC := by
  zujfu

  zude
  · zuezj
  · zuezh
  · zuezi

/-! ## The program -/

/-- The shooter's inputs other than the arc ends. -/
def shSetL : List ztw :=
  [ztsre, ztsrf, ztsrg, ztsrh, ztsri,
    ztsrj, ztsrk]

/-- **One shot at a chain arc** (its ends in `140001 … 140004`). -/
def shotI (sh : Stmt) : Stmt := .seq ztqea (.seq sh updI)

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
theorem shSet_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c', Exec P W ztqea c c' 7 ∧ c'.nreg 140000 = c.nreg 170078 ∧
      c'.nreg 140005 = c.nreg 170020 ∧ c'.nreg 140006 = c.nreg 170021 ∧
      c'.nreg 140007 = c.nreg 170022 ∧ c'.nreg 140008 = c.nreg 170008 ∧
      c'.nreg 140009 = c.nreg 170009 ∧ c'.nreg 140013 = c.nreg 170013 ∧
      (∀ r, r ≠ 140000 → (r < 140005 ∨ 140009 < r) → r ≠ 140013 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) shSetL c hw
    by_decide
    by_decide
  refine ⟨c', e, h1 ztsre by_decide, h1 ztsrf by_decide,
    h1 ztsrg by_decide, h1 ztsrh by_decide,
    h1 ztsri by_decide, h1 ztsrj by_decide,
    h1 ztsrk by_decide, fun r r1 r2 r3 => h2 r ?_, h3, h4, h5, h6⟩
  simp only [shSetL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **The context of the up-phase data** at the allocator, from the static environment. -/
theorem SEnv.ctx {c : Config} (hS : SEnv P W O s c) :
    (gradeCtx O).holds P c.nmem s.h ztm ∧
      s.γ ≤ (gradeCtx O).cap P c.nmem s.h := by
  have hloc : (gradeCtx O).holds P c.nmem s.h s.A₀ :=
    (gradeCtx O).local_ P s.m₀ c.nmem s.h s.A₀ (fun a ha => (hS.mem a ha).symm) hS.grade
  refine ⟨(gradeCtx O).mono P _ _ _ _ (by have := hS.alloc; omega) hloc, ?_⟩
  have hh := (ShootCut.grade_low hS.grade).1
  show s.γ ≤ 2 ^ (c.nmem s.h - 1)
  rw [hS.mem _ by_omega]
  exact hS.cap

/-- **One shot at a chain arc.** -/
theorem shotI_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ (Qof P).n} (hC : CEnv P W O s u L h1 h2 c)
    {sa ea : WPos} {Ap Sp : Set Point}
    (ha1 : c.nreg 140001 = sa.edge) (ha2 : c.nreg 140002 = sa.hgt)
    (ha3 : c.nreg 140003 = ea.edge) (ha4 : c.nreg 140004 = ea.hgt)
    (harc : CArc zta ztwls sa ea s.γ Ap)
    (hAC : Ap ⊆ (ch zta u L h1 h2).set)
    (ho1 : |(s.o.eval zta).1| ≤ Jordan.coordBound zta)
    (ho2 : |(s.o.eval zta).2| ≤ Jordan.coordBound zta) (hol : s.o.Lt P.n)
    (hoA : s.o.eval zta ∉ Ap)
    (hB : BestI P c Sp ztxah ztfhd)
    (hroom : c.nreg ALLOC + F s.γ + 700 ≤ W) :
    ∃ c' k, Exec P W ztkey c c' k ∧ k ≤ F s.γ + 700 ∧
      BestI P c' (Sp ∪ Ap) ztxah ztfhd ∧ CEnv P W O s u L h1 h2 c' ∧
      Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → Bupd r = false → c'.nreg r = c.nreg r) := by
  zuhxl

  zudq
  zudyq

  -- the inputs
  obtain ⟨c₁, e₁, i0, i5, i6, i7, i8, i9, i13, r₁, rr₁, m₁, rm₁, o₁⟩ := shSet_exec (P := P) c hw
  zud
  have k₁ : ztkom := fun r hr =>
    r₁ r by_omega by_omega by_omega
  have F₁ : Frame ioBands c c₁ 7 := by
    refine frameIO_of_frameB (B := fun r => decide ztnei)
      (fun r hr => io_of_band (Or.inr ztbmd)) ⟨fun r hr => ?_,
        fun r _ => by zunkd, m₁, rm₁, o₁⟩ 7
    grind
  have S₁ : zteeb := hS.keep (fun r h1 h2 => k₁ r h1) ztfrk
    ztbvs
  have D₁ : DescOK P c₁.nmem (c₁.nreg 140000) C ztbmq := by
    rw [i0, m₁, r₁ _ by_decide by_decide by_decide]; exact hC.desc
  obtain ⟨hMD, hMWF, hReg⟩ := D₁
  zuicn
  obtain ⟨sP, eP, sE, eE, sI', eI, hwt, hset⟩ := harc
  have horg : OriginIn c₁ ztbpu ztuvr := by
    show SymPtIn c₁ 140005 s.o
    exact NFLoc.symPtIn_copy hS.org i5 i6 i7
  have hinner : (chainModel C).InnerPt ztxah :=
    innerPt_chain C by_tauto by_tauto
  have b1 : c₁.nreg 140001 = sa.edge := by_simp_all
  have b2 : c₁.nreg 140002 = sa.hgt := by_simp_all
  have b3 : c₁.nreg 140003 = ea.edge := by_simp_all
  have b4 : c₁.nreg 140004 = ea.hgt := by_simp_all
  have e1 : rd c₁ bShoot 1 = sa.edge := b1
  have e2 : rd c₁ bShoot 2 = sa.hgt := b2
  have e3 : rd c₁ bShoot 3 = ea.edge := b3
  have e4 : rd c₁ bShoot 4 = ea.hgt := b4
  have hsa : (⟨c₁.nreg 140001, c₁.nreg 140002⟩ : WPos) = sa := by_simp_all
  have hea : (⟨c₁.nreg 140003, c₁.nreg 140004⟩ : WPos) = ea := by rw [b3, b4]
  have h9 : c₁.nreg 140009 = s.γ := by zuoxa; exact hS.r9
  have h13 : c₁.nreg 140013 = s.h := by zuoxb; exact hS.r13
  have h8 : c₁.nreg 140008 = s.dir := by rw [i8]; exact hS.r8
  -- the chain shooter
  obtain ⟨c₂, k₂, e₂, hk₂, hpost, F₂⟩ := hsh P W c₁ w₁ ⟨hG, hW,
    by show (gradeCtx O).holds P c₁.nmem ztvmn ztbmq; grind,
    by show c₁.nreg 140009 ≤ (gradeCtx O).cap P c₁.nmem ztvmn; grind,
    hMWF, hReg, chainModel C, hMD, okModel_sub hG,
    by grind,
    by grind,
    by omega,
    by omega,
    by grind,
    by grind,
    by show _ ≤ c₁.nreg 140009; grind,
    .sym s.o, hol, horg, Or.inr ⟨hinner, fun x hx => by cases hx⟩,
    by show s.o.eval zta ∉ _; grind⟩
    (by show c₁.nreg ALLOC + F (c₁.nreg 140009) ≤ W
        rw [h9, r₁ _ by_decide by_decide by_decide]; omega)
  have hp := hpost ztc ztuvr hMD horg
  have e8 : rd c₁ bShoot 8 = s.dir := h8
  rw [e1, e2, e3, e4, hset, e8] at hp
  obtain ⟨hhit, hno⟩ := hp
  zue
  -- the registers survive the shooter
  have g₂ : zthph := fun r h1 h2 =>
    F₂.1 r ztggs
      ztu
  zugll
  have C₂ : CEnv P W O s u L h1 h2 c₂ := (hC.keep (fun r hr => by
      zuokd) (fun a _ => by zvmxn)
      ztbvs).keep
    ztyji
    F₂.2.2.1 hA₂
  have S₂ := C₂.env
  have hR₂ : HRegs P W c₂ (cStart zta u L) L ztboi
      ((cStart zta u L + C.topIdx) % (Qof P).n) := ⟨S₂.r10, S₂.r11, S₂.r12, C₂.r37,
    C₂.r38, C₂.r76, C₂.r79, C₂.r89, by rw [← qn']; exact cStart_lt (by rw [qn']; exact C₂.hu),
    by have := C.sideS_lt C.sideBeta; tauto, h1,
    by omega, by_tauto⟩
  have hB₂ : BestI P c₂ Sp ztxah ztfhd := (hB.keep (fun r h1 h2 =>
    k₁ r by_omega)).keep (fun r h1 h2 => g₂ r by_omega by_omega)
  have d8 : c₂.nreg 170008 = s.dir := S₂.r8
  -- the update
  have hcm : (chainModel C).W.n = 2 * L + 7 := cm_n'
  obtain ⟨c₃, k₃, e₃, hk₃, hB₃, F₃⟩ := updI_exec (P := P) c₂ w₂ hG hR₂ (C := C) ch_P rfl ch_m rfl
    rfl (e := c₂.nreg 140011) (h := c₂.nreg 140012) rfl rfl
    (fun hf => by obtain ⟨_, _, _, hlt, _⟩ := hhit hf; rw [hcm] at hlt; tauto)
    (A := Ap) (Sp := Sp) (z := s.o.eval zta) (by rw [d8]) hAC
    (fun hf => by
      obtain ⟨t, hft, hpp, hlt, hpos⟩ := hhit hf
      exact ⟨t, hft, hpp, hpos⟩) hno hB₂
  have f₃ : ∀ r, Bupd r = false → c₃.nreg r = c₂.nreg r := F₃.1
  have ex : Exec P W ztkey c c₃ (7 + zttl) := .seq e₁ ztcr
  have hk₂' : k₂ ≤ F s.γ := by have := hk₂; simp only [rd, bandReg] at this; zuorp; exact this
  have F₃' : ztmtf := frameIO_of_frameB (B := Bupd) (fun r hr => io_of_band (by
    simp only [Bupd, Bk, Bool.or_eq_true, decide_eq_true_eq] at hr; omega)) F₃ k₃
  have F₂' : ztmte := F₂.mono oracleBands_sub_io le_rfl
  refine ⟨c₃, _, ex, by_omega, hB₃, C₂.keep (fun r hr => f₃ r (by
      unfold CRegs at hr; zunov; omega))
      (fun a _ => by rw [F₃.2.2.1]) (by rw [f₃ _ by_decide]),
    ((F₁.trans F₂').trans F₃').mono by_simp by_omega, fun r h1 h2 hr => ?_⟩
  rw [f₃ r hr, g₂ r h1 h2, k₁ r h1]
end exec
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)
@[expose] public section
def arcOne : Stmt :=
  block [.constN 170133 6, .addN 140001 170133 170077, .copyN 140002 170034,
    .addN 140003 140001 170035, .copyN 140004 170036]

/-- The first of two chain arcs: `⟨6 + τ, sh⟩ … ⟨2 L + 6, 0⟩`. -/
def arcTwoA : Stmt :=
  block [.constN 170133 6, .addN 140001 170133 170077, .copyN 140002 170034,
    .addN 140003 170089 170133, .constN 140004 0]

/-- The second of two chain arcs: `⟨6, 0⟩ … ⟨6 + (ee - (2 L - τ)), eh⟩`. -/
def arcTwoB : Stmt :=
  block [.constN 170133 6, .copyN 140001 170133, .constN 140002 0, .subN 170142 170089 170077,
    .subN 170143 170035 170142, .addN 140003 170133 170143, .copyN 140004 170036]

/-- **A sub-query of the interior shooter.** -/
def sqS (sh : Stmt) : Stmt :=
  .seq chainI (.ifLtN 170037 170077
    (.seq arcTwoA (.seq ztkey (.seq arcTwoB ztkey)))
    (.seq arcOne ztkey))

/-- The registers of band `17` a sub-query writes. -/
def BSQ (r : ℕ) : Bool :=
  decide ztekn || decide ztnew ||
    decide (170130 ≤ r ∧ r < 170144)

/-- The registers an arc block writes. -/
def Barc (r : ℕ) : Bool :=
  decide ztnei || decide (r = 170133 ∨ r = 170142 ∨ r = 170143)
theorem wr_arcOne : wr Barc arcOne = true := by_decide
theorem wr_arcTwoA : wr Barc arcTwoA = true := by_decide
theorem wr_arcTwoB : wr Barc arcTwoB = true := by_decide
theorem barc_io {r : ℕ} (h : Barc r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band (by simp only [Barc, Bool.or_eq_true, decide_eq_true_eq] at h; omega)

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
variable (c : Config)
theorem arcOne_exec (hw : WordsBounded W c) {τ sh ee eh : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (hW : 6 + τ + ee ≤ W) :
    ∃ c' k, Exec P W arcOne c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧ c'.nreg 140002 = sh ∧
      c'.nreg 140003 = 6 + τ + ee ∧ c'.nreg 140004 = eh ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcOne c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧
      c'.nreg 140002 = sh ∧ c'.nreg 140003 = 6 + τ + ee ∧ c'.nreg 140004 = eh by
    zuxk
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcOne⟩
  unfold arcOne
  exec_block
  · omega
  · config_simp; omega
  · simp_all
  simp_all
theorem arcTwoA_exec (hw : WordsBounded W c) {τ sh L : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h89 : c.nreg 170089 = 2 * L)
    (hW : 2 * L + 6 ≤ W) (hτ : 6 + τ ≤ W) :
    ∃ c' k, Exec P W arcTwoA c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧ c'.nreg 140002 = sh ∧
      c'.nreg 140003 = 2 * L + 6 ∧ c'.nreg 140004 = 0 ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoA c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧
      c'.nreg 140002 = sh ∧ c'.nreg 140003 = 2 * L + 6 ∧ c'.nreg 140004 = 0 by
    zuxk
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcTwoA⟩
  unfold arcTwoA
  exec_block
  · omega
  · simp_all
  · simp_all
  · omega
  simp_all
theorem arcTwoB_exec (hw : WordsBounded W c) {τ ee eh L : ℕ}
    (h77 : c.nreg 170077 = τ) (h35 : c.nreg 170035 = ee) (h36 : c.nreg 170036 = eh)
    (h89 : c.nreg 170089 = 2 * L) (hW : 6 + ee ≤ W) :
    ∃ c' k, Exec P W arcTwoB c c' k ∧ k = 7 ∧ c'.nreg 140001 = 6 ∧ c'.nreg 140002 = 0 ∧
      c'.nreg 140003 = 6 + ztxwk ∧ c'.nreg 140004 = eh ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoB c c' k ∧ k = 7 ∧ c'.nreg 140001 = 6 ∧
      c'.nreg 140002 = 0 ∧ c'.nreg 140003 = 6 + ztxwk ∧ c'.nreg 140004 = eh by
    zuxk
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcTwoB⟩
  unfold arcTwoB
  exec_block
  · omega
  · omega
  · config_simp; omega
  simp_all

/-- The frame of `chainI`. -/
theorem frame_chainI {c c' : Config} {k : ℕ} (hk : 14 ≤ k) (hA : c'.nreg ALLOC = c.nreg ALLOC + 6)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hr : ∀ r, Bchain r = false → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : ∀ r, Bchain r = false → c'.rreg r = c.rreg r) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : Frame ioBands c c' k := by
  have hB : ∀ r, Bchain r = true → bandOf r ∈ ioBands := fun r h => (io_of_band (by
    simp only [Bchain, Bk, Bool.or_eq_true, decide_eq_true_eq] at h; omega)).1
  refine ⟨fun r hr' ha => ?_, fun r hr' => ?_, hm, by_simp_all, ho, by_omega,
    by omega⟩
  · grind
  grind

/-- The subarc's offsets: its end offset is at most `L`. -/
theorem sub_y_le {Q : Polygon} {u L sh ee eh : ℕ} (h : SubOK Q u L sh ee eh) :
    (ee : ℝ) + (interiorModel Q).param Q ztuh ≤ L := by
  rcases h.hee with ⟨h0, h1⟩ | ⟨h0, h1, -⟩
  · simp_all
  · have := h.he.2.1
    have : (ee : ℝ) + 1 = L := by exact_mod_cast h1
    linarith

/-- **A sub-query of the interior shooter.** -/
theorem sqS_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F ztsy OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) {u L sh₀ ee eh : ℕ}
    (h33 : c.nreg 170033 = u) (h34 : c.nreg 170034 = sh₀) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h37 : c.nreg 170037 = L)
    (hsub : SubOK zta u L sh₀ ee eh) (hLγ : L ≤ s.γ)
    (ho1 : |(s.o.eval zta).1| ≤ Jordan.coordBound zta)
    (ho2 : |(s.o.eval zta).2| ≤ Jordan.coordBound zta) (hol : s.o.Lt P.n)
    (hoA : s.o.eval zta ∉ oset ztwsc u
      ztynr
      ztyer)
    {Sp : Set Point} (hB : BestI P c Sp ztxah ztfhd)
    (hroom : c.nreg ALLOC + 2 * F s.γ + 1204 * Nat.log 2 ztbtk + 4500 ≤ W) :
    ∃ c' k, Exec P W ztibb c c' k ∧ k ≤ 2 * F s.γ + 1204 * Nat.log 2 ztbtk + 4500 ∧
      BestI P c' (Sp ∪ oset ztwsc u
        ztynr
        ztyer)
        ztxah ztfhd ∧ SEnv P W O s c' ∧ Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → BSQ r = false → c'.nreg r = c.nreg r) := by
  zudq
  zucg

  zucgd

  zufpi
  set y := (ee : ℝ) + (interiorModel _).param _ ztbqv with hy
  zullr
  zucqk
  have hsubC : oset _ u x y ⊆ C.set := oset_sub_set hu h1 h2 hyL
  -- the chain
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', C₁, d78, dA, dm, dr, drr, drm, dout⟩ := chainI_exec c hw hS h33 h37
    by_omega h1 h2 hcap by_omega
  zufsu
  zud
  have g₁ : ∀ r, 170000 ≤ r → r < 180000 → BSQ r = false → c₁.nreg r = c.nreg r :=
    fun r r1 r2 hr => dr r (by
      zucqq
      zumzr; omega)
      ztu
  have hB₁ : BestI P c₁ Sp _ _ := hB.keep (fun r r1 r2 => dr r
    (by zumzr; omega)
    ztu)
  zumd

  -- the arc blocks keep the chain state and the best hit
  have keepArc : ∀ {d d' : Config}, FrameB Barc d d' → CEnv P W O s u L h1 h2 d →
      CEnv P W O s u L h1 h2 d' := fun F hC => hC.keep (fun r hr => F.1 r (by
        unfold CRegs at hr; zunfd; omega))
      ztbmr zthen
  have keepArcB : ∀ {d d' : Config} {S' : Set Point}, FrameB Barc d d' →
      BestI P d S' _ _ →
      BestI P d' S' ztxah ztfhd := fun F hb => hb.keep (fun r r1 r2 =>
        F.1 r (by zunfd; omega))
  have bandArc : ∀ {d d' : Config}, FrameB Barc d d' → ∀ r, 170000 ≤ r → r < 180000 →
      BSQ r = false → d'.nreg r = d.nreg r := fun F r r1 r2 hr => F.1 r (by
        zucqq
        zunfd; omega)
  have bandShot : ∀ {d d' : Config}, (∀ r, 170000 ≤ r → r < 180000 → Bupd r = false →
      d'.nreg r = d.nreg r) → ∀ r, 170000 ≤ r → r < 180000 → BSQ r = false →
      d'.nreg r = d.nreg r := fun F r r1 r2 hr => F r r1 r2 (by
        zucqq
        zunov; omega)
  zufrl
  · -- one chain arc
    have hb : ztrhm := by zunge; omega
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, Fa⟩ := arcOne_exec c₁ w₁ C₁.r77 b34 b35 b36
      by_omega
    zudmu
    zuixm
    obtain ⟨c₃, k₃, e₃, hk₃, hB₃, C₃, F₃, g₃⟩ := shotI_exec hsh c₂ e₂.wb_right C₂
      a1 a2 a3 a4 harc hsubC ho1 ho2 hol hoA zttqq (by
        zunyt; omega)
    have ex : Exec P W ztibb c c₃ _ :=
      .seq e₁ (.ifLtN_false hb ztcr)
    zuiup
    refine ⟨c₃, _, ex, by_omega, hB₃, C₃.env, ((F₁.trans Fa').trans F₃).mono by_simp
      by_omega, fun r r1 r2 hr => ?_⟩
    rw [bandShot g₃ r r1 r2 hr, bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]
  · -- two chain arcs meeting at the top
    zumis
    have hb : ztsgc := by zunge; exact hs
    zufyd
    set L₁ := 2 * L - tau _ u L h1 h2 with hL₁
    zucat
    have hx1 : x ≤ (L₁ : ℝ) := by
      have := hsub.hs.2.1
      have : ztiwy := by exact_mod_cast by_grind
      linarith
    have hL₁y : (L₁ : ℝ) ≤ y := by
      zuiuj
      have := hsub.he.1
      linarith
    have hU := oset_union ztwsc u hx1 hL₁y
    have sA : oset _ u x L₁ ⊆ C.set :=
      (oset_mono _ _ le_rfl hL₁y).trans hsubC
    have sB : oset _ u L₁ y ⊆ C.set :=
      (oset_mono _ _ hx1 le_rfl).trans hsubC
    have oA : s.o.eval _ ∉ oset _ u x L₁ := fun h =>
      hoA (oset_mono _ _ le_rfl hL₁y h)
    have oB : s.o.eval _ ∉ oset _ u L₁ y := fun h =>
      hoA (oset_mono _ _ hx1 le_rfl h)
    -- the first arc
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, Fa⟩ := arcTwoA_exec c₁ w₁ C₁.r77 b34 C₁.r89
      by_omega by_omega
    zudmu
    obtain ⟨c₃, k₃, e₃, hk₃, hB₃, C₃, F₃, g₃⟩ := shotI_exec hsh c₂ e₂.wb_right C₂
      a1 a2 a3 a4 harcA sA ho1 ho2 hol oA zttqq (by
        zunyt; omega)
    -- the second arc
    have c35 : zturw := by
      rw [bandShot g₃ _ by_norm_num by_norm_num by_decide,
        bandArc Fa _ by_norm_num by_norm_num by_decide]; omega
    have c36 : zturx := by
      rw [bandShot g₃ _ by_norm_num by_norm_num by_decide,
        bandArc Fa _ by_norm_num by_norm_num by_decide]; omega
    obtain ⟨c₄, k₄, e₄, hk₄, a1', a2', a3', a4', Fb⟩ := arcTwoB_exec c₃ e₃.wb_right
      C₃.r77 c35 c36 C₃.r89 by_omega
    zugkr

    obtain ⟨c₅, k₅, e₅, hk₅, hB₅, C₅, F₅, g₅⟩ := shotI_exec hsh c₄ e₄.wb_right C₄ a1' a2' a3' a4' harcB sB ho1 ho2 hol oB
      (keepArcB Fb hB₃) (by
        zukpe
        have := Fa.1 ALLOC by_decide
        omega)
    have ex : Exec P W ztibb c c₅ _ :=
      .seq e₁ (.ifLtN_true hb ztbq)
    zuiup
    have Fb' := frameIO_of_frameB ztikj Fb k₄
    refine ⟨c₅, _, ex, by_omega, ?_, C₅.env,
      ((((F₁.trans Fa').trans F₃).trans Fb').trans F₅).mono by_simp by_omega,
      fun r r1 r2 hr => ?_⟩
    · grind
    · rw [bandShot g₅ r r1 r2 hr, bandArc Fb r r1 r2 hr, bandShot g₃ r r1 r2 hr,
        bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]
end exec
open Set
variable {Q : Polygon}

/-- The facts of a normalized query. -/
structure QFacts (Q : Polygon) (e₁ h₁ e₂ h₂ : ℕ) : Prop where
  hn : 3 ≤ Q.n
  hD : DistinctHeights Q
  he₁ : e₁ < Q.n
  he₂ : e₂ < Q.n
  hs : ProperPos ztd Q Q.n ztcbt
  he : ProperPos ztd Q Q.n ztcbu
section
variable {e₁ h₁ e₂ h₂ : ℕ} (q : QFacts Q e₁ h₁ e₂ h₂)
include q in
/-- The end of the normalized query has the key of the end of the query. -/
theorem qkey_nh : (interiorModel Q).key Q ztww = (interiorModel Q).key Q ztcbu := by
  rw [key_eq, key_eq, param_nh q.he₂]
include q in
/-- **The plan of a normalized query.** -/
theorem qplan :
    let ee := eeOf Q e₁ h₁ e₂ ztsz
    let L := spanL ee ztsz
    (interiorModel Q).arcSet ztrr
        ztrs =
      oset ztkb e₁ ztwza
        (ee + (interiorModel Q).param Q ztww) ∧
    (interiorModel Q).param Q ztcbt < ee + (interiorModel Q).param Q ztww ∧
    zterx % Q.n = e₂ ∧ ee ≤ Q.n ∧
    ((nh Q e₂ h₂ = 0 ∧ ee = L) ∨
      (nh Q e₂ h₂ ≠ 0 ∧ ee + 1 = L ∧ 0 < (interiorModel Q).param Q ztww)) ∧
    1 ≤ L ∧
    (L ≤ Q.n → (interiorModel Q).arcWt ztrr
      ztrs = L) ∧
    (Q.n < L → (interiorModel Q).arcWt ztrr
      ztrs = Q.n) := by
  intro ee L
  have hx := q.hs
  have hy : 0 ≤ (interiorModel Q).param Q ztww ∧
      (interiorModel Q).param Q ztww < 1 := by
    rw [param_nh q.he₂]; exact ⟨q.he.1, q.he.2.1⟩
  have hnz : nh Q e₂ h₂ = 0 ∨ 0 < (interiorModel Q).param Q ztww := by
    by_cases h0 : nh Q e₂ h₂ = 0
    · omega
    · exact Or.inr (param_pos_nh q.hD (by have := q.hn; omega) q.he₂ q.he.2.2 q.he.1 h0)
  have := plan_arc q.hn q.he₁ q.he₂ ztuip hy hnz
  rw [qkey_nh q] at this
  omega
include q in
/-- **One sub-query** (`L ≤ n - 1`). -/
theorem plan_one (hL : spanL ztwso ztsz + 1 ≤ Q.n) :
    SubOK Q e₁ (spanL ztwso ztsz) h₁
      ztwso ztsz ∧
    (interiorModel Q).arcSet ztrr
        ztrs =
      oset ztkb e₁ ztwza
        (eeOf Q e₁ h₁ e₂ ztsz + (interiorModel Q).param Q
          ⟨(e₁ + eeOf Q e₁ h₁ e₂ ztsz) % Q.n, nh Q e₂ h₂⟩) ∧
    (interiorModel Q).arcWt ztrr
      ztrs = spanL ztwso ztsz := by
  obtain ⟨hS, hxy, hmod, -, hee, h1, hwt, -⟩ := qplan q
  zugvd
  have hpe : ztzpa :=
    ⟨by rw [param_nh q.he₂]; exact q.he.1, by rw [param_nh q.he₂]; exact q.he.2.1,
      le_trans nh_le q.he.2.2⟩
  refine ⟨⟨q.he₁, h1, hL, q.hs, by_simp_all, by_simp_all,
    by simp_all⟩, hS, hwt by_omega⟩
include q in
/-- **Two sub-queries** (`L ≥ n`): two edges to the vertex `(e₁ + 2) mod n`, then the rest. -/
theorem plan_two (hL : Q.n ≤ spanL ztwso ztsz) :
    SubOK Q e₁ 2 h₁ 2 0 ∧
    SubOK Q ztysx (spanL ztwso ztsz - 2) 0
      ztyjd ztsz ∧
    (interiorModel Q).arcSet ztrr
        ztrs =
      oset ztkb e₁ ztwza
          ((2 : ℕ) + (interiorModel Q).param Q ztzis) ∪
        oset ztkb ztysx ((interiorModel Q).param Q ztzis)
          ((eeOf Q e₁ h₁ e₂ ztsz - 2 : ℕ) + (interiorModel Q).param Q
            ⟨(zterw % Q.n + ztyjd) % Q.n, nh Q e₂ h₂⟩) ∧
    (interiorModel Q).arcWt ztrr
      ztrs = Q.n := by
  obtain ⟨hS, hxy, hmod, heen, hee, h1, hwt, hwt'⟩ := qplan q
  set ee := eeOf Q e₁ h₁ e₂ ztsz with heed
  set L := spanL ee ztsz with hLd
  have hn := q.hn
  zufvu
  zuhym
  have hLn : L ≤ Q.n + 1 := by_omega
  have hmod2 : (zterw % Q.n + ztjur) % Q.n = e₂ := by
    simp_all
  have hpe : ztzpa :=
    ⟨by rw [param_nh q.he₂]; exact q.he.1, by rw [param_nh q.he₂]; exact q.he.2.1,
      le_trans nh_le q.he.2.2⟩
  have hv0 : ∀ e, ProperPos ztd Q Q.n ztjy := fun e =>
    ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩
  have hp0 : ∀ e, (interiorModel Q).param Q ztjy = 0 := fun e => rfl
  have hx1 := q.hs.2.1
  have hx0 := q.hs.1
  refine ⟨⟨q.he₁, by_norm_num, by_omega, q.hs, hv0 _, Or.inl ztrh, by
      grind⟩,
    ⟨Nat.mod_lt _ hn0, by_omega, by_omega, hv0 _, by_simp_all, ?_, ?_⟩, ?_, ?_⟩
  · grind
  · rw [hp0, hmod2]
    rcases hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
    · have : (interiorModel Q).param Q ztww = 0 := by_grind
      rw [this, add_zero]
      exact_mod_cast (show 0 < ee - 2 by omega)
    grind
  · rw [hS, hp0, hmod2, add_zero]
    zudon
    have e1 : oset ztkb ztysx 0
        ztwpz =
        oset ztkb e₁ ((2 : ℕ) + 0)
          ((2 : ℕ) + ztwpz) := by
      rw [← hiw, oset_mod, oset_shift _ _ _ le_rfl]
    rw [e1, add_zero]
    have hc : ((2 : ℕ) : ℝ) + ztwpz =
        ee + (interiorModel Q).param Q ztww := by
      rw [Nat.cast_sub hee2]; grind
    rw [hc, oset_union _ _ by_grind (by
      grind)]
  omega
end
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

/-! ## The double boundary is not horizontal -/

/-- **The walk edges `6 … 2m + 6` of a chain model are not horizontal.** -/
theorem cm_nh {C : Chain} (hD : DistinctHeights C.P) {e : ℕ} (h6 : 6 ≤ e)
    (he : e ≤ 2 * C.m + 6) : ((chainModel C).wa e).2 ≠ ((chainModel C).wb e).2 := by
  zucmi
  zubt
  rcases he.lt_or_eq with he | rfl
  · have hwa : ztmrd := cm_vtx_tour C h6 he.le
    have hwb : ztbanl := by
      zueex

    zucav

    have hne : ztyym := by
      zulbj

      zuchg
      have := C.sideEdgeIdx_inj hk1 hk2 hc
      omega
    zucpy
    exact hD _ _ ztjsr ztnwt hne
  · have hwa : ztytp := by
      zujpz
      rw [cm_vtx_tour C by_omega le_rfl]
      zucfe

    have hwb : (chainModel C).wb ztcc = C.slitTop := by
      unfold Model.wb; rw [hn, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]; rfl
    zucpy
    have := C.top_snd_lt_radius
    simp only [Chain.slitTop]
    grind

/-! ## Stretches -/

/-- **A stretch** of the interior walk of `Q` from its vertex `u₀` agreeing with the walk of the
chain model of `C` from its vertex `g₀`, for `ℓ` steps inside the double boundary. -/
structure Stretch (Q : Polygon) (C : Chain) (u₀ g₀ ℓ : ℕ) : Prop where
  hu : u₀ < Q.n
  h6 : 6 ≤ g₀
  hend : g₀ + ℓ ≤ 2 * C.m + 6
  hCP : C.P = Q
  hD : DistinctHeights Q
  hn : 3 ≤ Q.n
  hℓ : ℓ < Q.n
  agree : WalkEmbed.Agree ztkb (chainModel C).W u₀ g₀ ℓ

/-- **The translation** of a chain-model position. -/
def trP (n u₀ g₀ : ℕ) (x : WPos) : WPos := ⟨ztoje % n, x.hgt⟩
section
variable {Q : Polygon} {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ)
include S in
omit S in
theorem str_cmn (_S : Stretch Q C u₀ g₀ ℓ) : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
include S in
omit S in
/-- The edge of a proper position with key in the stretch. -/
theorem str_edge (_S : Stretch Q C u₀ g₀ ℓ) {x : WPos} (hx : ProperPos ztc Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    g₀ ≤ x.edge ∧ x.edge ≤ g₀ + ℓ ∧ (x.edge < g₀ + ℓ ∨ (chainModel C).param Q x = 0) := by
  have hp0 := hx.1
  have hp1 := hx.2.1
  rw [key_eq] at hk0 hk1
  have a1 : (g₀ : ℝ) < x.edge + 1 := by_linarith
  have a2 : (x.edge : ℝ) ≤ g₀ + ℓ := by_linarith
  have b1 : g₀ < x.edge + 1 := by exact_mod_cast a1
  have b2 : x.edge ≤ g₀ + ℓ := by exact_mod_cast a2
  refine ⟨by_omega, b2, ?_⟩
  rcases b2.lt_or_eq with h | h
  · omega
  · right
    have : (x.edge : ℝ) = g₀ + ℓ := by_simp_all
    linarith
include S in
/-- **The translated position** has the same parameter, is proper, and has the same point. -/
theorem trP_spec {x : WPos} (hx : ProperPos ztc Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    (interiorModel Q).param Q ztcjc = (chainModel C).param Q x ∧
      ProperPos ztd Q Q.n ztcjc ∧ (trP Q.n u₀ g₀ x).edge < Q.n ∧
      (interiorModel Q).pos Q ztcjc = (chainModel C).pos Q x := by
  obtain ⟨hg1, hg2, hlt⟩ := str_edge S hx hk0 hk1
  zucmc

  zudyx

  set d := x.edge - g₀ with hd
  have hxe : x.edge = g₀ + d := by_omega
  have hxe' : x.edge = (g₀ + d) % (chainModel C).W.n := by
    rw [hcm, Nat.mod_eq_of_lt by_omega]; omega
  have htr : trP Q.n u₀ g₀ x = ⟨ztuco % (interiorModel Q).W.n, x.hgt⟩ := by
    unfold trP; rw [hmi]
  have hedge : (trP Q.n u₀ g₀ x).edge < Q.n := by
    unfold trP; exact Nat.mod_lt _ (by have := S.hn; omega)
  -- the parameter
  have hpar : (interiorModel Q).param Q ztcjc = (chainModel C).param Q x := by
    zukls
    · have := param_agree (M := interiorModel Q) S.agree Q (d := d)
        by_omega x.hgt
      zuhly
    · rw [hpz]
      -- the end of the stretch: both parameters vanish
      rcases Nat.eq_zero_or_pos x.hgt with h0 | h0
      · zuowy; show (interiorModel Q).param Q ⟨_, x.hgt⟩ = 0; zvmzn; rfl
      obtain ⟨h', hh⟩ : ∃ h', x.hgt = h' + 1 := ⟨x.hgt - 1, by_omega⟩
      have hDC : ztrfm := by rw [S.hCP]; exact S.hD
      have hnh := cm_nh hDC (e := x.edge) by_omega by_omega
      have hy : (Q.vtx h').2 = ((chainModel C).wa x.edge).2 := by
        have hp := hpz
        unfold Model.param at hp
        rw [hh] at hp
        simp only at hp
        rw [ite_eq_right hnh, div_eq_zero_iff] at hp
        zudsh
        · linarith
        grind
      have hva : (interiorModel Q).wa (ztuco % (interiorModel Q).W.n) =
          (chainModel C).wa x.edge := by
        zuhad

      zuowy
      zufde
      simp only [hh]
      split_ifs with hz
      · rfl
      grind
  refine ⟨hpar, ⟨by zvokb; exact hx.1, by zvokb; exact hx.2.1, hx.2.2⟩, hedge, ?_⟩
  -- the point
  zukls
  · have := pos_agree (M := interiorModel Q) S.agree Q (d := d)
      by_omega x.hgt
    zuhly
  · zueew
    rw [hpar, hpz, lerp_zero, lerp_zero, htr]
    zuhad
include S in
/-- The interior key of a translated position. -/
theorem trP_key {x : WPos} (hx : ProperPos ztc Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    (interiorModel Q).key Q ztcjc =
      ((ztoje % Q.n : ℕ) : ℝ) + (chainModel C).param Q x := by
  rw [key_eq, (trP_spec S hx hk0 hk1).1]; rfl
include S in
/-- **Arcs between translated positions** have the same point set and weight. -/
theorem trP_arc {x y : WPos} (hx : ProperPos ztc Q Q.n x)
    (hy : ProperPos ztc Q Q.n y) (hx0 : (g₀ : ℝ) ≤ (chainModel C).key Q x)
    (hy1 : (chainModel C).key Q y ≤ g₀ + ℓ)
    (hxy : (chainModel C).key Q x < (chainModel C).key Q y) :
    (interiorModel Q).arcSet ztynp
        ztifc =
      (chainModel C).arcSet ztlb ztov ∧
    (interiorModel Q).arcWt ztynp
        ztifc =
      (chainModel C).arcWt ztlb ztov := by
  have hx1 := hxy.le.trans hy1
  have hy0 := hx0.trans hxy.le
  obtain ⟨gx1, gx2, -⟩ := str_edge S hx hx0 hx1
  obtain ⟨gy1, gy2, gy3⟩ := str_edge S hy hy0 hy1
  zucmc

  zudon
  zudyx

  have hℓ := S.hℓ
  zuiyo
  have hu := S.hu
  rw [trP_key S hx hx0 hx1, trP_key S hy hy0 hy1]
  set tx := (chainModel C).param Q x with htx
  set ty := (chainModel C).param Q y with hty
  have tx0 := hx.1
  have tx1 := hx.2.1
  have ty0 := hy.1
  have ty1 := hy.2.1
  simp only [key_eq] at hxy hx0 hy1 ⊢
  set dx := x.edge - g₀ with hdx
  set dy := y.edge - g₀ with hdy
  have hxe : x.edge = g₀ + dx := by_omega
  have hye : y.edge = g₀ + dy := by_omega
  have hdxy : dx ≤ dy := by
    have : (x.edge : ℝ) < y.edge + 1 := by_linarith
    have : x.edge < y.edge + 1 := by exact_mod_cast this
    omega
  set e := dy - dx with he
  have hye' : y.edge = x.edge + e := by_omega
  have hxyr : tx < (e : ℝ) + ty := by
    zufst
    grind
  have hey : (e : ℝ) + ty ≤ ℓ - dx := by
    have h1 := hy1
    zufst
    have : (x.edge : ℝ) = g₀ + dx := by exact_mod_cast hxe
    linarith
  have hdyℓ : dy ≤ ℓ := by_omega
  have hmod : (ztkgj % Q.n + e) % Q.n = zthkw % Q.n := by
    grind
  have hmodc : (x.edge + e) % (chainModel C).W.n = y.edge := by
    rw [← hye', hcm, Nat.mod_eq_of_lt by_omega]
  have hen : (e : ℝ) + ty ≤ tx + Q.n := by
    zuiul
    grind
  have hu' : ztkgj % Q.n < (interiorModel Q).W.n := by rw [hmi]; exact Nat.mod_lt _ by_omega
  zukha
  constructor
  · -- the point sets
    have hb0 : (0 : ℝ) ≤ ((zthkw % Q.n : ℕ) : ℝ) + ty := by_positivity
    have hbn : ((zthkw % Q.n : ℕ) : ℝ) + ty < (interiorModel Q).W.n := by
      have : zthkw % Q.n + 1 ≤ Q.n := Nat.mod_lt _ by_omega
      have : ((zthkw % Q.n : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast this
      grind
    rw [arcSet_eq_oset _ hu' tx0 tx1 hb0 hbn, hmi, ← hmod,
      len_key by_omega tx1 ty0 hxyr hen]
    have hb0' : (0 : ℝ) ≤ (y.edge : ℝ) + ty := by_positivity
    have hbn' : (y.edge : ℝ) + ty < (chainModel C).W.n := by
      have : (y.edge : ℝ) + 1 ≤ (chainModel C).W.n := by
        rw [hcm]; exact_mod_cast by_grind
      linarith
    rw [arcSet_eq_oset _ hxe2 tx0 tx1 hb0' hbn']
    have hlap' : (e : ℝ) + ty ≤ tx + (chainModel C).W.n := by
      rw [hcm]; push_cast
      zuiul
      have : (e : ℝ) ≤ ℓ := by_grind
      have : (1 : ℝ) ≤ 2 * C.m + 7 - ℓ := by
        have : ℓ + 1 ≤ 2 * C.m + 7 := by_omega
        have : ((ℓ + 1 : ℕ) : ℝ) ≤ ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast this
        grind
      linarith
    have hl2 := len_key hxe2 tx1 ty0 hxyr hlap'
    rw [hmodc] at hl2
    zuowz
    have e1 : oset (interiorModel Q).W (ztkgj % Q.n) = oset ztkb ztkgj := by
      funext a b
      show oset ztkb _ a b = _
      rw [← hiw]; exact oset_mod _ _ _ _
    rw [e1, hxe, ← oset_shift _ _ _ tx0, ← oset_shift _ _ _ tx0]
    exact oset_congr S.agree (by
      grind)
  · -- the weights
    have hci : ∀ p, p < (interiorModel Q).W.n →
        ztcqn := fun p hp => by
      rw [hmi] at hp ⊢; exact interiorModel_counted_iff Q p by_omega
    have hkc : keyCeil e ty ≤ e + 1 := keyCeil_le_succ
    have hkc' : keyCeil e ty = e ∨ (keyCeil e ty = e + 1 ∧ 0 < ty) := by
      unfold keyCeil; split_ifs with h
      · omega
      grind
    have w1 := arcWt_off _ hci le_rfl
      hu' ztbg tx0 tx1 ty0 ty1 hxyr by_grind
    rw [hmi, hmod] at w1
    zuljv
    have w2 := arcWt_off _ hcc by_omega
      hxe2 by_omega tx0 tx1 ty0 ty1 hxyr (Or.inr ⟨by
        show x.edge + keyCeil e ty ≤ 2 * C.m + 6
        rcases hkc' with h | ⟨h, hpos⟩
        · omega
        · rcases gy3 with g | g
          · omega
          grind, by_omega⟩)
    grind
include S in
/-- **The interior walk agrees with the chain walk** at the translated position. -/
theorem trP_agree {x : WPos} (hx : g₀ ≤ x.edge) {a L' : ℕ} (h : x.edge - g₀ + a + L' ≤ ℓ) :
    WalkAgree (interiorModel Q).W (chainModel C).W (ztkpo % Q.n)
      (ztueh % (chainModel C).W.n) L' := by
  zuip
  have hmi : ztbdm := mi_n
  zuljw
  zumdk
  have := S.agree zthle by_omega
  have e1 : (ztkpo % Q.n + d) % Q.n =
      (u₀ + zthle) % Q.n := by
    unfold trP; grind
  have e2 : (ztueh % (chainModel C).W.n + d) % (chainModel C).W.n =
      (g₀ + zthle) % (chainModel C).W.n := by
    rw [Nat.mod_add_mod]; congr 1; omega
  zudon
  rw [hiw] at this
  rw [hmi, e1, e2]
  tauto
theorem walkAgree_trans {A B C' : Polygon} {a b c L : ℕ} (h₁ : WalkAgree A B a b L)
    (h₂ : WalkAgree B C' (b % B.n) c L) : WalkAgree A C' a c L := fun d hd => by
  rw [h₁ d hd, ← h₂ d hd, Nat.mod_add_mod]
include S in
/-- **The chain weight of an arc in the stretch** between two vertex positions. -/
theorem str_wt0 {x y : WPos} (hx : x.hgt = 0) (hy : y.hgt = 0) (hxy : x.edge < y.edge)
    (hx0 : g₀ ≤ x.edge) (hy1 : y.edge ≤ g₀ + ℓ) :
    (chainModel C).arcWt ztlb ztov = y.edge - x.edge := by
  zuljw
  zudyx

  zuljv
  zukha
  have kx : (chainModel C).key Q x = (x.edge : ℝ) + 0 := by
    rw [key_eq]; congr 1; show (chainModel C).param Q zthnv = 0; simp_all
  have ky : (chainModel C).key Q y = (((x.edge + ztfvl) % (chainModel C).W.n : ℕ) : ℝ) + 0 := by
    rw [key_eq, show x.edge + ztfvl = y.edge by omega,
      Nat.mod_eq_of_lt by_omega]
    congr 1; show (chainModel C).param Q ⟨y.edge, y.hgt⟩ = 0; simp_all
  rw [kx, ky]
  have hk : keyCeil ztfvl (0 : ℝ) = y.edge - x.edge := by unfold keyCeil; simp
  rw [arcWt_off _ hcc by_omega hxe2
    by_omega le_rfl zero_lt_one le_rfl zero_lt_one
    by_simp_all by_omega, hk]
include S in
/-- **`PieceWalk` along the stretch**: a kind-1 piece of the chain cutter inside the stretch is a
piece of the interior walk, its chain visited along the same vertices. -/
theorem trP_pieceWalk {s e : WPos} {Cα : Chain} (hpw : PieceWalk ztc Cα s e)
    (hwt : (chainModel C).arcWt ztbaj ztbai = Cα.m)
    (hse : (chainModel C).key Q s < (chainModel C).key Q e)
    (hs0 : (g₀ : ℝ) ≤ (chainModel C).key Q s) (he1 : (chainModel C).key Q e ≤ g₀ + ℓ)
    (hvl : (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ztjcp =
        Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ztjcp =
        Cα.vertex ztclf)) :
    PieceWalk ztd Cα (trP Q.n u₀ g₀ s) (trP Q.n u₀ g₀ e) ∧
      ((∀ d, d ≤ Cα.m → (interiorModel Q).W.vtx (ztkpn %
          (interiorModel Q).W.n) = Cα.vertex d) ∨
        (∀ d, d ≤ Cα.m → (interiorModel Q).W.vtx (ztkpn %
          (interiorModel Q).W.n) = Cα.vertex (Cα.m - d))) := by
  obtain ⟨hs, he, hsn, hee, g', hg', hw⟩ := hpw
  zucmc

  zumdk
  zuiyo
  have ks : (chainModel C).key Q s = s.edge := by
    rw [key_eq, show (chainModel C).param Q s = 0 by
      show (chainModel C).param Q ztujk = 0; zvmyz; rfl, add_zero]
  have ke : (chainModel C).key Q e = e.edge := by
    rw [key_eq, show (chainModel C).param Q e = 0 by
      show (chainModel C).param Q ⟨e.edge, e.hgt⟩ = 0; zvmxm; rfl, add_zero]
  rw [ks, ke] at hse
  rw [ks] at hs0
  rw [ke] at he1
  have hs0' : g₀ ≤ s.edge := by_simp_all
  have he1' : e.edge ≤ g₀ + ℓ := by exact_mod_cast he1
  have hse' : s.edge < e.edge := by_simp_all
  have hm : Cα.m = e.edge - s.edge := by rw [← hwt, str_wt0 S hs he hse' hs0' he1']
  have hdiff : s.edge + Cα.m = e.edge := by_omega
  have hA := trP_agree S hs0' (a := 0) (L' := Cα.m) by_omega
  zvnhg at hA
  have hsl := Nat.mod_eq_of_lt hsn
  have hts : (trP Q.n u₀ g₀ s).edge < Q.n := by unfold trP; exact Nat.mod_lt _ by_omega
  have htsmod := Nat.mod_eq_of_lt hts
  rw [htsmod, hsl] at hA
  have hte : (trP Q.n u₀ g₀ e).edge = ((trP Q.n u₀ g₀ s).edge + Cα.m) % (interiorModel Q).W.n := by
    unfold trP; simp only
    rw [hmi, Nat.mod_add_mod, ← hdiff, show u₀ + (s.edge - g₀) + Cα.m = u₀ + (s.edge + Cα.m - g₀) by
      omega]
  refine ⟨⟨hs, he, by_omega, hte, g', hg', ?_⟩, ?_⟩
  · rcases hw with hw | ⟨L₁, h1, h2, h3, hw1, hw2⟩
    · exact Or.inl (walkAgree_trans hA by_grind)
    · refine Or.inr ⟨L₁, h1, h2, h3, walkAgree_trans
        (fun d hd => hA d by_omega) by_grind, ?_⟩
      have hB := trP_agree S hs0' (a := L₁) (L' := Cα.m - L₁) by_omega
      rw [hmi]
      refine walkAgree_trans hB ?_
      rw [Nat.mod_mod]
      omega
  · rcases hvl with hv | hv
    · left; intro d hd; zuokc; exact hv d hd
    · right; intro d hd; zuokc; exact hv d hd
end
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)

/-! ## Paths of unwrapped keys from indexed facts -/

/-- **A path of unwrapped keys** from facts indexed by the pieces. -/
theorem kpath_of_idx {M : Model} {Q : Polygon} {n : ℝ} :
    ∀ (ps : List Pc) (Vs Ve : ℕ → ℝ), ps ≠ [] →
      (∀ i (hi : i < ps.length), (∃ k : ℤ, Vs i = M.key Q (ps[i]'hi).s + k * n) ∧
        (∃ k : ℤ, Ve i = M.key Q (ps[i]'hi).e + k * n) ∧ Vs i < Ve i) →
      (∀ i, i + 1 < ps.length → Vs ztg = Ve i) →
      KPath M Q n (Vs 0) ps (Ve zttwn)
  | [], _, _, hne, _, _ => absurd rfl hne
  | [pc], Vs, Ve, _, h, _ => by
    zufjb
    exact ⟨h1, Ve 0, h3, h2, rfl⟩
  | pc :: q :: qs, Vs, Ve, _, h, hc => by
    zufjb
    refine ⟨h1, Ve 0, h3, h2, ?_⟩
    have ih := kpath_of_idx _ (fun i => Vs _) (fun i => Ve _)
      by_simp_all (fun i hi => h ztg by_simp_all)
      by_simp_all
    simp_all

/-! ## The chain pieces go through increasing keys -/

/-- **The keys of the chain pieces increase** from the start of the arc to its end. -/
theorem chain_mono {K : WPos → ℝ} {ps : List Pc} {sa ea : WPos} (hne : ps ≠ [])
    (hlt : K sa < K ea) (h0 : K (ps[0]' zthre).s = K sa)
    (hl : K (ps[ps.length - 1]'(by have := List.length_pos_iff.2 hne; omega)).e = K ea)
    (hc : ∀ i (hi : i + 1 < ps.length), K (ps[i]' by_omega).e = K (ps[i + 1]'hi).s)
    (ht : ∀ i (hi : i + 1 < ps.length), sideInArc (K (ps[i]' by_omega).s) (K ea)
      (K (ps[i]' by_omega).e)) :
    ∀ i (hi : i < ps.length), K sa ≤ K (ps[i]'hi).s ∧ K (ps[i]'hi).s < K (ps[i]'hi).e ∧
      K (ps[i]'hi).e ≤ K ea := by
  zulkj
  -- the starts lie in `[K sa, K ea)`
  have hs : ∀ i (hi : i < ps.length), K sa ≤ K (ps[i]'hi).s ∧ K (ps[i]'hi).s < K ea := by
    zuibw
    induction i with
    | zero => intro hi; zvmzn; exact by_simp_all
    | succ i ih =>
      zulmu
      obtain ⟨a1, a2⟩ := ih by_omega
      have hti := ht i hi
      zumus
      rw [ite_eq_left a2] at hti
      rw [← hc i hi]
      zubfo
  zug
  obtain ⟨a1, a2⟩ := hs i hi
  by_cases hlast : i + 1 < ps.length
  · have hti := ht i hlast
    zumus
    grind
  grind

/-! ## Pieces in memory -/

/-- **The piece `i` of the list at `L`** in the memory `m` (the descriptor and normal-form
handles in the fields `entry` and `x0`). -/
def rdPc (m : ℕ → ℕ) (L i : ℕ) : Pc :=
  ⟨⟨m zthbc, m ztdla⟩, ⟨m ztclq, m ztdlb⟩,
    m ztley, m ztlez, m ztlfa, 0, 0⟩

/-- **The translation of a piece** along a stretch. -/
def trPc (n u₀ g₀ : ℕ) (pc : Pc) : Pc :=
  { pc with s := trP n u₀ g₀ pc.s, e := trP n u₀ g₀ pc.e }

/-- **The facts `CutterOK` asks of one piece** in the model `M` (memory `m`, bound `E`,
granularity bound `Hγ`). -/
def PcV (P : Polygon) (M : Model) (m : ℕ → ℕ) (E Hγ : ℕ) (pc : Pc) : Prop :=
  ProperPos M zta P.n pc.s ∧ ProperPos M zta P.n pc.e ∧ pc.s.edge < M.W.n ∧
    pc.e.edge < M.W.n ∧ pc.kind ≤ 1 ∧
    (pc.kind = 0 → M.arcWt ztypf ztype ≤ 1) ∧
    (pc.kind = 1 → ChainWF P E m pc.entry ∧ ∃ Hs Cα N, ChainDescAt m pc.entry zta Hs Cα ∧
      NFWithin m pc.x0 E N ∧ (∃ γ', γ' ≤ Hγ ∧ IsCanonicalNF ztbdc zta N γ' 4) ∧
      M.arcSet ztypf ztype = Cα.set ∧
      M.arcWt ztypf ztype = Cα.m ∧
      PieceWalk M Cα pc.s pc.e ∧ Cα.P = Qof P ∧
      ((∀ d, d ≤ Cα.m → M.W.vtx ztbaaf = Cα.vertex d) ∨
        (∀ d, d ≤ Cα.m → M.W.vtx ztbaaf = Cα.vertex ztclf)))

/-- **A chain descriptor determines the chain.** -/
theorem chainDesc_uniq {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {H : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H C') : C = C' := by
  obtain ⟨-, h2, h3, h4, -⟩ := h
  obtain ⟨-, h2', h3', h4', -⟩ := h'
  zubkt
variable {P : Polygon} {Q : Polygon}
/-- **The facts of a piece survive** memory changes at or above their bound. -/
theorem PcV.keep {M : Model} {m m' : ℕ → ℕ} {E E' Hγ : ℕ} {pc : Pc}
    (h : PcV P M m E Hγ pc) (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    PcV P M m' E' Hγ pc := by
  zumt
  refine ⟨h1, h2, h3, h4, h5, h6, fun hk => ?_⟩
  obtain ⟨hwf, Hs, Cα, N, hCD, hNF, hrest⟩ := h7 hk
  obtain ⟨hlen, hHwf, hEb, hs⟩ := hwf.2 Hs Cα hCD
  have hb5 := hwf.1
  have hCD' : ChainDescAt m' pc.entry _ Hs Cα :=
    ShotList.chainDescAt_copy hCD hEb he by_grind
  refine ⟨?_, Hs, Cα, N, hCD', (hNF.transport he).mono hE, hrest⟩
  refine ztgoe
  have hb : m' pc.entry = m pc.entry := by_grind
  have hH := NFLoc.hostAt_unique hC'.1 hCD'.1
  zulsw
  have hC := chainDesc_uniq hC' hCD'
  grind

/-- **A chain piece inside the stretch, translated, is a piece of the interior walk.** -/
theorem pcV_tr {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch zta C u₀ g₀ ℓ)
    {m : ℕ → ℕ} {E Hγ : ℕ} {pc : Pc} (hv : PcV P ztc m E Hγ pc)
    (hs0 : (g₀ : ℝ) ≤ (chainModel C).key zta pc.s)
    (he1 : (chainModel C).key zta pc.e ≤ g₀ + ℓ)
    (hse : (chainModel C).key zta pc.s < (chainModel C).key zta pc.e) :
    PcV P ztwiq m E Hγ (trPc (Qof P).n u₀ g₀ pc) := by
  zudq
  obtain ⟨sP, eP, sE, eE, hk, h0, h1⟩ := hv
  have sP' : ProperPos ztc zta (Qof P).n pc.s := by_grind
  have eP' : ProperPos ztc zta (Qof P).n pc.e := by_grind
  have hs1 : (chainModel C).key _ pc.s ≤ g₀ + ℓ := hse.le.trans he1
  have he0 : (g₀ : ℝ) ≤ (chainModel C).key _ pc.e := hs0.trans hse.le
  obtain ⟨-, sPI, sEI, -⟩ := trP_spec S sP' hs0 hs1
  obtain ⟨-, ePI, eEI, -⟩ := trP_spec S eP' he0 he1
  obtain ⟨hset, hwt⟩ := trP_arc S sP' eP' hs0 he1 hse
  have hmi : (interiorModel _).W.n = (Qof P).n := mi_n
  refine ⟨by zvnoq; tauto, by zvnoq; tauto, by rw [hmi]; tauto,
    by rw [hmi]; tauto, hk, fun hk0 => ?_, fun hk1 => ?_⟩
  · show (interiorModel _).arcWt _ _ ≤ 1
    rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
      show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hwt]
    exact h0 hk0
  · obtain ⟨hwf, Hs, Cα, N, hCD, hNF, hcan, hcs, hcw, hpw, hCαP, hvl⟩ := h1 hk1
    obtain ⟨hpw', hvl'⟩ := trP_pieceWalk S hpw hcw hse hs0 he1 hvl
    refine ⟨hwf, Hs, Cα, N, hCD, hNF, hcan, ?_, ?_, hpw', hCαP, hvl'⟩
    · show (interiorModel _).arcSet _ _ = _
      rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
        show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hset, hcs]
    · show (interiorModel _).arcWt _ _ = _
      rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
        show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hwt, hcw]

/-- **The unwrapped interior key** of a translated position. -/
theorem trP_cong {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ) {e₁ off : ℕ}
    (hu₀ : u₀ = ztnye % Q.n) {x : WPos} (hx : ProperPos ztc Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    ∃ k : ℤ, (e₁ : ℝ) + off - g₀ + (chainModel C).key Q x =
      (interiorModel Q).key Q ztcjc + k * Q.n := by
  obtain ⟨hg1, -, -⟩ := str_edge S hx hk0 hk1
  rw [trP_key S hx hk0 hk1, key_eq, hu₀, Nat.mod_add_mod]
  set a := e₁ + off + (x.edge - g₀) with ha
  refine ⟨((a / Q.n : ℕ) : ℤ), ?_⟩
  have e1 := Nat.mod_add_div a Q.n
  have e2 : ((a % Q.n : ℕ) : ℝ) + Q.n * ((a / Q.n : ℕ) : ℝ) = a := by exact_mod_cast e1
  have e3 : (a : ℝ) = e₁ + off + x.edge - g₀ := by
    rw [ha]; push_cast [Nat.cast_sub hg1]; ring
  zulrp
  linarith

/-- A default piece. -/
def pc0 : Pc := ⟨ztbqw, ztbqw, 0, 0, 0, 0, 0⟩

/-- **The translated pieces of one chain arc** form a path of unwrapped interior keys. -/
theorem slot_kpath {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ)
    {e₁ off : ℕ} (hu₀ : u₀ = ztnye % Q.n) {ps : List Pc} (hne : ps ≠ []) {sa ea : WPos}
    (hlt : (chainModel C).key Q sa < (chainModel C).key Q ea)
    (h0 : (chainModel C).key Q (ps[0]' zthre).s = (chainModel C).key Q sa)
    (hl : (chainModel C).key Q (ps[ps.length - 1]'(by
      grind)).e = (chainModel C).key Q ea)
    (hc : ∀ i (hi : i + 1 < ps.length), (chainModel C).key Q (ps[i]' by_omega).e =
      (chainModel C).key Q (ps[i + 1]'hi).s)
    (ht : ∀ i (hi : i + 1 < ps.length), sideInArc ztgvt
      ((chainModel C).key Q ea) ztgvs)
    (hpp : ∀ pc ∈ ps, ProperPos ztc Q Q.n pc.s ∧ ProperPos ztc Q Q.n pc.e)
    (hsa : (g₀ : ℝ) ≤ (chainModel C).key Q sa) (hea : (chainModel C).key Q ea ≤ g₀ + ℓ) :
    KPath ztd Q Q.n ((e₁ : ℝ) + off - g₀ + (chainModel C).key Q sa)
      (ps.map ztluf) ((e₁ : ℝ) + off - g₀ + (chainModel C).key Q ea) := by
  have hmono := chain_mono hne hlt h0 hl hc ht
  have hne' : ps.map ztluf ≠ [] := by_simp_all
  have hlen : (ps.map ztluf).length = ps.length := List.length_map _
  have key := kpath_of_idx
    _
    (fun i => (e₁ : ℝ) + off - g₀ + (chainModel C).key Q (ps.getD i pc0).s)
    (fun i => (e₁ : ℝ) + off - g₀ + (chainModel C).key Q (ps.getD i pc0).e) hne'
    (fun i hi => by
      zucpx
      have hgi : ps.getD i pc0 = ps[i]'hi := by_simp_all
      simp only [List.getElem_map, hgi]
      zufkk
      have hp := hpp _ ztdyp
      exact ⟨trP_cong S hu₀ hp.1 (hsa.trans m1) by_grind,
        trP_cong S hu₀ hp.2 by_grind (m3.trans hea), by_linarith⟩)
    (fun i hi => by
      zucpx
      have hgi : ps.getD i pc0 = ps[i]' by_omega := by simp [List.getD, show i < ps.length by omega]
      simp_all)
  have hg0 : ps.getD 0 pc0 = ps[0]' zthre := by
    simp [List.getD, List.length_pos_iff.2 hne]
  have hgl : ps.getD zttwn pc0 = ps[ps.length - 1]'(by
      grind) := by
    simp [List.getD, show ps.length - 1 < ps.length by have := List.length_pos_iff.2 hne; omega]
  grind
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)

/-! ## The translation on the RAM -/

/-- The translated edge as the RAM computes it. -/
def trE (n u₀ g₀ e : ℕ) : ℕ := if u₀ + ztjuh < n then u₀ + ztjuh else u₀ + ztjuh - n
theorem trE_eq {n u₀ g₀ e : ℕ} (hu : u₀ < n) (he : e - g₀ < n) :
    trE n u₀ g₀ e = (u₀ + ztjuh) % n := by
  unfold trE
  zus
  · zukp
  · zul

/-- The translated piece as the RAM computes it. -/
def trPcR (n u₀ g₀ : ℕ) (pc : Pc) : Pc :=
  { pc with s := ⟨trE n u₀ g₀ pc.s.edge, pc.s.hgt⟩, e := ⟨trE n u₀ g₀ pc.e.edge, pc.e.hgt⟩ }
theorem trPcR_eq {n u₀ g₀ : ℕ} {pc : Pc} (hu : u₀ < n) (hs : pc.s.edge - g₀ < n)
    (he : pc.e.edge - g₀ < n) : trPcR n u₀ g₀ pc = trPc n u₀ g₀ pc := by
  unfold trPcR trPc trP
  rw [trE_eq hu hs, trE_eq hu he]

/-- The words of a piece record. -/
def pcW (pc : Pc) : ℕ → ℕ
  | 0 => pc.s.edge
  | 1 => pc.s.hgt
  | 2 => pc.e.edge
  | 3 => pc.e.hgt
  | 4 => pc.kind
  | 5 => pc.entry
  | _ => pc.x0

/-! ## Slots -/

/-- **A slot**: the list address, the number of pieces, the stretch start in the chain walk and
in the interior walk. -/
structure Slot where
  L : ℕ
  q : ℕ
  g₀ : ℕ
  u₀ : ℕ

/-- The translated pieces of a slot. -/
def slotPcs (m : ℕ → ℕ) (n : ℕ) (sl : Slot) : List Pc :=
  (List.range sl.q).map fun i => trPcR n sl.u₀ sl.g₀ ztrwm

/-- **A valid slot**: the pieces of a chain arc `[sa, ea]` of the chain `C`, inside a stretch,
valid and in increasing key order, with unwrapped interior keys from `Va` to `Vb`. -/
def SlotOK (P : Polygon) (m : ℕ → ℕ) (E Hγ e₁ : ℕ) (Va Vb : ℝ) (sl : Slot) : Prop :=
  ∃ (C : Chain) (ℓ off : ℕ) (sa ea : WPos), Stretch zta C sl.u₀ sl.g₀ ℓ ∧
    sl.u₀ = ztnye % (Qof P).n ∧ m sl.L = sl.q ∧ 1 ≤ sl.q ∧ sl.L + 1 + 7 * sl.q ≤ E ∧
    (chainModel C).key zta (rdPc m sl.L 0).s = (chainModel C).key zta sa ∧
    (chainModel C).key zta (rdPc m sl.L (sl.q - 1)).e = (chainModel C).key zta ea ∧
    (∀ i, i + 1 < sl.q → (chainModel C).key zta (rdPc m sl.L i).e =
      (chainModel C).key zta (rdPc m sl.L ztg).s) ∧
    (∀ i, i + 1 < sl.q → sideInArc ((chainModel C).key zta (rdPc m sl.L i).s)
      ztxjj ((chainModel C).key zta (rdPc m sl.L i).e)) ∧
    (∀ i, i < sl.q → PcV P ztc m E Hγ ztrwm) ∧
    (sl.g₀ : ℝ) ≤ (chainModel C).key zta sa ∧
    (chainModel C).key zta ea ≤ sl.g₀ + ℓ ∧
    (chainModel C).key zta sa < (chainModel C).key zta ea ∧
    Va = (e₁ : ℝ) + off - sl.g₀ + (chainModel C).key zta sa ∧
    Vb = (e₁ : ℝ) + off - sl.g₀ + (chainModel C).key zta ea
theorem rdPc_congr {m m' : ℕ → ℕ} {L i E : ℕ} (he : ∀ a, a < E → m' a = m a)
    (hi : L + 1 + 7 * i + 7 ≤ E) : rdPc m' L i = rdPc m L i := by
  unfold rdPc
  grind
variable {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ}
/-- **A valid slot survives** memory changes at or above its bound. -/
theorem SlotOK.keep {m m' : ℕ → ℕ} {E E' Hγ e₁ : ℕ} {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    SlotOK P m' E' Hγ e₁ Va Vb sl := by
  zudy
  have hr : ∀ i, i < sl.q → rdPc m' sl.L i = rdPc m sl.L i := fun i hi =>
    rdPc_congr he by_omega
  refine ⟨C, ℓ, off, sa, ea, S, hu, by_grind, hq1, by_omega,
    by grind, by_grind,
    fun i hi => by_grind,
    fun i hi => by_grind,
    fun i hi => by zuoka; exact (hv i hi).keep he hE, r1, r2, r3, r4, r5⟩

/-- **The translated pieces of a valid slot** form a path of unwrapped interior keys and are
valid pieces of the interior walk. -/
theorem slotOK_out {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) :
    KPath ztwiq zta (Qof P).n Va (slotPcs m (Qof P).n sl) Vb ∧
      (∀ pc ∈ slotPcs m (Qof P).n sl, PcV P ztwiq m E Hγ pc) ∧
      slotPcs m (Qof P).n sl ≠ [] := by
  zudy
  zudq
  zudbp

  have hne : ztppl := by
    grind
  have hget : ztfxf := fun i hi => by
    simp_all
  -- the order facts in list form
  have h0' : (chainModel C).key zta (ps[0]' zthre).s =
      (chainModel C).key zta sa := by_simp_all
  have hl' : (chainModel C).key zta (ps[ps.length - 1]'(by
      omega)).e = (chainModel C).key (Qof P) ea := by
    simp_all
  have hc' : ∀ i (hi : i + 1 < ps.length), (chainModel C).key zta (ps[i]' by_omega).e =
      (chainModel C).key zta (ps[i + 1]'hi).s := fun i hi => by
    rw [hget, hget]; simp_all
  have ht' : ∀ i (hi : i + 1 < ps.length), sideInArc ztxji
      ztxjj ztxjh :=
    fun i hi => by rw [hget]; simp_all
  have hpp : ∀ pc ∈ ps, ProperPos ztc zta (Qof P).n pc.s ∧
      ProperPos ztc zta (Qof P).n pc.e := by
    zujbk
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpc
    zujiy
    have := hv i by_omega
    zvnao; exact ztknb
  have hmono := chain_mono hne r3 h0' hl' hc' ht'
  -- the RAM translation is the translation
  have hslot : slotPcs m (Qof P).n sl = ps.map (trPc (Qof P).n sl.u₀ sl.g₀) := by
    unfold slotPcs
    rw [hps, List.map_map]
    refine List.map_congr_left ztdp
    have hi' : i < sl.q := List.mem_range.1 hi
    obtain ⟨m1, m2, m3⟩ := hmono i by_omega
    zuijv
    have hp := hv i hi'
    zujz

    exact trPcR_eq S.hu by_omega by_omega
  refine ⟨?_, fun pc hpc => ?_, ?_⟩
  · rw [hslot, r4, r5]
    exact slot_kpath S hu hne r3 h0' hl' hc' ht' hpp r1 r2
  · rw [hslot] at hpc
    obtain ⟨pc', hpc', rfl⟩ := List.mem_map.1 hpc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpc'
    zufkk
    rw [hget] at m1 m2 m3 ⊢
    exact pcV_tr S (hv i by_omega) ztqvf ztqth m2
  · rw [hslot]; simpa using hne

/-! ## Chains of slots -/

/-- **A chain of valid slots** (oldest first), with unwrapped keys from `V` to `V'`. -/
def SlotsOK (P : Polygon) (m : ℕ → ℕ) (E Hγ e₁ : ℕ) : ℝ → List Slot → ℝ → Prop
  | V, [], V' => V = V'
  | V, sl :: sls, V' => ∃ V₁, SlotOK P m E Hγ e₁ V V₁ sl ∧ SlotsOK P m E Hγ e₁ V₁ sls V'
theorem SlotsOK.keep {m m' : ℕ → ℕ} {E E' Hγ e₁ : ℕ} (he : ∀ a, a < E → m' a = m a)
    (hE : E ≤ E') : ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      SlotsOK P m' E' Hγ e₁ V sls V'
  | _, [], _, h => h
  | _, _ :: _, _, ⟨V₁, h1, h2⟩ => ⟨V₁, h1.keep he hE, SlotsOK.keep he hE h2⟩
theorem SlotsOK.snoc :
    ∀ {V : ℝ} {sls : List Slot} {V₁ : ℝ}, SlotsOK P m E Hγ e₁ V sls V₁ →
      ∀ {sl : Slot} {V₂ : ℝ}, SlotOK P m E Hγ e₁ V₁ V₂ sl → SlotsOK P m E Hγ e₁ V ztped V₂
  | _, [], _, h, _, _, hs => by simp only [SlotsOK] at h; subst h; tauto
  | _, _ :: _, _, ⟨W₁, h1, h2⟩, _, _, hs => ⟨W₁, h1, SlotsOK.snoc h2 hs⟩

/-- **The translated pieces of a chain of valid slots.** -/
theorem slotsOK_out :
    ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      KPath ztwiq zta (Qof P).n V (sls.flatMap zthkm) V' ∧
        (∀ pc ∈ sls.flatMap zthkm, PcV P ztwiq m E Hγ pc) ∧
        (sls ≠ [] → sls.flatMap zthkm ≠ [])
  | _, [], _, h => by_tauto
  | _, sl :: sls, _, ⟨V₁, h1, h2⟩ => by
    obtain ⟨k1, v1, n1⟩ := slotOK_out h1
    obtain ⟨k2, v2, -⟩ := slotsOK_out h2
    refine ⟨?_, fun pc hpc => ?_, fun _ => ?_⟩
    · rw [List.flatMap_cons]; exact k1.append _ k2
    · grind
    simp_all
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)
open Machine

/-! ## Indexed facts of a path of unwrapped keys -/
variable {M : Model} {Q : Polygon} {P : Polygon} {c c' : Config} {Hγ Gγ e₁ : ℕ}
/-- Consecutive ends of a path of unwrapped keys are congruent. -/
theorem kpath_idx {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ},
    KPath M Q n V ps V' → ∀ i (hi : i + 1 < ps.length), ∃ (j j' : ℤ),
      M.key Q (ps[i]' by_omega).e + j * n = M.key Q (ps[i + 1]'hi).s + j' * n
  | _, [], _, _, i, hi => by_grind
  | _, [_], _, _, i, hi => by_grind
  | _, pc :: q :: qs, _, ⟨_, V₁, _, ⟨j, hj⟩, hp⟩, i, hi => by
    zubuk
    · obtain ⟨⟨j', hj'⟩, -⟩ := hp
      grind
    · have := kpath_idx hp i by_simp_all
      simp_all

/-- Keys of proper positions on the walk lie in `[0, n)`. -/
theorem pkey_bd {N : ℕ} {x : WPos} (hx : ProperPos M Q N x)
    (he : x.edge < M.W.n) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  zuxf

/-- **The answer of the interior cutter**: the order facts of `CutterOK` from a path of unwrapped
interior keys within one lap. -/
theorem cut_out {ps : List Pc} {V0 V1 : ℝ} {m : ℕ → ℕ} {E Hγ : ℕ} {s e : WPos}
    (hk : KPath ztwiq zta (Qof P).n V0 ps V1)
    (hv : ∀ pc ∈ ps, PcV P ztwiq m E Hγ pc) (hne : ps ≠ [])
    (hs : V0 = (interiorModel zta).key zta s)
    (he : ∃ j : ℤ, V1 = (interiorModel zta).key zta e + j * (Qof P).n)
    (hsb : 0 ≤ (interiorModel zta).key zta s ∧
      (interiorModel zta).key zta s < (Qof P).n)
    (heb : 0 ≤ (interiorModel zta).key zta e ∧
      (interiorModel zta).key zta e < (Qof P).n)
    (hle : V1 ≤ V0 + (Qof P).n) :
    (interiorModel zta).key zta (ps[0]' zthre).s =
        (interiorModel zta).key zta s ∧
      (interiorModel zta).key zta (ps[ps.length - 1]'(by
        have := List.length_pos_iff.2 hne; omega)).e = (interiorModel (Qof P)).key (Qof P) e ∧
      (∀ i (hi : i + 1 < ps.length), (interiorModel zta).key zta (ps[i]' by_omega).e =
        (interiorModel zta).key zta (ps[i + 1]'hi).s) ∧
      (∀ i (hi : i + 1 < ps.length), sideInArc ((interiorModel zta).key zta (ps[i]' by_omega).s)
        ((interiorModel zta).key zta e) ((interiorModel zta).key zta (ps[i]' by_omega).e)) := by
  set M := interiorModel zta with hM
  set Q := Qof P with hQd
  have hmi : M.W.n = Q.n := mi_n
  have hQ : ztlaf := qn'
  zulkj
  have hn0 : (0 : ℝ) < Q.n := by_grind
  have hb : ∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < Q.n) ∧
      (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < Q.n) := by
    zujbk
    obtain ⟨h1, h2, h3, h4, -⟩ := hv pc hpc
    have a := pkey_bd h1 h3
    have b := pkey_bd h2 h4
    simp_all
  have hget : ∀ i (hi : i < ps.length), ps[i]'hi ∈ ps := by_simp_all
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · -- the first key
    obtain ⟨pc, qs, rfl⟩ : ∃ pc qs, ps = pc :: qs := List.exists_cons_of_ne_nil hne
    obtain ⟨⟨i, hi⟩, -⟩ := hk
    zulrs
    exact (ShootCut.key_eq_of_unw hn0 by_grind hsb (i := i) (j := 0)
      by_grind).symm.symm
  · -- the last key
    zudeq

    rw [← List.getLast_eq_getElem hne]
    exact ShootCut.key_eq_of_unw hn0 by_simp_all heb (i := j) (j := j')
      by_simp_all
  · obtain ⟨j, j', h⟩ := kpath_idx hk i hi
    exact ShootCut.key_eq_of_unw hn0 by_simp_all by_simp_all h
  · have := ShootCut.e6_of_kpath hn0 hk hle hb hne i hi
    have hl : M.key Q (ps.getLast hne).e = M.key Q e := by
      zudeq

      exact ShootCut.key_eq_of_unw hn0 by_simp_all heb (i := j) (j := j')
        by_simp_all
    grind

/-! ## The edges of the pieces of a slot -/

/-- **The pieces of a valid slot lie in its stretch**: their edges are at most `ℓ < n` beyond
`g₀`, and the stretch starts at an interior vertex. -/
theorem slotOK_edges {m : ℕ → ℕ} {E Hγ e₁ : ℕ} {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) :
    sl.u₀ < (Qof P).n ∧ sl.L + 1 + 7 * sl.q ≤ E ∧ m sl.L = sl.q ∧ 1 ≤ sl.q ∧
      ∀ i, i < sl.q → (rdPc m sl.L i).s.edge - sl.g₀ < (Qof P).n ∧
        (rdPc m sl.L i).e.edge - sl.g₀ < (Qof P).n := by
  zudy
  zudq
  refine ⟨S.hu, hLE, hq, hq1, fun i hi => ?_⟩
  zudbp

  have hne : ztppl := by
    grind
  have hget : ztfxf := by_simp_all
  have h0' : (chainModel C).key zta (ps[0]' zthre).s =
      (chainModel C).key zta sa := by_simp_all
  have hl' : (chainModel C).key zta (ps[ps.length - 1]'(by
      omega)).e = (chainModel C).key (Qof P) ea := by
    simp_all
  have hc' : ∀ i (hi : i + 1 < ps.length), (chainModel C).key zta (ps[i]' by_omega).e =
      (chainModel C).key zta (ps[i + 1]'hi).s := by_simp_all
  have ht' : ∀ i (hi : i + 1 < ps.length), sideInArc ztxji
      ztxjj ztxjh :=
    by simp_all
  obtain ⟨m1, m2, m3⟩ := chain_mono hne r3 h0' hl' hc' ht' i by_omega
  zuijv
  have hp := hv i hi
  zujz

  omega

/-! ## The slot registers -/

/-- **Slot `k`** in the registers `170201 + 5 k … 170204 + 5 k` (its flag at `170200 + 5 k`). -/
def slotAt (c : Config) (k : ℕ) : Slot :=
  ⟨c.nreg zteko, c.nreg ztekp, c.nreg ztekq,
    c.nreg ztekr⟩

/-- **The recorded slots** among the first `k`, in order. -/
def slotsOf (c : Config) : ℕ → List Slot
  | 0 => []
  | k + 1 => slotsOf c k ++ (if c.nreg ztvc = 1 then [slotAt c k] else [])
theorem slotsOf_congr :
    ∀ {k : ℕ}, (∀ j f, j < k → f < 5 → c'.nreg ztney = c.nreg ztney) →
      slotsOf c' k = slotsOf c k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := slotsOf_congr (k := k) (fun j f hj hf => h j f by_omega hf)
    have h0 := h k 0 by_omega by_omega
    have h1 := h k 1 by_omega by_omega
    have h2 := h k 2 by_omega by_omega
    have h3 := h k 3 by_omega by_omega
    have h4 := h k 4 by_omega by_omega
    zudca
    have e : slotAt c' k = slotAt c k := by
      unfold slotAt
      grind
    simp only [slotsOf, ih, h0, e]
theorem slotsOf_free {c : Config} {k : ℕ} :
    ∀ {K : ℕ}, k ≤ K → (∀ j, k ≤ j → j < K → c.nreg ztbln = 0) →
      slotsOf c K = slotsOf c k
  | 0, hk, _ => by_simp_all
  | K + 1, hk, h => by
    zukln
    · have ih := slotsOf_free (K := K) by_omega (fun j h1 h2 => h j h1 by_omega)
      simp only [slotsOf, ih, h K by_omega by_omega]
      simp
    simp_all

/-- Recording slot `k`. -/
theorem slotsOf_rec {k : ℕ} (hk : k < 4)
    (hfree : ∀ j, k ≤ j → j < 4 → c.nreg ztbln = 0)
    (hfree' : ∀ j, k + 1 ≤ j → j < 4 → c'.nreg ztbln = 0)
    (hr : ∀ r, r < 170200 + 5 * k → c'.nreg r = c.nreg r)
    (hf : c'.nreg ztvc = 1) :
    slotsOf c' 4 = slotsOf c 4 ++ [slotAt c' k] := by
  rw [slotsOf_free by_omega hfree', slotsOf_free by_omega hfree]
  simp only [slotsOf, hf, ite_true]
  rw [slotsOf_congr (fun j f hj hf => hr _ by_omega)]

/-- **The slot state**: the recorded slots form a chain of valid slots from `V0` to `V`, the
slots from `k` on are free, the flags are bits, each slot has at most `Gγ` pieces. -/
structure SlotSt (P : Polygon) (Hγ Gγ e₁ : ℕ) (V0 V : ℝ) (k : ℕ) (c : Config) : Prop where
  ok : SlotsOK P c.nmem ztm Hγ e₁ V0 ztuap V
  free : ∀ j, k ≤ j → j < 4 → c.nreg ztbln = 0
  bit : ∀ j, j < 4 → c.nreg ztbln ≤ 1
  qG : ∀ sl ∈ slotsOf c 4, sl.q ≤ Gγ

/-- **The slot state survives** steps keeping the slot registers and the memory below the
allocator, not lowering the allocator. -/
theorem SlotSt.keep {V0 V : ℝ} {k : ℕ} {c c' : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hr : ∀ r, 170200 ≤ r → r < 170220 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SlotSt P Hγ Gγ e₁ V0 V k c' := by
  have hs : slotsOf c' 4 = slotsOf c 4 := slotsOf_congr by_grind
  refine ⟨?_, fun j h1 h2 => ?_, fun j hj => ?_, fun sl hsl => h.qG sl by_simp_all⟩
  · zvmyz; exact h.ok.keep hm ha
  · zuoej; exact h.free j h1 h2
  · zuoej; exact h.bit j hj

/-- **Recording slot `k`**: a valid slot from `V` to `V'` with at most `Gγ` pieces. -/
theorem SlotSt.add {V0 V V' : ℝ} {k : ℕ} {c c' : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hk : k < 4)
    (hr : ∀ r, ztcav → c'.nreg r = c.nreg r)
    (hf : c'.nreg ztvc = 1) (hm : c'.nmem = c.nmem)
    (hs : SlotOK P c.nmem ztm Hγ e₁ V V' (slotAt c' k)) (hq : (slotAt c' k).q ≤ Gγ) :
    SlotSt P Hγ Gγ e₁ V0 V' zts c' := by
  have hA : ztble := hr _ ztbaex
  have hfree' : ∀ j, k + 1 ≤ j → j < 4 → c'.nreg ztbln = 0 := fun j h1 h2 => by
    zunax; exact h.free j by_omega h2
  have he := slotsOf_rec hk h.free hfree' by_grind hf
  refine ⟨?_, hfree', fun j hj => ?_, fun sl hsl => ?_⟩
  · rw [he, hm, hA]; exact h.ok.snoc hs
  · rcases (show j < k ∨ j = k ∨ k < j by omega) with h1 | h1 | h1
    · zunax; exact h.bit j hj
    · grind
    grind
  · rw [he, List.mem_append, List.mem_singleton] at hsl
    rcases hsl with hsl | rfl
    · exact h.qG sl hsl
    omega

/-- The number of recorded slots is at most `k`. -/
theorem slotsOf_length {c : Config} : ∀ {k : ℕ}, (slotsOf c k).length ≤ k
  | 0 => le_rfl
  | k + 1 => by
    have := slotsOf_length (c := c) (k := k)
    simp only [slotsOf, List.length_append]
    grind

/-! ## One lap -/

/-- **A normalized query spans at most one lap.** -/
theorem ee_bound {e₁ h₁ e₂ h₂ : ℕ} (hn : 1 ≤ Q.n)
    (hx : 0 ≤ (interiorModel Q).param Q ztcbt)
    (hy : (interiorModel Q).param Q ztcbu < 1) :
    (eeOf Q e₁ h₁ e₂ h₂ : ℝ) + (interiorModel Q).param Q ztcbu ≤
      Q.n + (interiorModel Q).param Q ztcbt := by
  unfold eeOf
  zumpw
  · push_cast; have : (1 : ℝ) ≤ Q.n := by_simp_all
    linarith
  · simp_all
  · have hd : WalkEmbed.dOf Q.n e₁ e₂ < Q.n := by
      unfold WalkEmbed.dOf; exact Nat.mod_lt _ by_omega
    have : zthnx := by exact_mod_cast hd
    linarith
