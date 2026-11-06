module

public import Chazelle.Core.GranRamJw

/-!
# WP-F, RAM part 4: the front of the worklist body and the merged weight

* `MS`: the machine state of the worklist loop (constants, the state in memory, `top`,
  `nlive`, memory below the allocator of entry kept);
* `frontStmt`: pop the chord `c` (`r62`) and load its live bit (`r63`);
* `xyStmt`: its classes `X = r64`, `Y = r65` and their degrees `r66`, `r67`;
* `ndStmt`: its positions `n1 = r68`, `n2 = r69`, their counts and death bits `r72`, `r73`;
* `muStmt`: `r78 := St.mu E c`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The dimensions agree with the environment. -/
structure DimOK (E : Env) (d : Dm) (W : ℕ) : Prop where
  K : d.K = E.K
  A : d.A = E.A
  R : d.R = E.R
  D : d.D = E.D
  base : d.b0 + d.oEnd ≤ W
  sz : E.sz ≤ W
  W1 : 3 ≤ W

/-- **The machine state of the worklist loop.** -/
structure MS (W : ℕ) (E : Env) (d : Dm) (A₀ : ℕ) (m₀ : ℕ → ℕ) (c : Config) (st : St) : Prop where
  wb : WordsBounded W c
  cst : Cst c E d
  enc : Enc c.nmem d st
  top : c.nreg 90050 = st.top
  nlive : c.nreg 90051 = st.nlive
  low : ∀ a, a < A₀ → c.nmem a = m₀ a

/-- A weight bound of the static arrays. -/
theorem bx_le {E : Env} {st : St} (hE : E.Good) (h : StatOK E st) {j : ℕ} (hj : j < E.A) :
    st.eg j + st.pz j ≤ E.sz := by
  have he := edge_lt hE hj
  have hcnt := hE.hcd.2 _ he
  obtain ⟨h1, h2⟩ := h.pz j hj
  rw [h.eg j hj]
  unfold Env.sz cntIn bB
  have hnE : E.n = E.M.W.n := rfl
  cases hch : E.ch with
  | false => simp only [Bool.false_eq_true, ite_false]; omega
  | true =>
    have hn := hE.hn hch
    simp only [ite_true]
    rw [hch] at hcnt
    simp only [Bool.true_eq_false, false_or] at hcnt
    by_cases hz : st.pz j = 1
    · have := hcnt.1 (h2.1 hz).1
      omega
    · omega

/-! ## Popping -/

/-- `top := top - 1`. -/
def popStmt : Stmt := .instr (.subN 90050 90050 90019)

theorem MS.pop {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {P : Polygon} {c : Config}
    {st : St} (h : MS W E d A₀ m₀ c st) :
    ∃ c' k, Exec P W popStmt c c' k ∧ k = 1 ∧ MS W E d A₀ m₀ c' st.pop ∧
      (∀ r, r ≠ 90050 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have e := Exec.subN (P := P) h.wb 90050 90050 90019
  refine ⟨_, 1, e, rfl, ⟨e.wb_right, h.cst.frame fun r hr _ => ?_, ?_, ?_, ?_, h.low⟩,
    fun r hr => by simp [upd, hr], rfl⟩
  · simp [upd, show r ≠ 90050 by omega]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h.enc
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  · simp only [upd, ite_true, St.pop]; rw [h.top, h.cst.one]
  · simp only [upd, show (90051 : ℕ) ≠ 90050 by decide, ite_false, St.pop]; exact h.nlive

/-! ## The front -/

/-- Pop the chord `c` into `r62` and its live bit into `r63` (`r60 = top - 1`). -/
def frontStmt : Stmt := block [.subN 90060 90050 90019, .addN 90061 90043 90060,
  .loadN 90062 90061, .addN 90061 90030 90062, .loadN 90063 90061]

theorem front_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (h : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (htop : 0 < st.top) :
    ∃ c' k, Exec P W frontStmt c c' k ∧ k = 5 ∧ c'.nreg 90062 = st.cur ∧
      c'.nreg 90063 = st.live st.cur ∧ st.cur < E.K ∧
      (∀ r, r ≠ 90060 → r ≠ 90061 → r ≠ 90062 → r ≠ 90063 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  have hw := h.wb
  have hC := h.cst
  have hb := hD.base
  have hcap : st.top ≤ d.cap := by
    have h1 := hI.topLe
    rw [show d.cap = E.K + E.D * E.K by unfold Dm.cap; rw [hD.K, hD.D]]
    omega
  have hcurK : st.cur < E.K := hI.stk _ (by omega)
  unfold frontStmt
  exec_block
  · config_simp; rw [hC.bStk, h.top, hC.one]; dm_simp; omega
  · config_simp; rw [hC.bStk, h.top, hC.one, hC.bLive, show d.b0 + d.oStk + (st.top - 1) =
      d.b0 + d.oStk + (st.top - 1) from rfl, h.enc.stk _ (by omega)]
    unfold St.cur at hcurK; dm_simp; rw [hD.K] at *; omega
  · have e1 : c.nmem (d.b0 + d.oStk + (st.top - 1)) = st.cur := h.enc.stk _ (by omega)
    have e2 : c.nmem (d.b0 + st.cur) = st.live st.cur := h.enc.live _ (by rw [hD.K]; exact hcurK)
    refine ⟨rfl, ?_, ?_, hcurK, fun r a1 a2 a3 a4 => by simp [upd, a1, a2, a3, a4], rfl⟩
    · config_simp; rw [hC.bStk, h.top, hC.one, e1]
    · config_simp; rw [hC.bStk, h.top, hC.one, e1, hC.bLive, e2]

/-- The classes of `c` and their degrees. -/
def xyStmt : Stmt := block [.addN 90061 90031 90062, .loadN 90064 90061,
  .addN 90061 90032 90062, .loadN 90065 90061, .addN 90061 90035 90064, .loadN 90066 90061,
  .addN 90061 90035 90065, .loadN 90067 90061]

theorem xy_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hI : Inv E st)
    (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E) (h62 : c.nreg 90062 = cc) :
    ∃ c' k, Exec P W xyStmt c c' k ∧ k = 8 ∧ c'.nreg 90064 = st.s0 cc ∧
      c'.nreg 90065 = st.s1 cc ∧ c'.nreg 90066 = st.deg (st.s0 cc) ∧
      c'.nreg 90067 = st.deg (st.s1 cc) ∧
      (∀ r, r ≠ 90061 → r ≠ 90064 → r ≠ 90065 → r ≠ 90066 → r ≠ 90067 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨hX, hY, -, -⟩ := hI.sides cc hc
  have hcK : cc < d.K := by rw [hD.K]; exact hc.1
  have e1 : c.nmem (d.b0 + d.oS0 + cc) = st.s0 cc := henc.s0 _ hcK
  have e2 : c.nmem (d.b0 + d.oS1 + cc) = st.s1 cc := henc.s1 _ hcK
  have e3 : c.nmem (d.b0 + d.oDeg + st.s0 cc) = st.deg (st.s0 cc) :=
    henc.deg _ (by rw [hD.R]; exact hX)
  have e4 : c.nmem (d.b0 + d.oDeg + st.s1 cc) = st.deg (st.s1 cc) :=
    henc.deg _ (by rw [hD.R]; exact hY)
  have hR : st.s0 cc < d.R ∧ st.s1 cc < d.R := by rw [hD.R]; exact ⟨hX, hY⟩
  have hb := hD.base
  unfold xyStmt
  exec_block
  · rw [hC.bS0, h62]; dm_simp; omega
  · config_simp; rw [hC.bS1, h62]; dm_simp; omega
  · config_simp; rw [hC.bS0, h62, e1, hC.bDeg]; dm_simp; omega
  · config_simp; rw [hC.bS1, h62, e2, hC.bDeg]; dm_simp; omega
  · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => by simp [upd, a1, a2, a3, a4, a5], rfl⟩
    · config_simp; rw [hC.bS0, h62, e1]
    · config_simp; rw [hC.bS1, h62, e2]
    · config_simp; rw [hC.bS0, h62, e1, hC.bDeg, e3]
    · config_simp; rw [hC.bS1, h62, e2, hC.bDeg, e4]

/-! ## The positions of `c` -/

/-- The positions of `c`, their counts and death bits. -/
def ndStmt : Stmt :=
  .seq (block [.addN 90061 90033 90062, .loadN 90068 90061, .addN 90061 90034 90062,
      .loadN 90069 90061, .addN 90061 90038 90068, .loadN 90070 90061, .addN 90061 90038 90069,
      .loadN 90071 90061])
    (.seq (.ifLtN 90070 90021 (.instr (.constN 90072 1)) (.instr (.constN 90072 0)))
      (.ifLtN 90071 90021 (.instr (.constN 90073 1)) (.instr (.constN 90073 0))))

theorem wr_ndStmt : wr (Bin 90061 90074) ndStmt = true := by decide

/-- A death bit from a positive count. -/
theorem bitSet_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {rk rd : ℕ} (h21 : c.nreg 90021 = 2) (hk : 0 < c.nreg rk) :
    ∃ c' k, Exec P W (.ifLtN rk 90021 (.instr (.constN rd 1)) (.instr (.constN rd 0))) c c' k ∧
      k ≤ 3 ∧ c'.nreg rd = bit (decide (c.nreg rk = 1)) ∧
      (∀ r, r ≠ rd → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  by_cases h : c.nreg rk < 2
  · exact ⟨_, _, .ifLtN_true (by rw [h21]; exact h) (Exec.constN hw rd 1 hW), by omega,
      by simp [upd, bit, show c.nreg rk = 1 by omega], fun r hr => by simp [upd, hr], rfl⟩
  · exact ⟨_, _, .ifLtN_false (by rw [h21]; exact h) (Exec.constN hw rd 0 (by omega)),
      by omega, by simp [upd, bit, show c.nreg rk ≠ 1 by omega], fun r hr => by simp [upd, hr],
      rfl⟩

theorem nd_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hI : Inv E st)
    (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E) (h62 : c.nreg 90062 = cc) :
    ∃ c' k, Exec P W ndStmt c c' k ∧ k ≤ 14 ∧ c'.nreg 90068 = st.nd0 cc ∧
      c'.nreg 90069 = st.nd1 cc ∧
      c'.nreg 90072 = bit (decide (st.cnt (st.nd0 cc) = 1)) ∧
      c'.nreg 90073 = bit (decide (st.cnt (st.nd1 cc) = 1)) ∧ FrameB (Bin 90061 90074) c c' := by
  suffices hh : ∃ c' k, Exec P W ndStmt c c' k ∧ k ≤ 14 ∧ c'.nreg 90068 = st.nd0 cc ∧
      c'.nreg 90069 = st.nd1 cc ∧
      c'.nreg 90072 = bit (decide (st.cnt (st.nd0 cc) = 1)) ∧
      c'.nreg 90073 = bit (decide (st.cnt (st.nd1 cc) = 1)) by
    obtain ⟨c', k, e, hk, h1, h2, h3, h4⟩ := hh
    exact ⟨c', k, e, hk, h1, h2, h3, h4, exec_frameB e wr_ndStmt⟩
  have hb := hD.base
  have hcK : cc < d.K := by rw [hD.K]; exact hc.1
  obtain ⟨hn0, -⟩ := hI.stat.nd0 cc hc.1
  obtain ⟨hn1, -⟩ := hI.stat.nd1 cc hc.1
  have hL0 := (hI.lv_iff hn0).2 ⟨cc, hc, Or.inl rfl⟩
  have hL1 := (hI.lv_iff hn1).2 ⟨cc, hc, Or.inr rfl⟩
  rw [← hD.A] at hn0 hn1
  have e1 : c.nmem (d.b0 + d.oNd0 + cc) = st.nd0 cc := henc.nd0 _ hcK
  have e2 : c.nmem (d.b0 + d.oNd1 + cc) = st.nd1 cc := henc.nd1 _ hcK
  have e3 : c.nmem (d.b0 + d.oCnt + st.nd0 cc) = st.cnt (st.nd0 cc) := henc.cnt _ hn0
  have e4 : c.nmem (d.b0 + d.oCnt + st.nd1 cc) = st.cnt (st.nd1 cc) := henc.cnt _ hn1
  unfold ndStmt
  obtain ⟨c₁, k₁, ex₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90061 90033 90062,
      .loadN 90068 90061, .addN 90061 90034 90062, .loadN 90069 90061, .addN 90061 90038 90068,
      .loadN 90070 90061, .addN 90061 90038 90069, .loadN 90071 90061]) c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 90068 = st.nd0 cc ∧ c₁.nreg 90069 = st.nd1 cc ∧
        c₁.nreg 90070 = st.cnt (st.nd0 cc) ∧ c₁.nreg 90071 = st.cnt (st.nd1 cc) ∧
        c₁.nreg 90021 = 2) := by
    exec_block
    · rw [hC.bNd0, h62]; dm_simp; omega
    · config_simp; rw [hC.bNd1, h62]; dm_simp; omega
    · config_simp; rw [hC.bNd0, h62, e1, hC.bCnt]; dm_simp; omega
    · config_simp; rw [hC.bNd1, h62, e2, hC.bCnt]; dm_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
      · rw [hC.bNd0, h62, e1]
      · rw [hC.bNd1, h62, e2]
      · rw [hC.bNd0, h62, e1, hC.bCnt, e3]
      · rw [hC.bNd1, h62, e2, hC.bCnt, e4]
      · exact hC.two
  obtain ⟨q68, q69, q70, q71, q21⟩ := q
  obtain ⟨c₂, k₂, ex₂, hk₂, b₂, r₂, -⟩ := bitSet_exec (P := P) (rk := 90070) (rd := 90072) c₁
    ex₁.wb_right (by have := hD.W1; omega) q21 (by rw [q70]; exact hL0)
  obtain ⟨c₃, k₃, ex₃, hk₃, b₃, r₃, -⟩ := bitSet_exec (P := P) (rk := 90071) (rd := 90073) c₂
    ex₂.wb_right (by have := hD.W1; omega) (by rw [r₂ _ (by decide), q21])
    (by rw [r₂ _ (by decide), q71]; exact hL1)
  refine ⟨c₃, _, .seq ex₁ (.seq ex₂ ex₃), by omega, ?_, ?_, ?_, ?_⟩
  · rw [r₃ _ (by decide), r₂ _ (by decide), q68]
  · rw [r₃ _ (by decide), r₂ _ (by decide), q69]
  · rw [r₃ _ (by decide), b₂, q70]
  · rw [b₃, r₂ _ (by decide), q71]

/-! ## The merged weight -/

/-- `rd := max ra rb`. -/
theorem maxSet_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {ra rb rd : ℕ} :
    ∃ c' k, Exec P W (.ifLtN ra rb (.instr (.copyN rd rb)) (.instr (.copyN rd ra))) c c' k ∧
      k ≤ 3 ∧ c'.nreg rd = max (c.nreg ra) (c.nreg rb) ∧
      (∀ r, r ≠ rd → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  by_cases h : c.nreg ra < c.nreg rb
  · exact ⟨_, _, .ifLtN_true h (Exec.copyN hw rd rb), by omega,
      by simp [upd, max_eq_right h.le], fun r hr => by simp [upd, hr], rfl⟩
  · exact ⟨_, _, .ifLtN_false h (Exec.copyN hw rd ra), by omega,
      by simp [upd, max_eq_left (not_lt.1 h)], fun r hr => by simp [upd, hr], rfl⟩

/-- `r78 := max (max r74 r75) (max r76 r77)`. -/
def maxStmt : Stmt :=
  .seq (.ifLtN 90074 90075 (.instr (.copyN 90079 90075)) (.instr (.copyN 90079 90074)))
    (.seq (.ifLtN 90076 90077 (.instr (.copyN 90078 90077)) (.instr (.copyN 90078 90076)))
      (.ifLtN 90078 90079 (.instr (.copyN 90078 90079)) (.instr (.copyN 90078 90078))))

theorem maxStmt_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W maxStmt c c' k ∧ k ≤ 9 ∧
      c'.nreg 90078 = max (max (c.nreg 90074) (c.nreg 90075)) (max (c.nreg 90076) (c.nreg 90077)) ∧
      (∀ r, r ≠ 90078 → r ≠ 90079 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, m₁, r₁, n₁⟩ := maxSet_exec (P := P) (ra := 90074) (rb := 90075)
    (rd := 90079) c hw
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, r₂, n₂⟩ := maxSet_exec (P := P) (ra := 90076) (rb := 90077)
    (rd := 90078) c₁ e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, r₃, n₃⟩ := maxSet_exec (P := P) (ra := 90078) (rb := 90079)
    (rd := 90078) c₂ e₂.wb_right
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ?_, fun r a1 a2 => ?_, by rw [n₃, n₂, n₁]⟩
  · rw [m₃, m₂, r₂ _ (by decide), m₁, r₁ _ (by decide), r₁ _ (by decide)]
    exact max_comm _ _
  · rw [r₃ r a1, r₂ r a1, r₁ r a2]

/-- **The merged weight** `r78 := St.mu E c`. -/
def muStmt : Stmt :=
  .ifLtN 90019 90051
    (.seq (block [.addN 90061 90036 90064, .loadN 90074 90061, .addN 90061 90036 90065,
        .loadN 90075 90061, .copyN 90086 90068, .copyN 90087 90072])
      (.seq jwStmt (.seq (.instr (.copyN 90076 90085))
        (.seq (block [.copyN 90086 90069, .copyN 90087 90073])
          (.seq jwStmt (.seq (.instr (.copyN 90077 90085)) maxStmt))))))
    (.instr (.copyN 90078 90018))

theorem wr_muStmt : wr (Bin 90061 90100) muStmt = true := by decide

theorem mu_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hE : E.Good) (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st)
    (hI : Inv E st) (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E)
    (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit (decide (st.cnt (st.nd0 cc) = 1)))
    (h73 : c.nreg 90073 = bit (decide (st.cnt (st.nd1 cc) = 1)))
    (h51 : c.nreg 90051 = st.nlive) :
    ∃ c' k, Exec P W muStmt c c' k ∧ k ≤ 260 ∧ c'.nreg 90078 = st.mu E cc ∧
      FrameB (Bin 90061 90100) c c' := by
  suffices hh : ∃ c' k, Exec P W muStmt c c' k ∧ k ≤ 260 ∧ c'.nreg 90078 = st.mu E cc by
    obtain ⟨c', k, e, hk, h1⟩ := hh
    exact ⟨c', k, e, hk, h1, exec_frameB e wr_muStmt⟩
  have hb := hD.base
  have hW1 : 1 ≤ W := by have := hD.W1; omega
  have hfin : (st.L E).Finite := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
  have hnl : 1 ≤ st.nlive := by rw [hI.nlive]; exact (Set.ncard_pos hfin).2 ⟨cc, hc⟩
  unfold muStmt St.mu
  by_cases h1 : st.nlive = 1
  · refine spec_ifLtN_false (by rw [hC.one, h51]; omega)
      (spec_instr (Exec.copyN hw _ _) fun _ => ⟨by omega, ?_⟩)
    config_simp; rw [ite_eq_left h1, hC.sz]; rfl
  refine spec_ifLtN_true (by rw [hC.one, h51]; omega) ?_
  rw [ite_eq_right h1]
  obtain ⟨hX, hY, -, -⟩ := hI.sides cc hc
  rw [← hD.R] at hX hY
  have e1 : c.nmem (d.b0 + d.oWt + st.s0 cc) = st.wt (st.s0 cc) := henc.wt _ hX
  have e2 : c.nmem (d.b0 + d.oWt + st.s1 cc) = st.wt (st.s1 cc) := henc.wt _ hY
  obtain ⟨c₁, k₁, ex₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90061 90036 90064,
      .loadN 90074 90061, .addN 90061 90036 90065, .loadN 90075 90061, .copyN 90086 90068,
      .copyN 90087 90072]) c c₁ k₁ ∧ k₁ = 6 ∧
      (c₁.nreg 90074 = st.wt (st.s0 cc) ∧ c₁.nreg 90075 = st.wt (st.s1 cc) ∧
        c₁.nreg 90086 = st.nd0 cc ∧ c₁.nreg 90087 = bit (decide (st.cnt (st.nd0 cc) = 1)) ∧
        (∀ r, r ≠ 90061 → r ≠ 90074 → r ≠ 90075 → r ≠ 90086 → r ≠ 90087 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    · rw [hC.bWt, h64]; dm_simp; omega
    · config_simp; rw [hC.bWt, h65]; dm_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => by simp [upd, a1, a2, a3, a4, a5],
        rfl⟩ <;> config_simp
      · rw [hC.bWt, h64, e1]
      · rw [hC.bWt, h65, e2]
      · exact h68
      · exact h72
  obtain ⟨q74, q75, q86, q87, qr, qm⟩ := q
  -- common facts for the two gaps
  have hring : ∀ j, j < d.A → 0 < st.cnt j → st.prv j < d.A ∧ 0 < st.cnt (st.prv j) ∧
      st.nxt j < d.A ∧ 0 < st.cnt (st.nxt j) := by
    intro j hj hL
    rw [hD.A] at hj ⊢
    obtain ⟨⟨a, b, -, -⟩, ⟨a', b', -, -⟩⟩ := hI.ring j hj hL
    exact ⟨a', b', a, b⟩
  have hbx : ∀ j, j < d.A → st.eg j + st.pz j ≤ E.sz := fun j hj =>
    bx_le hE hI.stat (by rw [← hD.A]; exact hj)
  obtain ⟨hn0, -⟩ := hI.stat.nd0 cc hc.1
  obtain ⟨hn1, -⟩ := hI.stat.nd1 cc hc.1
  have hL0 := (hI.lv_iff hn0).2 ⟨cc, hc, Or.inl rfl⟩
  have hL1 := (hI.lv_iff hn1).2 ⟨cc, hc, Or.inr rfl⟩
  rw [← hD.A] at hn0 hn1
  have hC₁ : Cst c₁ E d := hC.frame fun r hr _ => qr r (by omega) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨c₂, k₂, ex₂, hk₂, j₂, f₂⟩ := jwStmt_exec (P := P) c₁ ex₁.wb_right hW1 hC₁
    (by rw [qm]; exact henc) (cc := cc) (k := st.nd0 cc) q86 q87
    (by rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h68])
    (by rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h69])
    (by rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h72])
    (by rw [qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h73])
    hn0 hL0 hring hbx hD.sz hb
  have g₂ : ∀ r, Bin 90080 90100 r = false → c₂.nreg r = c₁.nreg r := f₂.1
  obtain ⟨c₃, k₃, e₃, hk₃, q76, q3r, q3m⟩ : ∃ c₃ k₃, Exec P W (.instr (.copyN 90076 90085)) c₂ c₃
      k₃ ∧ k₃ = 1 ∧ c₃.nreg 90076 = c₂.nreg 90085 ∧ (∀ r, r ≠ 90076 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem :=
    ⟨_, 1, Exec.copyN ex₂.wb_right 90076 90085, rfl, by simp [upd],
      fun r hr => by simp [upd, hr], rfl⟩
  obtain ⟨c₄, k₄, ex₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 90086 90069,
      .copyN 90087 90073]) c₃ c₄ k₄ ∧ k₄ = 2 ∧
      (c₄.nreg 90086 = st.nd1 cc ∧ c₄.nreg 90087 = bit (decide (st.cnt (st.nd1 cc) = 1)) ∧
        (∀ r, r ≠ 90086 → r ≠ 90087 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem) := by
    have hw₃ := e₃.wb_right
    exec_block
    refine ⟨rfl, ?_, ?_, fun r a1 a2 => by simp [upd, a1, a2], rfl⟩ <;> config_simp
    · rw [q3r _ (by decide), g₂ _ (by decide), qr _ (by decide) (by decide) (by decide) (by decide) (by decide),
        h69]
    · rw [q3r _ (by decide), g₂ _ (by decide),
        qr _ (by decide) (by decide) (by decide) (by decide) (by decide), h73]
  obtain ⟨q86', q87', qr', qm'⟩ := q
  have c4r : ∀ r, r < 90080 → r ≠ 90061 → r ≠ 90074 → r ≠ 90075 → r ≠ 90076 →
      c₄.nreg r = c.nreg r := by
    intro r a0 a1 a2 a3 a4
    rw [qr' r (by omega) (by omega), q3r r a4, g₂ r (Bin_false (by omega)),
      qr r a1 a2 a3 (by omega) (by omega)]
  have hC₄ : Cst c₄ E d := hC.frame fun r hr _ => c4r r (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have m4 : c₄.nmem = c.nmem := by rw [qm', q3m, f₂.2.2.1, qm]
  obtain ⟨c₅, k₅, ex₅, hk₅, j₅, f₅⟩ := jwStmt_exec (P := P) c₄ ex₄.wb_right hW1 hC₄
    (by rw [m4]; exact henc) (cc := cc) (k := st.nd1 cc) q86' q87'
    (by rw [c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), h68])
    (by rw [c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), h69])
    (by rw [c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), h72])
    (by rw [c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), h73])
    hn1 hL1 hring hbx hD.sz hb
  have e₆ := Exec.copyN (P := P) ex₅.wb_right 90077 90085
  obtain ⟨c₇, k₇, ex₇, hk₇, m₇, -, -⟩ := maxStmt_exec (P := P) _ e₆.wb_right
  refine ⟨c₇, _, .seq ex₁ (.seq ex₂ (.seq e₃ (.seq ex₄ (.seq ex₅ (.seq e₆ ex₇))))), by omega, ?_⟩
  rw [m₇]
  have v76 : c₅.nreg 90076 = st.jw E cc (st.nd0 cc) := by
    rw [f₅.1 _ (by decide), qr' _ (by decide) (by decide), q76]
    exact j₂
  simp only [upd, ite_true, show (90074 : ℕ) ≠ 90077 by decide,
    show (90075 : ℕ) ≠ 90077 by decide, show (90076 : ℕ) ≠ 90077 by decide]
  have v74 : c₅.nreg 90074 = st.wt (st.s0 cc) := by
    rw [f₅.1 _ (by decide), qr' _ (by decide) (by decide), q3r _ (by decide),
      g₂ _ (by decide), q74]
  have v75 : c₅.nreg 90075 = st.wt (st.s1 cc) := by
    rw [f₅.1 _ (by decide), qr' _ (by decide) (by decide), q3r _ (by decide),
      g₂ _ (by decide), q75]
  rw [v74, v75, v76, j₅]
  simp only [ite_false]

end

end Gran

end Chazelle.Core
