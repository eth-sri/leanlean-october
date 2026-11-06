module

public import Chazelle.MacT
public import Chazelle.Core.GranWt
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.SpecNF
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Core.OracleBook

namespace Chazelle.Core
namespace Gran
open Machine Machine.Stmt Programs SignK
@[expose] public section
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
  zuhzi
  cases hch : E.ch with
  | false => zvnhh; omega
  | true =>
    have hn := hE.hn hch
    zuwa
    zubma

    by_cases hz : st.pz j = 1
    · grind
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
    fun r hr => by_simp_all, rfl⟩
  · simp [upd, show r ≠ 90050 by omega]
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h.enc
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  · simp only [upd, ite_true, St.pop]; rw [h.top, h.cst.one]
  · simp only [upd, show (90051 : ℕ) ≠ 90050 by decide, ite_false, St.pop]; exact h.nlive

/-! ## The front -/

/-- Pop the chord `c` into `r62` and its live bit into `r63` (`r60 = top - 1`). -/
def frontStmt : Stmt := block [.subN 90060 90050 90019, .addN 90061 90043 90060,
  .loadN 90062 90061, .addN 90061 90030 90062, .loadN 90063 90061]
variable {P : Polygon}
theorem front_exec {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (h : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (htop : 0 < st.top) :
    ∃ c' k, Exec P W frontStmt c c' k ∧ k = 5 ∧ c'.nreg 90062 = st.cur ∧
      c'.nreg 90063 = st.live st.cur ∧ st.cur < E.K ∧
      (∀ r, r ≠ 90060 → r ≠ 90061 → r ≠ 90062 → r ≠ 90063 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  zuesn
  have hC := h.cst
  zubga
  have hcap : st.top ≤ d.cap := by
    have h1 := hI.topLe
    rw [show d.cap = E.K + E.D * E.K by unfold Dm.cap; rw [hD.K, hD.D]]
    omega
  have hcurK : st.cur < E.K := hI.stk _ by_omega
  unfold frontStmt
  exec_block
  · config_simp; rw [hC.bStk, h.top, hC.one]; dm_simp; omega
  · config_simp; rw [hC.bStk, h.top, hC.one, hC.bLive, show d.b0 + d.oStk + zthkp =
      d.b0 + d.oStk + zthkp from rfl, h.enc.stk _ by_omega]
    unfold St.cur at hcurK; dm_simp; rw [hD.K] at *; omega
  · have e1 : c.nmem _ = st.cur := h.enc.stk _ by_omega
    have e2 : c.nmem _ = st.live st.cur := h.enc.live _ (by rw [hD.K]; omega)
    refine ⟨rfl, ?_, ?_, hcurK, by_simp_all, rfl⟩
    · config_simp; rw [hC.bStk, h.top, hC.one, e1]
    · config_simp; rw [hC.bStk, h.top, hC.one, e1, hC.bLive, e2]

/-- The classes of `c` and their degrees. -/
def xyStmt : Stmt := block [.addN 90061 90031 90062, .loadN 90064 90061,
  .addN 90061 90032 90062, .loadN 90065 90061, .addN 90061 90035 90064, .loadN 90066 90061,
  .addN 90061 90035 90065, .loadN 90067 90061]
theorem xy_exec {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hI : Inv E st)
    (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E) (h62 : c.nreg 90062 = cc) :
    ∃ c' k, Exec P W xyStmt c c' k ∧ k = 8 ∧ c'.nreg 90064 = st.s0 cc ∧
      c'.nreg 90065 = st.s1 cc ∧ c'.nreg 90066 = st.deg ztfis ∧
      c'.nreg 90067 = st.deg ztbnp ∧
      (∀ r, r ≠ 90061 → r ≠ 90064 → r ≠ 90065 → r ≠ 90066 → r ≠ 90067 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  zueip
  zudyv
  have e1 : c.nmem _ = st.s0 cc := henc.s0 _ hcK
  have e2 : c.nmem _ = st.s1 cc := henc.s1 _ hcK
  have e3 : ztsel :=
    henc.deg _ (by zuofg; exact hX)
  have e4 : ztsel :=
    henc.deg _ (by zuofg; exact hY)
  have hR : st.s0 cc < d.R ∧ st.s1 cc < d.R := by zuofg; omega
  zubga
  unfold xyStmt
  exec_block
  · rw [hC.bS0, h62]; dm_simp; omega
  · config_simp; rw [hC.bS1, h62]; dm_simp; omega
  · config_simp; rw [hC.bS0, h62, e1, hC.bDeg]; dm_simp; omega
  · config_simp; rw [hC.bS1, h62, e2, hC.bDeg]; dm_simp; omega
  · refine ⟨rfl, ?_, ?_, ?_, ?_, by_simp_all, rfl⟩
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
theorem wr_ndStmt : wr ztsvn ndStmt = true := by_decide

/-- A death bit from a positive count. -/
theorem bitSet_exec {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {rk rd : ℕ} (h21 : c.nreg 90021 = 2) (hk : 0 < c.nreg rk) :
    ∃ c' k, Exec P W (.ifLtN rk 90021 (.instr (.constN rd 1)) (.instr (.constN rd 0))) c c' k ∧
      k ≤ 3 ∧ c'.nreg rd = bit (decide (c.nreg rk = 1)) ∧
      ztcqi ∧ c'.nmem = c.nmem := by
  by_cases h : c.nreg rk < 2
  · exact ⟨_, _, .ifLtN_true by_omega (Exec.constN hw rd 1 hW), by_omega,
      by simp [upd, bit, show c.nreg rk = 1 by omega], by_simp_all, rfl⟩
  · exact ⟨_, _, .ifLtN_false by_omega (Exec.constN hw rd 0 by_omega),
      by omega, by simp [upd, bit, show c.nreg rk ≠ 1 by omega], by_simp_all,
      rfl⟩
theorem nd_exec {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hI : Inv E st)
    (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E) (h62 : c.nreg 90062 = cc) :
    ∃ c' k, Exec P W ndStmt c c' k ∧ k ≤ 14 ∧ c'.nreg 90068 = st.nd0 cc ∧
      c'.nreg 90069 = st.nd1 cc ∧
      c'.nreg 90072 = bit ztxwi ∧
      c'.nreg 90073 = bit ztxwj ∧ FrameB ztsvn c c' := by
  suffices hh : ∃ c' k, Exec P W ndStmt c c' k ∧ k ≤ 14 ∧ c'.nreg 90068 = st.nd0 cc ∧
      c'.nreg 90069 = st.nd1 cc ∧
      c'.nreg 90072 = bit _ ∧
      c'.nreg 90073 = bit _ by
    obtain ⟨c', k, e, hk, h1, h2, h3, h4⟩ := hh
    exact ⟨c', k, e, hk, h1, h2, h3, h4, exec_frameB e wr_ndStmt⟩
  zubga
  zudyv
  zuqt

  have e1 : c.nmem _ = st.nd0 cc := henc.nd0 _ hcK
  have e2 : c.nmem _ = st.nd1 cc := henc.nd1 _ hcK
  have e3 : ztsek := henc.cnt _ hn0
  have e4 : ztsek := henc.cnt _ hn1
  unfold ndStmt
  obtain ⟨c₁, k₁, ex₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90061 90033 90062,
      .loadN 90068 90061, .addN 90061 90034 90062, .loadN 90069 90061, .addN 90061 90038 90068,
      .loadN 90070 90061, .addN 90061 90038 90069, .loadN 90071 90061]) c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 90068 = st.nd0 cc ∧ c₁.nreg 90069 = st.nd1 cc ∧
        c₁.nreg 90070 = st.cnt ztmom ∧ c₁.nreg 90071 = st.cnt ztqwx ∧
        c₁.nreg 90021 = 2) := by
    exec_block
    · rw [hC.bNd0, h62]; dm_simp; omega
    · config_simp; rw [hC.bNd1, h62]; dm_simp; omega
    · config_simp; rw [hC.bNd0, h62, e1, hC.bCnt]; dm_simp; omega
    · config_simp; rw [hC.bNd1, h62, e2, hC.bCnt]; dm_simp; omega
    · refine ztbob <;> config_simp
      · rw [hC.bNd0, h62, e1]
      · rw [hC.bNd1, h62, e2]
      · rw [hC.bNd0, h62, e1, hC.bCnt, e3]
      · rw [hC.bNd1, h62, e2, hC.bCnt, e4]
      · exact hC.two
  obtain ⟨q68, q69, q70, q71, q21⟩ := q
  obtain ⟨c₂, k₂, ex₂, hk₂, b₂, r₂, -⟩ := bitSet_exec (P := P) (rk := 90070) (rd := 90072) c₁
    ex₁.wb_right (by have := hD.W1; omega) q21 (by rw [q70]; tauto)
  obtain ⟨c₃, k₃, ex₃, hk₃, b₃, r₃, -⟩ := bitSet_exec (P := P) (rk := 90071) (rd := 90073) c₂
    ex₂.wb_right (by have := hD.W1; omega) by_simp_all
    (by rw [r₂ _ by_decide, q71]; tauto)
  refine ⟨c₃, _, .seq ex₁ (.seq ex₂ ex₃), by_omega, ?_, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-! ## The merged weight -/

/-- `rd := max ra rb`. -/
theorem maxSet_exec {W : ℕ} (c : Config) (hw : WordsBounded W c) {ra rb rd : ℕ} :
    ∃ c' k, Exec P W (.ifLtN ra rb (.instr (.copyN rd rb)) (.instr (.copyN rd ra))) c c' k ∧
      k ≤ 3 ∧ c'.nreg rd = max (c.nreg ra) (c.nreg rb) ∧
      ztcqi ∧ c'.nmem = c.nmem := by
  by_cases h : c.nreg ra < c.nreg rb
  · exact ⟨_, _, .ifLtN_true h (Exec.copyN hw rd rb), by_omega,
      by simp [upd, max_eq_right h.le], by_simp_all, rfl⟩
  · exact ⟨_, _, .ifLtN_false h (Exec.copyN hw rd ra), by_omega,
      by simp_all, by_simp_all, rfl⟩

/-- `r78 := max (max r74 r75) (max r76 r77)`. -/
def maxStmt : Stmt :=
  .seq (.ifLtN 90074 90075 (.instr (.copyN 90079 90075)) (.instr (.copyN 90079 90074)))
    (.seq (.ifLtN 90076 90077 (.instr (.copyN 90078 90077)) (.instr (.copyN 90078 90076)))
      (.ifLtN 90078 90079 (.instr (.copyN 90078 90079)) (.instr (.copyN 90078 90078))))
theorem maxStmt_exec {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W maxStmt c c' k ∧ k ≤ 9 ∧
      c'.nreg 90078 = max (max (c.nreg 90074) (c.nreg 90075)) (max (c.nreg 90076) (c.nreg 90077)) ∧
      (∀ r, r ≠ 90078 → r ≠ 90079 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, m₁, r₁, n₁⟩ := maxSet_exec (P := P) (ra := 90074) (rb := 90075)
    (rd := 90079) c hw
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, r₂, n₂⟩ := maxSet_exec (P := P) (ra := 90076) (rb := 90077)
    (rd := 90078) c₁ e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, r₃, n₃⟩ := maxSet_exec (P := P) (ra := 90078) (rb := 90079)
    (rd := 90078) c₂ e₂.wb_right
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, ?_, fun r a1 a2 => ?_, by_simp_all⟩
  · grind
  simp_all

/-- **The merged weight** `r78 := St.mu E c`. -/
def muStmt : Stmt :=
  .ifLtN 90019 90051
    (.seq (block [.addN 90061 90036 90064, .loadN 90074 90061, .addN 90061 90036 90065,
        .loadN 90075 90061, .copyN 90086 90068, .copyN 90087 90072])
      (.seq jwStmt (.seq (.instr (.copyN 90076 90085))
        (.seq (block [.copyN 90086 90069, .copyN 90087 90073])
          (.seq jwStmt (.seq (.instr (.copyN 90077 90085)) maxStmt))))))
    (.instr (.copyN 90078 90018))
theorem wr_muStmt : wr ztsvo muStmt = true := by_decide
theorem mu_exec {W : ℕ} {E : Env} {d : Dm} {st : St} {c : Config}
    (hE : E.Good) (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st)
    (hI : Inv E st) (hD : DimOK E d W) {cc : ℕ} (hc : cc ∈ st.L E)
    (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit ztxwi)
    (h73 : c.nreg 90073 = bit ztxwj)
    (h51 : c.nreg 90051 = st.nlive) :
    ∃ c' k, Exec P W muStmt c c' k ∧ k ≤ 260 ∧ c'.nreg 90078 = st.mu E cc ∧
      FrameB ztsvo c c' := by
  suffices hh : ∃ c' k, Exec P W muStmt c c' k ∧ k ≤ 260 ∧ c'.nreg 90078 = st.mu E cc by
    obtain ⟨c', k, e, hk, h1⟩ := hh
    exact ⟨c', k, e, hk, h1, exec_frameB e wr_muStmt⟩
  zubga
  have hW1 : ztbla := by have := hD.W1; omega
  zubkj
  have hnl : ztsab := by rw [hI.nlive]; exact (Set.ncard_pos hfin).2 ⟨cc, hc⟩
  unfold muStmt St.mu
  zujso
  · refine spec_ifLtN_false ztlhl
      ztxcs
    config_simp; rw [ite_eq_left h1, hC.sz]; rfl
  refine spec_ifLtN_true ztlhl ?_
  zubmd
  zueip
  zuink
  have e1 : ztsem := henc.wt _ hX
  have e2 : ztsem := henc.wt _ hY
  obtain ⟨c₁, k₁, ex₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90061 90036 90064,
      .loadN 90074 90061, .addN 90061 90036 90065, .loadN 90075 90061, .copyN 90086 90068,
      .copyN 90087 90072]) c c₁ k₁ ∧ k₁ = 6 ∧
      (c₁.nreg 90074 = st.wt ztfis ∧ c₁.nreg 90075 = st.wt ztbnp ∧
        c₁.nreg 90086 = st.nd0 cc ∧ c₁.nreg 90087 = bit ztxwi ∧
        (∀ r, r ≠ 90061 → r ≠ 90074 → r ≠ 90075 → r ≠ 90086 → r ≠ 90087 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    · zuolc; dm_simp; omega
    · config_simp; rw [hC.bWt, h65]; dm_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, by_simp_all,
        rfl⟩ <;> config_simp
      · rw [hC.bWt, h64, e1]
      · rw [hC.bWt, h65, e2]
      · omega
      omega
  obtain ⟨q74, q75, q86, q87, qr, qm⟩ := q
  -- common facts for the two gaps
  have hring : ∀ j, j < d.A → 0 < st.cnt j → st.prv j < d.A ∧ 0 < st.cnt ztwez ∧
      st.nxt j < d.A ∧ 0 < st.cnt ztwey := by
    intro j hj hL
    rw [hD.A] at hj ⊢
    obtain ⟨⟨a, b, -, -⟩, ⟨a', b', -, -⟩⟩ := hI.ring j hj hL
    exact ⟨a', b', a, b⟩
  have hbx : ∀ j, j < d.A → st.eg j + st.pz j ≤ E.sz := fun j hj =>
    bx_le hE hI.stat (by rw [← hD.A]; exact hj)
  zuqt

  have hC₁ := hC.frame fun r hr _ => qr r by_omega by_omega by_omega
    by_omega by_omega
  obtain ⟨c₂, k₂, ex₂, hk₂, j₂, f₂⟩ := jwStmt_exec (P := P) c₁ ex₁.wb_right hW1 hC₁
    by_simp_all (cc := cc) (k := st.nd0 cc) q86 q87
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    hn0 hL0 hring hbx hD.sz hb
  zucgb
  obtain ⟨c₃, k₃, e₃, hk₃, q76, q3r, q3m⟩ : ∃ c₃ k₃, Exec P W (.instr (.copyN 90076 90085)) c₂ c₃
      k₃ ∧ k₃ = 1 ∧ c₃.nreg 90076 = c₂.nreg 90085 ∧ (∀ r, r ≠ 90076 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem :=
    ⟨_, 1, Exec.copyN ex₂.wb_right 90076 90085, rfl, by_simp,
      fun r hr => by_simp_all, rfl⟩
  obtain ⟨c₄, k₄, ex₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 90086 90069,
      .copyN 90087 90073]) c₃ c₄ k₄ ∧ k₄ = 2 ∧
      (c₄.nreg 90086 = st.nd1 cc ∧ c₄.nreg 90087 = bit ztxwj ∧
        (∀ r, r ≠ 90086 → r ≠ 90087 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem) := by
    zuboe
    exec_block
    refine ⟨rfl, ?_, ?_, fun r a1 a2 => by zunza, rfl⟩ <;> config_simp
    · rw [q3r _ by_decide, g₂ _ by_decide, qr _ by_decide by_decide by_decide by_decide by_decide,
        h69]
    · rw [q3r _ by_decide, g₂ _ by_decide,
        qr _ by_decide by_decide by_decide by_decide by_decide, h73]
  obtain ⟨q86', q87', qr', qm'⟩ := q
  have c4r : ∀ r, r < 90080 → r ≠ 90061 → r ≠ 90074 → r ≠ 90075 → r ≠ 90076 →
      c₄.nreg r = c.nreg r := by
    intro r a0 a1 a2 a3 a4
    rw [qr' r by_omega by_omega, q3r r a4, g₂ r ztpwi,
      qr r a1 a2 a3 by_omega by_omega]
  have hC₄ := hC.frame fun r hr _ => c4r r by_omega by_omega by_omega
    by_omega by_omega
  have m4 : zteid := by rw [qm', q3m, f₂.2.2.1, qm]
  obtain ⟨c₅, k₅, ex₅, hk₅, j₅, f₅⟩ := jwStmt_exec (P := P) c₄ ex₄.wb_right hW1 hC₄
    by_grind (cc := cc) (k := st.nd1 cc) q86' q87'
    by_grind
    by_grind
    by_grind
    by_grind
    hn1 hL1 hring hbx hD.sz hb
  have e₆ := Exec.copyN (P := P) ex₅.wb_right 90077 90085
  obtain ⟨c₇, k₇, ex₇, hk₇, m₇, -, -⟩ := maxStmt_exec (P := P) _ e₆.wb_right
  refine ⟨c₇, _, .seq ex₁ (.seq ex₂ (.seq e₃ (.seq ex₄ (.seq ex₅ (.seq e₆ ex₇))))), by_omega, ?_⟩
  zungk
  have v76 : c₅.nreg 90076 = st.jw E cc ztmom := by
    rw [f₅.1 _ by_decide, qr' _ by_decide by_decide, q76]
    exact j₂
  simp only [upd, ite_true, show (90074 : ℕ) ≠ 90077 by decide,
    show (90075 : ℕ) ≠ 90077 by decide, show (90076 : ℕ) ≠ 90077 by decide]
  have v74 : c₅.nreg 90074 = st.wt ztfis := by
    rw [f₅.1 _ by_decide, qr' _ by_decide by_decide, q3r _ by_decide,
      g₂ _ by_decide, q74]
  have v75 : c₅.nreg 90075 = st.wt ztbnp := by
    rw [f₅.1 _ by_decide, qr' _ by_decide by_decide, q3r _ by_decide,
      g₂ _ by_decide, q75]
  grind
def wrSOK (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrOK B i

/-- Every instruction of the statement satisfies `wrSOK B`. -/
def wrS (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrSOK B i
  | .seq s t => wrS B s && wrS B t
  | .ifLtN _ _ t e => wrS B t && wrS B e
  | .ifLtR _ _ t e => wrS B t && wrS B e
  | .whileLtN _ _ b => wrS B b
  | .whileLtR _ _ b => wrS B b

/-- Registers outside `B`, real memory and the output agree. -/
def FrameS (B : ℕ → Bool) (c c' : Config) : Prop :=
  ztcjh ∧ ztbge ∧
    c'.rmem = c.rmem ∧ c'.output = c.output
theorem FrameS.trans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameS B c₁ c₂)
    (h₂ : FrameS B c₂ c₃) : FrameS B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans zthhr, fun r hr => (h₂.2.1 r hr).trans ztfsm,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩
variable {P : Polygon}
/-- **Frame of a statement with stores.** -/
theorem exec_frameS {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrS B s = true) : FrameS B c c' := by
  induction h with
  | skip _ => exact ⟨by_omega, by_simp_all, rfl, rfl⟩
  | @instr ins c c' _ he _ _ =>
    simp only [wrS] at hs
    cases ins <;> simp only [wrSOK, wrOK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine zthmz <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrS, Bool.and_eq_true] at hs
    zueot
  | ifLtN_true _ _ ih =>
    zufcq
  | ifLtN_false _ _ ih =>
    zufcr
  | ifLtR_true _ _ ih =>
    zufcq
  | ifLtR_false _ _ ih =>
    zufcr
  | whileLtN_false _ _ => exact ⟨by_omega, by_simp_all, rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj
  | whileLtR_false _ _ => exact ⟨by_omega, by_simp_all, rfl, rfl⟩
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans zthyj

/-! ## The filtering append loop -/

/-- Append `r102` to the scratch list (`r44` base, `r100` length). -/
def appendV : Stmt := block [.addN 90105 90044 90100, .storeN 90105 90102, .addN 90100 90100 90019]

/-- One step: `v := m[rs + t]`; append `v` if `v ≠ c`; `t := t + 1`. -/
def appBody (rs : ℕ) : Stmt :=
  .seq (block [.addN 90105 rs 90101, .loadN 90102 90105])
    (.seq ztzaj
      ztnaz)

/-- The loop over `t < r rn`. -/
def appLoop (rs rn : ℕ) : Stmt := .whileLtN 90101 rn (appBody rs)

/-- The registers the loop writes. -/
def Bapp (r : ℕ) : Bool := decide (r = 90100) || decide (r = 90101) || decide (r = 90102) ||
  decide (r = 90105)

/-- The facts the loop keeps. -/
structure AppI (W rs rn S T D' cc ℓ₀ : ℕ) (l P₀ : List ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ l.length
  len : c.nreg 90100 = ℓ₀ + ((l.take ztmgq).filter ztvv).length
  tmp : ∀ i, i < c.nreg 90100 →
    c.nmem ztjnf = (P₀ ++ (l.take ztmgq).filter ztvv).getD i 0
  frame : ∀ a, zteoq → c.nmem a = m₀ a
  rs : c.nreg rs = S
  rn : c.nreg rn = l.length
  r62 : c.nreg 90062 = cc
  r44 : c.nreg 90044 = T
  r19 : c.nreg 90019 = 1
theorem take_succ_filter (l : List ℕ) (t cc : ℕ) (ht : t < l.length) :
    (l.take ztbx).filter ztvv =
      (l.take t).filter ztvv ++ if l.getD t 0 != cc then [l.getD t 0] else [] := by
  rw [List.take_add_one, List.filter_append, List.getElem?_eq_getElem ht]
  grind
theorem getD_append_left {l₁ l₂ : List ℕ} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  grind
theorem getD_append_len (l₁ : List ℕ) (v : ℕ) (l₂ : List ℕ) :
    (l₁ ++ v :: l₂).getD l₁.length 0 = v := by
  simp

/-- **The filtering append loop.** -/
theorem appLoop_exec {W rs rn S T D' cc ℓ₀ : ℕ} {l P₀ : List ℕ} (c : Config)
    (hrs : rs ≠ 90100 ∧ rs ≠ 90101 ∧ rs ≠ 90102 ∧ rs ≠ 90105 ∧ rs ≠ 90062 ∧ rs ≠ 90044 ∧
      rs ≠ 90019)
    (hrn : rn ≠ 90100 ∧ rn ≠ 90101 ∧ rn ≠ 90102 ∧ rn ≠ 90105 ∧ rn ≠ 90062 ∧ rn ≠ 90044 ∧
      rn ≠ 90019 ∧ rn ≠ rs)
    (hw : WordsBounded W c) (h101 : c.nreg 90101 = 0) (h100 : c.nreg 90100 = ℓ₀)
    (hP : P₀.length = ℓ₀) (hP₀ : ∀ i, i < ℓ₀ → c.nmem ztjnf = P₀.getD i 0)
    (hS : c.nreg rs = S) (hN : c.nreg rn = l.length) (h62 : c.nreg 90062 = cc)
    (h44 : c.nreg 90044 = T) (h19 : c.nreg 90019 = 1)
    (hsrc : ∀ t, t < l.length → c.nmem zttbz = l.getD t 0)
    (hdisj : ∀ t, t < l.length → S + t < T ∨ T + D' ≤ S + t)
    (hroom : ℓ₀ + l.length ≤ D') (hTW : T + D' ≤ W) (hSW : S + l.length ≤ W) :
    ∃ c' k, Exec P W (appLoop rs rn) c c' k ∧ k ≤ 14 * l.length + 2 ∧
      c'.nreg 90100 = ℓ₀ + (l.filter ztvv).length ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem ztjnf = (P₀ ++ l.filter ztvv).getD i 0) ∧
      (∀ a, zteoq → c'.nmem a = c.nmem a) ∧
      FrameS Bapp c c' := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hrs
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hrn
  have hWB : ∀ c₁ : Config, AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem c₁ → WordsBounded W c₁ :=
    fun _ h => h.wb
  have I0 : AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem c :=
    ⟨hw, by_omega, by_simp_all, by_simp_all, by_omega, hS, hN, h62, h44, h19⟩
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := rn)
    (body := appBody rs) (AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem)
    (fun d => l.length - d.nreg 90101) 12 hWB
    (fun d hI ht => by
      obtain ⟨hwd, ht_le, hlen, htmp, hfr, hrs', hrn', h62', h44', h19'⟩ := hI
      rw [hrn'] at ht
      set t := d.nreg 90101 with htdef
      have hflen : ((l.take t).filter ztvv).length ≤ t := by
        grind
      -- load `v`
      obtain ⟨d₁, k₁, e₁, hk₁, q⟩ : ∃ d₁ k₁, Exec P W (block [.addN 90105 rs 90101,
          .loadN 90102 90105]) d d₁ k₁ ∧ k₁ = 2 ∧ (d₁.nreg 90102 = l.getD t 0 ∧
          (∀ r, r ≠ 90105 → r ≠ 90102 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem) := by
        exec_block
        · omega
        · refine ztfkd
          config_simp; grind
      zugqo
      zuka
      -- append or skip
      have happ : ∀ d₂ : Config, WordsBounded W d₂ → d₂.nreg 90102 = l.getD t 0 →
          (∀ r, r ≠ 90105 → r ≠ 90102 → d₂.nreg r = d.nreg r) → d₂.nmem = d.nmem →
          ∃ d₃ k₃, Exec P W appendV d₂ d₃ k₃ ∧ k₃ = 3 ∧
            d₃.nreg 90100 = d.nreg 90100 + 1 ∧ d₃.nmem = upd d.nmem (T + d.nreg 90100) ztocn
            ∧ (∀ r, r ≠ 90105 → r ≠ 90102 → r ≠ 90100 → d₃.nreg r = d.nreg r) := by
        intro d₂ hw₂ v2 r2' m2
        unfold appendV
        exec_block
        · grind
        · config_simp; grind
        · refine ⟨rfl, ?_, ?_, fun r a1 a2 a3 => by simp [upd, a1, a3, r2' r a1 a2]⟩
          · config_simp; grind
          grind
      -- the step as a whole
      have hfs := take_succ_filter l t cc ht
      have hv : d₁.nreg 90062 = cc := by_grind
      -- the increment and the invariant, from the state after the (possible) append
      have fin : ∀ (d₂ : Config) (k₂ : ℕ), WordsBounded W d₂ → k₂ ≤ 8 →
          Exec P W ztzaj d₁ d₂ k₂ →
          (∀ r, r ≠ 90105 → r ≠ 90102 → r ≠ 90100 → d₂.nreg r = d.nreg r) →
          d₂.nreg 90100 = ℓ₀ + ((l.take ztbx).filter ztvv).length →
          (∀ i, i < d₂.nreg 90100 → d₂.nmem ztjnf =
            (P₀ ++ (l.take ztbx).filter ztvv).getD i 0) →
          (∀ a, zteoq → d₂.nmem a = c.nmem a) →
          ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
            ztdkd) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
            k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
        intro d₂ k₂ hw₂ hk₂ ex₂ r2' l2 t2 f2
        have e19 : d₂.nreg 90019 = 1 := by_grind
        have e101 : d₂.nreg 90101 = t := by_grind
        obtain ⟨d₅, ex, v101, vr, vm⟩ : ∃ d₅, Exec P W (.instr (.addN 90101 90101 90019)) d₂ d₅ 1 ∧
            d₅.nreg 90101 = t + 1 ∧ (∀ r, r ≠ 90101 → d₅.nreg r = d₂.nreg r) ∧
            d₅.nmem = d₂.nmem :=
          ⟨_, Exec.addN hw₂ 90101 90101 90019 by_omega,
            by simp [upd, e19, e101], fun r hr => by zunaw, rfl⟩
        refine ⟨_, _, .seq ex₂ ex, by_omega, ⟨ex.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          v101⟩
        · omega
        · grind
        · grind
        · grind
        · grind
        · grind
        · grind
        · grind
        grind
      have key : ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
          ztdkd) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
          k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
        by_cases hne : l.getD t 0 = cc
        · -- skip
          have hn1 : ¬ d₁.nreg 90102 < d₁.nreg 90062 := by_omega
          have hn2 : ¬ d₁.nreg 90062 < d₁.nreg 90102 := by_omega
          have hfs' : (l.take ztbx).filter ztvv = (l.take t).filter ztvv := by
            grind
          refine fin d₁ _ hw₁ by_omega (.ifLtN_false hn1 (.ifLtN_false hn2 ztekd))
            by_grind ?_ ?_ ?_
          · grind
          · grind
          grind
        · -- append
          have hbit : (l.getD t 0 != cc) = true := by_grind
          have hfs' : (l.take ztbx).filter ztvv =
              (l.take t).filter ztvv ++ [l.getD t 0] := by_grind
          obtain ⟨d₂, k₂, e₂, hk₂, l2, m2, r2'⟩ := happ d₁ hw₁ q102 qr qm
          have post : ∀ k₀, k₀ ≤ 5 → Exec P W (.ifLtN 90102 90062 appendV
              ztdkd) d₁ d₂ (k₂ + k₀) →
              ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
                ztdkd) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
                k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
            intro k₀ hk₀ ex₀
            refine fin d₂ _ ex₀.wb_right by_omega ex₀ r2' ?_ ?_ ?_
            · rw [l2, hlen, hfs', List.length_append, List.length_singleton]; omega
            · zug
              rw [l2] at hi
              zumop
              by_cases hil : i = d.nreg 90100
              · subst hil
                simp only [upd, ite_true]
                rw [hfs', ← List.append_assoc]
                have : ((P₀ ++ (l.take t).filter ztvv).length) = d.nreg 90100 := by
                  grind
                zvnnr; simp
              · simp only [upd, show T + i ≠ T + d.nreg 90100 by omega, ite_false]
                rw [htmp i by_omega, hfs', ← List.append_assoc]
                exact (getD_append_left
                  by_grind).symm
            · zuge
              zumop
              zuby
              zufa
              grind
          by_cases hlt : l.getD t 0 < cc
          · exact post 1 by_omega ztbxn
          · have hgt : cc < l.getD t 0 := by_omega
            exact post 3 by_omega ((Exec.ifLtN_false by_omega
              ztbxn).cast by_omega)
      obtain ⟨d₄, k₄, e₄, hk₄, I₄, t₄⟩ := key
      exact ⟨d₄, k₁ + k₄, .seq e₁ e₄, I₄, by_omega, by_omega⟩) I0
  obtain ⟨hw', ht', hlen', htmp', hfr', -, hrn', -, -, -⟩ := I'
  rw [hrn'] at hx
  have hfull : c'.nreg 90101 = l.length := by_omega
  rw [hfull, List.take_length] at hlen' htmp'
  refine ⟨c', k, e, ?_, hlen', htmp', hfr', exec_frameS e (by
    rfl)⟩
  omega
theorem Enc.mem_congr {m m' : ℕ → ℕ} {d : Dm} {st : St} (h : Enc m d st)
    (hm : ∀ a, d.b0 ≤ a → a < d.b0 + d.oTmp → m' a = m a) : Enc m' d st := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x t hx ht => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun t ht => ?_⟩
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.live i hi
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.s0 i hi
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.s1 i hi
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.nd0 i hi
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.nd1 i hi
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.deg x hx
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.wt x hx
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.exb x hx
  · have := slot_lt hx ht
    rw [hm _ by_omega (by dm_simp; omega)]; exact h.ex x t hx ht
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.cnt j hj
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.nxt j hj
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.prv j hj
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.eg j hj
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.pz j hj
  · rw [hm _ by_omega (by dm_simp; omega)]; exact h.stk t ht
variable {m : ℕ → ℕ} {P : Polygon} {W : ℕ} {E : Env}
theorem Enc.st_congr {d : Dm} {st st' : St} (h : Enc m d st)
    (h1 : ∀ i, i < d.K → st'.live i = st.live i) (h2 : ∀ i, i < d.K → st'.s0 i = st.s0 i)
    (h3 : ∀ i, i < d.K → st'.s1 i = st.s1 i) (h4 : ∀ i, i < d.K → st'.nd0 i = st.nd0 i)
    (h5 : ∀ i, i < d.K → st'.nd1 i = st.nd1 i) (h6 : ∀ x, x < d.R → st'.deg x = st.deg x)
    (h7 : ∀ x, x < d.R → st'.wt x = st.wt x)
    (h8 : ∀ x t, x < d.R → t < d.D → st'.ex x t = st.ex x t)
    (h9 : ∀ j, j < d.A → st'.cnt j = st.cnt j) (h10 : ∀ j, j < d.A → st'.nxt j = st.nxt j)
    (h11 : ∀ j, j < d.A → st'.prv j = st.prv j) (h12 : ∀ j, j < d.A → st'.eg j = st.eg j)
    (h13 : ∀ j, j < d.A → st'.pz j = st.pz j) (h14 : ∀ t, t < d.cap → st'.stk t = st.stk t) :
    Enc m d st' :=
  ⟨fun i hi => (h.live i hi).trans by_simp_all, fun i hi => (h.s0 i hi).trans by_simp_all,
    fun i hi => (h.s1 i hi).trans by_simp_all, fun i hi => (h.nd0 i hi).trans by_simp_all,
    fun i hi => (h.nd1 i hi).trans by_simp_all, fun x hx => (h.deg x hx).trans by_simp_all,
    fun x hx => (h.wt x hx).trans by_simp_all, h.exb,
    fun x t hx ht => (h.ex x t hx ht).trans by_simp_all,
    fun j hj => (h.cnt j hj).trans by_simp_all, fun j hj => (h.nxt j hj).trans by_simp_all,
    fun j hj => (h.prv j hj).trans by_simp_all, fun j hj => (h.eg j hj).trans by_simp_all,
    fun j hj => (h.pz j hj).trans by_simp_all, fun t ht => (h.stk t ht).trans by_simp_all⟩

/-! ## List facts -/
theorem exl_length (st : St) (x : ℕ) : (st.exl x).length = st.deg x := by
  unfold St.exl; simp
theorem exl_getD (st : St) {x t : ℕ} (ht : t < st.deg x) : (st.exl x).getD t 0 = st.ex x t := by
  unfold St.exl
  simp_all
theorem getD_not_mem_take {l : List ℕ} (hl : l.Nodup) {t : ℕ} (ht : t < l.length) :
    l.getD t 0 ∉ l.take t := by
  zujbb
  have e := List.take_append_drop t l
  rw [List.drop_eq_getElem_cons ht] at e
  grind
theorem mem_take_succ {l : List ℕ} {t : ℕ} (ht : t < l.length) (a : ℕ) :
    a ∈ l.take ztbx ↔ a ∈ l.take t ∨ a = l.getD t 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht]
  grind
theorem slot_le {D x t R : ℕ} (hx : x < R) (ht : t ≤ D) : D * x + t ≤ R * D := by
  have : D * x + t ≤ D * zthf := by_grind
  zuhvj

/-- Layout facts. -/
theorem Dm.lay (d : Dm) : d.oExb + d.R = d.oEx ∧ d.oEx + d.R * d.D ≤ d.oTmp ∧
    d.oTmp + d.D + 1 ≤ d.oEnd ∧ d.oStk + d.cap = d.oTmp ∧ d.oS0 = d.K ∧ d.oS1 = 2 * d.K ∧
    d.oDeg = 5 * d.K ∧ d.oWt = 5 * d.K + d.R ∧ d.oExb = 5 * d.K + 2 * d.R ∧
    d.oCnt = d.oEx + d.R * d.D ∧ d.oNxt = d.oCnt + d.A ∧ d.oPrv = d.oNxt + d.A ∧
    d.oEg = d.oPrv + d.A ∧ d.oPz = d.oEg + d.A ∧ d.oStk = d.oPz + d.A := by
  refine ztcl <;>
  simp only [Dm.oS0, Dm.oS1, Dm.oDeg, Dm.oWt, Dm.oExb, Dm.oEx,
    Dm.oCnt, Dm.oNxt, Dm.oPrv, Dm.oEg, Dm.oPz, Dm.oStk, Dm.cap, Dm.oTmp, Dm.oList, Dm.oEnd] <;>
  omega

/-! ## Gathering the merged exit list -/

/-- Load the exit bases of `X`, `Y` and clear the counters. -/
def rmHead : Stmt := block [.addN 90105 90037 90064, .loadN 90103 90105,
  .addN 90105 90037 90065, .loadN 90104 90105, .constN 90100 0, .constN 90101 0]

/-- Gather `newEx c` into the scratch area. -/
def gatherStmt : Stmt :=
  .seq rmHead (.seq (appLoop 90103 90066) (.seq ztouj (appLoop 90104 90067)))

/-- The registers `90100 … 90109`. -/
def Brm (r : ℕ) : Bool := decide (90100 ≤ r ∧ r < 90110)
theorem wrS_gather : wrS Brm gatherStmt = true := by_decide
theorem gather_exec {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hD : DimOK E d W)
    {cc X Y : ℕ} (hX : X < E.R) (hY : Y < E.R) (hdX : st.deg X ≤ E.D) (hdY : st.deg Y ≤ E.D)
    (hroom : ((st.exl X).filter ztvv).length + st.deg Y ≤ E.D + 1)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = X) (h65 : c.nreg 90065 = Y)
    (h66 : c.nreg 90066 = st.deg X) (h67 : c.nreg 90067 = st.deg Y) :
    ∃ c' k, Exec P W gatherStmt c c' k ∧ k ≤ 28 * E.D + 20 ∧
      c'.nreg 90100 = ((st.exl X).filter ztvv ++ (st.exl Y).filter ztvv).length ∧
      c'.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c'.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem ztqli =
        ((st.exl X).filter ztvv ++ (st.exl Y).filter ztvv).getD i 0) ∧
      ztdra ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W gatherStmt c c' k ∧ k ≤ 28 * E.D + 20 ∧
      c'.nreg 90100 = ((st.exl X).filter _ ++ (st.exl Y).filter _).length ∧
      c'.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c'.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem _ =
        ((st.exl X).filter _ ++ (st.exl Y).filter _).getD i 0) ∧
      ztdra by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5, h6⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, h5, h6, exec_frameS e wrS_gather⟩
  zubga
  zudoe

  zuink
  rw [← hD.D] at hdX hdY hroom
  have eX : c.nmem _ = d.b0 + d.oEx + d.D * X := henc.exb X hX
  have eY : c.nmem _ = d.b0 + d.oEx + d.D * Y := henc.exb Y hY
  have sX := slot_le (D := d.D) hX ztbhw
  have sY := slot_le (D := d.D) hY ztbhw
  have sX' := slot_le hX hdX
  have sY' := slot_le hY hdY
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W rmHead c c₁ k₁ ∧ k₁ = 6 ∧
      (c₁.nreg 90103 = d.b0 + d.oEx + d.D * X ∧ c₁.nreg 90104 = d.b0 + d.oEx + d.D * Y ∧
        c₁.nreg 90100 = 0 ∧ c₁.nreg 90101 = 0 ∧
        (∀ r, r ≠ 90100 → r ≠ 90101 → r ≠ 90103 → r ≠ 90104 → r ≠ 90105 →
          c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    unfold rmHead
    exec_block
    · rw [hC.bExb, h64]; omega
    · config_simp; rw [hC.bExb, h65]; omega
    · omega
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, ?_, by_simp_all,
        rfl⟩ <;> config_simp
      · rw [hC.bExb, h64, eX]
      · rw [hC.bExb, h65, eY]
  obtain ⟨q103, q104, q100, q101, qr, qm⟩ := q
  zuka
  have T44 : ztrgk := by
    rw [qr _ by_decide by_decide by_decide by_decide by_decide, hC.bTmp]
  have T19 : ztgas := by
    rw [qr _ by_decide by_decide by_decide by_decide by_decide, hC.one]
  have T62 : c₁.nreg 90062 = cc := by
    simp_all
  -- the exits of `X`
  obtain ⟨c₂, k₂, e₂, hk₂, l₂, t₂, f₂, F₂⟩ := appLoop_exec (P := P) (rs := 90103) (rn := 90066)
    (S := d.b0 + d.oEx + d.D * X) (T := d.b0 + d.oTmp) (D' := d.D + 1) (cc := cc) (ℓ₀ := 0)
    (l := st.exl X) (P₀ := []) c₁ by_decide by_decide hw₁ q101 q100 rfl (fun i hi => by_omega)
    q103 (by rw [exl_length, qr _ by_decide by_decide by_decide by_decide by_decide,
      h66]) T62 T44 T19
    (fun t ht => by
      zukrh
      rw [qm, henc.ex X t hX by_omega, exl_getD _ ht])
    (fun t ht => by rw [exl_length] at ht; omega)
    ztepu by_omega ztepu
  zuja
  have g₂ := F₂.1
  -- reset the counter
  have e₃ := Exec.constN (P := P) hw₂ 90101 0 by_omega
  zuboe
  -- the exits of `Y`
  obtain ⟨c₄, k₄, e₄, hk₄, l₄, t₄, f₄, F₄⟩ := appLoop_exec (P := P) (rs := 90104) (rn := 90067)
    (S := d.b0 + d.oEx + d.D * Y) (T := d.b0 + d.oTmp) (D' := d.D + 1) (cc := cc)
    (ℓ₀ := ((st.exl X).filter ztvv).length) (l := st.exl Y)
    (P₀ := (st.exl X).filter ztvv) _ by_decide by_decide hw₃ by_simp
    (by config_simp; omega) rfl
    (fun i hi => by
      grind)
    (by config_simp; zunzb)
    (by config_simp; rw [g₂ _ by_decide, exl_length,
      qr _ by_decide by_decide by_decide by_decide by_decide, h67])
    (by config_simp; rw [g₂ _ by_decide, T62])
    (by config_simp; rw [g₂ _ by_decide, T44])
    (by config_simp; rw [g₂ _ by_decide, T19])
    (fun t ht => by
      zukrh
      config_simp
      rw [f₂ _ by_omega,
        qm, henc.ex Y t hY by_omega, exl_getD _ ht])
    (fun t ht => by
      rw [exl_length] at ht; omega)
    ztepu by_omega
    ztepu
  refine ⟨c₄, _, .seq e₁ ztcb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := exl_length st X; have := exl_length st Y; rw [← hD.D]; omega
  · grind
  · zunpi; config_simp; rw [g₂ _ by_decide, q103]
  · zunpi; config_simp; zunzb
  · omega
  grind

/-! ## Relabelling the exits of `Y` -/

/-- The state with the exits in `l` of the class `Y = s1 c` relabelled to `X = s0 c`. -/
def St.rel (st : St) (c : ℕ) (l : List ℕ) : St :=
  { st with
    s0 := fun e => if e ∈ l ∧ e ≠ c ∧ st.s0 e = st.s1 c then st.s0 c else st.s0 e
    s1 := fun e => if e ∈ l ∧ e ≠ c ∧ st.s1 e = st.s1 c then st.s0 c else st.s1 e }

/-- Store `r v` at `r p` iff `r a = r b`. -/
def condStore (a b p v : ℕ) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip (.instr (.storeN p v)))
theorem condStore_exec (c : Config) (hw : WordsBounded W c)
    (a b p v : ℕ) :
    ∃ c' k, Exec P W (condStore a b p v) c c' k ∧ k ≤ 5 ∧ c'.nreg = c.nreg ∧
      c'.nmem = (if c.nreg a = c.nreg b then upd c.nmem ztfgw ztjsn else c.nmem) := by
  unfold condStore
  zubai
  · exact ⟨c, _, .ifLtN_true h1 ztjd, by_omega, rfl,
      by grind⟩
  zubjz
  · exact ⟨c, _, .ifLtN_false h1 ztxdj, by_omega, rfl,
      by grind⟩
  · exact ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (Exec.storeN hw p v)), by_omega, rfl,
      by grind⟩
theorem Enc.cond_s0 {d : Dm} {S : St} (h : Enc m d S) {e : ℕ} (he : e < d.K)
    (X Y : ℕ) : Enc (if S.s0 e = Y then upd m (d.b0 + d.oS0 + e) X else m) d
      { S with s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e) } := by
  split_ifs
  · exact h.set_s0 he X
  simp_all
theorem Enc.cond_s1 {d : Dm} {S : St} (h : Enc m d S) {e : ℕ} (he : e < d.K)
    (X Y : ℕ) : Enc (if S.s1 e = Y then upd m (d.b0 + d.oS1 + e) X else m) d
      { S with s1 := Function.update S.s1 e (if S.s1 e = Y then X else S.s1 e) } := by
  split_ifs
  · exact h.set_s1 he X
  simp_all

/-- Relabel the chord `e` from class `Y` to `X` on either side. -/
def St.relab (S : St) (e X Y : ℕ) : St :=
  { S with
    s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e)
    s1 := Function.update S.s1 e (if S.s1 e = Y then X else S.s1 e) }

/-- Relabel the chord `r102` from `Y = r65` to `X = r64` on either side. -/
def relOne : Stmt :=
  .seq (block [.addN 90105 90031 90102, .loadN 90106 90105])
    (.seq ztqjw
      (.seq (block [.addN 90105 90032 90102, .loadN 90106 90105])
        ztqjw))
theorem relOne_exec {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {e X Y : ℕ} (he : e < d.K) (h102 : c.nreg 90102 = e) (h64 : c.nreg 90064 = X)
    (h65 : c.nreg 90065 = Y) :
    ∃ c' k, Exec P W relOne c c' k ∧ k ≤ 14 ∧
      Enc c'.nmem d (S.relab e X Y) ∧
      ztgso ∧
      ztxbp := by
  zubga
  zudex
  have hN0 : ztfkz := rfl
  have hK : 3 * d.K ≤ d.oTmp := by
    have : d.oNd0 ≤ d.oTmp := by dm_simp; omega
    omega
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90105 90031 90102,
      .loadN 90106 90105]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 90105 = d.b0 + d.oS0 + e ∧
      c₁.nreg 90106 = S.s0 e ∧ (∀ r, r ≠ 90105 → r ≠ 90106 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem) := by
    exec_block
    · zuold; omega
    · refine ztdqx <;> config_simp
      · zuold
      · rw [hC.bS0, h102, henc.s0 e he]
  obtain ⟨q105, q106, qr, qm⟩ := q
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, m₂⟩ := condStore_exec (P := P) c₁ e₁.wb_right 90106 90065 90105 90064
  zuja
  rw [q106, qr _ by_decide by_decide, h65, q105, qr _ by_decide by_decide, h64, qm] at m₂
  have E₂ : Enc c₂.nmem d
      { S with s0 := Function.update S.s0 e (if S.s0 e = Y then X else S.s0 e) } := by
    zunbg; exact henc.cond_s0 he X Y
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.addN 90105 90032 90102,
      .loadN 90106 90105]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 90105 = d.b0 + d.oS1 + e ∧
      c₃.nreg 90106 = S.s1 e ∧ (∀ r, r ≠ 90105 → r ≠ 90106 → c₃.nreg r = c.nreg r) ∧
      c₃.nmem = c₂.nmem) := by
    have c32 : c₂.nreg 90032 = d.b0 + d.oS1 := by
      rw [r₂, qr _ by_decide by_decide, hC.bS1]
    have c102 : c₂.nreg 90102 = e := by_simp_all
    exec_block
    · omega
    · refine ztdqx <;>
        config_simp
      · omega
      · rw [c32, c102, E₂.s1 e he]
  obtain ⟨q105', q106', qr', qm'⟩ := q
  obtain ⟨c₄, k₄, e₄, hk₄, r₄, m₄⟩ := condStore_exec (P := P) c₃ e₃.wb_right 90106 90065 90105 90064
  rw [q106', qr' _ by_decide by_decide, h65, q105', qr' _ by_decide by_decide, h64,
    qm'] at m₄
  refine ztxmc
  · rw [m₄]; exact E₂.cond_s1 he X Y
  · simp_all
  · zuge
    rw [m₄, m₂]
    split_ifs <;> zvmwf <;> split_ifs <;> first | rfl | omega

/-- One step of the relabelling loop: the exit `t` of `Y` (at `r104 + t`), skipped if it is
`c = r62`. -/
def relBody : Stmt :=
  .seq (block [.addN 90105 90104 90101, .loadN 90102 90105])
    (.seq (.ifLtN 90102 90062 relOne ztprv)
      ztnaz)

/-- The relabelling loop. -/
def relStmt : Stmt := .seq ztouj (.whileLtN 90101 90067 relBody)
theorem wrS_rel : wrS Brm relStmt = true := by_decide

/-- The facts the relabelling loop keeps. -/
structure RelI (W : ℕ) (d : Dm) (st : St) (cc : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ st.deg ztbnp
  enc : Enc c.nmem d (st.rel cc ((st.exl ztbnp).take ztmgq))
  regs : ∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90106 → c.nreg r = c₀.nreg r
  mem : ∀ a, ztbzf → c.nmem a = c₀.nmem a
theorem relStmt_exec {d : Dm} {st : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st) (hD : DimOK E d W)
    {cc : ℕ} (hY : st.s1 cc < E.R) (hdY : st.deg ztbnp ≤ E.D)
    (hnd : (st.exl ztbnp).Nodup) (hK : ∀ i ∈ st.exl ztbnp, i < E.K)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h67 : c.nreg 90067 = st.deg ztbnp)
    (h104 : c.nreg 90104 = d.b0 + d.oEx + d.D * st.s1 cc) :
    ∃ c' k, Exec P W relStmt c c' k ∧ k ≤ 22 * E.D + 3 ∧
      Enc c'.nmem d (st.rel cc (st.exl ztbnp)) ∧
      ztegr ∧
      ztxbp ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W relStmt c c' k ∧ k ≤ 22 * E.D + 3 ∧
      Enc c'.nmem d _ ∧
      ztegr ∧
      ztxbp by
    zudec
    exact ⟨c', k, e, h1, h2, h3, h4, exec_frameS e wrS_rel⟩
  zubga
  zudoe

  rw [← hD.R] at hY
  rw [← hD.D] at hdY
  have hKd : ∀ i ∈ st.exl ztbnp, i < d.K := fun i hi => by rw [hD.K]; simp_all
  have e₀ := Exec.constN (P := P) hw 90101 0 by_omega
  have I0 : RelI W d st cc c { c with nreg := upd c.nreg 90101 0 } := by
    refine ⟨e₀.wb_right, by_simp, ?_, by_simp_all,
      by simp_all⟩
    tauto
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := 90067)
    (body := relBody) (RelI W d st cc c) (fun d' => st.deg ztbnp - d'.nreg 90101) 20
    ztpf
    (fun c₁ I ht => by
      obtain ⟨hw₁, ht₁, henc₁, hr₁, hm₁⟩ := I
      rw [hr₁ 90067 by_decide by_decide by_decide by_decide, h67] at ht
      set t := c₁.nreg 90101 with htdef
      set l := st.exl ztbnp with hldef
      have htl : t < l.length := by rw [exl_length]; exact ht
      set e₀ := l.getD t 0 with he₀
      have he₀K : e₀ < d.K := by_simp_all
      have hnot := getD_not_mem_take hnd htl
      -- load the exit
      obtain ⟨c₂, k₂, ex₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.addN 90105 90104 90101,
          .loadN 90102 90105]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 90102 = e₀ ∧
          (∀ r, r ≠ 90105 → r ≠ 90102 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem) := by
        have s := slot_le hY (show t ≤ d.D by omega)
        exec_block
        · grind
        · refine ztfkd
          config_simp
          rw [hr₁ _ by_decide by_decide by_decide by_decide, h104,
            henc₁.ex _ _ hY by_omega, he₀, exl_getD _ ht]
          rfl
      zugqo
      have hw₂ := ex₂.wb_right
      have c62 : c₂.nreg 90062 = cc := by
        simp_all
      -- the relabelling (or not)
      obtain ⟨c₃, k₃, ex₃, hk₃, enc₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 90102 90062 relOne
          ztprv) c₂ c₃ k₃ ∧ k₃ ≤ 17 ∧
          Enc c₃.nmem d ztywu ∧
          (∀ r, r ≠ 90105 → r ≠ 90106 → c₃.nreg r = c₂.nreg r) ∧
          (∀ a, ztbzf → c₃.nmem a = c₂.nmem a) := by
        by_cases hec : e₀ = cc
        · have n1 : ¬ c₂.nreg 90102 < c₂.nreg 90062 := by_omega
          have n2 : ¬ c₂.nreg 90062 < c₂.nreg 90102 := by_omega
          refine ⟨c₂, _, .ifLtN_false n1 (.ifLtN_false n2 ztuvp), by_omega, ?_,
            by omega, by_omega⟩
          zujlh
          refine henc₁.st_congr ztcj ztbzz ztbzz ztcj
            ztcj ztcj ztcj ztcnd
            ztcj ztcj ztcj ztcj ztcj
            ztcj <;>
          · simp only [St.rel, mem_take_succ htl]
            grind
        · have hC₂ : ztpjc := hC.frame by_grind
          have c64 : c₂.nreg 90064 = st.s0 cc := by
            simp_all
          have c65 : c₂.nreg 90065 = st.s1 cc := by
            grind
          obtain ⟨c₃, k₃, ex₃, hk₃, enc₃, r₃, m₃⟩ := relOne_exec hw₂ hC₂
            (by zunsl; omega) hD he₀K q102 c64 c65
          have fin : Enc c₃.nmem d ztywu := by
            refine enc₃.st_congr ztcj ztbzz ztbzz
              ztcj ztcj ztcj ztcj
              ztcnd ztcj ztcj ztcj
              ztcj ztcj ztcj <;>
            · simp only [St.rel, St.relab, mem_take_succ htl, ← he₀]
              by_cases hi : i = e₀
              · grind
              grind
          by_cases hlt : e₀ < cc
          · exact ⟨c₃, _, .ifLtN_true by_omega ex₃, by_omega, fin, r₃, m₃⟩
          · exact ⟨c₃, _, .ifLtN_false by_omega
              (.ifLtN_true by_omega ex₃), by_omega, fin, r₃, m₃⟩
      have hw₃ := ex₃.wb_right
      have c101 : c₃.nreg 90101 = t := by_grind
      have c19 : c₃.nreg 90019 = 1 := by
        rw [r₃ _ by_decide by_decide, qr _ by_decide by_decide,
          hr₁ _ by_decide by_decide by_decide by_decide, hC.one]
      have ex₄ := Exec.addN (P := P) hw₃ 90101 90101 90019 by_omega
      refine ⟨_, _, .seq ex₂ (.seq ex₃ ex₄), ⟨ex₄.wb_right, ?_, ?_, ?_, ?_⟩, by_omega, ?_⟩
      · config_simp; omega
      · config_simp; grind
      · zukjt
        config_simp
        rw [upd_other _ _ _ a1, r₃ r a3 a4, qr r a3 a2, hr₁ r a1 a2 a3 a4]
      · grind
      · config_simp; omega) I0
  zueiz
  rw [hr' 90067 by_decide by_decide by_decide by_decide] at hx
  rw [h67] at hx
  have hfull : c'.nreg 90101 = st.deg ztbnp := by_omega
  rw [hfull, ← exl_length, List.take_length] at henc'
  refine ⟨c', _, .seq e₀ e, ?_, henc', fun r a1 a2 a3 a4 => ?_, fun a ha => ?_⟩
  · simp only [upd, ite_true, Nat.sub_zero] at hk
    zukzg

  · simp_all
  simp_all
def St.wb (st : St) (X top1 : ℕ) (L : List ℕ) (t : ℕ) : St :=
  { st with
    ex := fun x u => if x = X ∧ u < t then L.getD u 0 else st.ex x u
    stk := fun u => if top1 ≤ u ∧ u < top1 + t then L.getD (u - top1) 0 else st.stk u }

/-- One step: `v := tmp[t]`; `ex X t := v`; `stk (top1 + t) := v`; `t := t + 1`. -/
def wbBody : Stmt := block [.addN 90105 90044 90101, .loadN 90102 90105, .addN 90105 90103 90101,
  .storeN 90105 90102, .addN 90105 90043 90108, .addN 90105 90105 90101, .storeN 90105 90102,
  .addN 90101 90101 90019]

/-- The write-back loop (`r108 := top - 1`). -/
def wbStmt : Stmt :=
  .seq (block [.constN 90101 0, .subN 90108 90050 90019]) (.whileLtN 90101 90100 wbBody)
theorem wrS_wb : wrS Brm wbStmt = true := by_decide

/-- The facts the write-back loop keeps. -/
structure WbI (W : ℕ) (d : Dm) (S : St) (X top1 : ℕ) (L : List ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ L.length
  enc : Enc c.nmem d (S.wb X top1 L ztmgq)
  regs : ∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → c.nreg r = c₀.nreg r
  mem : ∀ a, zteot → c.nmem a = c₀.nmem a
variable {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
theorem wbStmt_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {X top : ℕ} {L : List ℕ} (hX : X < E.R) (hL : L.length ≤ E.D)
    (hcap : top - 1 + L.length ≤ d.cap)
    (h100 : c.nreg 90100 = L.length) (h103 : c.nreg 90103 = d.b0 + d.oEx + d.D * X)
    (h50 : c.nreg 90050 = top)
    (htmp : ∀ i, i < L.length → c.nmem ztqli = L.getD i 0) :
    ∃ c' k, Exec P W wbStmt c c' k ∧ k ≤ 10 * E.D + 5 ∧
      Enc c'.nmem d (S.wb X ztkfv L L.length) ∧ c'.nreg 90108 = top - 1 ∧
      ztegs ∧
      ztybk ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W wbStmt c c' k ∧ k ≤ 10 * E.D + 5 ∧
      Enc c'.nmem d _ ∧ c'.nreg 90108 = top - 1 ∧
      ztegs ∧
      ztybk by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameS e wrS_wb⟩
  zubga
  zumcs
  zuf
  zujma
  rw [← hD.D] at hL
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90101 0,
      .subN 90108 90050 90019]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 90101 = 0 ∧
      c₁.nreg 90108 = top - 1 ∧ (∀ r, r ≠ 90101 → r ≠ 90108 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem) := by
    exec_block
    · omega
    · refine ztdqx <;> config_simp
      rw [h50, hC.one]
  obtain ⟨q101, q108, qr, qm⟩ := q
  have I0 : WbI W d S X ztkfv L c₁ c₁ := by
    refine ⟨e₁.wb_right, by_omega, ?_, by_omega, by_omega⟩
    rw [q101, qm]
    refine henc.st_congr ztcj ztcj ztcj ztcj
      ztcj ztcj ztcj ztnzp ztcj
      ztcj ztcj ztcj ztcj ztqof <;>
      simp [St.wb]
  have k44 : ztrgk := by rw [qr _ by_decide by_decide, hC.bTmp]
  have k43 : c₁.nreg 90043 = d.b0 + d.oStk := by rw [qr _ by_decide by_decide, hC.bStk]
  have k19 : ztgas := by rw [qr _ by_decide by_decide, hC.one]
  have k100 : c₁.nreg 90100 = L.length := by_simp_all
  have k103 : c₁.nreg 90103 = d.b0 + d.oEx + d.D * X := by
    simp_all
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := 90100)
    (body := wbBody) (WbI W d S X ztkfv L c₁) (fun d' => L.length - d'.nreg 90101) 8
    ztpf
    (fun c₂ I ht => by
      obtain ⟨hw₂, ht₂, henc₂, hr₂, hm₂⟩ := I
      rw [hr₂ 90100 by_decide by_decide by_decide, k100] at ht
      generalize htdef : c₂.nreg 90101 = t at ht ht₂ henc₂
      have s := slot_lt hX ztpea
      have r44 : c₂.nreg 90044 = d.b0 + d.oTmp := by
        grind
      have r43 : c₂.nreg 90043 = d.b0 + d.oStk := by
        grind
      have r19 : ztizn := by_grind
      have r103 : c₂.nreg 90103 = d.b0 + d.oEx + d.D * X := by
        grind
      have r108 : c₂.nreg 90108 = top - 1 := by
        grind
      have vt : c₂.nmem (d.b0 + d.oTmp + t) = L.getD t 0 := by
        grind
      unfold wbBody
      exec_block
      · omega
      · config_simp; grind
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · refine ⟨⟨by assumption, ?_, ?_, ?_, ?_⟩, by_omega, ?_⟩
        · config_simp; omega
        · config_simp
          rw [r44, r103, r43, r108, r19, htdef, vt]
          have E1 := henc₂.set_ex hX ztpea ztemz
          have E2 := E1.set_stk (show top - 1 + t < d.cap by omega) ztemz
          rw [show d.b0 + d.oStk + ztkfv + t = d.b0 + d.oStk + (top - 1 + t) by omega,
            show d.b0 + d.oEx + d.D * X + t = d.b0 + d.oEx + d.D * X + t from rfl]
          refine E2.st_congr ztcj ztcj ztcj ztcj
            ztcj ztcj ztcj (fun x u _ _ => ?_)
            ztcj ztcj ztcj ztcj ztcj
            (fun u _ => ?_)
          · simp only [St.wb]
            grind
          · simp only [St.wb, Function.update_apply]
            grind
        · intro r a1 a2 a3
          config_simp
          simp only [upd, a1, a2, a3, ite_false]
          grind
        · zuge
          config_simp
          zuby
          grind
        · config_simp; omega) I0
  zueiz
  rw [hr' 90100 by_decide by_decide by_decide, k100] at hx
  have hfull : c'.nreg 90101 = L.length := by_omega
  rw [hfull] at henc'
  refine ⟨c', _, .seq e₁ e, ?_, henc', ?_, fun r a1 a2 a3 a4 => ?_, fun a ha => ?_⟩
  · rw [q101] at hk
    zukzg

  · grind
  · grind
  grind

/-! ## The tail -/

/-- The class `X` gets the merged degree and weight, and `c` dies. -/
def St.tl (S : St) (cc X len μ : ℕ) : St :=
  { S with
    live := Function.update S.live cc 0
    deg := Function.update S.deg X len
    wt := Function.update S.wt X μ }

/-- `deg X := len`; `wt X := μ`; `live c := 0`; `top := top1 + len`; `nlive := nlive - 1`. -/
def tailStmt : Stmt := block [.addN 90105 90035 90064, .storeN 90105 90100,
  .addN 90105 90036 90064, .storeN 90105 90078, .addN 90105 90030 90062, .constN 90106 0,
  .storeN 90105 90106, .addN 90050 90108 90100, .subN 90051 90051 90019]
theorem tailStmt_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {cc X len μ top1 : ℕ} (hX : X < E.R) (hcc : cc < E.K) (hcap : top1 + len ≤ d.cap)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = X) (h100 : c.nreg 90100 = len)
    (h78 : c.nreg 90078 = μ) (h108 : c.nreg 90108 = top1) :
    ∃ c' k, Exec P W tailStmt c c' k ∧ k = 9 ∧ Enc c'.nmem d (S.tl cc X len μ) ∧
      c'.nreg 90050 = top1 + len ∧ c'.nreg 90051 = c.nreg 90051 - 1 ∧
      (∀ r, r ≠ 90050 → r ≠ 90051 → r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 ∨ d.b0 + d.oEx ≤ a) → c'.nmem a = c.nmem a) := by
  zubga
  zumcs
  zuf
  zujma
  rw [← hD.K] at hcc
  unfold tailStmt
  exec_block
  · rw [hC.bDeg, h64]; omega
  · config_simp; zuolc; omega
  · config_simp; rw [hC.bLive, h62]; omega
  · omega
  · config_simp; omega
  · refine ⟨rfl, ?_, ?_, ?_, by_simp_all, ?_⟩ <;>
      config_simp
    · rw [hC.bDeg, h64, hC.bWt, hC.bLive, h62, h100, h78]
      exact ((henc.set_deg hX len).set_wt hX μ).set_live hcc 0
    · omega
    · rw [hC.one]
    · zuge
      rw [hC.bDeg, h64, hC.bWt, hC.bLive, h62]
      zuby
      grind

/-! ## The ring -/

/-- Unlink the position `r rn` from the ring. -/
def unlinkS (rn : ℕ) : Stmt := block [.addN 90105 90040 rn, .loadN 90106 90105,
  .addN 90105 90039 rn, .loadN 90107 90105, .addN 90105 90039 90106, .storeN 90105 90107,
  .addN 90105 90040 90107, .storeN 90105 90106]

/-- Unlink position `j` if `b`. -/
def St.optUnl (S : St) (b : Bool) (j : ℕ) : St :=
  if b then { S with nxt := (St.unl (S.nxt, S.prv) j).1, prv := (St.unl (S.nxt, S.prv) j).2 }
  else S
theorem unlinkS_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rn j : ℕ} (h5 : rn ≠ 90105) (h6 : rn ≠ 90106) (_h7 : rn ≠ 90107) (hj : c.nreg rn = j)
    (hjA : j < d.A) (hp : S.prv j < d.A) (hn : S.nxt j < d.A) :
    ∃ c' k, Exec P W ztwgz c c' k ∧ k = 8 ∧ Enc c'.nmem d (S.optUnl true j) ∧
      ztcjn ∧
      ztfaa := by
  zubga
  zuf
  have ep : c.nmem _ = S.prv j := henc.prv j hjA
  have en : c.nmem _ = S.nxt j := henc.nxt j hjA
  unfold unlinkS
  exec_block
  · rw [hC.bPrv, hj]; omega
  · config_simp; simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]; rw [hC.bNxt, hj]; omega
  · config_simp; rw [hC.bNxt, hC.bPrv, hj, ep]; omega
  · config_simp; simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]; rw [hC.bPrv, hC.bNxt, hj, en]; omega
  · refine ztopi <;> config_simp <;>
      simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]
    · zufnb
      exact (henc.set_nxt hp _).set_prv hn _
    · zuge
      zufnb
      zuby
      grind

/-- Decrement the count at position `r rn`. -/
def decS (rn : ℕ) : Stmt := block [.addN 90105 90038 rn, .loadN 90106 90105,
  .subN 90106 90106 90019, .storeN 90105 90106]
theorem decS_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rn j : ℕ} (_h5 : rn ≠ 90105) (_h6 : rn ≠ 90106) (hj : c.nreg rn = j) (hjA : j < d.A) :
    ∃ c' k, Exec P W (decS rn) c c' k ∧ k = 4 ∧
      Enc c'.nmem d { S with cnt := Function.update S.cnt j (S.cnt j - 1) } ∧
      ztgso ∧
      (∀ a, zteor → c'.nmem a = c.nmem a) := by
  zubga
  zuf
  have ec : c.nmem _ = S.cnt j := henc.cnt j hjA
  unfold decS
  exec_block
  · zuole; omega
  · refine ztopi <;> config_simp
    · rw [hC.bCnt, hj, ec, hC.one]
      exact henc.set_cnt hjA _
    · zuge
      zuole
      zuby
      grind

/-- Unlink position `r rn` iff the bit `r rb` is set. -/
theorem optUnl_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rb rn j : ℕ} {b : Bool} (h5 : rn ≠ 90105) (h6 : rn ≠ 90106) (h7 : rn ≠ 90107)
    (hj : c.nreg rn = j) (hbit : c.nreg rb = bit b)
    (hjA : j < d.A) (hp : S.prv j < d.A) (hn : S.nxt j < d.A) :
    ∃ c' k, Exec P W (.ifLtN rb 90019 .skip ztwgz) c c' k ∧ k ≤ 10 ∧
      Enc c'.nmem d (S.optUnl b j) ∧
      ztcjn ∧
      ztfaa := by
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_true ztlhs ztjd, by_omega, henc,
      by omega, by_omega⟩
  | true =>
    obtain ⟨c', k, e, hk, h1, h2, h3⟩ := unlinkS_exec hw hC henc hD h5 h6 h7 hj hjA hp hn
    exact ⟨c', _, .ifLtN_false ztlhs e, by_omega, h1, h2, h3⟩

/-- Unlink the dying positions and decrement the counts. -/
def ringStmt : Stmt :=
  .seq (.ifLtN 90072 90019 .skip (unlinkS 90068))
    (.seq (.ifLtN 90073 90019 .skip (unlinkS 90069)) (.seq (decS 90068) (decS 90069)))

/-- The state after `ringStmt`. -/
def St.rg (S : St) (n1 n2 : ℕ) : St :=
  let S3 := (S.optUnl zthgl n1).optUnl ztbahj n2
  { S3 with cnt := Function.update (Function.update S.cnt n1 (S.cnt n1 - 1)) n2 (S.cnt n2 - 1) }
theorem optUnl_cnt (S : St) (b : Bool) (j : ℕ) : (S.optUnl b j).cnt = S.cnt := by
  unfold St.optUnl; grind
theorem optUnl_bound {S : St} {A : ℕ} (b : Bool) {j j' : ℕ} (hn : S.nxt j < A) (hp : S.prv j < A)
    (hn' : S.nxt j' < A) (hp' : S.prv j' < A) :
    (S.optUnl b j).nxt j' < A ∧ (S.optUnl b j).prv j' < A := by
  unfold St.optUnl St.unl
  split_ifs
  · grind
  omega
theorem ringStmt_exec
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {n1 n2 : ℕ} (h68 : c.nreg 90068 = n1) (h69 : c.nreg 90069 = n2)
    (h72 : c.nreg 90072 = bit zthgl)
    (h73 : c.nreg 90073 = bit ztbahj)
    (hn1 : n1 < d.A) (hn2 : n2 < d.A) (hne : n1 ≠ n2)
    (b1 : S.nxt n1 < d.A ∧ S.prv n1 < d.A) (b2 : S.nxt n2 < d.A ∧ S.prv n2 < d.A) :
    ∃ c' k, Exec P W ringStmt c c' k ∧ k ≤ 28 ∧ Enc c'.nmem d (S.rg n1 n2) ∧
      ztcjn ∧
      (∀ a, (a < d.b0 + d.oCnt ∨ d.b0 + d.oEg ≤ a) → c'.nmem a = c.nmem a) := by
  zuf
  obtain ⟨c₁, k₁, e₁, hk₁, E₁, r₁, m₁⟩ := optUnl_exec (P := P) (rb := 90072) (rn := 90068)
    (b := decide (S.cnt n1 = 1)) hw hC henc hD by_decide by_decide by_decide h68 h72 hn1
    b1.2 b1.1
  have hC₁ : ztukj := hC.frame by_grind
  have bb := optUnl_bound zthgl b1.1 b1.2 b2.1 b2.2
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, r₂, m₂⟩ := optUnl_exec (P := P) (rb := 90073) (rn := 90069)
    (b := decide ztlfq) e₁.wb_right hC₁ E₁ hD by_decide by_decide by_decide
    by_simp_all
    by_simp_all hn2 bb.2 bb.1
  have hC₂ : ztpjc := hC₁.frame by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, r₃, m₃⟩ := decS_exec (P := P) (rn := 90068) e₂.wb_right hC₂ E₂ hD
    by_decide by_decide
    by_grind hn1
  have hC₃ : ztukk := hC₂.frame by_grind
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, r₄, m₄⟩ := decS_exec (P := P) (rn := 90069) e₃.wb_right hC₃ E₃ hD
    by_decide by_decide
    by_grind hn2
  refine ztxmc
  · refine E₄.st_congr ztcj ztcj ztcj ztcj
      ztcj ztcj ztcj ztcnd ztchx
      ztcj ztcj ztcj ztcj ztcj
    simp only [St.rg, optUnl_cnt, Function.update_apply, ite_eq_right ztnr]
  · grind
  · zuge
    rw [m₄ a by_omega, m₃ a by_omega, m₂ a by_omega, m₁ a by_omega]
def rmStmt : Stmt := .seq gatherStmt (.seq relStmt (.seq wbStmt (.seq tailStmt ringStmt)))

/-- The registers the removal writes. -/
def Brm2 (r : ℕ) : Bool := Brm r || decide zttxv || decide zttxw
theorem wrS_rm : wrS Brm2 rmStmt = true := by_decide
theorem optUnl_eq (S : St) (b : Bool) (j : ℕ) : S.optUnl b j =
    { S with nxt := if b then (St.unl (S.nxt, S.prv) j).1 else S.nxt,
             prv := if b then (St.unl (S.nxt, S.prv) j).2 else S.prv } := by
  cases b <;> rfl
theorem rm_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) {cc μ : ℕ} (hc : cc ∈ st.L E) (_htop : 0 < st.top)
    (hlow : st.deg ztfis < 3 ∨ st.deg ztbnp < 3) (hI' : Inv E ztoim)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h66 : c.nreg 90066 = st.deg ztfis) (h67 : c.nreg 90067 = st.deg ztbnp)
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit ztxwi)
    (h73 : c.nreg 90073 = bit ztxwj)
    (h78 : c.nreg 90078 = μ) :
    ∃ c' k, Exec P W rmStmt c c' k ∧ k ≤ 60 * E.D + 65 ∧ MS W E d A₀ m₀ c' ztoim ∧
      FrameS Brm2 c c' := by
  suffices hh : ∃ c' k, Exec P W rmStmt c c' k ∧ k ≤ 60 * E.D + 65 ∧
      (WordsBounded W c' → FrameS Brm2 c c' → MS W E d A₀ m₀ c' ztoim) by
    zueif
    have F := exec_frameS e wrS_rm
    exact ⟨c', k, e, h1, h2 e.wb_right F, F⟩
  have hw := hM.wb
  have hC := hM.cst
  have henc := hM.enc
  zuf
  zufxf
  obtain ⟨P', hs⟩ := hI.split hE hc
  obtain ⟨hX, hY, -, htouch⟩ := hI.sides cc hc
  obtain ⟨hXr, hYr⟩ := hI.cl_mem hE hc
  have hcX : cc ∈ st.exl ztfis := (exl_X hE hI hc cc).2 ⟨hc, (htouch _ hXr).2 ztp⟩
  have hcY : cc ∈ st.exl ztbnp := (exl_Y hE hI hc cc).2 ⟨hc, (htouch _ hYr).2 ztbt⟩
  have clX := hI.cls _ ztpff
  have clY := hI.cls _ ztpfg
  have hlen := newEx_le hE hI hc hs hlow
  have hlen2 := newEx_length hE hI hc hs
  have hfY : ((st.exl ztbnp).filter ztvv).length + 1 = st.deg ztbnp := by
    rw [← clY.2.2.1.erase_eq_filter, List.length_erase_of_mem hcY, exl_length]
    have := List.length_pos_of_mem hcY
    rw [exl_length] at this
    omega
  have hroom : ((st.exl ztfis).filter ztvv).length + st.deg ztbnp ≤ E.D + 1 := by
    have : (st.newEx cc).length = ((st.exl ztfis).filter ztvv).length +
        ((st.exl ztbnp).filter ztvv).length := by
      unfold St.newEx; simp
    omega
  have hcap : st.top - 1 + (st.newEx cc).length ≤ d.cap := by
    have := hI'.topLe
    simp only [St.remove] at this
    have e : d.cap = E.K + E.D * E.K := by unfold Dm.cap; rw [hD.K, hD.D]
    omega
  -- gather
  obtain ⟨c₁, k₁, e₁, hk₁, g100, g103, g104, gtmp, gmem, gF⟩ := gather_exec (P := P) hw hC henc hD
    hX hY clX.2.2.2.2 clY.2.2.2.2 hroom h62 h64 h65 h66 h67
  have g₁ : ∀ r, Brm r = false → c₁.nreg r = c.nreg r := gF.1
  zuka
  have hC₁ : ztukj := hC.frame fun r hr h' => g₁ r ztnup
  have henc₁ : Enc c₁.nmem d st := henc.mem_congr fun a _ ha => gmem a ztbbu
  -- relabel
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, r₂, m₂, F₂⟩ := relStmt_exec (P := P) hw₁ hC₁ henc₁ hD hY
    clY.2.2.2.2 clY.2.2.1 (fun i hi => ((clY.2.2.2.1 i).1 hi).1.1)
    (by rw [g₁ _ by_decide, h62]) (by rw [g₁ _ by_decide, h64])
    (by rw [g₁ _ by_decide, h65]) (by rw [g₁ _ by_decide, h67]) g104
  zuja
  have hC₂ : ztpjc := hC₁.frame fun r hr h' => r₂ r by_omega by_omega by_omega
    by_omega
  -- write back
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, w108, r₃, m₃, F₃⟩ := wbStmt_exec (P := P) (top := st.top)
    (L := st.newEx cc) hw₂ hC₂ E₂ hD hX hlen hcap
    (by rw [r₂ _ by_decide by_decide by_decide by_decide, g100]; rfl)
    by_grind
    (by rw [r₂ _ by_decide by_decide by_decide by_decide, g₁ _ by_decide, hM.top])
    (fun i hi => by
      rw [m₂ _ by_omega]
      exact gtmp i (by rw [g100]; exact hi))
  zuboe
  have hC₃ : ztukk := hC₂.frame fun r hr h' => r₃ r by_omega by_omega by_omega
    by_omega
  have R₃ : ∀ r, r < 90100 → c₃.nreg r = c.nreg r := fun r hr => by
    rw [r₃ r by_omega by_omega by_omega by_omega,
      r₂ r by_omega by_omega by_omega by_omega, g₁ r ztnup]
  -- tail
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, t50, t51, r₄, m₄⟩ := tailStmt_exec (P := P) (len := (st.newEx cc).length)
    (μ := μ) hw₃ hC₃ E₃ hD hX hc.1 hcap by_grind
    by_grind
    (by rw [r₃ _ by_decide by_decide by_decide by_decide,
      r₂ _ by_decide by_decide by_decide by_decide, g100]; rfl)
    by_grind w108
  zubwq
  have hC₄ : Cst c₄ E d := hC₃.frame fun r hr h' => r₄ r by_omega by_omega by_omega
    by_omega
  have R₄ : ∀ r, r < 90100 → r ≠ 90050 → r ≠ 90051 → c₄.nreg r = c.nreg r := fun r hr a1 a2 => by
    rw [r₄ r a1 a2 by_omega by_omega, R₃ r hr]
  -- ring
  have hn0 := (hI.stat.nd0 cc hc.1).1
  have hn1 := (hI.stat.nd1 cc hc.1).1
  have hL0 := (hI.lv_iff hn0).2 ztpff
  have hL1 := (hI.lv_iff hn1).2 ztpfg
  obtain ⟨⟨a0, -, -, -⟩, ⟨b0', -, -, -⟩⟩ := hI.ring _ hn0 hL0
  obtain ⟨⟨a1, -, -, -⟩, ⟨b1', -, -, -⟩⟩ := hI.ring _ hn1 hL1
  rw [← hD.A] at hn0 hn1 a0 b0' a1 b1'
  obtain ⟨c₅, k₅, e₅, hk₅, E₅, r₅, m₅⟩ := ringStmt_exec (P := P) (n1 := st.nd0 cc)
    (n2 := st.nd1 cc) hw₄ hC₄ E₄ hD (by rw [R₄ _ by_decide by_decide by_decide, h68])
    (by rw [R₄ _ by_decide by_decide by_decide, h69])
    (by rw [R₄ _ by_decide by_decide by_decide, h72]; rfl)
    (by rw [R₄ _ by_decide by_decide by_decide, h73]; rfl) hn0 hn1 (hI.nd_ne hE hc)
    ⟨a0, b0'⟩ ⟨a1, b1'⟩
  refine ⟨c₅, _, .seq e₁ ztbq, ?_, fun hw₅ F => ?_⟩
  · omega
  refine ⟨hw₅, hC₄.frame fun r hr _ => r₅ r by_omega by_omega by_omega, ?_, ?_, ?_, ?_⟩
  · -- the encoding of the removed state
    refine E₅.st_congr ztbzz ztbzz ztbzz ztbzz
      ztbzz ztqoi ztqoi ztnzp ztchx
      ztchx ztchx ztchx ztchx ztqof <;>
      simp only [St.remove, St.rg, St.tl, St.wb, St.rel, optUnl_eq, St.newEx, St.ring2]
    · by_cases h1 : st.cnt ztmom = 1 <;> by_cases h2 : st.cnt ztqwx = 1 <;>
        zuggd
    · by_cases h1 : st.cnt ztmom = 1 <;> by_cases h2 : st.cnt ztqwx = 1 <;>
        zuggd
  · rw [r₅ _ by_decide by_decide by_decide, t50]; rfl
  · rw [r₅ _ by_decide by_decide by_decide, t51, R₃ _ by_decide, hM.nlive]; rfl
  · zuge
    have hab : a < d.b0 := by_omega
    rw [m₅ a by_omega, m₄ a by_omega, m₃ a by_omega, m₂ a by_omega,
      gmem a by_omega, hM.low a ha]
section Cases
variable {st : St}
theorem step_dead (h : st.live st.cur ≠ 1) : st.step E = st.pop := by
  zujqg
theorem step_keep (h : st.live st.cur = 1)
    (hd : 3 ≤ st.deg ztgmf ∧ 3 ≤ st.deg ztgmg) : st.step E = st.pop := by
  zujqg
theorem step_heavy (h : st.live st.cur = 1)
    (hd : ¬ ztdfb)
    (hm : E.γ < st.mu E st.cur) : st.step E = st.pop := by
  zujqg
theorem step_rm (h : st.live st.cur = 1)
    (hd : ¬ ztdfb)
    (hm : ¬ E.γ < st.mu E st.cur) : st.step E = st.remove st.cur ztoil := by
  unfold St.step; grind
end Cases

/-- A machine state survives a statement changing only temporaries (`≥ 90060`) and no memory. -/
theorem MS.frameT {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c c' : Config} {st : St}
    (h : MS W E d A₀ m₀ c st) (hw : WordsBounded W c')
    (hr : ∀ r, r < 90060 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem) :
    MS W E d A₀ m₀ c' st :=
  ⟨hw, h.cst.frame fun r hr' _ => hr r by_omega, by zvmwi; exact h.enc,
    by zumwn; exact h.top, by zumwn; exact h.nlive,
    fun a ha => by zvmwi; exact h.low a ha⟩

/-! ## The body -/

/-- Compute the merged weight; pop if it exceeds `γ`, else remove. -/
def tryStmt : Stmt := .seq muStmt (.ifLtN 90014 90078 popStmt rmStmt)

/-- **One step of the worklist.** -/
def bodyStmt : Stmt :=
  .seq frontStmt (.ifLtN 90063 90019 popStmt
    (.seq xyStmt (.seq ndStmt (.ifLtN 90066 90020 tryStmt (.ifLtN 90067 90020 tryStmt popStmt)))))

/-- The registers `muStmt` writes. -/
def Bmu (r : ℕ) : Bool := decide zttxx || decide (90074 ≤ r ∧ r < 90100)
theorem wr_mu_fine : wr Bmu muStmt = true := by_decide

/-- The registers `ndStmt` writes. -/
def Bnd (r : ℕ) : Bool := decide zttxx || decide (90068 ≤ r ∧ r < 90074)
theorem wr_nd_fine : wr Bnd ndStmt = true := by_decide

/-- The registers of the body. -/
def Bbody (r : ℕ) : Bool := decide (90060 ≤ r ∧ r < 90110) || decide zttxv ||
  decide zttxw
theorem wrS_body : wrS Bbody bodyStmt = true := by_decide
variable {P : Polygon}
theorem try_exec {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) (hc : st.cur ∈ st.L E) (htop : 0 < st.top)
    (hlow : ¬ ztdfb)
    (h62 : c.nreg 90062 = st.cur) (h64 : c.nreg 90064 = st.s0 st.cur)
    (h65 : c.nreg 90065 = st.s1 st.cur)
    (h66 : c.nreg 90066 = st.deg ztgmf) (h67 : c.nreg 90067 = st.deg ztgmg)
    (h68 : c.nreg 90068 = st.nd0 st.cur) (h69 : c.nreg 90069 = st.nd1 st.cur)
    (h72 : c.nreg 90072 = bit (decide (st.cnt (st.nd0 st.cur) = 1)))
    (h73 : c.nreg 90073 = bit (decide (st.cnt (st.nd1 st.cur) = 1))) :
    ∃ c' k, Exec P W tryStmt c c' k ∧ k ≤ 60 * E.D + 330 ∧ MS W E d A₀ m₀ c' ztmoo := by
  obtain ⟨c₁, k₁, e₁, hk₁, m78, -⟩ := mu_exec (P := P) hE hM.wb hM.cst hM.enc hI hD hc h64 h65
    h68 h69 h72 h73 hM.nlive
  have F₁ := exec_frameB e₁ wr_mu_fine
  have g : ∀ r, r < 90100 → r ≠ 90061 → (r < 90074) → c₁.nreg r = c.nreg r := fun r a1 a2 a3 =>
    F₁.1 r (by simp [Bmu]; omega)
  have hM₁ : ztoqm := hM.frameT e₁.wb_right (fun r hr => g r by_omega by_omega
    by_omega) F₁.2.2.1
  by_cases hm : E.γ < st.mu E st.cur
  · zucdt
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true ztktf e₂), by_omega, ?_⟩
    rw [step_heavy hc.2 hlow hm]; omega
  · have hlow' : ztylx := by_omega
    have hI' := hI.step hE htop
    rw [step_rm hc.2 hlow hm] at hI' ⊢
    obtain ⟨c₂, k₂, e₂, hk₂, hM₂, -⟩ := rm_exec (P := P) (μ := st.mu E st.cur) hE hM₁ hI hD hA hc
      htop hlow' hI'
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all
      by_simp_all m78
    exact ⟨c₂, _, .seq e₁ (.ifLtN_false ztktf e₂), by_omega, hM₂⟩

/-- **One step of the worklist on the RAM.** -/
theorem body_exec {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) (htop : 0 < st.top) :
    ∃ c' k, Exec P W bodyStmt c c' k ∧ k ≤ 60 * E.D + 400 ∧ MS W E d A₀ m₀ c' ztmoo ∧
      FrameS Bbody c c' := by
  suffices hh : ∃ c' k, Exec P W bodyStmt c c' k ∧ k ≤ 60 * E.D + 400 ∧
      MS W E d A₀ m₀ c' ztmoo by
    zueif
    exact ⟨c', k, e, h1, h2, exec_frameS e wrS_body⟩
  obtain ⟨c₁, k₁, e₁, hk₁, f62, f63, hcK, fr, fm⟩ := front_exec (P := P) hM hI hD htop
  have hM₁ : ztoqm := hM.frameT e₁.wb_right (fun r hr => fr r by_omega
    by_omega by_omega by_omega) fm
  have hl01 := hI.live01 _ hcK
  by_cases hl : st.live st.cur = 1
  swap
  · zucdt
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rw [f63, hM₁.cst.one]; omega) e₂), by_omega, ?_⟩
    rw [step_dead hl]; omega
  have hc : ztjap := ⟨hcK, hl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, x64, x65, x66, x67, xr, xm⟩ := xy_exec (P := P) hM₁.wb hM₁.cst
    hM₁.enc hI hD hc f62
  have hM₂ : MS W E d A₀ m₀ c₂ st := hM₁.frameT e₂.wb_right (fun r hr => xr r by_omega
    by_omega by_omega by_omega by_omega) xm
  obtain ⟨c₃, k₃, e₃, hk₃, n68, n69, n72, n73, F₃⟩ := nd_exec (P := P) hM₂.wb hM₂.cst hM₂.enc hI hD
    hc by_simp_all
  have hM₃ : MS W E d A₀ m₀ c₃ st := hM₂.frameT e₃.wb_right (fun r hr => F₃.1 r (Bin_false
    by_omega)) F₃.2.2.1
  have F₃' := exec_frameB e₃ wr_nd_fine
  have g : ∀ r, 90061 < r → r < 90068 → c₃.nreg r = c₂.nreg r := fun r a1 a2 =>
    F₃'.1 r (by simp [Bnd]; omega)
  have t62 : c₃.nreg 90062 = st.cur := by
    grind
  have t64 : c₃.nreg 90064 = st.s0 st.cur := by_grind
  have t65 : c₃.nreg 90065 = st.s1 st.cur := by_grind
  have t66 : c₃.nreg 90066 = st.deg ztgmf := by_grind
  have t67 : c₃.nreg 90067 = st.deg ztgmg := by_grind
  have tryE := fun (hlow : ¬ (3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur))) =>
    try_exec (P := P) hE hM₃ hI hD hA hc htop hlow t62 t64 t65 t66 t67 n68 n69 n72 n73
  have hnl : ¬ c₁.nreg 90063 < c₁.nreg 90019 := by rw [f63, hM₁.cst.one, hl]; omega
  by_cases h3X : 3 ≤ st.deg ztgmf
  · by_cases h3Y : 3 ≤ st.deg ztgmg
    · obtain ⟨c₄, k₄, e₄, hk₄, hM₄, -, -⟩ := hM₃.pop (P := P)
      refine ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_false
        ztfpu (.ifLtN_false ztliu
          e₄))))), by_omega, ?_⟩
      rw [step_keep hl ⟨h3X, h3Y⟩]; omega
    · zueaq
      exact ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_false
        ztfpu (.ifLtN_true ztliu
          e₄))))), by_omega, hM₄⟩
  · zueaq
    exact ⟨c₄, _, .seq e₁ (.ifLtN_false hnl (.seq e₂ (.seq e₃ (.ifLtN_true
      ztfpu e₄)))), by_omega, hM₄⟩

/-! ## The loop -/

/-- **The worklist loop** (`r52 = 0`). -/
def loopStmt : Stmt := .whileLtN 90052 90050 bodyStmt
theorem loop_exec {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) (h52 : c.nreg 90052 = 0) :
    ∃ c' k st', Exec P W loopStmt c c' k ∧ k ≤ (60 * E.D + 402) * st.meas E + 2 ∧
      MS W E d A₀ m₀ c' st' ∧ Inv E st' ∧ st'.top = 0 ∧
      (∀ r, Bbody r = false → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, e, ⟨st', hM', hI', h52', hr'⟩, hx, hk⟩ := Exec.whileLtN_bounded (P := P)
    (a := 90052) (b := 90050) (body := bodyStmt)
    (fun c₁ => ∃ st₁, MS W E d A₀ m₀ c₁ st₁ ∧ Inv E st₁ ∧ c₁.nreg 90052 = 0 ∧
      (∀ r, Bbody r = false → c₁.nreg r = c.nreg r))
    (fun c₁ => c₁.nreg 90050 + zteml * c₁.nreg 90051) (60 * E.D + 400)
    (fun _ ⟨_, h, _⟩ => h.wb)
    (fun c₁ ⟨st₁, hM₁, hI₁, h52₁, hr₁⟩ ht => by
      have htop : 0 < st₁.top := by rw [h52₁, hM₁.top] at ht; exact ht
      obtain ⟨c₂, k₂, e₂, hk₂, hM₂, F₂⟩ := body_exec (P := P) hE hM₁ hI₁ hD hA htop
      have hI₂ := hI₁.step hE htop
      have hms := measure_step hE hI₁ htop
      refine ⟨c₂, k₂, e₂, ⟨_, hM₂, hI₂, by rw [F₂.1 _ by_decide, h52₁],
        fun r hr => by rw [F₂.1 r hr, hr₁ r hr]⟩, hk₂, ?_⟩
      unfold St.meas at hms
      rw [hM₂.top, hM₂.nlive, hM₁.top, hM₁.nlive]
      omega) ⟨st, hM, hI, h52, fun _ _ => rfl⟩
  refine ⟨c', k, st', e, ?_, hM', hI', ?_, hr'⟩
  · rw [hM.top, hM.nlive] at hk
    tauto
  · rw [h52', hM'.top] at hx; omega
end
end Gran
namespace Loc
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sidePrev sideNext SideClean
  ChordSystem freeIn regionsIn TouchesIn IsHChordIn)
open Chazelle.Jordan (offset)
open Chazelle.Visibility (hseg)

/-- Scaling keeps the right-neighbourhood filter of `0`. -/
theorem tendsto_mul_const_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => δ * c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  zuloq
  · have : Tendsto (fun δ : ℝ => δ * c) (𝓝 0) (𝓝 (0 * c)) :=
      (continuous_id.mul continuous_const).tendsto 0
    zudvn
    zuhv
  simp_all
variable {Q : Polygon}

/-- **Near a non-cut position, the domain is in the region faced just after it.** -/
theorem near_sub_region (hQ : Q.Simple) {F : Set ztf}
    (hF : F ⊆ (interiorModel Q).Adm) (hfin : F.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (interiorModel Q).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hcut : ¬ (interiorModel Q).IsCut F ztk) {U : Set Point}
    (hU : U ∈ (interiorModel Q).regions F)
    (hfU : ∀ᶠ s in 𝓝[>] (0 : ℝ), (interiorModel Q).Faces p ztwlx U) :
    ∃ r > 0, ∀ x ∈ ball (sidePt (interiorModel Q).W p t) r, x ∈ (interiorModel Q).D → x ∈ U := by
  zubze
  set W := M.W
  set z := sidePt W p t with hz
  zudg
  zuys
  have hD : M.D = W.filled \ W.boundary := by
    show Q.filled \ Q.boundary = (interiorWalk Q).filled \ (interiorWalk Q).boundary
    simp_all
  obtain ⟨rL, hrL, hleft⟩ := FactsInterior.interior_left hWs hWo hp ht0 ht1
  zuebi
  -- the point is on no chord of `F`
  have hzF : ∀ c ∈ F, z ∉ c := by
    intro c hc hzc
    obtain ⟨y, a, b, hh, rfl⟩ := hF hc
    have hzD : z ∉ M.D := hM.trace p hp t ht0 ht1.le
    zumcx
    have hzy : ztlbm := hzc.1
    refine hcut ⟨hseg y a b, hc, p, t, ⟨hp, ht0, ht1, hzc, min zthu rL,
      lt_min by_linarith hrL, fun x hx hxz hdist => ?_⟩, rfl⟩
    have hd1 : |x.1 - z.1| < b - a := by
      have h := lt_of_lt_of_le hdist ztff
      have h2 : dist x.1 z.1 ≤ dist x z := by zuowp; simp
      rw [Real.dist_eq] at h2; grind
    have hxy : ztsnb := hx.1
    -- `z` is an end of the chord
    have hzend : z.1 = a ∨ z.1 = b := by
      zuct
      zumip
      apply hzD
      have := hh.open_mem z.1 (lt_of_le_of_ne hzc.2.1 ztvbk)
        (lt_of_le_of_ne hzc.2.2 hne.2)
      rw [← hzy] at this
      tauto
    have hx1 : x.1 ≠ z.1 := fun e => hxz (Prod.ext e (hxy.trans hzy.symm))
    have hxD : x ∈ M.D := by
      have hxo : a < x.1 ∧ x.1 < b := by
        rcases hzend with he | he <;> zvncj at hd1 <;> refine ⟨?_, ?_⟩
        · exact lt_of_le_of_ne hx.2.1 ztqnr
        · linarith
        · linarith
        · exact lt_of_le_of_ne hx.2.2 ztqnr
      have := hh.open_mem x.1 hxo.1 hxo.2
      rw [← hxy] at this; tauto
    refine hleft x (lt_of_lt_of_le hdist ztgh) ?_
    rw [hWb, hWf]; tauto
  -- a ball avoiding all chords
  have hev : ∀ᶠ x in 𝓝 z, ∀ c ∈ F, x ∉ c := by
    refine (hfin.eventually_all (p := fun c x => x ∉ c)).2 fun c hc => ?_
    obtain ⟨y, a, b, -, rfl⟩ := hF hc
    exact (Chazelle.Chain.isClosed_hseg y a b).isOpen_compl.mem_nhds (hzF _ hc)
  obtain ⟨rF, hrF, hballF⟩ := Metric.eventually_nhds_iff.1 hev
  set r := min rF (min rL rC)
  have hr : ztixt := lt_min hrF (lt_min hrL hrC)
  have hrF' : r ≤ rF := min_le_left _ _
  have hrL' : r ≤ rL := le_trans ztgh ztff
  have hrC' : r ≤ rC := le_trans ztgh ztgh
  -- the corner
  zukec
  have hbv : sideNext W p ≠ z := by
    zumuu
    zudur
    zucky
    exact (Chazelle.Jordan.lerp_ne_right hnd ht1).symm
  have hav : sidePrev W p t ≠ z := by
    zulcf
    zujpo
    · zucfb
      rw [hz, Chazelle.Chain.sidePt_zero]
      have hn : ztmsm := by_omega
      have hq := hM.nd ztbvk zthp
      rw [BoxT.prev_succ hp] at hq
      zuito
    · zvncr; unfold sidePt
      exact (Chazelle.Jordan.lerp_ne_left hnd ztpcs).symm
  have hsec := Chazelle.Chain.sideSector (S := (freeIn M.D F)ᶜ) hav hbv hr (by
    zulnp
    apply hxS
    refine ⟨?_, fun ⟨c, hc, hxc⟩ => hballF (lt_of_lt_of_le hx hrF') c hc hxc⟩
    zujuk
    exact hclean x (lt_of_lt_of_le hx hrC') ztdlx hxl)
  obtain ⟨hsub, hpre, hoff⟩ := hsec
  set L := ball z r ∩ {x | sideLeftOf ztltl z ztevm x}
  have hLfree : ztgua := fun x hx => not_not.1 (hsub hx)
  -- the sector meets `U`
  have hmeet : (L ∩ U).Nonempty := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset ztltl z zteb ztckn ∈ L ∧ offset z ztevm s ztckn ∈ L) ∧
        M.Faces p ztwlx U := hoff.and hfU
    obtain ⟨s, hs1, hs2⟩ := h1.exists
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset ztpr ztoa ztwlx ztxlw ∈ U :=
      (tendsto_mul_const_nhdsGT ztmns).eventually hs2
    zubrw
    refine ⟨_, hδ1.2, ?_⟩
    zugwu
    have e : offset z ztevm s δ =
        offset ztpr ztoa ztwlx ztxlw := by
      zvncr; unfold sidePt sideNext
      exact Chazelle.Chain.offset_lerp_left _ _ _ _ _
    grind
  have hLU : ztpkn := Chazelle.Chain.subset_regionsIn_of_inter hU hpre hLfree hmeet
  refine ⟨r, hr, fun x hx hxD => hLU zthne⟩
  have := hleft x (lt_of_lt_of_le hx hrL') ztdlx
  tauto

/-! ## Adding chords inside one region -/
section Local
variable {D : Set Point} {S F : Set (Set Point)} {R : Set Point}
end Local
end
end Loc
namespace DownStep
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn)

/-- Every chord of `T` outside `G` meets the domain only inside a region `R' ≠ R` of `S`. -/
def OutOther (D : Set Point) (S G T : Set ztf) (R : Set Point) : Prop :=
  ∀ c ∈ T, c ∉ G → ∃ R' ∈ regionsIn D S, R' ≠ R ∧ c ∩ D ⊆ R'
variable {D : Set Point} {S G T : Set (Set Point)} {R V : Set Point}
theorem OutOther.mono {H : Set ztf} (h : OutOther D S G T R) (hGH : G ⊆ H) :
    OutOther D S H T R := fun c hc hcH => h c hc fun hcG => hcH (hGH hcG)

/-- **A region inside `R` of the full family is a region of the intermediate family.** -/
theorem region_restrict (hSG : S ⊆ G) (hGT : G ⊆ T) (hR : R ∈ regionsIn D S)
    (hK : OutOther D S G T R) (hV : V ∈ regionsIn D T) (hVR : V ⊆ R) : V ∈ regionsIn D G := by
  zuov
  have hVG : V ⊆ freeIn D G :=
    (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti D hGT)
  set W := connectedComponentIn zttkd v with hW
  have hvW : v ∈ W := mem_connectedComponentIn (hVG hv)
  have hWS : W ⊆ freeIn D S :=
    (connectedComponentIn_subset _ _).trans (Chazelle.Chain.freeIn_anti D hSG)
  have hWR : W ⊆ R := Chazelle.Chain.subset_regionsIn_of_inter hR
    isPreconnected_connectedComponentIn hWS ⟨v, hvW, hVR hv⟩
  have hWT : W ⊆ freeIn D T := fun w hw => by
    have hwG : w ∈ freeIn D G := connectedComponentIn_subset _ _ hw
    refine ⟨hwG.1, ?_⟩
    zuifk
    by_cases hcG : c ∈ G
    · exact hwG.2 ⟨c, hcG, hwc⟩
    · zueaj
      exact (Chazelle.Chain.regionsIn_disjoint_of_ne hR' hR hne).le_bot
        ⟨hsub ⟨hwc, hwG.1⟩, hWR hw⟩
  have hWV : W ⊆ V := by
    rw [Chazelle.Chain.regionsIn_eq_component hV hv]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hvW hWT
  have hVW : V ⊆ W := (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVG
  exact ⟨v, hVG hv, Subset.antisymm hVW hWV⟩

/-- **The chords of the other regions do not touch `V`.** -/
theorem touch_restrict (hsys : ChordSystem D T) (hST : S ⊆ T) (hR : R ∈ regionsIn D S)
    (hK : OutOther D S G T R) (hVR : V ⊆ R) {c : Set Point} (hc : c ∈ T) (hcG : c ∉ G) :
    ¬ TouchesIn D c V := by
  rintro ⟨z, ⟨hzc, hzD⟩, hzV⟩
  zueaj
  have hRo : IsOpen R' := hsys.regionsIn_open hST hR'
  obtain ⟨w, hwR', hwV⟩ := mem_closure_iff.1 hzV R' hRo (hsub ztklu)
  exact (Chazelle.Chain.regionsIn_disjoint_of_ne hR' hR hne).le_bot ⟨hwR', hVR hwV⟩

/-- **The exits of `V` in the full family are its exits in the intermediate family.** -/
theorem exits_restrict (hsys : ChordSystem D T) (hST : S ⊆ T) (hGT : G ⊆ T)
    (hR : R ∈ regionsIn D S) (hK : OutOther D S G T R) (hVR : V ⊆ R) :
    {c | c ∈ T ∧ TouchesIn D c V} = {c | c ∈ G ∧ TouchesIn D c V} := by
  zubcj
  constructor
  · zukoi
    by_contra hcG
    exact touch_restrict hsys hST hR hK hVR hc (fun h => hcG ⟨h, ht⟩) ht
  grind

/-- **The weight of `V` in the full family is its weight in the intermediate family.** -/
theorem weight_restrict {M : Model} (hM : WalkAx M) (hT : T ⊆ M.Adm) (hfin : T.Finite)
    (hSG : S ⊆ G) (hGT : G ⊆ T) (hR : R ∈ M.regions S) (hK : OutOther M.D S G T R)
    (hV : V ∈ M.regions T) (hVR : V ⊆ R) : M.weight T V = M.weight G V := by
  have hloc := Gran.weightLocal hM hT hfin
  have hsys := hM.sys T hT hfin
  have hST : S ⊆ T := hSG.trans hGT
  have key : ∀ K : Set ztf, K.Finite → K ⊆ T \ G →
      M.weight ztsxs V = M.weight G V := by
    intro K hKf
    refine Set.Finite.induction_on
      (motive := fun K _ => K ⊆ T \ G → M.weight ztsxs V = M.weight G V) K hKf ?_ ?_
    · simp
    · intro c K hcK _ ih hsub
      have hcT : c ∈ T := (hsub ztodi).1
      have hcG : c ∉ G := (hsub ztodi).2
      have hKsub : K ⊆ T \ G := fun d hd => hsub ztttg
      set H := G ∪ insert c K with hH
      have hHT : H ⊆ T := union_subset hGT (insert_subset hcT fun d hd => (hKsub hd).1)
      have hHd : H \ {c} = G ∪ K := by
        simp_all
      have hVH : V ∈ M.regions H :=
        region_restrict (hSG.trans subset_union_left) hHT hR (hK.mono subset_union_left) hV hVR
      have hnt : ¬ TouchesIn M.D c V := touch_restrict hsys hST hR hK hVR hcT hcG
      have := hloc H hHT c (Or.inr ztodi) V hVH hnt
      simp_all
  have hTG : T = G ∪ (T \ G) := (union_sdiff_cancel hGT).symm
  rw [hTG]
  exact key _ (hfin.subset sdiff_subset) subset_rfl
end
end DownStep
namespace TourA
@[expose] public section
open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE)
open Chazelle.Geometry (lerp)
variable (C : Chain) (β : Bool)

/-- The start of the tour, reduced. -/
noncomputable def sA : ℕ := C.sideS β % ztbb

/-- **The side-`A` tour index** of chain edge `k`. -/
noncomputable def tourA (k : ℕ) : ℕ := ztcnp % ztbb
variable {C β}
theorem sA_lt : sA C β < 2 * C.m := Nat.mod_lt _ C.two_m_pos
theorem tourA_lt (k : ℕ) : tourA C β k < 2 * C.m := Nat.mod_lt _ C.two_m_pos
variable {k : ℕ}
theorem mod_tourA (hk : k < 2 * C.m) : (C.sideS β + tourA C β k) % ztbb = k := by
  zudpe

  rw [Nat.add_mod, show C.sideS β % ztbb = sA C β from rfl, Nat.mod_mod]
  have e : sA C β + ztcnp % ztbb ≡ k [MOD 2 * C.m] := by
    have h1 : sA C β + ztcnp % ztbb ≡
        sA C β + ztcnp [MOD 2 * C.m] :=
      Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
    have h2 : sA C β + ztcnp = k + 2 * C.m := by_omega
    simp_all
  rw [e, Nat.mod_eq_of_lt hk]
theorem sideIdx_tourA (hk : k < C.m) : C.sideIdx β (tourA C β k) = k := by
  rw [Chain.sideIdx_eq, mod_tourA by_omega]
  zumu
theorem sideIdx_tourA_succ (hk : k < C.m) : C.sideIdx β (tourA C β k + 1) = k + 1 := by
  rw [C.sideIdx_succ, mod_tourA by_omega]
  zuhay
theorem vtx_tourA (hk : k < C.m) :
    (C.sideWalk β).vtx ztdal = C.vertex k := by
  rw [C.sideWalk_vtx_tour β (tourA_lt k).le]
  unfold Chain.sideTour; rw [sideIdx_tourA hk]
theorem vtx_tourA_succ (hk : k < C.m) :
    (C.sideWalk β).vtx ztgqi = C.vertex zts := by
  rw [C.sideWalk_next_tour β ztqxj, C.sideWalk_vtx_tour β ztqxj]
  unfold Chain.sideTour; rw [sideIdx_tourA_succ hk]

/-- **The points of side `A`.** -/
theorem sidePt_tourA (hk : k < C.m) (s : ℝ) :
    sidePt ztft ztdal s = lerp ztib ztwkj s := by
  unfold sidePt; zunyv

/-- **Contiguity of side `A`**: consecutive side-`A` edges are consecutive walk edges, except at
the tour start. -/
theorem tourA_succ (hk : k + 1 < 2 * C.m) (hne : k + 1 ≠ sA C β) :
    tourA C β zts = tourA C β k + 1 := by
  zudpe

  rcases Nat.lt_or_ge k (sA C β) with h | h
  · -- `k < sA`, so `k + 1 < sA`
    have h' : k + 1 < sA C β := lt_of_le_of_ne h hne
    rw [Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt by_omega]; omega
  · rw [show k + 1 + 2 * C.m - sA C β = (k + 1 - sA C β) + 2 * C.m by omega,
      show k + 2 * C.m - sA C β = (k - sA C β) + 2 * C.m by omega,
      Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega,
      Nat.mod_eq_of_lt by_omega]
    omega

/-- The side-`A` tour index is positive away from the tour start. -/
theorem tourA_pos (hk : k < 2 * C.m) (hne : k ≠ sA C β) : 0 < tourA C β k := by
  zubq

  have h0 : tourA C β k = 0 := by_omega
  have := mod_tourA (C := C) (β := β) hk
  rw [h0, add_zero] at this
  tauto

/-- **The left sector at a side-`A` vertex** away from the tour start: the corner of the chain. -/
theorem sideLeft_tourA_vtx (h0 : 0 < k) (hk : k < C.m) (hne : k ≠ sA C β) (x : Point) :
    sideLeft ztft ztdal 0 x ↔
      sideLeftOf ztyhj ztib ztwkj x := by
  have hpos := tourA_pos (C := C) (β := β) (show k < 2 * C.m by omega) hne
  have hsucc : tourA C β k = tourA C β ztie + 1 := by
    have := tourA_succ (C := C) (β := β) (k := k - 1) by_omega by_omega
    grind
  rw [C.sideLeft_tour_inner β hpos ztqxj]
  zueev
  rw [hsucc, Nat.add_sub_cancel, sideIdx_tourA by_omega, ← hsucc, sideIdx_tourA hk,
    sideIdx_tourA_succ hk]

/-- **The left sector inside a side-`A` edge**: the left half-plane of the chain edge. -/
theorem sideLeft_tourA_edge (hP : C.P.Simple) {k : ℕ} (hk : k < C.m) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft ztft ztdal s x ↔
      0 < Chazelle.det ztib ztwkj x := by
  have hne : (C.sideWalk β).vtx ztdal ≠
      (C.sideWalk β).vtx ztgqi := by
    zunyv; exact C.sideVertex_succ_ne hP k
  rw [Chazelle.Chain.sideLeft_edge hne hs, vtx_tourA hk, vtx_tourA_succ hk]

/-- The side-`A` walk edges are counted. -/
theorem counted_tourA (k : ℕ) : (chainModel C).counted ztdal := by
  have := tourA_lt (C := C) (β := β) k
  show 6 ≤ tourA C β k + 6 ∧ tourA C β k + 6 < 2 * C.m + 6
  omega
end
end TourA
namespace TourB
@[expose] public section
open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE)
open Chazelle.Geometry (lerp)
open TourA (sA tourA)
variable (C : Chain) (β : Bool)

/-- **The side-`B` tour index** of chain edge `k`. -/
noncomputable def tourB (k : ℕ) : ℕ := tourA C β (2 * C.m - zts)
variable {C β}
theorem tourB_lt (k : ℕ) : tourB C β k < 2 * C.m := TourA.tourA_lt _
variable {k : ℕ}
theorem sideIdx_tourB (hk : k < C.m) : C.sideIdx β (tourB C β k) = k + 1 := by
  zumvf
  rw [Chain.sideIdx_eq, TourA.mod_tourA by_omega]
  zumu
theorem sideIdx_tourB_succ (hk : k < C.m) : C.sideIdx β (tourB C β k + 1) = k := by
  zumvf
  rw [C.sideIdx_succ, TourA.mod_tourA by_omega]
  zumu
theorem vtx_tourB (hk : k < C.m) :
    (C.sideWalk β).vtx (tourB C β k + 6) = C.vertex zts := by
  rw [C.sideWalk_vtx_tour β (tourB_lt k).le]
  unfold Chain.sideTour; rw [sideIdx_tourB hk]
theorem vtx_tourB_succ (hk : k < C.m) :
    (C.sideWalk β).vtx ((tourB C β k + 6 + 1) % (C.sideWalk β).n) = C.vertex k := by
  rw [C.sideWalk_next_tour β ztwgu, C.sideWalk_vtx_tour β ztwgu]
  unfold Chain.sideTour; rw [sideIdx_tourB_succ hk]

/-- **Contiguity of side `B`**: the pass of edge `k` follows the pass of edge `k + 1`, except at
the tour start. -/
theorem tourB_succ (hk : k + 1 < C.m) (hne : 2 * C.m - zts ≠ sA C β) :
    tourB C β k = tourB C β zts + 1 := by
  zumvf
  have := TourA.tourA_succ (C := C) (β := β) (k := 2 * C.m - ztcnq) by_omega
    by_omega
  grind
end
end TourB
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
inductive SymSrc where
  /-- The vertex whose index is in register `r`. -/
  | vtx (r : ℕ)
  /-- The point of the edge in register `re` at the height of the vertex in register `rh`. -/
  | edge (re rh : ℕ)
  /-- Three registers `r, r + 1, r + 2` in the `SymPtIn` layout. -/
  | regs (r : ℕ)

/-- The instructions loading a source into the slot `t`. -/
def SymSrc.load (t : ℕ) : SymSrc → List Instr
  | .vtx r => [.constN t 0, .copyN ztbx r]
  | .edge re rh => [.constN t 1, .copyN ztbx re, .copyN ztois rh]
  | .regs r => [.copyN t r, .copyN ztbx ztgu, .copyN ztois ztbcu]

/-- The source holds the symbolic point `p` in `c`. -/
def SymSrc.Holds (c : Config) : SymSrc → SymPt → Prop
  | .vtx r, p => p = .vtx ztfgx
  | .edge re rh, p => p = .onEdge ztvjw ztvjx
  | .regs r, p => SymPtIn c r p

/-- The registers read by a source avoid the kernel's registers. -/
def SymSrc.Out : SymSrc → Prop
  | .vtx r => Bk r = false
  | .edge re rh => Bk re = false ∧ Bk rh = false
  | .regs r => Bk r = false ∧ Bk ztgu = false ∧ Bk ztbcu = false

/-- A frame for fewer registers is a frame for more. -/
theorem FrameB.mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ <;>
  · grind
instance (s : SymSrc) : Decidable s.Out := by
  cases s <;> unfold SymSrc.Out <;> infer_instance

/-- **Calling the sign kernel** on three sources with the test `op`. -/
def sgnS (op : ℕ) (s₁ s₂ s₃ : SymSrc) : Stmt :=
  .seq (block (s₁.load 10000)) (.seq (block (s₂.load 10003)) (.seq (block (s₃.load 10006))
    (.seq ztifn signProg)))
theorem wr_load (t : ℕ) (ht : 10000 ≤ t ∧ t + 2 < 10500) (s : SymSrc) :
    wr Bk ztqeb = true := by
  cases s <;> simp [SymSrc.load, block, wr, wrOK, Bk] <;> omega

/-- Two sources agree on configurations that agree on their registers. -/
theorem holds_congr {c c' : Config} {s : SymSrc} {p : SymPt} (hs : s.Out)
    (hc : ∀ r, Bk r = false → c'.nreg r = c.nreg r) (h : s.Holds c p) : s.Holds c' p := by
  cases s with
  | vtx r => simp only [SymSrc.Holds] at h ⊢; rw [hc r hs]; exact h
  | edge re rh =>
    simp only [SymSrc.Holds] at h ⊢; rw [hc re hs.1, hc rh hs.2]; exact h
  | regs r =>
    simp only [SymSrc.Holds] at h ⊢
    cases p with
    | vtx i =>
      zuipe
      rw [hc r hs.1, hc ztgu hs.2.1]; exact h
    | onEdge e h' =>
      zuipe
      rw [hc r hs.1, hc ztgu hs.2.1, hc ztbcu hs.2.2]; exact h

/-- Close a goal about explicit register updates by case analysis. -/
macro "upd_solve" : tactic =>
  `(tactic| (simp only [Machine.upd_apply]; (repeat' split_ifs) <;> first | rfl | omega | simp_all))
variable {P : Polygon} {W : ℕ}
/-- **Loading a source** into the slot `t`. -/
theorem load_exec (t : ℕ) (hW : 1 ≤ W) (s : SymSrc) (c : Config)
    (hw : WordsBounded W c) (hs : s.Out) (hts : ∀ r, Bk r = false → r ≠ t ∧ r ≠ t + 1 ∧ r ≠ t + 2)
    {p : SymPt} (hp : s.Holds c p) :
    ∃ c' k, Exec P W ztqeb c c' k ∧ k ≤ 3 ∧ SymPtIn c' t p ∧
      (∀ r, r ≠ t → r ≠ t + 1 → r ≠ t + 2 → c'.nreg r = c.nreg r) := by
  cases s with
  | vtx r =>
    zufbe
    subst hp
    have h1 := hts r hs
    simp only [SymSrc.load]
    exec_block
    · omega
    · refine ztexu
      · zulal

      simp_all
  | edge re rh =>
    zufbe
    subst hp
    have h1 := hts re hs.1
    have h2 := hts rh hs.2
    simp only [SymSrc.load]
    exec_block
    · omega
    · refine ztexu
      · zulal

      simp_all
  | regs r =>
    zufbe
    have h1 := hts r hs.1
    have h2 := hts ztgu hs.2.1
    have h3 := hts ztbcu hs.2.2
    simp only [SymSrc.load]
    exec_block
    refine ztexu
    · cases p with
      | vtx i =>
        zuipg
        zuict
        refine ⟨?_, ?_⟩ <;> upd_solve
      | onEdge e h =>
        zuipg
        config_simp
        obtain ⟨hp1, hp2, hp3⟩ := hp
        refine ⟨?_, ?_, ?_⟩ <;> upd_solve
    · simp_all
theorem Bk_false_ne {r : ℕ} (h : Bk r = false) (t : ℕ) (ht : 10000 ≤ t ∧ t + 2 < 10500) :
    r ≠ t ∧ r ≠ t + 1 ∧ r ≠ t + 2 := by
  simp only [Bk, decide_eq_false_iff_not, not_and, not_lt] at h
  omega

/-- **The sign kernel on three sources.** -/
theorem sgnS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (op : ℕ)
    (hop : op ≤ 3) (s₁ s₂ s₃ : SymSrc) (c : Config) (hw : WordsBounded W c) (o₁ : s₁.Out)
    (o₂ : s₂.Out) (o₃ : s₃.Out) {p₁ p₂ p₃ : SymPt} (h₁ : s₁.Holds c p₁) (h₂ : s₂.Holds c p₂)
    (h₃ : s₃.Holds c p₃) (l₁ : p₁.Lt P.n) (l₂ : p₂.Lt P.n) (l₃ : p₃.Lt P.n) :
    ∃ c' k, Exec P W (sgnS op s₁ s₂ s₃) c c' k ∧ k ≤ 245 ∧ FrameB Bk c c' ∧
      c'.nreg 10010 ≤ 1 ∧
      (c'.nreg 10010 = 1 ↔ SignTest op (p₁.eval zta) (p₂.eval zta) (p₃.eval zta)) := by
  zudk
  obtain ⟨c₁, k₁, e₁, hk₁, i₁, r₁⟩ := load_exec (P := P) 10000 hW1 s₁ c hw o₁
    (fun r hr => Bk_false_ne hr 10000 by_norm_num) h₁
  have f₁ := exec_frameB e₁ (wr_load 10000 by_norm_num s₁)
  obtain ⟨c₂, k₂, e₂, hk₂, i₂, r₂⟩ := load_exec (P := P) 10003 hW1 s₂ c₁ e₁.wb_right o₂
    (fun r hr => Bk_false_ne hr 10003 by_norm_num) (holds_congr o₂ f₁.1 h₂)
  have f₂ := exec_frameB e₂ (wr_load 10003 by_norm_num s₂)
  obtain ⟨c₃, k₃, e₃, hk₃, i₃, r₃⟩ := load_exec (P := P) 10006 hW1 s₃ c₂ e₂.wb_right o₃
    (fun r hr => Bk_false_ne hr 10006 by_norm_num)
    (holds_congr o₃ (fun r hr => (f₂.1 r hr).trans ztjwt) h₃)
  have f₃ := exec_frameB e₃ (wr_load 10006 by_norm_num s₃)
  have w₄ := WordsBounded.upd_nreg e₃.wb_right ztpdu c₃.pc (r := 10009)
  have e₄ := Exec.constN e₃.wb_right 10009 op (P := P) ztpdu
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 10009 op } with hc₄
  -- the slots survive the later loads
  have keep : ∀ (d : Config) (t : ℕ) (q : SymPt), SymPtIn d t q →
      ∀ d' : Config, (∀ r, r = t ∨ r = t + 1 ∨ r = t + 2 → d'.nreg r = d.nreg r) →
        SymPtIn d' t q := by
    intro d t q hq d' hd
    cases q with
    | vtx i =>
      zuiph
      rw [hd t ztp, hd ztbx ztwiz]; exact hq
    | onEdge e h =>
      zuiph
      rw [hd t ztp, hd ztbx ztwiz, hd ztois ztwrm]
      zuito
  have j₁ : SymPtIn c₄ 10000 p₁ := keep c₁ 10000 p₁ i₁ c₄ fun r hr => by
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ by_omega, r₃ r by_omega by_omega by_omega,
      r₂ r by_omega by_omega by_omega]
  have j₂ : SymPtIn c₄ 10003 p₂ := keep c₂ 10003 p₂ i₂ c₄ fun r hr => by
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ by_omega, r₃ r by_omega by_omega by_omega]
  have j₃ : SymPtIn c₄ 10006 p₃ := keep c₃ 10006 p₃ i₃ c₄ fun r hr => by
    rw [hc₄]; config_simp
    zubc
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ w₄ hG hW
    by_tauto l₁ l₂ l₃ j₁ j₂ j₃
  have op₄ : ztusr := by_rfl
  rw [op₄] at sig₅
  have f₄ : FrameB Bk c₃ c₄ := by
    refine ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    rw [hc₄]; config_simp
    rw [Machine.upd_other _ _ _ (by simp only [Bk, decide_eq_false_iff_not, not_and, not_lt] at hr; omega)]
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (1 + k₅))), .seq e₁ ztbq, by_omega,
    f₁.trans ztmkc, bit₅, sig₅⟩
end
end OracleR
namespace OutTrap
open Chazelle.Visibility
open Chazelle.Geometry (point_ext)
open Chazelle.Mountain (TrapData exists_trapData)
open OutWalk OutNF
@[expose] public section
structure Acc where
  /-- A top chord was seen. -/
  hT : Bool
  /-- A bottom chord was seen. -/
  hB : Bool
  /-- A left end inside the left side edge was seen. -/
  hL : Bool
  /-- A right end inside the right side edge was seen. -/
  hR : Bool
  /-- The top vertex. -/
  vt : ℕ
  /-- The bottom vertex. -/
  vb : ℕ
  /-- The walk edge of the left side edge. -/
  pl : ℕ
  /-- The walk edge of the right side edge. -/
  pr : ℕ

/-- The initial state. -/
def Acc.init : Acc := ⟨false, false, false, false, 0, 0, 0, 0⟩

/-- One chord record. -/
def accStep (b : Bool) (n ri : ℕ) (a : Acc) (c : CRec) : Acc where
  hT := a.hT || decide ztthl
  hB := a.hB || !decide ztthl
  hL := a.hL || !decide (wv b n c.lp = c.h)
  hR := a.hR || !decide (wv b n c.rp = c.h)
  vt := if c.dn = ri then c.h else a.vt
  vb := if c.dn = ri then a.vb else c.h
  pl := if wv b n c.lp = c.h then a.pl else c.lp
  pr := if wv b n c.rp = c.h then a.pr else c.rp

/-- The scan of the exit chords of region `ri`. -/
def accOf (b : Bool) (n : ℕ) (N : NF) (ri : ℕ) : Acc :=
  ((N.region ri).chords.map N.chord).foldl ztbvn Acc.init

/-- Completion of the record. -/
def finish (b : Bool) (n : ℕ) (a : Acc) : Final.TrapRec :=
  let pl := if a.hL then a.pl else if a.hT then wv b n a.vt else nxt n a.pr
  let pr := if a.hR then a.pr else if a.hB then wv b n a.vb else nxt n pl
  ⟨inp b n pl, inp b n pr, if a.hT then a.vt else wv b n (nxt n pr),
    if a.hB then a.vb else wv b n (nxt n pl)⟩

/-- **The trapezoid record of region `ri`.** -/
def trapOf (b : Bool) (n : ℕ) (N : NF) (ri : ℕ) : Final.TrapRec := finish b n (accOf b n N ri)

/-! ## The scan -/
variable (b : Bool)
/-- The flags of the scan. -/
theorem fold_flags (n ri : ℕ) (L : List CRec) (a : Acc) :
    ((L.foldl ztbvn a).hT = true ↔ a.hT = true ∨ ∃ c ∈ L, c.dn = ri) ∧
      ((L.foldl ztbvn a).hB = true ↔ a.hB = true ∨ ∃ c ∈ L, c.dn ≠ ri) ∧
      ((L.foldl ztbvn a).hL = true ↔ a.hL = true ∨ ∃ c ∈ L, wv b n c.lp ≠ c.h) ∧
      ((L.foldl ztbvn a).hR = true ↔ a.hR = true ∨ ∃ c ∈ L, wv b n c.rp ≠ c.h) := by
  induction L generalizing a with
  | nil => simp
  | cons c L ih =>
    zuhpf
    obtain ⟨h1, h2, h3, h4⟩ := ih _
    zudfi
    · zvmwp; simp only [accStep, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · grind
      grind
    · zvmxx; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · grind
      grind
    · zvncq; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · grind
      grind
    · rw [h4]; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · grind
      grind

/-- The values of the scan, when every record satisfies the facts of `chord_facts`. -/
theorem fold_vals (n ri T B pI pJ : ℕ) (L : List CRec)
    (hL : ∀ c ∈ L, (c.dn = ri → c.h = T) ∧ (c.dn ≠ ri → c.h = B) ∧
      (wv b n c.lp ≠ c.h → c.lp = pI) ∧ (wv b n c.rp ≠ c.h → c.rp = pJ))
    (a : Acc) (ha : (a.hT = true → a.vt = T) ∧ (a.hB = true → a.vb = B) ∧
      (a.hL = true → a.pl = pI) ∧ (a.hR = true → a.pr = pJ)) :
    let a' := L.foldl ztbvn a
    (a'.hT = true → a'.vt = T) ∧ (a'.hB = true → a'.vb = B) ∧
      (a'.hL = true → a'.pl = pI) ∧ (a'.hR = true → a'.pr = pJ) := by
  induction L generalizing a with
  | nil => exact ha
  | cons c L ih =>
    zuhpf
    apply ih by_grind
    obtain ⟨h1, h2, h3, h4⟩ := hL c List.mem_cons_self
    zufiq
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp only [accStep, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at h ⊢
    · grind
    · grind
    · grind
    · grind

/-! ## Correctness of the record -/
variable {Q : Polygon} {N : NF} {reg : ℕ → Set Point}

/-- **The computed record of a region is its trapezoid record.** -/
theorem trapOf_eq (H : RegCtx Q N reg) {ri : ℕ} (hr : ri < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg ri) : trapOf ztgl Q.n N ri = Final.trapRecOf D := by
  zuiwv
  zudov
  zumdm
  zumdp
  have hpi := inp_lt (b := revOf Q) hi
  have hpj := inp_lt (b := revOf Q) hj
  have htn := D.top_lt hQ
  have hbn := D.bot_lt hQ
  have hy1 := D.bot_snd hQ
  have hy2 := D.top_snd hQ
  set L := (N.region ri).chords.map N.chord with hL
  have hfacts : ∀ c ∈ L, (c.dn = ri → c.h = D.top) ∧ (c.dn ≠ ri → c.h = D.bot) ∧
      (wv ztgl Q.n c.lp ≠ c.h → c.lp = inp ztgl Q.n D.i) ∧
      (wv ztgl Q.n c.rp ≠ c.h → c.rp = inp ztgl Q.n D.j) := by
    zung
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    zubds
    obtain ⟨f1, f2, f3, f4⟩ := H.facts hr D hD hk
    obtain ⟨hlp, hrp, -⟩ := rec_attach H.nf hkN
    refine ⟨f1, f2, fun h => ?_, fun h => ?_⟩
    · rw [← f3 h, inp_inp hlp]
    · rw [← f4 h, inp_inp hrp]
  obtain ⟨vT, vB, vL, vR⟩ := fold_vals ztgl Q.n ri D.top D.bot ztwpd
    ztwql L hfacts Acc.init by_tauto
  obtain ⟨fT, fB, fL, fR⟩ := fold_flags ztgl Q.n ri L Acc.init
  simp only [show Acc.init.hT = false from rfl, show Acc.init.hB = false from rfl,
    show Acc.init.hL = false from rfl, show Acc.init.hR = false from rfl, Bool.false_eq_true,
    false_or] at fT fB fL fR
  have hacc : accOf _ Q.n N ri = L.foldl (accStep ztgl Q.n ri) Acc.init := rfl
  set a := accOf _ Q.n N ri with ha
  rw [← hacc] at vT vB vL vR fT fB fL fR
  have hmemk : ∀ k ∈ (N.region ri).chords, N.chord k ∈ L := by_grind
  -- the four geometric situations
  have peak : a.hT = false → wv ztgl Q.n ztwpd = D.top ∧
      wv ztgl Q.n ztbami = D.top := by
    zuq
    have hno : ∀ k ∈ (N.region ri).chords, (N.chord k).dn ≠ ri := by_grind
    obtain ⟨e1, e2⟩ := OutGeom.top_empty hQ H.dh D (H.no_top hr D hD hno)
    exact ⟨walk_left_upper hQ D (OutGeom.top_left_upper hQ D e1),
      walk_right_upper hQ D (OutGeom.top_right_upper hQ D e2)⟩
  have valley : a.hB = false → wv ztgl Q.n ztbamh = D.bot ∧
      wv ztgl Q.n ztwql = D.bot := by
    zuq
    have hno : ∀ k ∈ (N.region ri).chords, (N.chord k).dn = ri := fun k hk => by
      grind
    obtain ⟨e1, e2⟩ := OutGeom.bot_empty hQ H.dh D (H.no_bot hr D hD hno)
    exact ⟨walk_left_lower hQ D (OutGeom.bot_left_lower hQ D e1),
      walk_right_lower hQ D (OutGeom.bot_right_lower hQ D e2)⟩
  have noL : a.hL = false → wv ztgl Q.n ztwpd = D.top ∧
      wv ztgl Q.n ztbamh = D.bot := by
    zuq
    have hall : ∀ k ∈ (N.region ri).chords,
        wv ztgl Q.n (N.chord k).lp = (N.chord k).h := fun k hk => by
      grind
    obtain ⟨e1, e2⟩ := H.all_left hr D hD hall
    exact ⟨walk_left_upper hQ D (OutGeom.top_left_upper hQ D by_grind),
      walk_left_lower hQ D (OutGeom.bot_left_lower hQ D by_grind)⟩
  have noR : a.hR = false → wv ztgl Q.n ztbami = D.top ∧
      wv ztgl Q.n ztwql = D.bot := by
    zuq
    have hall : ∀ k ∈ (N.region ri).chords,
        wv ztgl Q.n (N.chord k).rp = (N.chord k).h := fun k hk => by
      grind
    obtain ⟨e1, e2⟩ := H.all_right hr D hD hall
    exact ⟨walk_right_upper hQ D (OutGeom.top_right_upper hQ D by_grind),
      walk_right_lower hQ D (OutGeom.bot_right_lower hQ D by_grind)⟩
  -- not a peak and a valley at once
  have hTB : a.hT = true ∨ a.hB = true := by
    zuho

    zujnj
    obtain ⟨p1, p2⟩ := peak hcon.1
    obtain ⟨v1, v2⟩ := valley hcon.2
    have e1 : inp _ Q.n D.i = nxt Q.n _ :=
      wv_inj hpi ztwav (p1.trans p2.symm)
    have e2 : inp _ Q.n D.j = nxt Q.n _ :=
      wv_inj hpj ztwau (v2.trans v1.symm)
    zvnlz at e1
    unfold nxt at e1
    grind
  have hLR : a.hL = true ∨ a.hR = true := by
    zuho

    zujnj
    have hempty := fun k hk => by
      zubds
      refine H.not_both hkN ?_ ?_
      · grind
      grind
    grind
  -- the walk edge of the left side
  have hpl : (if a.hL then a.pl else if a.hT then wv ztgl Q.n a.vt else nxt Q.n a.pr) =
      inp ztgl Q.n D.i := by
    cases hLa : a.hL
    · cases hTa : a.hT
      · have hRa : a.hR = true := by_grind
        zuma
        rw [vR hRa]
        exact (wv_inj ztwav hpi ((peak hTa).2.trans by_grind))
      · zuhot
        rw [vT hTa, ← (noL hLa).1, wv_wv hpi]
    grind
  have hpr : (if a.hR then a.pr else if a.hB then wv ztgl Q.n a.vb
      else nxt Q.n ztwpd) = inp (revOf Q) Q.n D.j := by
    cases hRa : a.hR
    · cases hBa : a.hB
      · zuma
        exact wv_inj ztwau hpj ((valley hBa).1.trans by_grind)
      · zuhot
        rw [vB hBa, ← (noR hRa).2, wv_wv hpj]
    grind
  simp only [trapOf, finish, ← ha]
  rw [hpl, hpr]
  simp only [Final.trapRecOf, Final.TrapRec.mk.injEq]
  refine ⟨inp_inp hi, inp_inp hj, ?_, ?_⟩
  · grind
  grind

/-- **The records of all regions form a trapezoid table of `Q`.** -/
theorem table_ok (H : RegCtx Q N reg) :
    Final.IsTrapTable Q ((List.range N.nRegions).map (trapOf ztgl Q.n N)) := by
  zuiwv
  have hregQ : ztkoz := fun s hs => by
    rw [← model_regions H.full]; exact H.corr.1 s hs
  set Dof : ∀ s, s ∈ List.range N.nRegions → TrapData Q := fun s hs =>
    Classical.choose (exists_trapData hQ (hregQ s (List.mem_range.1 hs))) with hDof
  have hDspec : ∀ s hs, (Dof s hs).region = reg s := by_grind
  refine ⟨(List.range N.nRegions).pmap Dof ztb, ?_, ?_, fun R => ⟨fun hR => ?_, ?_⟩⟩
  · zumll
    rw [List.pmap_congr_left _ (H₂ := fun _ h => h)
      (fun s hs h1 _ => (trapOf_eq H (List.mem_range.1 hs) _ by_grind).symm)]
    simp
  · zumll
    rw [List.pmap_congr_left _
      (H₂ := fun _ h => h) (fun s _ h1 _ => hDspec s h1), List.pmap_eq_map]
    refine List.Nodup.map_on ztmjz List.nodup_range
    exact H.corr.2.1 x y ztpzs (List.mem_range.1 hy) hxy
  · rw [← model_regions H.full] at hR
    obtain ⟨s, hs, rfl⟩ := H.corr.2.2 R hR
    grind
  grind

/-- **No vertex-to-vertex chords** (distinct heights): the empty vertex-chord table is valid. -/
theorem vtxChordTable_nil (hQ : Q.Simple) (hdh : DistinctHeights Q) :
    Final.IsVtxChordTable Q [] := by
  refine ⟨fun c => ⟨fun h => absurd h List.not_mem_nil, fun ⟨h1, h2, h3, h4⟩ => ?_⟩, List.nodup_nil⟩
  exfalso
  have hy : (Q.vtx c.dst).2 = (Q.vtx c.src).2 := by rw [← h4, chordEnd_snd]
  have hsd : c.dst = c.src := by
    zuisa
  exact chordEnd_ne_vtx hQ h1 h3 by_simp_all

/-- **A region has at most four exit chords** (two at the top vertex, two at the bottom
vertex). -/
theorem chords_length_le (H : RegCtx Q N reg) {ri : ℕ} (hr : ri < N.nRegions) :
    (N.region ri).chords.length ≤ 4 := by
  classical
  zuiwv
  have hregQ : reg ri ∈ regions Q := by rw [← model_regions H.full]; exact H.corr.1 ri hr
  obtain ⟨D, hD⟩ := exists_trapData hQ hregQ
  set f : ℕ → Set Point := fun k => (N.chord k).toSet _ Q with hf
  set T : Finset _ := {chordSet Q D.top 1, chordSet Q D.top (-1), chordSet Q D.bot 1,
    chordSet Q D.bot (-1)} with hT
  have hnd : ((N.region ri).chords.map f).Nodup := by
    refine List.Nodup.map_on ztmjz ((H.regs ri hr).2.1)
    exact H.nf.2.1 x y (((H.regs ri hr).1 x).1 hx).1 (((H.regs ri hr).1 y).1 hy).1 hxy
  have hsub : ((N.region ri).chords.map f).toFinset ⊆ T := by
    zuh
    zuigm
    obtain ⟨k, hk, rfl⟩ := hx
    zubds
    obtain ⟨v, σ, hv, hσ, -, hS, -⟩ := chords_spec hQ (rec_chords H.full hkN)
    have hvh : v = (N.chord k).h := by
      have e : hseg (Q.vtx v).2 ztilp
          ztilo = hseg (Q.vtx (N.chord k).h).2
            ((interiorModel Q).pos Q (N.chord k).lpos).1
            ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
        zugxo
      obtain ⟨e1, -⟩ := Merge.hseg_inj (min_le_max) e
      zuct
      exact H.dh _ _ hv (H.hlt k hkN) hne e1
    obtain ⟨f1, f2, -, -⟩ := H.facts hr D hD hk
    grind
  have hT4 : T.card ≤ 4 := by
    grind
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
  omega
end
end OutTrap
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn)
open Chazelle.Merge (exitsIn potential ConfStep IsSplit)
variable {M : Model}

/-! ## Degrees as exit-chord counts -/

/-! ## Adding chords keeps semigranularity -/

/-- **Adding one admissible chord keeps γ-semigranularity**: the region split by the chord is
replaced by two regions whose arcs lie inside its arcs, and the other regions keep their arcs. -/
theorem semigranular_insert (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) {γ : ℕ}
    (h : M.Semigranular S γ) : M.Semigranular ztrc γ := by
  have hT : insert e S ⊆ M.Adm := insert_subset he hS
  have hTfin : (insert e S).Finite := hfin.insert e
  have hsys := hM.sys _ hT hTfin
  have heT : ztsih := mem_insert e S
  have hsd : insert e S \ {e} = S := insert_sdiff_self_of_notMem heS
  obtain ⟨P, hP, heP⟩ := Merge.exists_region_of_chord hsys ztoiq heT heS
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hsys ztoiq heT heS hP heP
  have hs' : IsSplit M.D ztobo e P R₁ R₂ := by_simp_all
  have hPγ : M.weight ztobo P ≤ γ := by rw [hsd]; tauto
  zucne
  rcases Gran.split_cases heT hs' hU with rfl | rfl | ⟨hU', hUP⟩
  · exact (Gran.weight_le_merged₁ hM hT hTfin heT hs').trans hPγ
  · exact (Gran.weight_le_merged₂ hM hT hTfin heT hs').trans hPγ
  · have h1 : U ≠ R₁ := hs'.ne_of_mem_old hU' hUP
    have h2 : U ≠ R₂ := hs'.symm.ne_of_mem_old hU' hUP
    rw [← Gran.weight_other hM hT hTfin heT hs' hU h1 h2]
    rw [hsd] at hU' ⊢
    tauto

/-- **Adding any finite set of admissible chords keeps γ-semigranularity.** -/
theorem semigranular_mono (hM : WalkAx M) {S T : Set ztf} (hST : S ⊆ T)
    (hT : T ⊆ M.Adm) (hTfin : T.Finite) {γ : ℕ} (h : M.Semigranular S γ) :
    M.Semigranular T γ := by
  suffices key : ∀ k, ∀ S : Set ztf, S ⊆ T → (T \ S).ncard ≤ k →
      M.Semigranular S γ → M.Semigranular T γ from key _ S hST le_rfl h
  zugoi
  induction k with
  | zero =>
    zulmi
    have he : T \ S = ∅ :=
      (ncard_eq_zero ztvug).1 (Nat.le_zero.1 hk)
    zuium
    zvmwk; exact hS
  | succ k ih =>
    zulmi
    by_cases he : (T \ S).Nonempty
    · obtain ⟨e, heT, heS⟩ := he
      have hins : insert e S ⊆ T := insert_subset heT hST
      refine ih ztrc hins ?_ ?_
      · have hsub : T \ insert e S ⊆ (T \ S) \ {e} := by
          grind
        have h1 := ncard_le_ncard hsub ((hTfin.subset sdiff_subset).sdiff)
        have h2 := ncard_sdiff_singleton_add_one (show e ∈ T \ S from ⟨heT, heS⟩)
          ztvug
        omega
      · exact semigranular_insert hM (hST.trans hT) (hTfin.subset hST) (hT heT) heS hS
    · zukxz
      zuium
      simp_all

/-! ## The full map of a good model -/

/-- A vertex chord of a simple polygon is an admissible chord of its interior model. -/
theorem chords_subset_interiorAdm {Q : Polygon} (hQ : Q.Simple) :
    Visibility.chords Q ⊆ (interiorModel Q).Adm := by
  zung
  obtain ⟨i, σ, -, -, -, rfl, hch⟩ := Visibility.chords_spec hQ hc
  refine ⟨_, _, _, ⟨hch.lt, fun h => h.2 hch.left_mem, fun h => h.2 hch.right_mem,
    fun x h1 h2 => hch.open_int x h1 h2⟩, Visibility.chordSet_eq_hseg Q i σ⟩

/-- **The full map of a good model is admissible.** -/
theorem full_subset_adm (hG : GoodModel M) : M.Full ⊆ M.Adm := by
  zudfb
  · exact Merge.chords_subset_augChords C
  · exact chords_subset_interiorAdm hQ

/-- **The full map of a good model is finite.** -/
theorem full_finite (hG : GoodModel M) : M.Full.Finite := by
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact C.chords_finite
  · exact Visibility.chords_finite Q

/-- For a finite admissible `S`, the augmented full map `M.Full ∪ S` is a chord system. -/
theorem fullSystem (hG : GoodModel M) {S : Set ztf} (hS : S ⊆ M.Adm) (hfin : S.Finite) :
    ChordSystem M.D (M.Full ∪ S) :=
  (walkAx_of_goodModel hG).sys _ (union_subset (full_subset_adm hG) hS)
    ((full_finite hG).union hfin)

/-! ## Good splitting steps -/

/-- **The chord `e` splits the region `R` of `S` well**: `e` is a new chord whose open part lies
in `R`, and each of the two regions of `insert e S` inside `R` is touched by at least two exit
chords of `R` (in the paper's words, `e` joins two nonconsecutive arcs of `R`). -/
def SplitsWell (M : Model) (S : Set ztf) (R e : Set Point) : Prop :=
  e ∉ S ∧ e ∩ M.D ⊆ R ∧ ∀ P ∈ regionsIn M.D ztrc, P ⊆ R → 2 ≤ (exitsIn M.D S P).ncard

/-- **Lemma 3.3 for good models.**  If a region `R` of the chord family `S` has more than `D`
exit chords while the augmented full maps have degree `≤ D`, then a chord of the full map splits
`R` well. -/
theorem exists_step (hG : GoodModel M) {Q : Polygon} {D : ℕ} (hfull : M.FullDegLe Q D)
    {S : Set ztf} (hS : M.ChordFamily Q S) {R : Set Point} (hR : R ∈ regionsIn M.D S)
    (hdeg : D < (exitsIn M.D S R).ncard) : ∃ e ∈ M.Full, SplitsWell M S R e := by
  obtain ⟨e, he, heS, heR, hsplit⟩ := Merge.lemma_3_3 (fullSystem hG hS.2.1 hS.1)
    subset_union_right hR (fun U hU _ => hfull S hS U hU) hdeg
  exact ⟨e, he.resolve_right heS, heS, heR, hsplit⟩

/-- **The two halves of a good split** have at least `3` and fewer than `deg R` exit chords. -/
theorem splitsWell_degrees (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) (hw : SplitsWell M S R e) :
    ∀ P ∈ regionsIn M.D ztrc, P ⊆ R →
      3 ≤ (exitsIn M.D ztrc P).ncard ∧
        (exitsIn M.D ztrc P).ncard < (exitsIn M.D S R).ncard := by
  obtain ⟨heS, heR, hsplit⟩ := hw
  zuivy
  have hSF : S ⊆ insert e S := subset_insert e S
  have heF : ztsih := mem_insert e S
  zujas
  obtain ⟨R₁, R₂, h⟩ := Merge.exists_split hF hSF heF heS hR heR
  have e0 := h.ncard_exits hF hSF heF heS ztqxc
  have e1 := h.exits_insert₁ hF hSF heF heS
  have e2 := h.exits_insert₂ hF hSF heF heS
  have b1 := hsplit R₁ h.mem₁ h.sub₁
  have b2 := hsplit R₂ h.mem₂ h.sub₂
  zugrp

/-! ## Runs of good steps (Lemma 3.4) -/
open Metric
open Chazelle.Chain (SideAttach SideSectorIn sideInArc sidePt sideLeft freeIn regionsIn_subset regionsIn_isPreconnected regionsIn_nonempty)
open Chazelle.Geometry (lerp)
def sideExits (M : Model) (S : Set ztf) (R : Set Point) (k₁ k₂ : ℝ) : Set ztf :=
  {c | c ∈ exitsIn M.D S R ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc k₁ k₂ ztk}
theorem sideExits_subset (S : Set ztf) (R : Set Point) (k₁ k₂ : ℝ) :
    sideExits M S R k₁ k₂ ⊆ exitsIn M.D S R := fun _ h => h.1

/-- Points of a segment close to its start. -/
theorem exists_lerp_near {a b : Point} (hab : a ≠ b) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ lerp a b s ≠ a ∧ dist ztlqt a < ρ := by
  have hd := dist_pos.2 hab.symm
  set s := min ztcn (ρ / ztjff) with hs
  zucmo
  have hs1 : ztdrm := lt_of_le_of_lt ztff by_norm_num
  have hdist : dist ztlqt a = s * dist b a := by
    rw [Geometry.lerp_eq_add_smul, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs0, dist_eq_norm]
  refine ⟨s, hs0, hs1, ?_, ?_⟩
  · zuq
    have h' : dist ztlqt a = 0 := by_simp_all
    grind
  · rw [hdist]
    have : s ≤ ρ / ztjff := by_simp_all
    calc s * dist b a ≤ ρ / ztjff * dist b a :=
          mul_le_mul_of_nonneg_right this hd.le
      _ = ρ / 2 := by field_simp
      _ < ρ := by_linarith

/-- **An attached admissible chord enters the left sector**: for every set `K` containing the
small left sector at the attachment, the chord has a point in the domain lying in `K`. -/
theorem exists_near_attach (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {K : Set Point} (hK : SideSectorIn M.W K p t) :
    ∃ x ∈ c ∩ M.D, x ∈ K := by
  obtain ⟨a, b, hab, rfl, -, hopen, -, -⟩ := hM.ends c hc
  zucgh
  obtain ⟨hp, ht, ht1, hmem, r, hr, hsec⟩ := hA
  obtain ⟨r', hr', hK⟩ := hK
  have hend := hM.attach_endpoint hopen hA'
  -- a point of the open part near the attachment point
  have key : ∀ u v : Point, u ≠ v → (∀ s ∈ Ioo (0 : ℝ) 1, lerp u v s ∈ M.D) →
      Chazelle.segment u v = Chazelle.segment a b → sidePt M.W p t = u →
      ∃ x ∈ Chazelle.segment a b ∩ M.D, x ∈ K := by
    intro u v huv hop hseg hpt
    obtain ⟨s, hs0, hs1, hne, hd⟩ := exists_lerp_near huv zttsr
    have hxs : lerp u v s ∈ Chazelle.segment a b := by
      zufow
    have hxD : lerp u v s ∈ M.D := by_grind
    refine ⟨_, ⟨hxs, hxD⟩, hK _ ?_ ?_⟩
    · rw [mem_ball, hpt]; grind
    grind
  rcases hend with h | h
  · grind
  · exact key b a hab.symm ztjnr ztfnp h

/-- **A touched connected set lies on the side of the chord.**  If `c ≠ e` are chords of a chord
system, `x` is a point of `c` in the domain lying in the component `K` of `D \ e`, and the
preconnected set `U ⊆ D \ e` is touched by `c`, then `U ⊆ K`. -/
theorem subset_component_of_touches (hD : IsOpen M.D) {F : Set ztf}
    (hF : ChordSystem M.D F) {c e : Set Point} (hc : c ∈ F) (he : e ∈ F) (hce : c ≠ e)
    {x c₀ : Point} (hx : x ∈ c ∩ M.D) (hxK : x ∈ connectedComponentIn ztbto c₀)
    {U : Set Point} (hU : U ⊆ M.D \ e) (hUc : IsPreconnected U) (ht : TouchesIn M.D c U) :
    U ⊆ connectedComponentIn ztbto c₀ := by
  have hK := connectedComponentIn_eq hxK
  have hcD : c ∩ M.D ⊆ M.D \ e := fun z hz =>
    ⟨hz.2, fun hze => hF.inter_subset_compl hc he hce by_simp_all hz.2⟩
  have hcK : c ∩ M.D ⊆ connectedComponentIn ztbto c₀ := by
    zummo
    exact (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hx hcD
  have hopen : IsOpen (connectedComponentIn _ c₀) :=
    (hD.sdiff (hF.isClosed_chord he)).connectedComponentIn
  obtain ⟨z, hz, hzU⟩ := ht
  obtain ⟨u, huK, huU⟩ := mem_closure_iff.1 hzU _ hopen (hcK hz)
  rw [connectedComponentIn_eq huK]
  exact hUc.subset_connectedComponentIn huU hU

/-- Two distinct components of one set are disjoint. -/
theorem components_disjoint {A : Set Point} {c₁ c₂ : Point}
    (hne : connectedComponentIn A c₁ ≠ connectedComponentIn A c₂) :
    Disjoint (connectedComponentIn A c₁) (connectedComponentIn A c₂) := by
  zugua
  zuchi
  exact hne ((connectedComponentIn_eq h1).trans (connectedComponentIn_eq h2).symm)
theorem pair_cases {X u v a b : Set Point} (hx : X = u ∨ X = v) (ha : a = u ∨ a = v)
    (hb : b = u ∨ b = v) (hab : a ≠ b) : X = a ∨ X = b := by
  grind

/-- **The link lemma.**  Let `R` be a region of the finite admissible family `S`, and `e ∉ S` an
admissible chord with open part in `R`, attached at two positions with distinct points and keys
`ka`, `kb`.  If at least two exit chords of `R` are attached strictly between `ka` and `kb`, and
at least two strictly between `kb` and `ka`, then `e` splits `R` well. -/
theorem splitsWell_of_sideExits (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (h1 : 2 ≤ (sideExits M S R ztbf ztbd).ncard)
    (h2 : 2 ≤ (sideExits M S R ztbd ztbf).ncard) : SplitsWell M S R e := by
  refine ⟨heS, heR, ?_⟩
  zusa

  zubjh
  zuljy
  -- the halves are connected subsets of `D \ e`
  have hsub : ztkns := fun Q hQ z hz =>
    ⟨(regionsIn_subset hQ hz).1, fun hze => (regionsIn_subset hQ hz).2 by_simp_all⟩
  have hfinS : ztjba := fun Q =>
    hfin.subset zttag
  -- an exit chord attached on a side touches a half, which lies in that side's component
  have side : ∀ (c₀ : Point) (k₁ k₂ : ℝ),
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc k₁ k₂ ztk →
        SideSectorIn M.W ztyqg p t) →
      ∀ c ∈ sideExits M S R k₁ k₂, ztlfr ∧
        ∀ Q ∈ regionsIn M.D F, TouchesIn M.D c Q → Q ⊆ connectedComponentIn ztbto c₀ := by
    intro c₀ k₁ k₂ hsec c hc
    obtain ⟨⟨hcS, hcR⟩, p, t, hat, hin⟩ := hc
    zukbk
    refine ⟨?_, fun Q hQ hcQ => ?_⟩
    · have hmem : c ∈ exitsIn M.D S R := ⟨hcS, hcR⟩
      rw [hs.exits_eq_union hF hSF heF heS ztqxc] at hmem
      zucov
      · exact Or.inl h.2
      · exact Or.inr h.2
    · obtain ⟨hp, ht0, ht1, -⟩ := id hat
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM ztmkv hat ztobf
      exact subset_component_of_touches hM.isOpen hF ztqpp heF hce hx hxK by_simp_all
        ztqvp hcQ
  have hs1 := side c₁ _ _ hsec₁
  have hs2 := side c₂ _ _ hsec₂
  -- pick one exit chord on each side
  have hne1 : (sideExits M S R ztbf ztbd).Nonempty :=
    nonempty_of_ncard_ne_zero by_omega
  have hne2 : (sideExits M S R ztbd ztbf).Nonempty :=
    nonempty_of_ncard_ne_zero by_omega
  obtain ⟨d₁, hd₁⟩ := hne1
  obtain ⟨d₂, hd₂⟩ := hne2
  have hR12 : ∀ Q, Q = R₁ ∨ Q = R₂ → Q ∈ regionsIn M.D F := by
    rintro Q (rfl | rfl)
    · exact hs.mem₁
    · exact hs.mem₂
  -- the half touched by `d₁` lies in `K₁`, the one touched by `d₂` in `K₂`
  obtain ⟨Ra, hRa, hRaK⟩ : ∃ Ra, (Ra = R₁ ∨ Ra = R₂) ∧ TouchesIn M.D d₁ Ra := by
    grind
  obtain ⟨Rb, hRb, hRbK⟩ : ∃ Rb, (Rb = R₁ ∨ Rb = R₂) ∧ TouchesIn M.D d₂ Rb := by
    grind
  have hRa1 := (hs1 d₁ hd₁).2 Ra by_grind hRaK
  have hRb2 := (hs2 d₂ hd₂).2 Rb by_grind hRbK
  have notBoth : ∀ Q ∈ regionsIn M.D F, Q ⊆ connectedComponentIn ztbto c₁ →
      Q ⊆ connectedComponentIn ztbto c₂ → False := by
    intro Q hQ h₁ h₂
    zuhid
    exact hdisj.notMem_of_mem_left (h₁ hz) (h₂ hz)
  have hab : Ra ≠ Rb := by
    zunq
    exact notBoth Ra by_grind hRa1 hRb2
  zujas
  have hP12 := hs.eq_of_subset hP hPR
  have gen : ∀ (c₀ c₀' : Point) (k₁ k₂ : ℝ) (Rx Ry : Set Point),
      (∀ c ∈ sideExits M S R k₁ k₂, ztlfr ∧
        ∀ Q ∈ regionsIn M.D F, TouchesIn M.D c Q → Q ⊆ connectedComponentIn ztbto c₀) →
      (Ry = R₁ ∨ Ry = R₂) → Ry ⊆ connectedComponentIn ztbto c₀' →
      Disjoint ztyqg (connectedComponentIn ztbto c₀') →
      (∀ Q, ztnnx → Q = Rx ∨ Q = Ry) →
      2 ≤ (sideExits M S R k₁ k₂).ncard → 2 ≤ (exitsIn M.D S Rx).ncard := by
    intro c₀ c₀' k₁ k₂ Rx Ry hside hRy hRyK hdis hcases hcount
    refine hcount.trans (ncard_le_ncard (fun c hc => ⟨(hside c hc).1.elim
      ztrps ztrps, ?_⟩) (hfinS Rx))
    have hQ : ∀ Q, ztnnx → TouchesIn M.D c Q → Q = Rx := by
      intro Q hQ12 hcQ
      rcases hcases Q hQ12 with h | h
      · zubh
      · exfalso
        have hQK := (hside c hc).2 Q zttms hcQ
        obtain ⟨z, hz⟩ := regionsIn_nonempty zttms
        zvmwc at hz hQK
        exact hdis.notMem_of_mem_left ztvto (hRyK hz)
    rcases (hside c hc).1 with h | h
    · rw [← hQ R₁ ztp h]; exact h
    · rw [← hQ R₂ ztbt h]; exact h
  rcases pair_cases hP12 hRa hRb hab with rfl | rfl
  · exact gen c₁ c₂ _ _ P Rb hs1 hRb hRb2 hdisj
      (fun Q hQ => pair_cases hQ hRa hRb hab) h1
  · exact gen c₂ c₁ _ _ P Ra hs2 hRa hRa1 hdisj.symm
      (fun Q hQ => (pair_cases hQ hRa hRb hab).symm) h2
open Chazelle.Machine (Stmt)
def NFRegs (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  RegionCorr M Q N reg ∧ ChordSidesOK M Q N reg ∧ ArcsOK M Q N reg ∧ RegionsOK M Q N reg

/-- **The contract of a splitting step.** -/
def FindOK (s : Stmt) (κ : ℕ → ℕ) (F G H : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (Bo : Finset ℕ) : Prop :=
  Meets s zttys
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem ztjsd ztm ∧
      c.nreg 81003 ≤ X.cap P c.nmem ztjsd ∧
      ModelDescWF P ztm c.nmem ztbzs ∧
      (c.nmem ztbzs = 0 → ∀ H C, ChainDescAt c.nmem zthuy zta H C →
        HostRegular (Qof P).n H) ∧
      (c.nmem ztbzs = 0 → ∀ H C, ChainDescAt c.nmem zthuy zta H C →
        C.P.Simple) ∧
      ∃ M N, ModelDescAt c.nmem ztbzs zta M ∧ GoodModel M ∧ Ok P M ∧
        NFWithin c.nmem ztqib ztm N ∧ IsNF M zta N ∧
        M.DegLe ztwiv ztghi ∧
        M.Semigranular ztwiv ztbol ∧ c.nreg 81002 < N.nRegions)
    (fun P c c' => (∀ q, bandOf q = bRestore → q < 81000 → c'.nreg q = c.nreg q) ∧
      c'.nreg 81007 ≤ 1 ∧
      ∀ M N reg, ModelDescAt c.nmem ztbzs zta M → NFAt c.nmem ztqib N →
        IsNF M zta N → NFRegs M zta N reg →
        (c'.nreg 81007 = 1 →
          (recOf ztdzg).Attached M zta ∧
          c'.nreg 81008 < (Qof P).n ∧
          (recOf ztdzg).toSet M zta ∈ M.Adm ∧
          SplitsWell M ztwiv ztqvk
            ((recOf ztdzg).toSet M zta)) ∧
        (M.FullDegLe zta (c.nreg 81006) →
          c.nreg 81006 < M.deg ztwiv ztqvk → c'.nreg 81007 = 1))
    (fun _ c => κ ztghi * F ztbol * G ztbol *
      ztwwz)

/-- **The splitting step exists** for all oracles (the procedure is built from the oracle
statements, like `RestoreSpec`'s), for chain models of `OkModel` and for the interior model of
`Q` (finding E7-B: the down phase restores conformality in the interior model). -/
def FindSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    ∀ Bo : Finset ℕ, oracleBands ⊆ Bo → bRestore ∉ Bo →
    X.CapLocal → X.Halves → (∀ P M, Ok P M → OkModel P M ∨ M = interiorModel zta) →
    Bs ⊆ Bo → Bc ⊆ Bo →
    ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    FindOK ztdvk κ F G H X Ok Bo
