module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranRamMu

/-!
# WP-F, RAM part 3: the joined-gap weights on the RAM

* `Cst c E d`: the constant registers of the worklist loop (band `bGran`);
* `gwStmt`: `r92 := gwt sz eg pz r90 r91`;
* `ddStmt`: `r89 := [r88 dies]` from the positions `n1 = r68`, `n2 = r69` of the chord and their
  death bits `r72`, `r73`;
* `jwStmt`: `r85 := jw` for the position `r86` with death bit `r87`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- **The constant registers of the worklist loop.** -/
structure Cst (c : Config) (E : Env) (d : Dm) : Prop where
  γ : c.nreg 90014 = E.γ
  sz : c.nreg 90018 = E.sz
  one : c.nreg 90019 = 1
  three : c.nreg 90020 = 3
  two : c.nreg 90021 = 2
  bLive : c.nreg 90030 = d.b0
  bS0 : c.nreg 90031 = d.b0 + d.oS0
  bS1 : c.nreg 90032 = d.b0 + d.oS1
  bNd0 : c.nreg 90033 = d.b0 + d.oNd0
  bNd1 : c.nreg 90034 = d.b0 + d.oNd1
  bDeg : c.nreg 90035 = d.b0 + d.oDeg
  bWt : c.nreg 90036 = d.b0 + d.oWt
  bExb : c.nreg 90037 = d.b0 + d.oExb
  bCnt : c.nreg 90038 = d.b0 + d.oCnt
  bNxt : c.nreg 90039 = d.b0 + d.oNxt
  bPrv : c.nreg 90040 = d.b0 + d.oPrv
  bEg : c.nreg 90041 = d.b0 + d.oEg
  bPz : c.nreg 90042 = d.b0 + d.oPz
  bStk : c.nreg 90043 = d.b0 + d.oStk
  bTmp : c.nreg 90044 = d.b0 + d.oTmp

/-- The constant registers survive any statement writing only registers of `B` avoiding
`90000 … 90059`. -/
theorem Cst.frame {c c' : Config} {E : Env} {d : Dm} (h : Cst c E d)
    (hr : ∀ r, r < 90045 → 90000 ≤ r → c'.nreg r = c.nreg r) : Cst c' E d := by
  core_grind

/-! ## The weight of a gap -/

/-- `r92 := gwt sz eg pz r90 r91`. -/
def gwStmt : Stmt :=
  .seq (block [.addN 90093 90041 90090, .loadN 90094 90093, .addN 90093 90041 90091,
      .loadN 90095 90093, .addN 90093 90042 90091, .loadN 90096 90093, .addN 90097 90095 90096])
    (.ifLtN 90090 90091 (.instr (.subN 90092 90097 90094))
      (.ifLtN 90091 90090
        (.seq (.instr (.subN 90098 90018 90094))
          (.seq (.ifLtN 90097 90094 (.instr (.copyN 90099 90097)) (.instr (.copyN 90099 90094)))
            (.instr (.addN 90092 90098 90099))))
        (.instr (.copyN 90092 90018))))

/-- Registers in `[a, b)`. -/
def Bin (a b r : ℕ) : Bool := decide (a ≤ r ∧ r < b)

theorem wr_gwStmt : wr (Bin 90092 90100) gwStmt = true := by decide

/-- **The weight of a gap between two positions.** -/
theorem gwStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} (c : Config)
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d st)
    (ha : c.nreg 90090 < d.A) (hb : c.nreg 90091 < d.A)
    (hbx : st.eg (c.nreg 90091) + st.pz (c.nreg 90091) ≤ E.sz) (hszW : E.sz ≤ W)
    (hbase : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W gwStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90092 = gwt E.sz st.eg st.pz (c.nreg 90090) (c.nreg 90091) ∧
      FrameB (Bin 90092 90100) c c' := by
  suffices h : ∃ c' k, Exec P W gwStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90092 = gwt E.sz st.eg st.pz (c.nreg 90090) (c.nreg 90091) by
    obtain ⟨c', k, e, hk, hr⟩ := h
    exact ⟨c', k, e, hk, hr, exec_frameB e wr_gwStmt⟩
  set a := c.nreg 90090
  set b := c.nreg 90091
  have ra := henc.eg a ha
  have rb := henc.eg b hb
  have rx := henc.pz b hb
  have hEg := hC.bEg
  have hPz := hC.bPz
  have hsz := hC.sz
  unfold gwStmt
  refine spec_seq ?_
  exec_block
  · rw [hEg]; dm_simp; omega
  · config_simp; rw [hEg]; dm_simp; omega
  · config_simp; rw [hPz]; dm_simp; omega
  · config_simp; grind
  -- after the loads
  
  unfold gwt
  by_cases hab : a < b
  · refine spec_ifLtN_true (by config_simp; exact hab)
      (spec_instr (Exec.subN ‹_› _ _ _) fun _ => ⟨by omega, ?_⟩)
    config_simp
    grind
  · refine spec_ifLtN_false (by config_simp; exact hab) ?_
    by_cases hba : b < a
    · refine spec_ifLtN_true (by config_simp; exact hba) ?_
      refine spec_seq (spec_instr (Exec.subN ‹_› _ _ _) fun hw₁ => ?_)
      have hmin : ∀ (c₁ : Config), WordsBounded W c₁ → c₁.nreg 90099 =
          min (st.eg b + st.pz b) (st.eg a) → c₁.nreg 90098 = E.sz - st.eg a →
          ∃ c' k, Exec P W (.instr (.addN 90092 90098 90099)) c₁ c' k ∧ k = 1 ∧
            c'.nreg 90092 = (E.sz - st.eg a) + min (st.eg b + st.pz b) (st.eg a) := by
        intro c₁ hw₁ h99 h98
        refine ⟨_, 1, Exec.addN hw₁ _ _ _ (by omega), rfl, ?_⟩
        config_simp; omega
      by_cases hm : st.eg b + st.pz b < st.eg a
      · have e1 := Exec.copyN (P := P) hw₁ 90099 90097
        obtain ⟨c', k₂, e2, hk₂, hr⟩ := hmin _ e1.wb_right
          (by config_simp; grind)
          (by config_simp; grind)
        refine ⟨c', _, .seq (Exec.ifLtN_true (by ram_simp )
          e1) e2, by omega, ?_⟩
        grind
      · have e1 := Exec.copyN (P := P) hw₁ 90099 90094
        obtain ⟨c', k₂, e2, hk₂, hr⟩ := hmin _ e1.wb_right
          (by config_simp; rw [hEg, ra, min_eq_right (by omega)])
          (by config_simp; grind)
        refine ⟨c', _, .seq (Exec.ifLtN_false (by ram_simp )
          e1) e2, by omega, ?_⟩
        grind
    · refine spec_ifLtN_false (by config_simp; exact hba)
        (spec_instr (Exec.copyN ‹_› _ _) fun _ => ⟨by omega, ?_⟩)
      config_simp
      grind

/-! ## The death test -/

/-- `r89 := [r88 = r68 ∧ r72 = 1] ∨ [r88 = r69 ∧ r73 = 1]`. -/
def ddStmt : Stmt :=
  .seq (.instr (.constN 90089 0))
    (.seq (.ifLtN 90088 90068 .skip (.ifLtN 90068 90088 .skip
        (.ifLtN 90072 90019 .skip (.instr (.constN 90089 1)))))
      (.ifLtN 90088 90069 .skip (.ifLtN 90069 90088 .skip
        (.ifLtN 90073 90019 .skip (.instr (.constN 90089 1))))))

theorem wr_ddStmt : wr (Bin 90089 90090) ddStmt = true := by decide

section
variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
include hw hW
/-- One test of `ddStmt`. -/
theorem ddOne_exec
    {rj rn rb : ℕ} {b : Bool} (h19 : c.nreg 90019 = 1) (hb : c.nreg rb = bit b)
    (_hv : c.nreg 90089 ≤ 1) :
    ∃ c' k, Exec P W (.ifLtN rj rn .skip (.ifLtN rn rj .skip
        (.ifLtN rb 90019 .skip (.instr (.constN 90089 1))))) c c' k ∧ k ≤ 7 ∧
      c'.nreg 90089 = (if c.nreg rj = c.nreg rn ∧ b = true then 1 else c.nreg 90089) ∧
      ∀ r, r ≠ 90089 → c'.nreg r = c.nreg r := by
  by_cases h1 : c.nreg rj < c.nreg rn
  · exact ⟨c, _, .ifLtN_true h1 (.skip hw), by omega, by grind,
      fun _ _ => rfl⟩
  by_cases h2 : c.nreg rn < c.nreg rj
  · exact ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw)), by omega,
      by grind, fun _ _ => rfl⟩
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true (by aesop)
      (.skip hw))), by omega, by simp, fun _ _ => rfl⟩
  | true =>
    refine ⟨_, _, .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false (by rw [hb, h19]; decide)
      (Exec.constN hw 90089 1 hW))), by omega, ?_, fun r hr => by simp_all⟩
    aesop (add safe (by omega))

/-- **The death test.** -/
theorem ddStmt_exec
    {b1 b2 : Bool} (h19 : c.nreg 90019 = 1) (h72 : c.nreg 90072 = bit b1)
    (h73 : c.nreg 90073 = bit b2) :
    ∃ c' k, Exec P W ddStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90089 = bit ((decide (c.nreg 90088 = c.nreg 90068) && b1) ||
        (decide (c.nreg 90088 = c.nreg 90069) && b2)) ∧ FrameB (Bin 90089 90090) c c' := by
  suffices h : ∃ c' k, Exec P W ddStmt c c' k ∧ k ≤ 20 ∧
      c'.nreg 90089 = bit ((decide (c.nreg 90088 = c.nreg 90068) && b1) ||
        (decide (c.nreg 90088 = c.nreg 90069) && b2)) by
    obtain ⟨c', k, e, hk, hr⟩ := h
    exact ⟨c', k, e, hk, hr, exec_frameB e wr_ddStmt⟩
  have e0 := Exec.constN (P := P) hw 90089 0 (by omega)
  set c₀ := { c with nreg := upd c.nreg 90089 0 }
  obtain ⟨c₁, k₁, e₁, hk₁, h₁, f₁⟩ := ddOne_exec (P := P) (rj := 90088) (rn := 90068) (rb := 90072)
    c₀ e0.wb_right hW (b := b1) (by ram_simp ) (by ram_simp )
    (by aesop)
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, f₂⟩ := ddOne_exec (P := P) (rj := 90088) (rn := 90069) (rb := 90073)
    c₁ e₁.wb_right hW (b := b2) (by ram_simp )
    (by ram_simp ) (by rw [h₁]; split_ifs <;> aesop)
  refine ⟨c₂, _, .seq e0 (.seq e₁ e₂), by omega, ?_⟩
  rw [h₂, h₁, f₁ _ (by decide), f₁ _ (by decide)]
  simp only [c₀, upd, ite_eq_right (show (90088 : ℕ) ≠ 90089 by decide),
    ite_eq_right (show (90068 : ℕ) ≠ 90089 by decide), ite_eq_right (show (90069 : ℕ) ≠ 90089 by decide)]
  grind [bit]

/-! ## The weight of the gap around a dying position -/


end

theorem Bin_false {a b r : ℕ} (h : r < a ∨ b ≤ r) : Bin a b r = false := by
  core_grind

/-- The skip-or-load step of `jwStmt`. -/
theorem skipLoad_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {rb rp : ℕ}
    {b : Bool} (h19 : c.nreg 90019 = 1) (h89 : c.nreg 90089 = bit b)
    (hW : b = true → c.nreg rb + c.nreg rp ≤ W) (_h80 : rb ≠ 90080) (_h19' : rb ≠ 90019)
    (_hp80 : rp ≠ 90080) (_hp89 : rp ≠ 90089) :
    ∃ c' k, Exec P W (.ifLtN 90089 90019 .skip (block [.addN 90080 rb rp, .loadN rp 90080]))
      c c' k ∧ k ≤ 4 ∧
      c'.nreg rp = (if b then c.nmem (c.nreg rb + c.nreg rp) else c.nreg rp) ∧
      (∀ r, r ≠ 90080 → r ≠ rp → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_true (by aesop) (.skip hw), by omega, by simp,
      fun _ _ _ => rfl, rfl⟩
  | true =>
    refine spec_ifLtN_false (by rw [h89, h19]; decide) ?_
    exec_block
    all_goals simp_all

/-- `r85 := jw` for the position `r86` with death bit `r87`. -/
def jwStmt : Stmt :=
  .ifLtN 90087 90019 (.instr (.constN 90085 0))
    (.seq (block [.addN 90080 90040 90086, .loadN 90081 90080, .copyN 90088 90081])
      (.seq ddStmt
        (.seq (.ifLtN 90089 90019 .skip (block [.addN 90080 90040 90081, .loadN 90081 90080]))
          (.seq (block [.addN 90080 90039 90086, .loadN 90082 90080, .copyN 90088 90082])
            (.seq ddStmt
              (.seq (.ifLtN 90089 90019 .skip (block [.addN 90080 90039 90082, .loadN 90082 90080]))
                (.seq (block [.copyN 90090 90081, .copyN 90091 90082])
                  (.seq gwStmt (.instr (.copyN 90085 90092))))))))))

theorem wr_jwStmt : wr (Bin 90080 90100) jwStmt = true := by decide

/-- **The weight of the gap around a dying position** (`St.jw`). -/
theorem jwStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {st : St} (c : Config)
    (hw : WordsBounded W c) (hW1 : 1 ≤ W) (hC : Cst c E d) (henc : Enc c.nmem d st) {cc k : ℕ}
    (h86 : c.nreg 90086 = k) (h87 : c.nreg 90087 = bit (decide (st.cnt k = 1)))
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit (decide (st.cnt (st.nd0 cc) = 1)))
    (h73 : c.nreg 90073 = bit (decide (st.cnt (st.nd1 cc) = 1)))
    (hk : k < d.A) (hkL : 0 < st.cnt k)
    (hring : ∀ j, j < d.A → 0 < st.cnt j → st.prv j < d.A ∧ 0 < st.cnt (st.prv j) ∧
      st.nxt j < d.A ∧ 0 < st.cnt (st.nxt j))
    (hbx : ∀ j, j < d.A → st.eg j + st.pz j ≤ E.sz) (hszW : E.sz ≤ W)
    (hbase : d.b0 + d.oEnd ≤ W) :
    ∃ c' k', Exec P W jwStmt c c' k' ∧ k' ≤ 100 ∧ c'.nreg 90085 = st.jw E cc k ∧
      FrameB (Bin 90080 90100) c c' := by
  suffices h : ∃ c' k', Exec P W jwStmt c c' k' ∧ k' ≤ 100 ∧ c'.nreg 90085 = st.jw E cc k by
    obtain ⟨c', k', e, hk', hr⟩ := h
    exact ⟨c', k', e, hk', hr, exec_frameB e wr_jwStmt⟩
  unfold jwStmt St.jw
  by_cases h1 : st.cnt k = 1
  swap
  · refine spec_ifLtN_true (by rw [h87, hC.one]; grind [bit])
      (spec_instr (Exec.constN hw _ _ (by omega)) fun _ => ⟨by omega, ?_⟩)
    simp_all
  refine spec_ifLtN_false (by rw [h87, hC.one]; grind [bit]) ?_
  rw [ite_eq_left h1]
  obtain ⟨hpA, hpL, hsA, hsL⟩ := hring k hk hkL
  -- the predecessor
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 90080 90040 90086,
      .loadN 90081 90080, .copyN 90088 90081]) c c₁ k₁ ∧ k₁ = 3 ∧
      (c₁.nreg 90081 = st.prv k ∧ c₁.nreg 90088 = st.prv k ∧
        (∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90088 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    · rw [hC.bPrv, h86]; dm_simp; omega
    · have e : c.nmem (d.b0 + d.oPrv + k) = st.prv k := henc.prv k hk
      refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => by simp_all, rfl⟩ <;>
        (config_simp; rw [hC.bPrv, h86, e])
  obtain ⟨q81, q88, qr, qm⟩ := q
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, d₂, f₂⟩ := ddStmt_exec (P := P) c₁ w₁ hW1
    (b1 := decide (st.cnt (st.nd0 cc) = 1)) (b2 := decide (st.cnt (st.nd1 cc) = 1))
    (by rw [qr _ (by decide) (by decide) (by decide), hC.one])
    (by grind)
    (by grind)
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, Bin 90089 90090 r = false → c₂.nreg r = c₁.nreg r := f₂.1
  have hdd1 : c₂.nreg 90089 = bit (st.dd cc (st.prv k)) := by
    rw [d₂, q88, qr _ (by decide) (by decide) (by decide),
      qr _ (by decide) (by decide) (by decide), h68, h69]
    rfl
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, r₃, m₃⟩ := skipLoad_exec (P := P) c₂ w₂ (rb := 90040) (rp := 90081)
    (b := st.dd cc (st.prv k)) (by rw [g₂ _ (by decide), qr _ (by decide) (by decide) (by decide),
      hC.one]) hdd1
    (fun _ => by
      rw [g₂ _ (by decide), g₂ _ (by decide), qr _ (by decide) (by decide) (by decide), q81,
        hC.bPrv]
      dm_simp; omega) (by decide) (by decide) (by decide) (by decide)
  have hpr : c₃.nreg 90081 = st.prD cc k := by
    rw [p₃, g₂ _ (by decide), g₂ _ (by decide), qr _ (by decide) (by decide) (by decide), q81,
      hC.bPrv, f₂.2.2.1, qm]
    unfold St.prD
    split_ifs
    · exact henc.prv _ hpA
    · rfl
  have w₃ := e₃.wb_right
  -- the successor
  have c3r : ∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90088 → r ≠ 90089 → c₃.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4
    rw [r₃ r a1 a2, g₂ r (Bin_false (by omega)), qr r a1 a2 a3]
  have m3 : c₃.nmem = c.nmem := by rw [m₃, f₂.2.2.1, qm]
  obtain ⟨c₄, k₄, e₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W (block [.addN 90080 90039 90086,
      .loadN 90082 90080, .copyN 90088 90082]) c₃ c₄ k₄ ∧ k₄ = 3 ∧
      (c₄.nreg 90082 = st.nxt k ∧ c₄.nreg 90088 = st.nxt k ∧
        (∀ r, r ≠ 90080 → r ≠ 90082 → r ≠ 90088 → c₄.nreg r = c₃.nreg r) ∧
        c₄.nmem = c₃.nmem) := by
    exec_block
    · rw [c3r _ (by decide) (by decide) (by decide) (by decide),
        c3r _ (by decide) (by decide) (by decide) (by decide), hC.bNxt, h86]; dm_simp; omega
    · have e : c.nmem (d.b0 + d.oNxt + k) = st.nxt k := henc.nxt k hk
      refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => by simp [upd, h1, h2, h3], rfl⟩ <;>
        (config_simp; rw [c3r _ (by decide) (by decide) (by decide) (by decide),
          c3r _ (by decide) (by decide) (by decide) (by decide), hC.bNxt, h86, m3, e])
  obtain ⟨q82, q88', qr', qm'⟩ := q
  have w₄ := e₄.wb_right
  have c4r : ∀ r, r ≠ 90080 → r ≠ 90081 → r ≠ 90082 → r ≠ 90088 → r ≠ 90089 →
      c₄.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 => by grind
  obtain ⟨c₅, k₅, e₅, hk₅, d₅, f₅⟩ := ddStmt_exec (P := P) c₄ w₄ hW1
    (b1 := decide (st.cnt (st.nd0 cc) = 1)) (b2 := decide (st.cnt (st.nd1 cc) = 1))
    (by rw [c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), hC.one])
    (by grind)
    (by grind)
  have w₅ := e₅.wb_right
  have g₅ : ∀ r, Bin 90089 90090 r = false → c₅.nreg r = c₄.nreg r := f₅.1
  have hdd2 : c₅.nreg 90089 = bit (st.dd cc (st.nxt k)) := by
    rw [d₅, q88', c4r _ (by decide) (by decide) (by decide) (by decide) (by decide),
      c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), h68, h69]
    rfl
  have hb6 : st.dd cc (st.nxt k) = true → c₅.nreg 90039 + c₅.nreg 90082 ≤ W := by
    intro _
    rw [g₅ _ (by decide), g₅ _ (by decide),
      c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), q82, hC.bNxt]
    dm_simp; omega
  obtain ⟨c₆, k₆, e₆, hk₆, p₆, r₆, m₆⟩ := skipLoad_exec (P := P) c₅ w₅ (rb := 90039) (rp := 90082)
    (b := st.dd cc (st.nxt k)) (by rw [g₅ _ (by decide),
      c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), hC.one]) hdd2
    hb6 (by decide) (by decide) (by decide) (by decide)
  have m6 : c₆.nmem = c.nmem := by rw [m₆, f₅.2.2.1, qm', m3]
  have hsu : c₆.nreg 90082 = st.suD cc k := by
    rw [p₆, g₅ _ (by decide), g₅ _ (by decide),
      c4r _ (by decide) (by decide) (by decide) (by decide) (by decide), q82, hC.bNxt,
      f₅.2.2.1, qm', m3]
    unfold St.suD
    split_ifs
    · exact henc.nxt _ hsA
    · rfl
  have hpr6 : c₆.nreg 90081 = st.prD cc k := by
    rw [r₆ _ (by decide) (by decide), g₅ _ (by decide), qr' _ (by decide) (by decide)
      (by decide), hpr]
  have w₆ := e₆.wb_right
  have c6r : ∀ r, r < 90080 → c₆.nreg r = c.nreg r := fun r hr => by
    rw [r₆ r (by omega) (by omega), g₅ r (Bin_false (by omega)),
      c4r r (by omega) (by omega) (by omega) (by omega) (by omega)]
  -- the bounds of the two neighbours
  have hpD : st.prD cc k < d.A := by
    unfold St.prD; split_ifs
    · grind
    · exact hpA
  have hsD : st.suD cc k < d.A := by
    unfold St.suD; split_ifs
    · grind
    · exact hsA
  -- the copies and the weight
  obtain ⟨c₇, k₇, e₇, hk₇, q90, q91, r₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.copyN 90090 90081, .copyN 90091 90082]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
      c₇.nreg 90090 = st.prD cc k ∧ c₇.nreg 90091 = st.suD cc k ∧
      (∀ r, r ≠ 90090 → r ≠ 90091 → c₇.nreg r = c₆.nreg r) := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => by simp [upd, h1, h2]⟩
    · config_simp; exact hpr6
    · config_simp; exact hsu
  have hC₇ : Cst c₇ E d := hC.frame fun r hr _ => by
    rw [r₇ r (by omega) (by omega), c6r r (by omega)]
  have henc₇ : Enc c₇.nmem d st := by
    have : c₇.nmem = c₆.nmem := (exec_frameB e₇ (B := Bin 90090 90092) (by decide)).2.2.1
    grind
  obtain ⟨c₈, k₈, e₈, hk₈, g₈, -⟩ := gwStmt_exec (P := P) c₇ e₇.wb_right hC₇ henc₇
    (by omega) (by omega) (by grind) hszW hbase
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈
    (Exec.copyN e₈.wb_right 90085 90092)))))))), by omega, ?_⟩
  ram_simp 

end

end Gran

end Chazelle.Core
