module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.OraclePrepMain
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.GranWt
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.OracleBook

section
set_option hygiene false
local macro "zqbhq" : tactic => `(tactic| (have hwm : zttd := rfl
                                           have hlm : ztcql := rfl
                                           have hrm : ztdjs := rfl))
local macro "zqbhr" : tactic => `(tactic| (have tR := WalkEmbed.tpos_lt J.whole J.m₁
                                           have tR' := WalkEmbed.tpos_lt J.right 0
                                           have tL := WalkEmbed.tpos_lt J.whole ztbv
                                           have tL' := WalkEmbed.tpos_lt J.left J.m₁))
local macro "zqbhs" : tactic => `(tactic| (exec_block
                                           all_goals try omega))
set_option hygiene true

/-!
# Sweep RAM primitives (WP-D2), part 11: the index arithmetic of a junction

design-merge-v2 §9.1 and §9.6 item 5 (`corrL`, `corrR`, `wholePos`): the walks of
`M = chainModel J.whole`, `M₁ = chainModel J.left`, `M₂ = chainModel J.right` agree along the
stretches of the correspondences `Sweep.corr_right` (base `g = 6 + tpos J.whole J.m₁` in `M`,
`g' = 6 + tpos J.right 0` in `M₂`, lengths `rL1`, `rL2`, gap `rδ`) and `Sweep.corr_left` (base
`6 + tpos J.whole (J.m₁ + 2 J.m₂)`, `6 + tpos J.left J.m₁`, `lL1`, `lL2`, `lδ`).

* `junConst` computes the ten constants from the three chain descriptors (`junConst_meets`);
  `tpos C J` is `candIdx m S J` (`tpos_eq_cand`).
* The conversions are then index arithmetic on these constants (`SweepPrimIdx`): a walk index of
  `M` at offset `d` is `(g + d) mod n`, the corresponding index of `M₂` is
  `(g' + dq L1 δ d) mod n₂`, and `Sweep.Corr.sidePt_eq`, `attach_iff`, `faces_iff` transfer
  points, attachments and faced sets.
-/
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK
@[expose] public section
theorem tpos_eq_cand (C : Chain) {J : ℕ} (hJ : J < 2 * C.m) :
    WalkEmbed.tpos C J = candIdx C.m ztboi J := by
  zuec
  unfold WalkEmbed.tpos WalkEmbed.bS candIdx
  zus
  · zupd
  · rw [show J + 2 * C.m - C.sideS C.sideBeta = (J - C.sideS C.sideBeta) + 2 * C.m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]

/-! ## Reading a descriptor -/

/-- Read the number of edges (`50101`), `2m` (`50108`) and the tour position `S = sideS` of the
box (`50102`) of the chain descriptor at the address in `50100`. -/
def readS : Stmt :=
  .seq (block [.constN 50104 2, .addN 50105 50100 50104, .loadN 50101 50105,
      .constN 50104 3, .addN 50105 50100 50104, .loadN 50106 50105,
      .constN 50104 4, .addN 50105 50100 50104, .loadN 50107 50105,
      .addN 50108 50101 50101, .constN 50109 1])
    (.ifLtN 50107 50109 ztejv
      ztzac)
variable {P : Polygon} {W : ℕ} (c : Config)
theorem readS_exec (hw : WordsBounded W c) {X : ℕ}
    (hX : c.nreg 50100 = X) {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem X Q H C) (hXW : X + 5 ≤ W) (hmW : 2 * C.m ≤ W) :
    ∃ c' k, Exec P W readS c c' k ∧ k ≤ 16 ∧ c'.nreg 50101 = C.m ∧
      c'.nreg 50102 = C.sideS C.sideBeta ∧ c'.nreg 50108 = 2 * C.m ∧
      (∀ r, zthjw → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨-, -, -, hm, hT, hb⟩ := hC
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50104 2,
      .addN 50105 50100 50104, .loadN 50101 50105, .constN 50104 3, .addN 50105 50100 50104,
      .loadN 50106 50105, .constN 50104 4, .addN 50105 50100 50104, .loadN 50107 50105,
      .addN 50108 50101 50101, .constN 50109 1]) c c₁ k₁ ∧ k₁ = 11 ∧
      (c₁.nreg 50101 = C.m ∧ c₁.nreg 50106 = C.topIdx ∧ c₁.nreg 50107 = c.nmem ztjns ∧
        c₁.nreg 50108 = 2 * C.m ∧ c₁.nreg 50109 = 1 ∧
        (∀ r, zthjw → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    zqbhs
    all_goals try (config_simp; rw [hX]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp_all
    · simp_all
    · simp_all
    · config_simp; grind
    · config_simp
    · zufxq
  obtain ⟨q01, q06, q07, q08, q09, r₁, m₁⟩ := q
  zud
  have hsS : C.sideS C.sideBeta = if C.sideBeta = true then C.topIdx else 2 * C.m - C.topIdx := by
    rfl
  obtain ⟨c₂, k₂, e₂, hk₂, q02, r₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 50107 50109 ztejv
        ztzac)
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50102 = C.sideS C.sideBeta ∧
      ∀ r, r ≠ 50102 → c₂.nreg r = c₁.nreg r := by
    by_cases h0 : c.nmem ztjns < 1
    · have hβ : ztidl := by
        simp_all
      refine spec_ifLtN_true by_omega (spec_instr ztbly
        fun _ => ztbfk)
      simp_all
    · zubv
      by_cases h2 : 1 < c.nmem ztjns
      · have hβ : ztidl := by
          grind
        refine spec_ifLtN_true by_omega (spec_instr ztbly
          fun _ => ztbfk)
        simp_all
      · zukhn
        refine spec_ifLtN_false by_omega (spec_instr zteeh
          fun _ => ztbfk)
        simp_all
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by_simp_all, q02,
    by simp_all, fun r hr => by_grind,
    by rw [(exec_frameB e₂ (B := fun r => r == 50102) by_decide).2.2.1, m₁]⟩

/-! ## Generic arithmetic blocks -/

/-- `dst := candIdx`-style: `if j < s then j + d else j - s`. -/
def candR (j s d dst : ℕ) : Stmt := .ifLtN j s (.instr (.addN dst j d)) (.instr (.subN dst j s))
theorem candR_exec (hw : WordsBounded W c) {j s d dst : ℕ}
    (hjd : c.nreg j < c.nreg s → c.nreg j + c.nreg d ≤ W) :
    ∃ c' k, Exec P W (candR j s d dst) c c' k ∧ k ≤ 3 ∧
      c'.nreg dst = (if c.nreg j < c.nreg s then c.nreg j + c.nreg d else c.nreg j - c.nreg s) ∧
      ∀ r, r ≠ dst → c'.nreg r = c.nreg r := by
  unfold candR
  by_cases h : c.nreg j < c.nreg s
  · exact spec_ifLtN_true h (spec_instr (Exec.addN hw _ _ _ (hjd h)) by_simp_all)
  · exact spec_ifLtN_false h (spec_instr ztbbq by_simp_all)

/-- The right lengths `rL1, rL2, rδ` from `A = 2m - τ` (`50130`), `B = 2m₂ - τ'` (`50131`), `2m₂` (`50115`). -/
def selR : Stmt :=
  .ifLtN 50130 50115 (block [.addN 50212 50115 50160, .constN 50213 0, .constN 50214 0])
    (.ifLtN 50131 50115 (block [.copyN 50212 50131, .subN 50213 50115 50131, .constN 50214 7])
      (block [.copyN 50212 50115, .constN 50213 0, .constN 50214 0]))
theorem selR_exec (hw : WordsBounded W c)
    (h7 : c.nreg 50160 = 7) (hW : c.nreg 50115 + 7 ≤ W) :
    ∃ c' k, Exec P W selR c c' k ∧ k ≤ 7 ∧
      c'.nreg 50212 = (if c.nreg 50130 < c.nreg 50115 then c.nreg 50115 + 7 else
        if c.nreg 50131 < c.nreg 50115 then c.nreg 50131 else c.nreg 50115) ∧
      c'.nreg 50213 = (if c.nreg 50130 < c.nreg 50115 then 0 else
        if c.nreg 50131 < c.nreg 50115 then c.nreg 50115 - c.nreg 50131 else 0) ∧
      c'.nreg 50214 = (if c.nreg 50130 < c.nreg 50115 then 0 else
        if c.nreg 50131 < c.nreg 50115 then 7 else 0) ∧
      ∀ r, r ≠ 50212 → r ≠ 50213 → r ≠ 50214 → c'.nreg r = c.nreg r := by
  unfold selR
  by_cases ha : c.nreg 50130 < c.nreg 50115
  · refine spec_ifLtN_true ha ?_
    zqbhs
    simp_all
  · zumjo
    by_cases hb : c.nreg 50131 < c.nreg 50115
    · zugst
      zqbhs
      simp_all
    · zugsq
      zqbhs
      refine ztlvk <;> config_simp <;>
        zulag

/-- The left lengths `lL1, lL2, lδ` from `A' = 2m - τL` (`50132`), `B' = 2m₁ - τ'L` (`50133`), `2m₁` (`50118`). -/
def selL : Stmt :=
  .ifLtN 50132 50118 (block [.addN 50217 50118 50160, .constN 50218 0, .constN 50219 0])
    (.ifLtN 50133 50118 (block [.copyN 50217 50133, .subN 50218 50118 50133, .constN 50219 7])
      (block [.copyN 50217 50118, .constN 50218 0, .constN 50219 0]))
theorem selL_exec (hw : WordsBounded W c)
    (h7 : c.nreg 50160 = 7) (hW : c.nreg 50118 + 7 ≤ W) :
    ∃ c' k, Exec P W selL c c' k ∧ k ≤ 7 ∧
      c'.nreg 50217 = (if c.nreg 50132 < c.nreg 50118 then c.nreg 50118 + 7 else
        if c.nreg 50133 < c.nreg 50118 then c.nreg 50133 else c.nreg 50118) ∧
      c'.nreg 50218 = (if c.nreg 50132 < c.nreg 50118 then 0 else
        if c.nreg 50133 < c.nreg 50118 then c.nreg 50118 - c.nreg 50133 else 0) ∧
      c'.nreg 50219 = (if c.nreg 50132 < c.nreg 50118 then 0 else
        if c.nreg 50133 < c.nreg 50118 then 7 else 0) ∧
      ∀ r, r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → c'.nreg r = c.nreg r := by
  unfold selL
  by_cases ha : c.nreg 50132 < c.nreg 50118
  · refine spec_ifLtN_true ha ?_
    zqbhs
    simp_all
  · zumjo
    by_cases hb : c.nreg 50133 < c.nreg 50118
    · zugst
      zqbhs
      simp_all
    · zugsq
      zqbhs
      refine ztlvk <;> config_simp <;>
        zulag

/-! ## The constants of a junction -/

/-- Read the three descriptors: `C` into `50110 … 50112`, `C₂` into `50113 … 50115`, `C₁` into
`50101`, `50102`, `50108` (number of edges, `sideS`, `2m`). -/
def junHead : Stmt :=
  .seq (block [.constN 50119 6, .constN 50160 7, .copyN 50100 50202]) (.seq readS
    (.seq (block [.copyN 50110 50101, .copyN 50111 50102, .copyN 50112 50108, .copyN 50100 50201])
      (.seq readS
        (.seq (block [.copyN 50113 50101, .copyN 50114 50102, .copyN 50115 50108,
            .copyN 50100 50200]) readS))))

/-- The four tour offsets. -/
def junMid : Stmt :=
  .seq (block [.copyN 50116 50101, .copyN 50117 50102, .copyN 50118 50108,
      .subN 50121 50112 50111, .constN 50123 0, .subN 50124 50115 50114,
      .addN 50126 50116 50115, .subN 50128 50118 50117])
    (.seq (candR 50116 50111 50121 50120) (.seq (candR 50123 50114 50124 50122)
      (.seq (candR 50126 50111 50121 50125) (candR 50116 50117 50128 50127))))

/-- The bases and the differences. -/
def junOut : Stmt :=
  block [.addN 50210 50119 50120, .addN 50211 50119 50122, .subN 50130 50112 50120,
    .subN 50131 50115 50122, .addN 50215 50119 50125, .addN 50216 50119 50127,
    .subN 50132 50112 50125, .subN 50133 50118 50127]

/-- **The constants of a junction** from the descriptors of `C₁` (`50200`), `C₂` (`50201`) and
`C` (`50202`): `50210 = 6 + tpos C m₁`, `50211 = 6 + tpos C₂ 0`, `50212 … 50214 = rL1, rL2, rδ`,
`50215 = 6 + tpos C (m₁ + 2 m₂)`, `50216 = 6 + tpos C₁ m₁`, `50217 … 50219 = lL1, lL2, lδ`. -/
def junConst : Stmt :=
  .seq junHead (.seq junMid (.seq junOut (.seq selR selL)))

/-- The registers `junConst` writes. -/
def Bjun (r : ℕ) : Bool := decide (50100 ≤ r ∧ r < 50200) || decide (50210 ≤ r ∧ r < 50220)
theorem wr_junConst : wr Bjun junConst = true := by_decide

/-- The machine value of a candidate. -/
theorem cand_val {m S j : ℕ} :
    (if j < S then j + ztbru else j - S) = candIdx m S j := rfl

/-- The values read by `junHead`. -/
structure HeadVals (J : Merge.Junction) (c : Config) : Prop where
  v10 : c.nreg 50110 = J.whole.m
  v11 : c.nreg 50111 = J.whole.sideS J.whole.sideBeta
  v12 : c.nreg 50112 = 2 * J.whole.m
  v13 : c.nreg 50113 = J.right.m
  v14 : c.nreg 50114 = J.right.sideS J.right.sideBeta
  v15 : c.nreg 50115 = 2 * J.right.m
  v01 : c.nreg 50101 = J.left.m
  v02 : c.nreg 50102 = J.left.sideS J.left.sideBeta
  v08 : c.nreg 50108 = 2 * J.left.m
  v19 : c.nreg 50119 = 6
  v60 : c.nreg 50160 = 7
theorem junHead_exec (hw : WordsBounded W c) {H : Host}
    {J : Merge.Junction}
    (hJ : JunctionAt c.nmem ztbok ztcuv ztjsc zta H J)
    (hXl : c.nreg 50200 + 5 ≤ W) (hXr : c.nreg 50201 + 5 ≤ W) (hXw : c.nreg 50202 + 5 ≤ W)
    (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junHead c c' k ∧ k ≤ 70 ∧ HeadVals J c' ∧ c'.nmem = c.nmem ∧
      ∀ r, ztofu → c'.nreg r = c.nreg r := by
  zugpf
  zqbhq
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50119 6, .constN 50160 7,
      .copyN 50100 50202]) c c₁ k₁ ∧ k₁ = 3 ∧ (c₁.nreg 50119 = 6 ∧ c₁.nreg 50160 = 7 ∧
      c₁.nreg 50100 = c.nreg 50202 ∧
      (∀ r, r ≠ 50119 → r ≠ 50160 → r ≠ 50100 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    zqbhs
    simp_all
  obtain ⟨p19, p60, p00, r₁, m₁⟩ := q
  obtain ⟨c₂, k₂, e₂, hk₂, a01, a02, a08, r₂, m₂⟩ := readS_exec (P := P) c₁ e₁.wb_right p00
    (by zvmxn; omega) hXw by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50110 50101,
      .copyN 50111 50102, .copyN 50112 50108, .copyN 50100 50201]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 50110 = J.whole.m ∧ c₃.nreg 50111 = J.whole.sideS J.whole.sideBeta ∧
        c₃.nreg 50112 = 2 * J.whole.m ∧ c₃.nreg 50100 = c.nreg 50201 ∧
        (∀ r, r ≠ 50110 → r ≠ 50111 → r ≠ 50112 → r ≠ 50100 → c₃.nreg r = c₂.nreg r)) := by
    zuja
    exec_block
    simp_all
  obtain ⟨p10, p11, p12, p00', r₃⟩ := q
  have m₃ : ztckd := by
    rw [(exec_frameB e₃ (B := fun r => decide (50100 ≤ r ∧ r < 50113)) by_decide).2.2.1, m₂, m₁]
  obtain ⟨c₄, k₄, e₄, hk₄, b01, b02, b08, r₄, m₄⟩ := readS_exec (P := P) c₃ e₃.wb_right p00'
    (by zumzp; omega) hXr by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 50113 50101,
      .copyN 50114 50102, .copyN 50115 50108, .copyN 50100 50200]) c₄ c₅ k₅ ∧ k₅ = 4 ∧
      (c₅.nreg 50113 = J.right.m ∧ c₅.nreg 50114 = J.right.sideS J.right.sideBeta ∧
        c₅.nreg 50115 = 2 * J.right.m ∧ c₅.nreg 50100 = c.nreg 50200 ∧
        (∀ r, r ≠ 50113 → r ≠ 50114 → r ≠ 50115 → r ≠ 50100 → c₅.nreg r = c₄.nreg r)) := by
    zubwq
    exec_block
    refine ⟨rfl, by config_simp; omega, by config_simp; omega, by config_simp; omega,
      ?_, fun r h1 h2 h3 h4 => by zunaf⟩
    config_simp
    grind
  obtain ⟨p13, p14, p15, p00'', r₅⟩ := q
  have m₅ : ztlaq := by
    rw [(exec_frameB e₅ (B := fun r => decide (50100 ≤ r ∧ r < 50116)) by_decide).2.2.1, m₄, m₃]
  obtain ⟨c₆, k₆, e₆, hk₆, d01, d02, d08, r₆, m₆⟩ := readS_exec (P := P) c₅ e₅.wb_right p00''
    (by zunjy; omega) hXl by_omega
  have ex : Exec P W junHead c c₆ _ := .seq e₁ ztfv
  have k₅₆ : ∀ r, zthjw → r ≠ 50113 → r ≠ 50114 → r ≠ 50115 → r ≠ 50100 →
      c₆.nreg r = c₄.nreg r := by_grind
  refine ⟨c₆, _, ex, by_omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, d01, d02, d08, ?_, ?_⟩, by_grind,
    fun r hr => ?_⟩
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · rw [k₅₆ _ by_omega by_omega by_omega by_omega by_omega, r₄ _ by_omega,
      r₃ _ by_omega by_omega by_omega by_omega, r₂ _ by_omega,
      r₁ _ by_omega by_omega by_omega]

/-- The tour offsets computed by `junMid`. -/
structure MidVals (J : Merge.Junction) (c : Config) : Prop where
  t20 : c.nreg 50120 = WalkEmbed.tpos J.whole J.m₁
  t22 : c.nreg 50122 = WalkEmbed.tpos J.right 0
  t25 : c.nreg 50125 = WalkEmbed.tpos J.whole ztbv
  t27 : c.nreg 50127 = WalkEmbed.tpos J.left J.m₁
  v12 : c.nreg 50112 = 2 * J.whole.m
  v15 : c.nreg 50115 = 2 * J.right.m
  v18 : c.nreg 50118 = 2 * J.left.m
  v19 : c.nreg 50119 = 6
  v60 : c.nreg 50160 = 7
theorem junMid_exec (hw : WordsBounded W c)
    {J : Merge.Junction} (hv : HeadVals J c) (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junMid c c' k ∧ k ≤ 20 ∧ MidVals J c' ∧
      ∀ r, ztofu → c'.nreg r = c.nreg r := by
  zqbhq
  zufz

  have hSw := J.whole.sideS_lt J.whole.sideBeta
  have hSr := J.right.sideS_lt J.right.sideBeta
  have hSl := J.left.sideS_lt J.left.sideBeta
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50116 50101, .copyN 50117 50102,
      .copyN 50118 50108, .subN 50121 50112 50111, .constN 50123 0, .subN 50124 50115 50114,
      .addN 50126 50116 50115, .subN 50128 50118 50117]) c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 50116 = J.m₁ ∧ c₁.nreg 50117 = J.left.sideS J.left.sideBeta ∧
        c₁.nreg 50118 = 2 * J.m₁ ∧
        c₁.nreg 50121 = 2 * J.whole.m - J.whole.sideS J.whole.sideBeta ∧ c₁.nreg 50123 = 0 ∧
        c₁.nreg 50124 = 2 * J.right.m - J.right.sideS J.right.sideBeta ∧
        c₁.nreg 50126 = J.m₁ + 2 * J.m₂ ∧
        c₁.nreg 50128 = 2 * J.m₁ - J.left.sideS J.left.sideBeta ∧
        ∀ r, r ≠ 50116 → r ≠ 50117 → r ≠ 50118 → r ≠ 50121 → r ≠ 50123 → r ≠ 50124 →
          r ≠ 50126 → r ≠ 50128 → c₁.nreg r = c.nreg r) := by
    zqbhs
    all_goals try (config_simp; zunuk; omega)
    refine ztfwv
    · config_simp; exact hv.v01
    · config_simp; exact hv.v02
    · config_simp; exact hv.v08
    · config_simp; rw [hv.v12, hv.v11]
    · config_simp
    · config_simp; rw [hv.v15, hv.v14]
    · config_simp; zunuk
    · config_simp; rw [hv.v08, hv.v02, hlm]
    simp_all
  obtain ⟨u16, u17, u18, u21, u23, u24, u26, u28, r₁⟩ := q
  have k1 : ∀ r, r = 50110 ∨ r = 50111 ∨ r = 50112 ∨ r = 50113 ∨ r = 50114 ∨ r = 50115 ∨
      r = 50119 ∨ r = 50160 → c₁.nreg r = c.nreg r := fun r hr => by
    grind
  obtain ⟨c₂, k₂, e₂, hk₂, t20, r₂⟩ := candR_exec (P := P) (j := 50116) (s := 50111) (d := 50121)
    (dst := 50120) c₁ e₁.wb_right (by
      rw [u16, u21, k1 _ by_omega, hv.v11]; grind)
  obtain ⟨c₃, k₃, e₃, hk₃, t22, r₃⟩ := candR_exec (P := P) (j := 50123) (s := 50114) (d := 50124)
    (dst := 50122) c₂ e₂.wb_right (by
      grind)
  obtain ⟨c₄, k₄, e₄, hk₄, t25, r₄⟩ := candR_exec (P := P) (j := 50126) (s := 50111) (d := 50121)
    (dst := 50125) c₃ e₃.wb_right (by
      rw [r₃ _ by_decide, r₃ _ by_decide, r₃ _ by_decide, r₂ _ by_decide,
        r₂ _ by_decide, r₂ _ by_decide, u26, u21, k1 _ by_omega, hv.v11]
      grind)
  obtain ⟨c₅, k₅, e₅, hk₅, t27, r₅⟩ := candR_exec (P := P) (j := 50116) (s := 50117) (d := 50128)
    (dst := 50127) c₄ e₄.wb_right (by
      grind)
  have k5 : ∀ r, r ≠ 50120 → r ≠ 50122 → r ≠ 50125 → r ≠ 50127 → c₅.nreg r = c₁.nreg r :=
    by grind
  have ex : Exec P W junMid c c₅ _ := .seq e₁ ztbq
  refine ⟨c₅, _, ex, by_omega, ztbfh, fun r hr => ?_⟩
  · rw [r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide, t20, u16, k1 _ by_omega, hv.v11,
      u21, cand_val, tpos_eq_cand _ by_omega]
  · rw [r₅ _ by_decide, r₄ _ by_decide, t22, r₂ _ by_decide, r₂ _ by_decide,
      r₂ _ by_decide, u23, k1 _ by_omega, hv.v14, u24, cand_val, tpos_eq_cand _ by_omega]
  · rw [r₅ _ by_decide, t25, r₃ _ by_decide, r₃ _ by_decide, r₃ _ by_decide,
      r₂ _ by_decide, r₂ _ by_decide, r₂ _ by_decide, u26, k1 _ by_omega, hv.v11, u21,
      cand_val, tpos_eq_cand _ by_omega]
  · rw [t27, r₄ _ by_decide, r₄ _ by_decide, r₄ _ by_decide, r₃ _ by_decide,
      r₃ _ by_decide, r₃ _ by_decide, r₂ _ by_decide, r₂ _ by_decide, r₂ _ by_decide,
      u16, u17, u28, cand_val, ← hlm, tpos_eq_cand _ by_omega]
  · rw [k5 _ by_decide by_decide by_decide by_decide, k1 _ by_omega, hv.v12]
  · rw [k5 _ by_decide by_decide by_decide by_decide, k1 _ by_omega, hv.v15]
  · grind
  · rw [k5 _ by_decide by_decide by_decide by_decide, k1 _ by_omega, hv.v19]
  · rw [k5 _ by_decide by_decide by_decide by_decide, k1 _ by_omega, hv.v60]
  · rw [k5 r by_omega by_omega by_omega by_omega,
      r₁ r by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega]
theorem junOut_exec (hw : WordsBounded W c)
    {J : Merge.Junction} (hv : MidVals J c) (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junOut c c' k ∧ k = 8 ∧
      c'.nreg 50210 = 6 + WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50211 = 6 + WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50130 = 2 * J.whole.m - WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50131 = 2 * J.right.m - WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50215 = 6 + WalkEmbed.tpos J.whole ztbv ∧
      c'.nreg 50216 = 6 + WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50132 = 2 * J.whole.m - WalkEmbed.tpos J.whole ztbv ∧
      c'.nreg 50133 = 2 * J.left.m - WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50115 = 2 * J.right.m ∧ c'.nreg 50118 = 2 * J.left.m ∧ c'.nreg 50160 = 7 ∧
      ∀ r, (r < 50100 ∨ 50220 ≤ r) → c'.nreg r = c.nreg r := by
  zqbhr
  zqbhq
  unfold junOut
  exec_block
  all_goals try (config_simp; zuopp; omega)
  all_goals try (config_simp; zuopq; omega)
  all_goals try (config_simp; zuopr; omega)
  all_goals try (config_simp; zuops; omega)
  refine ztedv
  · config_simp; zuopp
  · config_simp; zuopq
  · config_simp; rw [hv.v12, hv.t20]
  · config_simp; rw [hv.v15, hv.t22]
  · config_simp; zuopr
  · config_simp; zuops
  · config_simp; rw [hv.v12, hv.t25]
  · config_simp; rw [hv.v18, hv.t27]
  · config_simp; exact hv.v15
  · config_simp; exact hv.v18
  · config_simp; exact hv.v60
  · zufxq

/-- **Contract of `junConst`** (at most `120` steps). -/
theorem junConst_meets : Meets junConst {bLocate}
    (fun P W c => c.nreg 50200 + 5 ≤ W ∧ c.nreg 50201 + 5 ≤ W ∧ c.nreg 50202 + 5 ≤ W ∧
      ∃ H J, JunctionAt c.nmem ztbok ztcuv ztjsc zta H J ∧
        2 * J.whole.m + 7 ≤ W)
    (fun P c c' => ∀ H J, JunctionAt c.nmem ztbok ztcuv ztjsc
      zta H J →
      c'.nreg 50210 = 6 + WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50211 = 6 + WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50212 = Sweep.rL1 J ∧ c'.nreg 50213 = Sweep.rL2 J ∧ c'.nreg 50214 = Sweep.rδ J ∧
      c'.nreg 50215 = 6 + WalkEmbed.tpos J.whole ztbv ∧
      c'.nreg 50216 = 6 + WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50217 = Sweep.lL1 J ∧ c'.nreg 50218 = Sweep.lL2 J ∧ c'.nreg 50219 = Sweep.lδ J)
    (fun _ _ => 120) := by
  intro P W c hw ⟨hXl, hXr, hXw, H, J, hJ, hWm⟩ hroom
  zqbhq
  obtain ⟨c₁, k₁, e₁, hk₁, hv₁, -, -⟩ := junHead_exec c hw hJ hXl hXr hXw hWm
  obtain ⟨c₂, k₂, e₂, hk₂, hv₂, -⟩ := junMid_exec c₁ e₁.wb_right hv₁ hWm
  obtain ⟨c₃, k₃, e₃, hk₃, o10, o11, a30, a31, o15, o16, a32, a33, a15, a18, a60, -⟩ :=
    junOut_exec c₂ e₂.wb_right hv₂ hWm
  obtain ⟨c₄, k₄, e₄, hk₄, s12, s13, s14, r₄⟩ := selR_exec (P := P) c₃ e₃.wb_right a60
    by_omega
  have k4 := r₄
  obtain ⟨c₅, k₅, e₅, hk₅, s17, s18, s19, r₅⟩ := selL_exec (P := P) c₄ e₄.wb_right
    by_grind
    by_grind
  have k5 := r₅
  have ex : Exec P W junConst c c₅ _ := .seq e₁ ztbq
  refine ⟨c₅, _, ex, by_grind, ?_, ?_⟩
  · intro H' J' ⟨hCl', hCr', hCw'⟩
    zugpf
    have eL := NFLoc.chain_eq_of_desc hCl' hCl
    have eR := NFLoc.chain_eq_of_desc hCr' hCr
    have eW := NFLoc.chain_eq_of_desc hCw' hCw
    have e1 : J'.m₁ = J.m₁ := congrArg Chain.m eL
    have e2 : J'.m₂ = J.m₂ := congrArg Chain.m eR
    have k45 : ∀ r, r ≠ 50212 → r ≠ 50213 → r ≠ 50214 → r ≠ 50217 → r ≠ 50218 → r ≠ 50219 →
        c₅.nreg r = c₃.nreg r := by_grind
    zqbhr
    have w12 : c₅.nreg 50212 = c₄.nreg 50212 := by_grind
    have w13 : c₅.nreg 50213 = c₄.nreg 50213 := by_grind
    have w14 : c₅.nreg 50214 = c₄.nreg 50214 := by_grind
    have x32 : c₄.nreg 50132 = c₃.nreg 50132 := by_grind
    have x33 : c₄.nreg 50133 = c₃.nreg 50133 := by_grind
    have x18 : c₄.nreg 50118 = c₃.nreg 50118 := by_grind
    refine ztbbh
    · grind
    · grind
    · unfold Sweep.rL1; rw [eW, eR, e1, e2, w12, s12, a30, a31, a15, hrm]; grind
    · unfold Sweep.rL2; rw [eW, eR, e1, e2, w13, s13, a30, a31, a15, hrm]; grind
    · unfold Sweep.rδ; rw [eW, eR, e1, e2, w14, s14, a30, a31, a15, hrm]; grind
    · grind
    · grind
    · unfold Sweep.lL1; rw [eW, eL, e1, e2, s17, x32, x33, x18, a32, a33, a18, hlm]
      grind
    · unfold Sweep.lL2; rw [eW, eL, e1, e2, s18, x32, x33, x18, a32, a33, a18, hlm]
      grind
    · unfold Sweep.lδ; rw [eW, eL, e1, e2, s19, x32, x33, x18, a32, a33, a18, hlm]
      grind
  · exact NFLoc.frame_of_frameB (exec_frameB ex wr_junConst) (fun r hr => by
      simp only [Bjun, Bool.or_eq_true, decide_eq_true_eq] at hr
      zumkh
      zunfm; omega) _
end
end SweepPrim
end Chazelle.Core
end
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK
open Chazelle.Chain (sidePt)
@[expose] public section
def Bidx (r : ℕ) : Bool := decide (50100 ≤ r ∧ r < 50110) || decide (50210 ≤ r ∧ r < 50212)
theorem Bidx_frame {c c' : Config} (h : FrameB Bidx c c') (k : ℕ) : Frame {bLocate} c c' k :=
  NFLoc.frame_of_frameB h (fun r hr => by
    simp only [Bidx, Bool.or_eq_true, decide_eq_true_eq] at hr
    zumkh
    zunfm; omega) k

/-! ## `(a + b) mod n` -/

/-! ## `(p + n - g) mod n` -/

/-! ## The offset of the other walk: `dq` and its inverse -/

/-! ## The geometric meaning -/
variable (J : Merge.Junction)
/-- **`corrR`**: the walk point at offset `d` of the right stretch of `M` is the walk point of
`M₂` at `dq rL1 rδ d` from its base. -/
theorem corrR_sidePt (hP : J.P.Simple)
    {d : ℕ} (hd : d < Sweep.rL1 J + Sweep.rL2 J) (t : ℝ) :
    sidePt (chainModel J.whole).W ((6 + WalkEmbed.tpos J.whole J.m₁ + d) %
        (chainModel J.whole).W.n) t =
      sidePt (chainModel J.right).W ((6 + WalkEmbed.tpos J.right 0 +
        Sweep.dq ztvds ztvdt d) % (chainModel J.right).W.n) t :=
  (Sweep.corr_right0 J hP (S₂ := ∅) ztjmt Set.finite_empty).sidePt_eq hd t

/-- **`corrL`**: the walk point at offset `d` of the left stretch of `M` is the walk point of
`M₁` at `dq lL1 lδ d` from its base. -/
theorem corrL_sidePt (hP : J.P.Simple) 
    {d : ℕ} (hd : d < Sweep.lL1 J + Sweep.lL2 J) (t : ℝ) :
    sidePt (chainModel J.whole).W ((6 + WalkEmbed.tpos J.whole ztbv + d) %
        (chainModel J.whole).W.n) t =
      sidePt (chainModel J.left).W ((6 + WalkEmbed.tpos J.left J.m₁ +
        Sweep.dq ztvdq ztvdr d) % (chainModel J.left).W.n) t :=
  (Sweep.corr_left0 J hP (S₁ := ∅) ztjmt Set.finite_empty).sidePt_eq hd t

/-- **`boxTwin`**: on the vertical sides of the box (walk edges `1` and `3`) two chain models with
the same box have the same positions. -/
theorem boxTwin_pos {C₁ C₂ : Chain} (hR : C₁.radius = C₂.radius) {e : ℕ} (he : e = 1 ∨ e = 3)
    (Q : Polygon) (h : ℕ) :
    (chainModel C₁).wa e = (chainModel C₂).wa e ∧ (chainModel C₁).wb e = (chainModel C₂).wb e ∧
      (chainModel C₁).param Q ztcq = (chainModel C₂).param Q ztcq ∧
      (chainModel C₁).pos Q ztcq = (chainModel C₂).pos Q ztcq := by
  have ha : (chainModel C₁).wa e = (chainModel C₂).wa e := by
    simp only [Model.wa]
    zudsd
    · rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
        show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl, C₁.sideWalk_vtx_one,
        C₂.sideWalk_vtx_one, hR]
    · rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
        show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl, C₁.sideWalk_vtx_three,
        C₂.sideWalk_vtx_three, hR]
  have hb : (chainModel C₁).wb e = (chainModel C₂).wb e := by
    simp only [Model.wb]
    rw [show (chainModel C₁).W = C₁.sideWalk C₁.sideBeta from rfl,
      show (chainModel C₂).W = C₂.sideWalk C₂.sideBeta from rfl,
      C₁.sideWalk_mod_small _ by_omega,
      C₂.sideWalk_mod_small _ by_omega]
    zudsd
    · rw [C₁.sideWalk_vtx_two, C₂.sideWalk_vtx_two, hR]
    · rw [C₁.sideWalk_vtx_four, C₂.sideWalk_vtx_four, hR]
  have hp : (chainModel C₁).param Q ztcq = (chainModel C₂).param Q ztcq := by
    zudcl
  refine ⟨ha, hb, hp, ?_⟩
  zuckw
def mulAdd (d a : ℕ) : ℕ → Stmt
  | 0 => .skip
  | s + 1 => .seq (.instr (.addN d d a)) ztlri
theorem wr_mulAdd {B : ℕ → Bool} {d a : ℕ} (hd : B d = true) : ∀ s, wr B ztlri = true
  | 0 => rfl
  | s + 1 => by simp [mulAdd, wr, wrOK, hd, wr_mulAdd hd s]
variable {P : Polygon} {W : ℕ} (k s f : ℕ) {c : Config} {N : NF}
theorem mulAdd_exec {d a : ℕ} (hda : d ≠ a) :
    ∀ (s : ℕ) (c : Config), WordsBounded W c → c.nreg d + s * c.nreg a ≤ W →
      ∃ c' k, Exec P W ztlri c c' k ∧ k = s ∧ c'.nreg d = c.nreg d + s * c.nreg a ∧
        FrameB (fun r => r == d) c c'
  | 0, c, hw, _ => ⟨c, 0, .skip hw, rfl, by_simp, FrameB.refl _ _⟩
  | s + 1, c, hw, hb => by
    have e₁ := Exec.addN (P := P) hw d d a by_nlinarith
    obtain ⟨c', k, e', hk, v, f⟩ := mulAdd_exec hda s _ e₁.wb_right (by
      zunqw; nlinarith)
    refine ⟨c', _, .seq e₁ e', by_omega, ?_, (exec_frameB e₁ (by simp [wr, wrOK])).trans f⟩
    rw [v]; zunqw; ring

/-! ## One indexed load -/

/-- `50210 := m (m (B + k) + s · i + f)` for the handle `B = 50200` and the index `i = 50201`. -/
def nfRd (k s f : ℕ) : Stmt :=
  .seq (block [.constN 50100 k, .addN 50100 50200 50100, .loadN 50101 50100])
    (.seq (mulAdd 50101 50201 s) (block [.constN 50100 f, .addN 50101 50101 50100,
      .loadN 50210 50101]))
theorem wr_nfRd : wr Bidx zthyy = true := by
  simp only [nfRd, wr, block, wrOK, wr_mulAdd (B := Bidx) (d := 50101) by_decide]
  decide

/-- The address condition of `nfRd k s f`. -/
def NFRdOK (k s f W : ℕ) (c : Config) : Prop :=
  c.nreg 50200 + k ≤ W ∧ c.nmem ztrmg + s * c.nreg 50201 + f ≤ W

/-- The value read by `nfRd k s f`. -/
def nfVal (k s f : ℕ) (c : Config) : ℕ :=
  c.nmem (c.nmem ztrmg + s * c.nreg 50201 + f)
theorem nfRd_exec (c : Config) (hw : WordsBounded W c)
    (h : NFRdOK k s f W c) :
    ∃ c' j, Exec P W zthyy c c' j ∧ j = s + 6 ∧ c'.nreg 50210 = nfVal k s f c ∧
      FrameB Bidx c c' := by
  zubkx
  have e₁ := Exec.constN (P := P) hw 50100 k by_omega
  have e₂ := Exec.addN (P := P) e₁.wb_right 50100 50200 50100 by_simp_all
  have e₃ := Exec.loadN (P := P) e₂.wb_right 50101 50100
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := mulAdd_exec (P := P) (d := 50101) (a := 50201) by_decide
    s _ e₃.wb_right ztbaw
  have e₅ := Exec.constN (P := P) e₄.wb_right 50100 f by_omega
  have e₆ := Exec.addN (P := P) e₅.wb_right 50101 50101 50100 (by
    simp_all)
  zuffm
  have ex : Exec P W zthyy c _ (ztxjy + (k₄ + ztxjy)) :=
    .seq (.seq e₁ (.seq e₂ (.seq e₃ ztjdx)))
      ztcqq
  refine ⟨_, _, ex, by_omega, ?_, exec_frameB ex (wr_nfRd k s f)⟩
  simp only [upd_same, upd_other _ _ _ (show (50101 : ℕ) ≠ 50100 by decide)]
  rw [f₄.2.2.1, v₄]
  rfl

/-- **Contract of `nfRd k s f`** (at most `s + 6` steps). -/
theorem nfRd_meets : Meets zthyy {bLocate}
    (fun _ W c => NFRdOK k s f W c) (fun _ c c' => c'.nreg 50210 = nfVal k s f c)
    (fun _ _ => s + 6) := by
  zujaq
  obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_exec (P := P) k s f c hw h
  exact ztinx

/-! ## The fields of a normal form -/

/-- Field `f` of a chord record: `h, lp, rp, up, dn`. -/
def crFld (c : CRec) : ℕ → ℕ
  | 0 => c.h
  | 1 => c.lp
  | 2 => c.rp
  | 3 => c.up
  | _ => c.dn

/-- Field `f` of an arc record: `reg, s.edge, s.hgt, e.edge, e.hgt`. -/
def arFld (a : ARec) : ℕ → ℕ
  | 0 => a.reg
  | 1 => a.s.edge
  | 2 => a.s.hgt
  | 3 => a.e.edge
  | _ => a.e.hgt

/-- Field `f ∈ {0, 2, 4}` of a region record: number of arcs, number of exit chords, weight. -/
def rrFld (r : RRec) : ℕ → ℕ
  | 0 => r.arcs.length
  | 2 => r.chords.length
  | _ => r.wt
theorem nfVal_chord (hN : NFAt c.nmem ztbok N)
    (hi : c.nreg 50201 < N.chords.length) {f : ℕ} (hf : f < 5) :
    nfVal 3 5 f c = crFld ztbaem f := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hN.2.2.2.2.2.1 _ hi
  zumto
  interval_cases f <;> simp only [add_zero, crFld] <;> assumption
theorem nfVal_arc (hN : NFAt c.nmem ztbok N)
    (hi : c.nreg 50201 < N.arcs.length) {f : ℕ} (hf : f < 5) :
    nfVal 4 5 f c = arFld ztbael f := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hN.2.2.2.2.2.2.1 _ hi
  zumto
  interval_cases f <;> simp only [add_zero, arFld] <;> assumption
theorem nfVal_region (hN : NFAt c.nmem ztbok N)
    (hi : c.nreg 50201 < N.regions.length) {f : ℕ} (hf : f = 0 ∨ f = 2 ∨ f = 4) :
    nfVal 5 5 f c = rrFld ztbaen f := by
  obtain ⟨q0, q2, q4, -, -⟩ := hN.2.2.2.2.2.2.2.1 _ hi
  zumto
  rcases hf with rfl | rfl | rfl <;> simp only [add_zero, rrFld] <;> assumption

/-- **`chordRd f`**: field `f` of chord `i = 50201` (`0` the height vertex, `1`/`2` the edges of
`lpos`/`rpos`, `3`/`4` the regions `up`/`dn`). -/
def chordRd (f : ℕ) : Stmt := nfRd 3 5 f
theorem chordRd_meets {f : ℕ} (hf : f < 5) : Meets ztvli {bLocate}
    (fun _ W c => NFRdOK 3 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem ztbok N → c.nreg 50201 < N.chords.length →
      c'.nreg 50210 = crFld ztbaem f)
    ztjvj :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 3 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_chord hN hi hf), fr⟩

/-- **`arcRd f`**: field `f` of arc `j = 50201` (`0` its region, `1`/`2` its start, `3`/`4` its
end). -/
def arcRd (f : ℕ) : Stmt := nfRd 4 5 f
theorem arcRd_meets {f : ℕ} (hf : f < 5) : Meets ztvel {bLocate}
    (fun _ W c => NFRdOK 4 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem ztbok N → c.nreg 50201 < N.arcs.length →
      c'.nreg 50210 = arFld ztbael f)
    ztjvj :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 4 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_arc hN hi hf), fr⟩

/-- **`regRd f`**: field `f ∈ {0, 2, 4}` of region `r = 50201` (number of arcs, number of exit
chords, weight). -/
def regRd (f : ℕ) : Stmt := nfRd 5 5 f
theorem regRd_meets {f : ℕ} (hf : f = 0 ∨ f = 2 ∨ f = 4) : Meets ztwcp {bLocate}
    (fun _ W c => NFRdOK 5 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem ztbok N → c.nreg 50201 < N.regions.length →
      c'.nreg 50210 = rrFld ztbaen f)
    ztjvj :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 5 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_region hN hi hf), fr⟩

/-! ## The lists of a region -/

/-- `50210 := m (m (B + 7) + m (m (B + 5) + 5 r + f) + t)` for the handle `B = 50200`, the region
`r = 50201` and the place `t = 50202`: the `t`-th arc (`f = 1`) or exit chord (`f = 3`). -/
def nfLst (f : ℕ) : Stmt :=
  .seq (nfRd 5 5 f) (block [.constN 50100 7, .addN 50100 50200 50100, .loadN 50101 50100,
    .addN 50101 50101 50210, .addN 50101 50101 50202, .loadN 50210 50101])
theorem wr_nfLst (f : ℕ) : wr Bidx ztkbl = true := by
  rfl

/-- The address condition of `nfLst f`. -/
def NFLstOK (f W : ℕ) (c : Config) : Prop :=
  NFRdOK 5 5 f W c ∧ c.nreg 50200 + 7 ≤ W ∧
    c.nmem (c.nreg 50200 + 7) + nfVal 5 5 f c + c.nreg 50202 ≤ W
theorem nfLst_exec (f : ℕ) (c : Config) (hw : WordsBounded W c)
    (h : NFLstOK f W c) :
    ∃ c' j, Exec P W ztkbl c c' j ∧ j = 17 ∧
      c'.nreg 50210 = c.nmem ztgre ∧
      FrameB Bidx c c' := by
  zuboy
  obtain ⟨c₁, j₁, e₁, hj₁, v₁, f₁⟩ := nfRd_exec (P := P) 5 5 f c hw h0
  have g : ∀ r, Bidx r = false → c₁.nreg r = c.nreg r := f₁.1
  zuesu
  have e₂ := Exec.constN (P := P) e₁.wb_right 50100 7 by_omega
  have e₃ := Exec.addN (P := P) e₂.wb_right 50100 50200 50100 (by
    simp only [upd_same, upd_other _ _ _ ztddi]
    rw [g 50200 by_decide]; omega)
  have e₄ := Exec.loadN (P := P) e₃.wb_right 50101 50100
  have e₅ := Exec.addN (P := P) e₄.wb_right 50101 50101 50210 (by
    simp only [upd_same, upd_other _ _ _ ztfck,
      upd_other _ _ _ ztfcj,
      upd_other _ _ _ ztddi]
    rw [g 50200 by_decide, m₁, v₁]; omega)
  have e₆ := Exec.addN (P := P) e₅.wb_right 50101 50101 50202 (by
    simp only [upd_same, upd_other _ _ _ ztfck,
      upd_other _ _ _ ztfcj,
      upd_other _ _ _ ztddi,
      upd_other _ _ _ ztkxi,
      upd_other _ _ _ ztkxh]
    zunjg; omega)
  zuffm
  have ex : Exec P W ztkbl c _ (j₁ + (1 + (1 + (1 + ztxjy)))) :=
    .seq e₁ ztyoh
  refine ⟨_, _, ex, by_omega, ?_, exec_frameB ex (wr_nfLst f)⟩
  simp only [upd_same, upd_other _ _ _ ztfck,
    upd_other _ _ _ ztfcj,
    upd_other _ _ _ ztddi,
    upd_other _ _ _ ztkxi,
    upd_other _ _ _ ztkxh]
  zunjg
end
end SweepPrim
end Chazelle.Core
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc WalkEmbed
@[expose] public section
theorem off_pos (M : Model) (Q : Polygon) {g : ℕ} (hg : g < M.W.n) {x : WPos}
    (hx : x.edge < M.W.n) (h0 : 0 ≤ M.param Q x) (h1 : M.param Q x < 1) :
    off M.W.n g ztbys = dOf M.W.n g x.edge + M.param Q x :=
  off_key' hg hx h0 h1
theorem dOf_inj {n g p q : ℕ} (hg : g < n) (hp : p < n) (hq : q < n) (h : dOf n g p = dOf n g q) :
    p = q := by
  rw [← add_dOf hg hp, ← add_dOf hg hq, h]

/-- **The order of the offsets** of two proper positions. -/
theorem off_lt_iff (M : Model) (Q : Polygon) {g : ℕ} (hg : g < M.W.n) {x y : WPos}
    (hx : x.edge < M.W.n) (hx0 : 0 ≤ M.param Q x) (hx1 : M.param Q x < 1)
    (hy : y.edge < M.W.n) (hy0 : 0 ≤ M.param Q y) (hy1 : M.param Q y < 1) :
    off M.W.n g ztbys < off M.W.n g ztfof ↔
      dOf M.W.n g x.edge < dOf M.W.n g y.edge ∨
        ztkhe := by
  rw [off_pos M Q hg hx hx0 hx1, off_pos M Q hg hy hy0 hy1]
  constructor
  · zuq
    rcases lt_trichotomy (dOf M.W.n g x.edge) (dOf M.W.n g y.edge) with h' | h' | h'
    · omega
    · refine Or.inr ⟨dOf_inj hg hx hy h', ?_⟩
      simp_all
    · exfalso
      have : (dOf M.W.n g y.edge : ℝ) + 1 ≤ dOf M.W.n g x.edge := by exact_mod_cast h'
      linarith
  · zuczb
    · have : (dOf M.W.n g x.edge : ℝ) + 1 ≤ dOf M.W.n g y.edge := by exact_mod_cast h
      linarith
    simp_all

/-- The parameters of two positions on one edge compare like their keys. -/
theorem param_lt_iff_same_edge (M : Model) (Q : Polygon) {x y : WPos} (he : x.edge = y.edge) :
    M.param Q x < M.param Q y ↔
      (dirCode M x.edge = 1 ∧ M.hgtY Q x < M.hgtY Q y) ∨
        (dirCode M x.edge = 2 ∧ M.hgtY Q y < M.hgtY Q x) := by
  by_cases hh : (M.wa x.edge).2 = (M.wb x.edge).2
  · have hy : (M.wa y.edge).2 = (M.wb y.edge).2 := by_simp_all
    rw [Model.param_horizontal hh, Model.param_horizontal hy]
    have : dirCode M x.edge = 0 := by unfold dirCode; simp_all
    simp_all
  · have hk := Model.key_lt_key_iff_of_same_edge (Q := Q) he hh
    zuckv
    rw [he, add_lt_add_iff_left] at hk
    zvndl at hk
    zujja
    unfold dirCode
    grind

/-! ## The machine -/

/-- The height of the position `(50201, 50202)` as a symbolic point in `50130`: the tour vertex
`e - 6` for the code `0`, the vertex `h - 1` of `Q` otherwise. -/
def yLoadX : Stmt :=
  .ifLtN 50202 50032 (.seq ztbdp ztkgf)
    (block [.constN 50130 0, .subN 50131 50202 50032])
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
theorem yLoadX_exec
    (hE : CEnv P W H C c) {e h : ℕ} (he : c.nreg 50201 = e) (hh : c.nreg 50202 = h)
    (h0 : h = 0 → 6 ≤ e ∧ e < 2 * C.m + 7) (hhn : h ≤ P.n) :
    ∃ c' k, Exec P W yLoadX c c' k ∧ k ≤ 27 * H.length + 45 ∧ CEnv P W H C c' ∧
      ztegn ∧
      (∀ r, 50130 ≤ r → r < 50139 → (r < 50130 ∨ 50132 < r) → c'.nreg r = c.nreg r) ∧
      ∃ s : SymPt, SymPtIn c' 50130 s ∧ s.Lt P.n ∧
        (s.eval zta).2 = (chainModel C).hgtY zta ztcq := by
  zuyv
  unfold yLoadX
  zujtb
  · zudxv

    have e₁ := Exec.subN (P := P) hw 50120 50201 50081
    zumz
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
      ztnuu by_omega (dst := 50130) by_norm_num
    refine ⟨c₂, _, .ifLtN_true ztdcg ztvqc, by_omega, hE₂,
      fun r hr => ?_, fun r h1 h2 h3 => ?_, sp, isp, lsp, ?_⟩
    · rw [f₂.1 r (by first | (simp [Btv, Btvi, Bhost]; omega))]
      simp only; rw [upd_other _ _ _ by_omega]
    · rw [f₂.1 r (by first | (simp [Btv, Btvi, Bhost]; omega))]
      simp only; rw [upd_other _ _ _ by_omega]
    · zudav
  · zumjq
    exec_block
    all_goals try omega
    refine ⟨by_omega, ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_, .vtx _, ⟨by config_simp,
      ?_⟩, by show h - 1 < P.n; omega, ?_⟩
    · exact hE.keep ‹_› rfl (fun r hr => by
        zujs
        zvmwf; split_ifs <;> first | rfl | omega)
    · zubd
    · zubd
    · config_simp; rw [hh, hE.r32]
    · zulr
      rfl

/-- The height of the position `(50203, 50204)` as a symbolic point in `50136`: the tour vertex
`e - 6` for the code `0`, the vertex `h - 1` of `Q` otherwise. -/
def yLoadY : Stmt :=
  .ifLtN 50204 50032 (.seq (.instr (.subN 50120 50203 50081)) ztkgg)
    (block [.constN 50136 0, .subN 50137 50204 50032])
theorem yLoadY_exec
    (hE : CEnv P W H C c) {e h : ℕ} (he : c.nreg 50203 = e) (hh : c.nreg 50204 = h)
    (h0 : h = 0 → 6 ≤ e ∧ e < 2 * C.m + 7) (hhn : h ≤ P.n) :
    ∃ c' k, Exec P W yLoadY c c' k ∧ k ≤ 27 * H.length + 45 ∧ CEnv P W H C c' ∧
      ztegn ∧
      (∀ r, 50130 ≤ r → r < 50139 → (r < 50136 ∨ 50138 < r) → c'.nreg r = c.nreg r) ∧
      ∃ s : SymPt, SymPtIn c' 50136 s ∧ s.Lt P.n ∧
        (s.eval zta).2 = (chainModel C).hgtY zta ztcq := by
  zuyv
  unfold yLoadY
  zujtb
  · zudxv

    have e₁ := Exec.subN (P := P) hw 50120 50203 50081
    zumz
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
      ztnuu by_omega (dst := 50136) by_norm_num
    refine ⟨c₂, _, .ifLtN_true ztdcg ztvqc, by_omega, hE₂,
      fun r hr => ?_, fun r h1 h2 h3 => ?_, sp, isp, lsp, ?_⟩
    · rw [f₂.1 r (by first | (simp [Btv, Btvi, Bhost]; omega))]
      simp only; rw [upd_other _ _ _ by_omega]
    · rw [f₂.1 r (by first | (simp [Btv, Btvi, Bhost]; omega))]
      simp only; rw [upd_other _ _ _ by_omega]
    · zudav
  · zumjq
    exec_block
    all_goals try omega
    refine ⟨by_omega, ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_, .vtx _, ⟨by config_simp,
      ?_⟩, by show h - 1 < P.n; omega, ?_⟩
    · exact hE.keep ‹_› rfl (fun r hr => by
        zujs
        zvmwf; split_ifs <;> first | rfl | omega)
    · zubd
    · zubd
    · config_simp; rw [hh, hE.r32]
    · zulr
      rfl

/-- Output two bits. -/
def offOut (a b : ℕ) : Stmt := block [.constN 50210 a, .constN 50211 b]

/-- The height comparison on one walk edge: the two height bits, swapped for a descending edge. -/
def offHgt : Stmt :=
  .seq yLoadX (.seq yLoadY (.seq (kbit 50130 50136 50130 1 50150)
    (.seq (kbit 50136 50130 50136 1 50151)
      (.ifLtN 50032 10502 ztksj
        ztksi))))

/-- Both positions on one walk edge: its direction code, then `offHgt` unless horizontal. -/
def offSame : Stmt :=
  .seq ztfex (.seq dirAt (.ifLtN 10502 50032 (offOut 0 0) offHgt))

/-- The rotated edge indices `50142`, `50144` (with `50143 = n - g`). -/
def offHead : Stmt :=
  .seq (block [.addN 50140 50053 50053, .addN 50140 50140 50081, .addN 50140 50140 50032,
      .subN 50143 50140 50205])
    (.seq (candR 50201 50205 50143 50142) (candR 50203 50205 50143 50144))

/-- **`offCmp`** (positions `(50201, 50202)`, `(50203, 50204)`, base vertex `50205`): the bits of
`off x < off y` (`50210`) and `off y < off x` (`50211`). -/
def offCore : Stmt :=
  .seq offHead (.ifLtN 50142 50144 (offOut 1 0) (.ifLtN 50144 50142 (offOut 0 1) offSame))

/-- **The primitive `offCmp`.** -/
def offCmp : Stmt := .seq pHead offCore
theorem wr_offCmp : wr Bprim offCmp = true := by_decide

/-- The machine offset of a walk vertex. -/
theorem dOf_eq {n g p : ℕ} (hg : g < n) (hp : p < n) :
    (if p < g then p + ztodp else p - g) = dOf n g p := by
  zujqj
  zus
  · zupd
  · zucub

/-- The input condition of `offCmp`: two proper positions of the walk and a walk vertex; a
position with height code `0` is a vertex of the tour or of the up-slit edge (`6 ≤ e`); the walk
indices within the word bound. -/
def OffIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧ c.nreg 50203 < (chainModel C).W.n ∧
    c.nreg 50205 < (chainModel C).W.n ∧
    ProperPos ztc zta P.n ztbce ∧
    ProperPos ztc zta P.n ztrbj ∧
    (c.nreg 50202 = 0 → 6 ≤ c.nreg 50201) ∧ (c.nreg 50204 = 0 → 6 ≤ c.nreg 50203) ∧
    2 * C.m + 7 ≤ W

/-- The output condition of `offCmp`. -/
def OffOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  let M := chainModel C
  let ox := off M.W.n ztvik (M.key zta ztbce)
  let oy := off M.W.n ztvik (M.key zta ztrbj)
  BitIs c' 50210 (ox < oy) ∧ BitIs c' 50211 (oy < ox)
theorem offOut_exec (hw : WordsBounded W c) {a b : ℕ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hW : 1 ≤ W) {p q : Prop} (hp : a = 1 ↔ p) (hq : b = 1 ↔ q) :
    ∃ c' k, Exec P W (offOut a b) c c' k ∧ k = 2 ∧ BitIs c' 50210 p ∧ BitIs c' 50211 q := by
  unfold offOut
  exec_block
  all_goals try omega
  trivial

/-- **Contract of `offCmp`** (at most `11000` steps). -/
theorem offCmp_meets : Meets offCmp primBands (PrimPre OffIn) (PrimPost OffOut)
    (fun _ _ => 11000) := by
  refine prim_meets by_simp_all wr_offCmp ?_
  intro P W H C c₀ c _hC hE ⟨hx, hy, hg, ⟨hx0, hx1, hxn⟩, ⟨hy0, hy1, hyn⟩, hx6, hy6, hWm⟩ hinp
  unfold OffOut
  zubvt
  zuhq

  zucwu
  have i04 := hinp 50204 by_norm_num by_norm_num
  have i05 := hinp 50205 by_norm_num by_norm_num
  set px := c₀.nreg 50201
  set qx := c₀.nreg 50202
  set py := c₀.nreg 50203
  set qy := c₀.nreg 50204
  set g := c₀.nreg 50205
  zubio
  have hn : ztcri := C.sideWalk_n _
  zubgf
  zuol
  set x : WPos := zteyw
  set y : WPos := ⟨py, qy⟩
  have hlt := off_lt_iff M _ hg hx hx0 hx1 hy hy0 hy1
  have hgt := off_lt_iff M _ hg hy hy0 hy1 hx hx0 hx1
  change _ ↔ dOf M.W.n g px < dOf M.W.n g py ∨ (px = py ∧ _) at hlt
  change _ ↔ dOf M.W.n g py < dOf M.W.n g px ∨ (py = px ∧ _) at hgt
  -- the rotated edge indices
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.addN 50140 50053 50053,
      .addN 50140 50140 50081, .addN 50140 50140 50032, .subN 50143 50140 50205]) c c₁ k₁ ∧
      k₁ = 4 ∧ (c₁.nreg 50140 = M.W.n ∧ c₁.nreg 50143 = M.W.n - g ∧
        ∀ r, r ≠ 50140 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    zuyv
    exec_block
    all_goals try (config_simp; zunkz; omega)
    all_goals try (config_simp; rw [hE.r53, hE.r81]; omega)
    all_goals try (config_simp; rw [hE.r53, hE.r81, hE.r32]; omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => by zungi⟩
    · config_simp; rw [hE.r53, hE.r81, hE.r32, hn]; ring
    · config_simp; rw [hE.r53, hE.r81, hE.r32, hn, i05]; ring_nf
  obtain ⟨q40, q43, r₁⟩ := q
  have hE₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50140 || r == 50143) by_decide).2.2.1
    ztwxf
  obtain ⟨c₂, k₂, e₂, hk₂, v42, r₂⟩ := candR_exec (P := P) (j := 50201) (s := 50205) (d := 50143)
    (dst := 50142) c₁ e₁.wb_right (by
      grind)
  obtain ⟨c₃, k₃, e₃, hk₃, v44, r₃⟩ := candR_exec (P := P) (j := 50203) (s := 50205) (d := 50143)
    (dst := 50144) c₂ e₂.wb_right (by
      grind)
  have d42 : c₃.nreg 50142 = dOf M.W.n g px := by
    rw [r₃ _ by_decide, v42, r₁ _ by_decide by_decide, r₁ _ by_decide by_decide, q43,
      i01, i05, dOf_eq hg hx]
  have d44 : c₃.nreg 50144 = dOf M.W.n g py := by
    rw [v44, r₂ _ by_decide, r₂ _ by_decide, r₂ _ by_decide, r₁ _ by_decide by_decide,
      r₁ _ by_decide by_decide, q43, i03, i05, dOf_eq hg hy]
  have hE₃ := hE₁.keep e₃.wb_right
    (by rw [(exec_frameB e₃ (B := fun r => r == 50144) by_rfl).2.2.1,
      (exec_frameB e₂ (B := fun r => r == 50142) by_rfl).2.2.1])
    (fun r hr => by rw [r₃ r ztbjp,
      r₂ r ztbjp])
  have g3 : ∀ r, 50200 ≤ r → r < 50210 → c₃.nreg r = c₀.nreg r := fun r h1 h2 => by
    grind
  have eH : Exec P W offHead c c₃ _ := e₁.seq (e₂.seq e₃)
  by_cases hd1 : c₃.nreg 50142 < c₃.nreg 50144
  · zuihh
    obtain ⟨c₄, k₄, e₄, hk₄, b0, b1⟩ := offOut_exec c₃ e₃.wb_right (b := 0)
      le_rfl by_omega by_omega (p := off M.W.n g ztwzj < off M.W.n g
        ztxvj) (q := off M.W.n g (M.key (Qof P) y) < off M.W.n g (M.key (Qof P) x))
      by_grind (by
        grind)
    exact ⟨c₄, _, .seq eH ztspe,
      by omega, b0, b1⟩
  have t1 := hd1
  zuihh
  by_cases hd2 : c₃.nreg 50144 < c₃.nreg 50142
  · zuihi
    obtain ⟨c₄, k₄, e₄, hk₄, b0, b1⟩ := offOut_exec c₃ e₃.wb_right (a := 0)
      by_omega le_rfl by_omega (p := off M.W.n g ztwzj < off M.W.n g
        ztxvj) (q := off M.W.n g (M.key (Qof P) y) < off M.W.n g (M.key (Qof P) x))
      (by
        grind)
      by_grind
    exact ⟨c₄, _, .seq eH (.ifLtN_false t1
      ztspe), by_omega, b0, b1⟩
  have t2 := hd2
  zuihi
  -- the same walk edge
  have hpq : px = py := by_grind
  have hlt' : off M.W.n g ztwzj < off M.W.n g ztxvj ↔
      M.param zta x < M.param zta y := by
    grind
  have hgt' : off M.W.n g ztxvj < off M.W.n g ztwzj ↔
      M.param zta y < M.param zta x := by
    grind
  have hpx := param_lt_iff_same_edge M zta (x := x) (y := y) hpq
  have hpy := param_lt_iff_same_edge M zta (x := y) (y := x) hpq.symm
  rw [hlt', hpx]
  rw [hgt', hpy]
  simp only [x, y] at hpq ⊢
  rw [← hpq]
  -- the direction of the edge
  have e₄ := Exec.copyN (P := P) e₃.wb_right 50002 50201
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 50002 _ } with hc₄
  have hE₄ := hE₃.frame (exec_frameB e₄ (B := fun r => r == 50002)
    by_decide) e₄.wb_right by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, hE₅, d₅⟩ := dirAt_exec c₄ hE₄ (e := px)
    (by show upd c₃.nreg 50002 (c₃.nreg 50201) 50002 = px
        zunkc; grind) by_omega
  rw [← hM] at d₅
  have g5 : ∀ r, 50200 ≤ r → r < 50210 → c₅.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [f₅.1 r ztcpm, hc₄]
    zubi
    rw [upd_other _ _ _ by_omega, g3 r h1 h2]
  have hdl := dirCode_le_two M px
  by_cases hd0 : c₅.nreg 10502 < c₅.nreg 50032
  · zuiir
    have h0 : dirCode M px = 0 := by_omega
    obtain ⟨c₆, k₆, e₆, hk₆, b0, b1⟩ := offOut_exec c₅ e₅.wb_right (a := 0) (b := 0)
      by_omega by_omega by_omega
      (p := (dirCode M px = 1 ∧ M.hgtY _ zteyw < M.hgtY _ ztfwu) ∨
        (dirCode M px = 2 ∧ M.hgtY _ ztfwu < M.hgtY _ zteyw))
      (q := (dirCode M px = 1 ∧ M.hgtY _ ztfwu < M.hgtY _ zteyw) ∨
        (dirCode M px = 2 ∧ M.hgtY _ zteyw < M.hgtY _ ztfwu))
      by_omega by_omega
    exact ⟨c₆, _, .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      (.seq e₄ (.seq e₅ (.ifLtN_true (by rw [hE₅.r32, d₅]; omega) e₆))))), by_omega, b0, b1⟩
  have t3 := hd0
  zuiir
  -- the heights
  obtain ⟨c₆, k₆, e₆, hk₆, hE₆, f6a, f6b, sx, ix, lx, vx⟩ := yLoadX_exec c₅ hE₅
    (g5 50201 by_norm_num by_norm_num) (g5 50202 by_norm_num by_norm_num)
    (fun h => ⟨hx6 h, by_omega⟩) hxn
  obtain ⟨c₇, k₇, e₇, hk₇, hE₇, f7a, f7b, sy, iy, ly, vy⟩ := yLoadY_exec c₆ hE₆
    (e := px) (h := qy)
    ((f6a _ by_omega).trans ((g5 50203 by_norm_num by_norm_num).trans hpq.symm))
    ((f6a _ by_omega).trans (g5 50204 by_norm_num by_norm_num))
    (fun h => ztufy) hyn
  have ix₇ := symPtIn_of_eq ix fun j h1 h2 => f7b j by_omega by_omega
    by_omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b₈, t₈⟩ := kbit_exec (op := 1) (dst := 50150) hE.hG hW c₇
    e₇.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lx ly lx
    ix₇ iy ix₇
  have ix₈ := symPtIn_keep ix₇ f₈ by_decide
  have iy₈ := symPtIn_keep iy f₈ by_decide
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b₉, t₉⟩ := kbit_exec (op := 1) (dst := 50151) hE.hG hW c₈
    e₈.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num ly lx ly
    iy₈ ix₈ iy₈
  have p10502 : c₉.nreg 10502 = dirCode M px := by
    rw [f₉.1 _ by_decide, f₈.1 _ by_decide, f7a _ by_omega, f6a _ by_omega, d₅]
  have p32 := (hE₇.frame f₈ e₈.wb_right by_decide |>.frame f₉
    e₉.wb_right by_decide).r32
  have B50 : BitIs c₉ 50150 (M.hgtY zta zteyw < M.hgtY zta ztfwu) := by
    have := BitIs.keep ⟨b₈, t₈⟩ f₉ by_decide
    zuipc

  have B51 : BitIs c₉ 50151 (M.hgtY zta ztfwu < M.hgtY zta zteyw) := by
    have : BitIs c₉ 50151 _ := ⟨b₉, t₉⟩
    zuipc

  zujaj
  by_cases hd2' : c₉.nreg 50032 < c₉.nreg 10502
  · zuima
    have h2 : dirCode M px = 2 := by_omega
    obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, q⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.copyN 50210 50151,
        .copyN 50211 50150]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧ c₁₀.nreg 50210 = c₉.nreg 50151 ∧
        c₁₀.nreg 50211 = c₉.nreg 50150 := by
      exec_block; simp
    zucie
    have eF : Exec P W (.ifLtN 50032 10502 _
        ztksi) c₉ c₁₀ _ := .ifLtN_true by_omega e₁₀
    have eAll : ztpjs := .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      ztejz))
    refine ztkkj
    · refine (B51.of_eq q10).congr ?_; zvmxx; simp
    · refine (B50.of_eq q11).congr ?_; zvmxx; simp
  · zuima
    have h1 : dirCode M px = 1 := by_omega
    obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, q⟩ : ∃ c₁₀ k₁₀, Exec P W (block [.copyN 50210 50150,
        .copyN 50211 50151]) c₉ c₁₀ k₁₀ ∧ k₁₀ = 2 ∧ c₁₀.nreg 50210 = c₉.nreg 50150 ∧
        c₁₀.nreg 50211 = c₉.nreg 50151 := by
      exec_block; simp
    zucie
    have eF : Exec P W (.ifLtN 50032 10502 ztksj
        _) c₉ c₁₀ _ := .ifLtN_false by_omega e₁₀
    have eAll : ztpjs := .seq eH (.ifLtN_false t1 (.ifLtN_false t2
      ztejz))
    refine ztkkj
    · refine (B50.of_eq q10).congr ?_; zvmwp; simp
    · refine (B51.of_eq q11).congr ?_; zvmwp; simp
end
end SweepPrim
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCross freeIn regionsIn
  IsHChordIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
namespace Sweep
def Genuine (C : Chain) (a : Point) (σ τ : ℝ) : Prop :=
  0 < τ ∧ (∀ s, 0 < s → s < τ → rayPt a σ s ∈ C.dom) ∧ rayPt a σ τ ∉ C.dom

/-- **An arrival position** of the ray in direction `σ` at the point `w`: a walk position of `w`
whose left sector contains the points just before `w` on the ray. -/
def Arrival (W : Polygon) (w : Point) (σ : ℝ) (p : ℕ) (t : ℝ) : Prop :=
  p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t = w ∧ sideLeft W p t (rayPt w (-σ) 1)

/-- A genuine hit is the first hit of the chain. -/
theorem genuine_iff (C : Chain) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {τ : ℝ} : Genuine C a σ τ ↔ Merge.FreeAt C a σ ∧ C.hitParam a σ = τ := by
  constructor
  · rintro ⟨h0, hin, hout⟩
    have hfree : Merge.FreeAt C a σ := by
      filter_upwards [Ioo_mem_nhdsGT h0] with s hs
      simp_all
    zuknu
    zuein
    grind
  · rintro ⟨hfree, rfl⟩
    zuein
    tauto
section ChainModel
variable (C : Chain)

/-! ## Soundness -/

/-! ## Completeness -/

/-- **A genuine hit has an arrival position.** -/
theorem arrival_exists (hP : C.P.Simple) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine C a σ τ) :
    ∃ p t, Arrival (chainModel C).W ztiu σ p t := by
  obtain ⟨hT, hdom, hwD⟩ := hg
  set T := τ
  set w := rayPt a σ T with hw
  have hback : ∀ s, rayPt w (-σ) s = rayPt a σ ztctq := fun s => rayPt_back a σ T s
  have hzR : |a.2| < C.radius := by
    have := C.dom_subset_box ztxoe
    zugie
  have he : ztdea := by
    zudjj
    · zulpb

      · zuum

        zueek
        zusv
        zuesq

        have h1 : |(rayPt a σ ztbpt).1| < C.radius := hbox.1
        have h2 : |w.1| ≤ |(rayPt a σ ztbpt).1| + ε := by
          have e : w.1 = (rayPt a σ ztbpt).1 + σ * ε := by simp [hw, rayPt]; ring
          zui
          zuxs

        grind
      · zube

        tauto
    simp_all
  zufua
  have hee : ztwym := by
    grind
  have hopen : ztbajt := by
    zugg
    have e : lerp w ztwmv s = rayPt a σ ztxvx := by
      zubvk
    zui
    zuhct
  obtain ⟨p, t, hp, ht, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee by_simp hopen he
  refine ⟨p, t, hp, ht, ht1, hpt, ?_⟩
  have hl' : ztxja := by
    rw [show sidePt (chainModel C).W p t = w from hpt]; exact hl
  have := (sideLeft_rayPt_iff _ p t (-σ) hT2 one_pos).1 hl'
  rw [show sidePt (chainModel C).W p t = w from hpt] at this
  omega

/-! ## The arriving ray at a cut key -/

/-- A horizontal ray from `w` either starts along an admissible chord or eventually avoids it. -/
theorem ray_chord_dichotomy {e : Set Point} (he : e ∈ Merge.augChords C) (w : Point) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w τ s ∈ e) ∨ (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w τ s ∉ e) := by
  zuvj
  zubwk
  by_cases hy : w.2 = y
  swap
  · right
    exact Filter.Eventually.of_forall fun s hs => hy (by simpa [rayPt] using hs.1)
  zujj
  · by_cases h1 : w.1 < l
    · right
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < l - w.1 by linarith)] with s hs hm
      have := hm.2.1; zvmxf at this; grind
    · by_cases h2 : w.1 < r
      · left
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - w.1 by linarith)] with s hs
        zuekg
      · zuhjf

        have := hm.2.2; zvmxf at this
        grind
  · by_cases h1 : r < w.1
    · right
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < w.1 - r by linarith)] with s hs hm
      have := hm.2.2; zvmxf at this; grind
    · by_cases h2 : l < w.1
      · left
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < w.1 - l by linarith)] with s hs
        zuekg
      · zuhjf

        have := hm.2.1; zvmxf at this
        grind

/-- The determinant of a walk edge against a horizontal shift of one of its points. -/
theorem det_lerp_shift (u v : Point) (t α : ℝ) :
    det u v ((lerp u v t).1 + α, (lerp u v t).2) = -α * ztgv := by
  simp only [det, Geometry.lerp_fst, Geometry.lerp_snd]; ring

/-- **No cut inside a walk edge under an arriving ray off the chords**: at an arrival position
inside a walk edge, if no chord of the family lies along the arriving ray, the key is not a
cut (a chord attached inside an edge leaves it in the only horizontal direction of the left
half-plane, which is the direction of the arriving ray reversed). -/
theorem not_cut_of_edge (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {w : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hA : Arrival (chainModel C).W w σ p t) (ht0 : 0 < t)
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ e) :
    ¬ (chainModel C).IsCut F ztk := by
  zubkf
  obtain ⟨hp, -, ht1, hpt, hsec⟩ := hA
  rintro ⟨c, hcF, p', t', hAc, hkey⟩
  obtain ⟨hp', ht'0, ht'1, hc', r₀, hr₀, hnear⟩ := hAc
  obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht0.le ht1 ht'0 ht'1 hkey
  have hcA : c ∈ Merge.augChords C := hFam.2.1 hcF
  obtain ⟨y, l, r, hH, -, hceq, -, -⟩ := Merge.augChords_spec hcA
  subst hceq
  zvmxe at hc' hnear
  obtain ⟨hwy, hwl, hwr⟩ := hc'
  have hwD : w ∉ C.dom := by
    zvnbr; exact hM.trace p hp t ht0.le ht1.le
  zund
  set u := (chainModel C).W.vtx p with hu
  set v := (chainModel C).W.vtx ztwkm with hv
  have hwlerp : w = lerp u v t := hpt.symm
  have hedge : ∀ x, sideLeft (chainModel C).W p t x ↔ 0 < det u v x :=
    fun x => Chazelle.Chain.sideLeft_edge hne ztcoy x
  have hshift : ∀ α, det u v (ztqyl : Point) = -α * ztgv := by
    intro α; rw [hwlerp]; exact det_lerp_shift u v t α
  -- the arriving ray reversed is in the left half-plane
  have h1 : 0 < σ * ztgv := by
    have := (hedge _).1 hsec
    have e : rayPt w (-σ) 1 = ((w.1 + -σ, w.2) : Point) := by
      zueob
    rw [e, hshift] at this; linarith
  zubwk
  set δ := min r₀ ztbju / 2 with hδ
  have hδ0 : ztcfy := by
    positivity
  have hδr : δ < r₀ := by have := min_le_left r₀ ztbju; linarith
  have hδl : δ < r - l := by have := min_le_right r₀ ztbju; linarith
  have hdist : ∀ α, |α| = δ → dist (ztqyl : Point) w < r₀ := by
    intro α hα
    zugtz
    zuhpp
    rw [hα, max_eq_left hδ0.le]; omega
  have hno' := fun e he => hno e he
  -- `w` is an end of the chord
  rcases hwl.lt_or_eq with hl | hl
  · rcases hwr.lt_or_eq with hr | hr
    · exact hwD (by rw [show w = (zthla : Point) from Prod.ext rfl hwy]; exact hH.open_mem _ hl hr)
    · -- `w` is the right end: the chord leaves it to the left
      have hx : sideLeft (chainModel C).W p t ((w.1 + -δ, w.2) : Point) :=
        hnear _ ztran
          ztbay
          (hdist _ (by rw [abs_neg, abs_of_pos hδ0]))
      zuijr
      have hσ1 : ztgbc := by
        zur
        · rfl
        · nlinarith
      zubqg

  · -- `w` is the left end: the chord leaves it to the right
    have hx : sideLeft (chainModel C).W p t ((w.1 + δ, w.2) : Point) :=
      hnear _ ztran
        ztbay
        (hdist _ (abs_of_pos hδ0))
    zuijr
    have hσ1 : ztgbb := by
      zur
      · nlinarith
      · rfl
    zubqg
end ChainModel
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)
namespace Sweep
section ChainModel
variable (C : Chain)

/-- **A ray along an admissible chord from one endpoint** first leaves the domain at the other
endpoint. -/
theorem genuine_along_chord {e : Set Point} (he : e ∈ Merge.augChords C) {z : Point}
    (hze : z ∈ e) (hzD : z ∉ C.dom) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ)
    (hwe : rayPt z σ τ ∈ e) (hwD : rayPt z σ τ ∉ C.dom) : Genuine C z σ τ := by
  zuvj
  obtain ⟨hzy, hzl, hzr⟩ := hze
  obtain ⟨-, hwl, hwr⟩ := hwe
  zvogc at hwl hwr
  have hend : ∀ x : ℝ, l ≤ x → x ≤ r → (ztjw : Point) ∉ C.dom → x = l ∨ x = r := by
    zuhgx
    zuff
    · zudt
      · exact absurd ztrrl hx
      simp_all
    simp_all
  have hz := hend z.1 hzl hzr by_grind
  have hw := hend (z.1 + σ * τ) hwl hwr (by
    rw [show ((z.1 + σ * τ, y) : Point) = rayPt z σ τ from
      point_ext by_simp by_simp_all]; omega)
  refine ⟨hτ, fun s h0 h1 => ?_, hwD⟩
  rw [show rayPt z σ s = ((z.1 + σ * s, y) : Point) from
    point_ext by_simp by_simp_all]
  zubwk
  apply hH.open_mem <;> rcases hσ with rfl | rfl <;> rcases hz with hz | hz <;>
    rcases hw with hw | hw <;> nlinarith
end ChainModel
section Junction
variable (J : Merge.Junction)
end Junction
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open WalkEmbed
namespace Sweep
section Junction
variable (J : Merge.Junction)

/-- In case G, the vertex after the gap is the top of `C₁`. -/
theorem left_split_top (h : 0 < lδ J) :
    (chainModel J.left).W.vtx ((6 + tpos J.left J.m₁ + ztjzy) %
      (chainModel J.left).W.n) = J.left.top := by
  zucmz
  have e : lL1 J + lδ J = 2 * J.left.m - tpos J.left J.m₁ + 7 := by
    unfold lL1 lδ at *
    grind
  rw [e, show 6 + tpos J.left J.m₁ + (2 * J.left.m - tpos J.left J.m₁ + 7) =
    6 + tpos J.left J.m₁ + ztnfc + 7 by omega]
  exact walk_box J.left J.m₁ 7 le_rfl
end Junction
/-! ## Lemma (Q) -/
section Query
variable (J : Merge.Junction)
end Query
section Answer
variable (J : Merge.Junction)
end Answer
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Merge (FreeAt)
namespace Sweep
section ChainModel
variable (C : Chain)

/-- **The cases at a cut walk vertex** for a ray arriving (equivalently, its reverse leaving)
off the chords: the chords attached there avoid the ray, and one of the two turning conditions
holds (`vertex_cases_of_genuine` without the genuine hypothesis, given `1 ≤ p`). -/
theorem vertex_cases (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {w : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {p : ℕ} (hA : Arrival (chainModel C).W w σ p 0) (hp1 : 1 ≤ p)
    (hcut : (chainModel C).IsCut F ztmm)
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∈ e) :
    (∀ c ∈ F, SideAttach (chainModel C).W c p 0 →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c) ∧
      (0 < sideCross ((chainModel C).W.vtx ztwkm -
          (chainModel C).W.vtx p) ((-σ, 0) : Point) ∨
        0 < sideCross ((-σ, 0) : Point) ((chainModel C).W.vtx
          ztcrw - (chainModel C).W.vtx p)) := by
  zudyl
  zubl

  zukv
  obtain ⟨hp, -, -, hpt, hsec⟩ := hA
  have hnot : ∀ c ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w (-σ) s ∉ c := by
    zung
    rcases ray_chord_dichotomy C ztlz w hnσ with h | h
    · grind
    omega
  zulos
  -- the arriving ray reversed lies in a region
  obtain ⟨r₀, hr₀, hsf⟩ := sector_free hM hF hfin hp le_rfl one_pos
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p 0 (rayPt w (-σ) s) := by
    zugg
    have h1 : sideLeft (chainModel C).W p 0 (rayPt ztcwj (-σ) 1) := by
      simp_all
    have := (sideLeft_rayPt_iff _ p 0 _ one_pos hs).1 h1
    simp_all
  have hall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ c ∈ F, rayPt w _ s ∉ c :=
    (hfin.eventually_all).2 hnot
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hall.and (Ioo_mem_nhdsGT hr₀))
  zucmu
  have hfree : ∀ s ∈ Ioo (0 : ℝ) δ, rayPt w (-σ) s ∈ freeIn C.dom F := by
    zugg
    obtain ⟨hc, hs'⟩ := hsub hs
    have hball : rayPt w (-σ) s ∈ ball ztcwj r₀ := by
      rw [hpt, mem_ball, dist_rayPt _ hnσ hs.1.le]; grind
    refine ⟨(hsf _ hball by_grind).1, ?_⟩
    grind
  set z := rayPt w (-σ) ztbfe with hz
  have hzfree : z ∈ freeIn C.dom F := by_grind
  set U := connectedComponentIn (freeIn C.dom F) z with hU
  have hUreg := Chazelle.Chain.mem_regionsIn hzfree
  have hconn : IsPreconnected ((fun s => rayPt w (-σ) s) '' Ioo (0 : ℝ) δ) :=
    isPreconnected_Ioo.image _ (by unfold rayPt; fun_prop)
  have hsubU : (fun s => rayPt w _ s) '' Ioo (0 : ℝ) δ ⊆ U :=
    hconn.subset_connectedComponentIn ⟨δ / 2, by_grind, rfl⟩
      (by rintro _ ⟨s, hs, rfl⟩; grind)
  have happ : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztcwj (-σ) s ∈ U := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with s hs
    zvmxe; exact by_grind
  have hsecv : ∀ s > 0, sideLeft (chainModel C).W p 0
      (rayPt ztcwj (-σ) s) := by
    grind
  exact ((approach_vertex hM hF hfin hUreg hp hp1 hnσ hsecv happ).2 hcut).1

/-- **A query ray is free in its own chain**: a ray leaving a walk position into its left sector
starts in the domain. -/
theorem freeAt_of_leave (hP : C.P.Simple) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t zthzp) :
    FreeAt C z σ := by
  zudyl
  obtain ⟨r, hr, hsf⟩ := sector_free hM (F := ∅) ztzi finite_empty hp ht ht1
  zuhuo
  have hsec' : sideLeft (chainModel C).W p t (rayPt ztic σ s) := by
    zubil
    have h1 : ztwnr := by
      simp_all
    have := (sideLeft_rayPt_iff _ p t σ one_pos hs.1).1 h1
    simp_all
  have hball : rayPt ztic σ s ∈ ball ztic r := by
    rw [mem_ball, dist_rayPt _ hσ hs.1.le]; simp_all
  have := (hsf _ hball hsec').1
  rwa [hpt] at this

/-- **The cases of a ray leaving a walk position** (a query in its own chain): along a chord of
the family attached there; or the key is not a cut (then `ray_mem_region_of_arc` applies to the
arc around it); or a cut walk vertex `p ≥ 1` whose chords avoid the ray, with one of the two
turning conditions (then `ray_mem_region_after` / `ray_mem_region_before` apply). -/
theorem leave_cases (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t zthzp)
    (hzR : |z.2| < C.radius) :
    (∃ e ∈ F, SideAttach (chainModel C).W e p t ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) ∨
      ¬ (chainModel C).IsCut F ztk ∨
      (t = 0 ∧ 1 ≤ p ∧ (∀ c ∈ F, SideAttach (chainModel C).W c p 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∉ c) ∧
        (0 < sideCross ((chainModel C).W.vtx ztwkm -
            (chainModel C).W.vtx p) ((σ, 0) : Point) ∨
          0 < sideCross (ztwn : Point) ((chainModel C).W.vtx
            ztcrw - (chainModel C).W.vtx p))) := by
  zudyl
  zuglo
  zukv
  have hA : Arrival (chainModel C).W z (-σ) p t := ⟨hp, ht, ht1, hpt, by_simp_all⟩
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p t ztbwc := by
    zugg
    have h1 : ztwnr := by
      simp_all
    have := (sideLeft_rayPt_iff _ p t σ one_pos hs).1 h1
    simp_all
  have hzD : ztsnn := by zvnbr; exact hM.trace p hp t ht ht1.le
  by_cases hch : ∃ e ∈ F, ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e
  · left
    obtain ⟨e, he, hev⟩ := hch
    refine ⟨e, he, ?_, hev⟩
    have heA := hF he
    obtain ⟨y, l, r, hH, -, rfl, -, -⟩ := Merge.augChords_spec heA
    zubwk
    zubrt
    zufhk
    have hzpt : ∀ x : ℝ, x = z.1 → (ztjw : Point) = z := by_grind
    refine ztfwq
    · zubil
      zur
      · have hzl : ztlaz := by
          zubq

          obtain ⟨s, hs, hs'⟩ := (hev.and ztbyk).exists
          have := hs.2.1; zvmxf at this; grind
        have hzr : ztlbk := by
          have := hs₁.2.2; zvmxf at this; grind
        tauto
      · have hzr : ztlbk := by
          zubq

          obtain ⟨s, hs, hs'⟩ := (hev.and ztbyl).exists
          have := hs.2.2; zvmxf at this; grind
        have hzl : ztlaz := by
          have := hs₁.2.1; zvmxf at this; grind
        tauto
    · zvmxe at hxz
      zugpy
      zur
      · -- σ = 1: `z` is the left end
        have hzl : z.1 = l := by
          have h1 : ztlaz := by
            zubq

            obtain ⟨s, hs, hs'⟩ :=
              (hev.and ztbyk).exists
            have := hs.2.1; zvmxf at this; grind
          have h2 : z.1 < r := by
            have := hs₁.2.2; zvmxf at this; grind
          zucop
          · exact absurd (by zuogh; exact hH.open_mem _ h h2) hzD
          simp_all
        have hxl' : l < x.1 := by
          grind
        have e : ztlyy := point_ext by_simp_all by_simp_all
        grind
      · -- σ = -1: `z` is the right end
        have hzr : z.1 = r := by
          have h1 : ztlbk := by
            zubq

            obtain ⟨s, hs, hs'⟩ :=
              (hev.and ztbyl).exists
            have := hs.2.2; zvmxf at this; grind
          have h2 : l < z.1 := by
            have := hs₁.2.1; zvmxf at this; grind
          zucop
          · exact absurd (by zuogh; exact hH.open_mem _ h2 h) hzD
          omega
        have hxr' : x.1 < r := by
          grind
        have e : ztjat :=
          point_ext by_simp_all by_simp_all
        grind
  · right
    have hch' : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e :=
      by simp_all
    have hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z (-(-σ)) s ∈ e := by
      simp_all
    zugjl
    · right
      zubhu
      · exact absurd hcut (not_cut_of_edge C hP hFam hnσ hA ht0 hno)
      · zudlw
        have hp1 : 1 ≤ p := by
          zuccr
          zuken
          subst hp0
          have h0 : ztdxs := by
            zudtj
          have := congrArg Prod.snd ztqqn
          zudbt
          grind
        obtain ⟨h1, h2⟩ := vertex_cases C hP hFam hnσ hA hp1 hcut hno
        refine ⟨rfl, hp1, by_simp_all, ?_⟩
        simpa using h2
    simp_all
end ChainModel
section Junction
variable (J : Merge.Junction)
end Junction
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft freeIn regionsIn
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open WalkEmbed
namespace Sweep
section Bracket
variable (J : Merge.Junction)

/-- **Brackets have no label.**  Let a chord `e` of `F₂⁺` be attached at two positions of the
`C₁` part (offsets from the base of the right stretch at least the length of the stretch), and let
a non-cut position inside a walk edge, strictly between them in offsets, face the region `G`.
Then `G` has no label. -/
theorem no_label_of_bracket (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbf)
    (hBo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd)
    {px : ℕ} {tx : ℝ} (hpx : px < (chainModel J.whole).W.n) (htx : tx ∈ Ioo (0 : ℝ) 1)
    (hcx : ¬ (chainModel J.whole).IsCut ztbi ztcat)
    (hfx : (chainModel J.whole).Faces px tx G)
    (hbtw : Btw (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbf)
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd)
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcat)) :
    ∀ V, ¬ RLabel J S₂ G V := by
  zudjo
  zuv
  zupo

  have hne := (hC.hM.eq_iff_not_separates hC.hF hC.hfin hG hG hpx zthp htx ht hcx
    hc hfx hf).1 rfl e he
  zudgo

  zucu

  zucii

  have hoy : ztbaol := off_key hg (by have := hC.hL; omega)
    ht.1.le ht.2
  have hyrl : ztfkl := by
    zubfq
    zujcc
  have hxy : ztxcz := by
    zuq
    have := congrArg zttut h
    rw [hoy] at this
    unfold Btw at hbtw
    grind
  zuis

  rw [hoy]
  unfold Btw at hbtw ⊢
  constructor
  · grind
  grind
end Bracket

/-! ## Transition across a fused chord -/
section Transition
variable (J : Merge.Junction)

/-- Two regions containing the points just above (below) an open point of a chord are equal. -/
theorem region_eq_of_side {M : Model} {F : Set ztf} {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {z : Point} {τ : ℝ}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ U)
    (h' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ U') : U = U' := by
  zuejp
  rw [Chazelle.Chain.regionsIn_eq_component hU h1, Chazelle.Chain.regionsIn_eq_component hU' h2]

/-- A region containing the points just above (below) a point of a chord in the domain touches
the chord (it is an exit chord of the region). -/
theorem touches_of_side {D : Set Point} {c U : Set Point} {z : Point} (hz : z ∈ c) (hzD : z ∈ D)
    {τ : ℝ} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ U) :
    Chazelle.Chain.TouchesIn D c U := by
  refine ⟨z, ztuit, ?_⟩
  have hlim : Tendsto (fun δ : ℝ => ((z.1, z.2 + τ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous (fun δ : ℝ => (ztbfc : Point)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp_all
  exact mem_closure_of_tendsto hlim h
end Transition
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
@[expose] public section
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt hseg)
open Chazelle.Merge (lend rend lend_hseg rend_hseg hseg_inj)
variable (z : Point) (J : Merge.Junction) (Q : Polygon) (i : ℕ)
/-- The point `(z.1 + σ, z.2)` is the ray point at parameter `1`. -/
theorem ray_one (σ : ℝ) : ((z.1 + σ, z.2) : Point) = rayPt z σ 1 := by
  zugyz

/-- **The chord-end queries.** -/
theorem queryOK_ends (r : CRec)
    (hA : r.Attached ztxgp Q)
    (hadm : r.toSet ztxgp Q ∈ (chainModel ztgi).Adm)
    (hh : r.h < Q.n) :
    QueryOK J Q i ztdic ∧ QueryOK J Q i ztdid ∧
      (chainModel ztgi).pos Q r.lpos = lend ztbars ∧
      (chainModel ztgi).pos Q r.rpos = rend ztbars := by
  zukzi
  zubzd
  obtain ⟨y, a, b, hIH, hytop, hc⟩ := hadm
  have hab : ztmua := hIH.lt
  have hdef : r.toSet M Q = hseg (Q.vtx r.h).2 (M.pos Q r.lpos).1 (M.pos Q r.rpos).1 := rfl
  obtain ⟨⟨hpl, htl0, htl1, hml, rl, hrl, hsl⟩, ⟨hpr, htr0, htr1, hmr, rr, hrr, hsr⟩⟩ := hA
  have el : M.pos Q r.lpos = sidePt M.W r.lp ztfog := rfl
  have er : M.pos Q r.rpos = sidePt M.W r.rp zthbi := rfl
  rw [← el] at hml hsl
  rw [← er] at hmr hsr
  have hml' := hml
  rw [hdef] at hml'
  obtain ⟨-, -, hlr⟩ := hml'
  obtain ⟨-, ha, hb⟩ := hseg_inj hlr (hdef.symm.trans hc)
  -- the end points
  have pl : M.pos Q r.lpos = ztdv := by
    zvnmd at hml
    exact Prod.ext (ha) hml.1
  have pr : M.pos Q r.rpos = ztdy := by
    zvnmd at hmr
    exact Prod.ext (hb) hmr.1
  have hL : lend ztkdo = ztdv := by rw [hc, lend_hseg hab.le]
  have hR : rend ztkdo = ztdy := by rw [hc, rend_hseg hab.le]
  -- the sectors
  have secL : sideLeft M.W r.lp ztfog (rayPt zthbj 1 1) := by
    set s := min zttyx ztwsh
    zuiah
    have hx : rayPt zthbj 1 s ∈ r.toSet M Q := by
      rw [hc, pl]; refine ztkw <;> zvmxf <;>
        (have := min_le_right zttyx ztwsh; linarith)
    have hne : rayPt zthbj 1 s ≠ M.pos Q r.lpos := by
      zudig
    have hd : dist (rayPt zthbj 1 s) zthbj < rl := by
      zueww

    have h := hsl _ hx hne hd
    rw [el] at h ⊢
    exact (Sweep.sideLeft_rayPt_iff _ _ _ 1 hs one_pos).1 h
  have secR : sideLeft M.W r.rp zthbi (rayPt zthbk (-1) 1) := by
    set s := min zttyz ztwsh
    zuiah
    have hx : rayPt zthbk (-1) s ∈ r.toSet M Q := by
      rw [hc, pr]; refine ztkw <;> zvmxf <;>
        (have := min_le_right zttyz ztwsh; linarith)
    have hne : rayPt zthbk (-1) s ≠ M.pos Q r.rpos := by
      zudig
    have hd : dist (rayPt zthbk (-1) s) zthbk < rr := by
      zueww

    have h := hsr _ hx hne hd
    rw [er] at h ⊢
    exact (Sweep.sideLeft_rayPt_iff _ _ _ (-1) hs one_pos).1 h
  refine ⟨⟨hpl, by_simp, by_simp_all, htl0, htl1, ?_, ?_⟩,
    ⟨hpr, by_simp, by_simp_all, htr0, htr1, ?_, ?_⟩,
    by simp_all, by_simp_all⟩
  · show (M.pos Q r.lpos).2 ≤ C.top.2
    grind
  · show sideLeft M.W r.lp ztfog ((M.pos Q r.lpos).1 + dirOf 1, (M.pos Q r.lpos).2)
    zukyo
  · show (M.pos Q r.rpos).2 ≤ C.top.2
    grind
  · show sideLeft M.W r.rp zthbi ((M.pos Q r.rpos).1 + dirOf 0, (M.pos Q r.rpos).2)
    zukyo

/-- **Equal chords have equal records** (for attached records of a model with the walk axioms and
a height polygon with distinct vertex heights): the heights fix `h`, the ends fix the points of
the positions, and an admissible chord is attached at most once at each of its points
(`WalkAx.attach_unique`).  So removing duplicate triples removes duplicate chords. -/
theorem rec_eq_of_toSet {M : Model} (hM : WalkAx M) {Q : Polygon} (hQ : DistinctHeights Q)
    {r r' : CRec} (hA : r.Attached M Q) (hA' : r'.Attached M Q) (hadm : r.toSet M Q ∈ M.Adm)
    (hh : r.h < Q.n) (hh' : r'.h < Q.n) (he : r.toSet M Q = r'.toSet M Q) :
    r.h = r'.h ∧ r.lp = r'.lp ∧ r.rp = r'.rp := by
  have hne : (M.pos Q r.lpos).1 ≤ (M.pos Q r.rpos).1 := by
    obtain ⟨⟨-, -, -, hml, -⟩, -⟩ := hA
    exact hml.2.1.trans hml.2.2
  obtain ⟨hy, hl, hr⟩ := hseg_inj hne he
  have hml := hA.1.2.2.2.1
  have hml' := hA'.1.2.2.2.1
  have hmr := hA.2.2.2.2.1
  have hmr' := hA'.2.2.2.2.1
  have el : ∀ (s : CRec), M.pos Q s.lpos = sidePt M.W s.lp (M.param Q s.lpos) := fun _ => rfl
  have er : ∀ (s : CRec), M.pos Q s.rpos = sidePt M.W s.rp (M.param Q s.rpos) := fun _ => rfl
  have pyl : (M.pos Q r.lpos).2 = (Q.vtx r.h).2 := by rw [el]; exact hml.1
  have pyl' : (M.pos Q r'.lpos).2 = (Q.vtx r'.h).2 := by rw [el]; exact hml'.1
  have pyr : (M.pos Q r.rpos).2 = (Q.vtx r.h).2 := by rw [er]; exact hmr.1
  have pyr' : (M.pos Q r'.rpos).2 = (Q.vtx r'.h).2 := by rw [er]; exact hmr'.1
  have hhh : r.h = r'.h := by
    by_contra hne'; tauto
  have ptl : sidePt M.W r.lp ztfog = sidePt M.W r'.lp zttac := by
    grind
  have ptr : sidePt M.W r.rp zthbi = sidePt M.W r'.rp zttad := by
    grind
  have hA'l : SideAttach M.W ztkdo r'.lp zttac := he ▸ hA'.1
  have hA'r : SideAttach M.W ztkdo r'.rp zttad := he ▸ hA'.2
  exact ⟨hhh, (hM.attach_unique hadm hA.1 hA'l ptl).1, (hM.attach_unique hadm hA.2 hA'r ptr).1⟩

/-- The side chains share the ambient polygon of the junction. -/
theorem sideChain_P : (sideChain J i).P = J.P := by
  zulcd

/-- The domain of `C` at heights `≤ top(Cᵢ)` lies in the domain of `Cᵢ`. -/
theorem dom_side {x : Point} (hx : x ∈ J.whole.dom)
    (hx2 : x.2 ≤ (sideChain J i).top.2) : x ∈ (sideChain J i).dom := by
  unfold sideChain at hx2 ⊢
  split_ifs at hx2 ⊢
  · exact Sweep.dom_left J hx hx2
  · exact Sweep.dom_right J hx hx2
theorem lerp_rayPt (σ T s : ℝ) :
    Geometry.lerp z ztxn s = rayPt z σ ztohf := by
  apply Geometry.point_ext <;> zuokw; ring

/-- **A free direction at a point of `Cᵢ` has a departure position** in the walk of `Cᵢ`
(`arrivalPos` finds it): some position at the point has the direction in its left sector. -/
theorem arrival_of_free (hP : J.P.Simple) (i : ℕ) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hf : Merge.FreeAt J.whole z σ) :
    ∃ p t, Sweep.Arrival (chainModel ztgi).W z (-σ) p t := by
  zukzi
  have hPC : C.P.Simple := by rw [sideChain_P]; exact hP
  zublc

  zubat
  have hee : ztrhf := by
    zuq
    zuegg

  have hopen : ztxjb := by
    zugg
    zugwa
    zukam
    have hm : rayPt z σ ztohf ∈ J.whole.dom := hsub ⟨mul_pos hs.1 hT, by
      have := hs.2; zuoxz; nlinarith⟩
    exact dom_side J i hm by_tauto
  obtain ⟨p, t, hp, ht0, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hPC C.sideBeta hee by_simp hopen (Or.inl hz)
  zukev
  have hl' : sideLeft (chainModel C).W p t ztxn := hl
  refine ztiom
  zuduy
  have h1 : ztxrq := by
    simp_all
  have := (Sweep.sideLeft_rayPt_iff _ p t σ hT one_pos).1 h1
  simp_all

/-! ## Queries at points found by `arrivalPos` -/

/-- The parameter of the height code of the start vertex of a walk edge is `0`. -/
theorem param_of_vertex (M : Model) (Q : Polygon) (p h : ℕ) (hy : (Q.vtx h).2 = (M.wa p).2) :
    M.param Q ztdw = 0 := by
  zufde
  simp_all

/-- **A query from a departure position**: a position with the direction `dirOf ρ` in its left
sector (`Sweep.Arrival` for `-dirOf ρ`, as `arrivalPos` reports it), written with the height code
`h + 1` of the point, is a valid sweep query at that point. -/
theorem queryOK_of_arrival {p h ρ : ℕ} {z : Point}
    {t : ℝ} (hA : Sweep.Arrival (chainModel ztgi).W z ztdep p t)
    (hpar : (chainModel ztgi).param Q ztdw = t) (hh : h + 1 ≤ Q.n)
    (hz2 : z.2 ≤ (sideChain J i).top.2) :
    QueryOK J Q i (p, h + 1, ρ) ∧ (chainModel ztgi).pos Q ztdw = z := by
  obtain ⟨hp, ht0, ht1, hpt, hl⟩ := hA
  have hpos : (chainModel ztgi).pos Q ztdw = z := by
    rw [Gran.pos_eq_sidePt]; simp_all
  refine ⟨⟨hp, by_simp, hh, by_simp_all, by_simp_all,
    by simp_all, ?_⟩, hpos⟩
  zubi
  rw [hpos, hpar, ray_one]
  simp_all
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
open Chazelle.Merge (lend rend)
@[expose] public section
def endQL (cs : List CRec) : List zte :=
  (List.range ztssj).map fun j =>
    let r := cs.getD ztwm ztrp
    if j % 2 = 0 then ztdic else ztdid
variable (cs : List CRec) {P : Polygon}
/-- The query list is the one of `SweepSpec` (finding S-1). -/
theorem endQL_eq : endQL cs = sweepEndQ cs := rfl
theorem endQL_length : (endQL cs).length = 2 * cs.length := by
  simp [endQL]
theorem endQL_get {j : ℕ} (hj : j < 2 * cs.length) :
    (endQL cs).getD j ztt =
      let r := cs.getD ztwm ztrp
      if j % 2 = 0 then ztdic else ztdid := by
  simp [endQL, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-- One chord: two queries. -/
def qlBody : Stmt := block [.loadN 70103 70101, .addN 70104 70103 70105,
  .addN 70107 70101 70105, .loadN 70103 70107,
  .storeN ALLOC 70103, .addN ALLOC ALLOC 70105, .storeN ALLOC 70104, .addN ALLOC ALLOC 70105,
  .storeN ALLOC 70105, .addN ALLOC ALLOC 70105,
  .addN 70107 70107 70105, .loadN 70103 70107,
  .storeN ALLOC 70103, .addN ALLOC ALLOC 70105, .storeN ALLOC 70104, .addN ALLOC ALLOC 70105,
  .storeN ALLOC 70108, .addN ALLOC ALLOC 70105,
  .addN 70101 70101 70106, .addN 70102 70102 70105]

/-- The query loop. -/
def qlLoop : Stmt := .whileLtN 70102 70100 qlBody
set_option maxHeartbeats 4000000 in
theorem qlBody_exec {W : ℕ} (c : Config) (hw : WordsBounded W c) {s a : ℕ}
    (h01 : c.nreg 70101 = s) (hA : c.nreg ALLOC = a) (h05 : c.nreg 70105 = 1)
    (h06 : c.nreg 70106 = 5) (h08 : c.nreg 70108 = 0) (hs : s + 5 ≤ W) (ha : a + 6 ≤ W)
    (hi : c.nreg 70102 + 1 ≤ W) (hh : c.nmem s + 1 ≤ W) (hsa : s + 2 < a) :
    ∃ c' k, Exec P W qlBody c c' k ∧ k = 20 ∧ c'.nreg 70101 = s + 5 ∧ c'.nreg ALLOC = a + 6 ∧
      c'.nreg 70102 = c.nreg 70102 + 1 ∧
      (∀ x, (x < a ∨ a + 6 ≤ x) → c'.nmem x = c.nmem x) ∧
      c'.nmem a = c.nmem ztbk ∧ c'.nmem ztdf = c.nmem s + 1 ∧ c'.nmem ztvj = 1 ∧
      c'.nmem (a + 3) = c.nmem ztfp ∧ c'.nmem (a + 4) = c.nmem s + 1 ∧ c'.nmem ztnqo = 0 ∧
      (∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold qlBody
  zubtg
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h01, hA', h05, h06, h08, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h01, hA', h05, h06, h08, ALLOC])
  · have a6' : zteif := a6
    zup

/-- The invariant of the query loop. -/
structure QLI (W K CB LB : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 70102 ≤ K
  cur : c.nreg 70101 = CB + 5 * c.nreg 70102
  alloc : c.nreg ALLOC = LB + 6 * c.nreg 70102
  regs : ∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
    c.nreg r = c₀.nreg r
  low : ∀ a, a < LB → c.nmem a = c₀.nmem a
  done : ∀ i, i < c.nreg 70102 →
    c.nmem ztpzm = c₀.nmem ztbye ∧
    c.nmem ztnmg = c₀.nmem ztblv + 1 ∧ c.nmem ztnmh = 1 ∧
    c.nmem ztnmi = c₀.nmem ztbyf ∧
    c.nmem ztnmj = c₀.nmem ztblv + 1 ∧ c.nmem ztnmk = 0
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
set_option maxHeartbeats 4000000 in
/-- **The query loop.** -/
theorem qlLoop_exec {W K CB LB : ℕ} {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h06 : c₀.nreg 70106 = 5) (h08 : c₀.nreg 70108 = 0)
    (h00 : c₀.nreg 70100 = K) (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB)
    (hh : ∀ i, i < K → c₀.nmem ztblv + 1 ≤ W) (hW : LB + 6 * K ≤ W) (hWK : K + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), QLI W K CB LB c₀ c → c.nreg 70102 + n = K →
      ∃ c' k, Exec P W qlLoop c c' k ∧ k ≤ 22 * n + 2 ∧ 6 * n ≤ k ∧ QLI W K CB LB c₀ c' ∧
        c'.nreg 70102 = K
  | 0, c, hI, hn => ⟨c, 2, .whileLtN_false (by rw [hI.regs 70100 by_decide by_decide
      by_decide by_decide by_decide by_decide, h00]; omega) hI.wb, by_omega, by_omega, hI,
      by omega⟩
  | n + 1, c, hI, hn => by
    obtain ⟨i, hi⟩ : ∃ i, c.nreg 70102 = i := by_simp_all
    have hiK : i < K := by_omega
    have hCBi := hCB i hiK
    have hmem : c.nmem _ = c₀.nmem ztblv := hI.low _ by_omega
    obtain ⟨c', k, e, hk, v01, vA, v02, mo, m0, m1, m2, m3, m4, m5, R, rr, rm, ro⟩ :=
      qlBody_exec (P := P) c hI.wb (by rw [hI.cur, hi]) (by zuoks)
        (by rw [hI.regs _ by_decide by_decide by_decide by_decide by_decide
          by_decide, h05])
        (by rw [hI.regs _ by_decide by_decide by_decide by_decide by_decide
          by_decide, h06])
        (by rw [hI.regs _ by_decide by_decide by_decide by_decide by_decide
          by_decide, h08])
        by_omega by_omega by_omega (by rw [hmem]; exact hh i hiK) by_omega
    rw [hi] at v02
    have hI' : QLI W K CB LB c₀ c' := by
      refine ⟨e.wb_right, by_omega, by rw [v01, v02]; ring, by rw [vA, v02]; ring,
        fun r a1 a2 a3 a4 a5 a6 => by rw [R r a1 a2 a3 a4 a5 a6, hI.regs r a1 a2 a3 a4 a5 a6],
        fun a ha => by rw [mo a by_omega, hI.low a ha], fun i' hi' => ?_,
        by zuokt, by zuoku, by zuokv⟩
      rw [v02] at hi'
      zuidn
      · obtain ⟨d0, d1, d2, d3, d4, d5⟩ := hI.done i' by_omega
        refine ztcbl
        · rw [mo _ by_omega, d0]
        · rw [mo _ by_omega, d1]
        · rw [mo _ by_omega, d2]
        · rw [mo _ by_omega, d3]
        · rw [mo _ by_omega, d4]
        · rw [mo _ by_omega, d5]
      · zugml

        have e1 : c.nmem _ = c₀.nmem (CB + 5 * i' + 1) := hI.low _ by_omega
        have e2 : c.nmem _ = c₀.nmem (CB + 5 * i' + 2) := hI.low _ by_omega
        refine ztcbl
        · rw [m0, ← e1]
        · rw [m1, hmem]
        · exact m2
        · rw [m3, ← e2]
        · rw [m4, hmem]
        · exact m5
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := qlLoop_exec h05 h06 h08 h00 hCB hh hW hWK n c'
      hI' by_omega
    exact ⟨c'', k + 2 + k₂, .whileLtN_true (by
      rw [hi, hI.regs 70100 by_decide by_decide by_decide by_decide by_decide
        by_decide, h00]; omega) e e₂, by_omega, by_omega, hI'', hK⟩

/-- **The written query list.** -/
theorem chordList_endQL {m m₀ : ℕ → ℕ} {LB CB : ℕ} {cs : List CRec}
    (hcs : ∀ i, i < cs.length → m₀ ztblv = (cs.getD i ztrp).h ∧
      m₀ ztbye = (cs.getD i ztrp).lp ∧
      m₀ ztbyf = (cs.getD i ztrp).rp)
    (hdone : ∀ i, i < cs.length →
      m ztpzm = m₀ ztbye ∧ m ztnmg = m₀ ztblv + 1 ∧
      m ztnmh = 1 ∧ m ztnmi = m₀ ztbyf ∧
      m ztnmj = m₀ ztblv + 1 ∧ m ztnmk = 0) :
    ChordListAt m LB (endQL cs) := by
  zun
  rw [endQL_length] at hj
  rw [endQL_get cs hj]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by_omega⟩
  · zucrv

    obtain ⟨d0, d1, d2, -, -, -⟩ := hdone i hi
    have e1 : ztpid := by_omega
    have e2 : 2 * i % 2 = 0 := by_omega
    grind
  · zucrv

    obtain ⟨-, -, -, d3, d4, d5⟩ := hdone i hi
    have e1 : ztzrh := by_omega
    have e2 : ztzrg := by_omega
    simp only [e1, e2, one_ne_zero, ite_false]
    grind

/-- **The chord-end queries of a normal form** are valid and ask exactly the chord ends. -/
theorem endQL_ok (J : Merge.Junction) (Q : Polygon) (i : ℕ) {N : NF}
    (hN : IsNF ztxgp Q N) :
    (∀ q ∈ endQL N.chords, QueryOK J Q i q) ∧
      geoQ J Q i ztvpw = endQ (N.F ztxgp Q) := by
  zulrj
  obtain ⟨-, -, -, -, -, -, -, -, -, hhQ, -⟩ := id hN
  have memk : ∀ k, k < N.chords.length → N.chord k ∈ N.chords := fun k hk => by
    zuub
  have key : ∀ k, k < N.chords.length →
      QueryOK J Q i ztgvk ∧
        QueryOK J Q i ztgvl ∧
        M.pos Q (N.chord k).lpos = lend ztbpa ∧
        M.pos Q (N.chord k).rpos = rend ztbpa := fun k hk =>
    queryOK_ends J Q i _ zttmn
      (hN.1.2.1 zting)
      (hhQ k hk)
  have mem : ∀ q, q ∈ endQL N.chords ↔ ∃ k, k < N.chords.length ∧
      (q = ztgvk ∨ q = ztgvl) := by
    intro q
    simp only [endQL, List.mem_map, List.mem_range, NF.chord]
    constructor
    · zuecp
      refine ⟨j / 2, by_omega, ?_⟩
      split_ifs
      · simp
      simp
    · rintro ⟨k, hk, rfl | rfl⟩
      · exact ⟨2 * k, by_omega, by_simp⟩
      · exact ⟨2 * k + 1, by_omega, by
          rw [show ztekz / 2 = k by omega, ite_eq_right by_omega]⟩
  refine ⟨fun q hq => ?_, ?_⟩
  · grind
  · zumx
    simp only [geoQ, endQ, NF.F, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · zuecr
      obtain ⟨k, hk, rfl | rfl⟩ := (mem q).1 hq
      · left
        refine ztzib
        show ztkqb = _
        rw [(key k hk).2.2.1]; rfl
      · right
        refine ztzib
        show ztkqc = _
        rw [(key k hk).2.2.2]; rfl
    · rintro (⟨c, ⟨r, hr, rfl⟩, rfl⟩ | ⟨c, ⟨r, hr, rfl⟩, rfl⟩)
      · zubhj
        zugmb
        refine ⟨_, (mem _).2 ⟨k, hk, Or.inl rfl⟩, ?_⟩
        show (lend _, 1) = ztkqb
        rw [(key k hk).2.2.1, hck]; rfl
      · zubhj
        zugmb
        refine ⟨_, (mem _).2 ⟨k, hk, Or.inr rfl⟩, ?_⟩
        show (rend _, -1) = ztkqc
        rw [(key k hk).2.2.2, hck]; rfl
theorem chordListAt_append {m : ℕ → ℕ} {A : ℕ} {L : List zte} (h : ChordListAt m A L)
    {x : ℕ × ℕ × ℕ} (h0 : m ztgcw = x.1) (h1 : m ztnid = x.2.1)
    (h2 : m ztnie = x.2.2) : ChordListAt m A ztffm := by
  zug
  zucjh
  rcases Nat.lt_or_ge i L.length with hlt | hge
  · have e : (L ++ [x]).getD i ztt = L.getD i ztt := by
      simp_all
    zvmwe; exact h i hlt
  grind
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def trip (m : ℕ → ℕ) (T a : ℕ) : ℕ × ℕ × ℕ := (m ztjmz, m zthcr, m zthcs)

/-- The lexicographic order of triples. -/
def tle (x y : ℕ × ℕ × ℕ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 ≤ y.2.2)))
instance (x y : ℕ × ℕ × ℕ) : Decidable (tle x y) := by unfold tle; infer_instance
theorem tle_antisymm {x y : ℕ × ℕ × ℕ} (h1 : tle x y) (h2 : tle y x) : x = y := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y
  unfold tle at h1 h2; grind

/-- The order of the items. -/
def le3 (m : ℕ → ℕ) (T K a b : ℕ) : Bool :=
  if a < K then (if b < K then decide (tle ztrxm ztrxn) else true)
  else ztdva
variable (m : ℕ → ℕ) {P : Polygon} {W : ℕ} (c : Config)
theorem le3_total (T K a b : ℕ) : (le3 m T K a b || le3 m T K b a) = true := by
  unfold le3 tle
  grind
theorem le3_trans (T K a b c : ℕ) (h1 : le3 m T K a b = true)
    (h2 : le3 m T K b c = true) : le3 m T K a c = true := by
  unfold le3 tle at *
  grind

/-- Load the triples of the two items into `70210 … 70215`. -/
def ld3 : Stmt := block [.addN 70210 30000 30000, .addN 70210 70210 30000,
  .addN 70210 70210 70216, .loadN 70211 70210, .constN 70215 1, .addN 70210 70210 70215,
  .loadN 70212 70210, .addN 70210 70210 70215, .loadN 70213 70210,
  .addN 70210 30001 30001, .addN 70210 70210 30001, .addN 70210 70210 70216,
  .loadN 70214 70210, .addN 70210 70210 70215, .loadN 70215 70210]

/-- The comparison of two loaded triples: `(70211, 70212, 70213)` against `(70214, 70215, ·)`,
the third component of `b` loaded on demand. -/
def cmpT : Stmt :=
  .ifLtN 70211 70214 ztjo
    (.ifLtN 70214 70211 ztlr
      (.ifLtN 70212 70215 ztjo
        (.ifLtN 70215 70212 ztlr
          (.seq (block [.addN 70210 30001 30001, .addN 70210 70210 30001,
              .addN 70210 70210 70216, .constN 70214 2, .addN 70210 70210 70214,
              .loadN 70214 70210])
            (.ifLtN 70214 70213 ztlr ztjo)))))

/-- **The comparator.** -/
def cmp3 : Stmt :=
  .ifLtN 30000 70217
    (.ifLtN 30001 70217 (.seq ld3 cmpT) ztjo)
    (.ifLtN 30001 70217 ztlr
      ztxft)

/-- The invariant of the comparator: the base, the bound and the memory below `A₀`. -/
def Cmp3J (m₀ : ℕ → ℕ) (A₀ T K : ℕ) (g : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 70216 = T ∧ c.nreg 70217 = K ∧ ztiuf ∧
    ∀ r, 70000 ≤ r → r < 70105 → c.nreg r = g r
theorem cmp3J_stable (m₀ : ℕ → ℕ) (A₀ T K : ℕ) (g : ℕ → ℕ) :
    SortR.JStable ztowm A₀ := by
  zudid
  have hb : ∀ r, 70000 ≤ r → r < 80000 → c'.nreg r = c.nreg r := fun r a b =>
    hr r ztfgf ztu
  exact ⟨by_simp_all,
    by simp_all, fun a ha => (hm a ha).trans (h3 a ha),
    fun r a b => by_grind⟩
set_option maxHeartbeats 4000000 in
theorem ld3_exec (hw : WordsBounded W c) {T a b : ℕ}
    (hT : c.nreg 70216 = T) (ha : c.nreg 30000 = a) (hb : c.nreg 30001 = b)
    (haW : T + 3 * a + 2 ≤ W) (hbW : T + 3 * b + 2 ≤ W) :
    ∃ c' k, Exec P W ld3 c c' k ∧ k = 15 ∧
      c'.nreg 70211 = c.nmem ztjmz ∧ c'.nreg 70212 = c.nmem zthcr ∧
      c'.nreg 70213 = c.nmem zthcs ∧ c'.nreg 70214 = c.nmem ztqcw ∧
      c'.nreg 70215 = c.nmem ztnpp ∧
      (∀ r, zthjy → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ld3
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, ha, hb]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, ha, hb]
  all_goals first | rfl | (congr 1; ring)
set_option maxHeartbeats 4000000 in
theorem cmpT_exec (hw : WordsBounded W c) (hW : 1 ≤ W)
    {T b x0 x1 x2 y0 y1 : ℕ} (hT : c.nreg 70216 = T) (hb : c.nreg 30001 = b)
    (hbW : T + 3 * b + 2 ≤ W) (h11 : c.nreg 70211 = x0) (h12 : c.nreg 70212 = x1)
    (h13 : c.nreg 70213 = x2) (h14 : c.nreg 70214 = y0) (h15 : c.nreg 70215 = y1) :
    ∃ c' k, Exec P W cmpT c c' k ∧ k ≤ 18 ∧
      c'.nreg 30002 = (if tle (x0, x1, x2) (y0, y1, c.nmem zteof) then 1 else 0) ∧
      (∀ r, r ≠ 30002 → zthjy → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmpT tle
  by_cases c1 : x0 < y0
  · refine spec_ifLtN_true by_omega (spec_instr ztcsz
      fun _ => ⟨by_omega, by_simp_all, fun r hr _ => by_simp_all, rfl, rfl, rfl, rfl⟩)
  zubv
  by_cases c2 : y0 < x0
  · refine spec_ifLtN_true by_omega (spec_instr (Exec.constN hw _ _
      ztbg) fun _ => ⟨by_omega, ?_, fun r hr _ => by_simp_all, rfl, rfl, rfl, rfl⟩)
    zumb
  zubv
  by_cases c3 : x1 < y1
  · refine spec_ifLtN_true by_omega (spec_instr ztcsz
      fun _ => ⟨by_omega, ?_, fun r hr _ => by_simp_all, rfl, rfl, rfl, rfl⟩)
    zumb
  zubv
  by_cases c4 : y1 < x1
  · refine spec_ifLtN_true by_omega (spec_instr (Exec.constN hw _ _
      ztbg) fun _ => ⟨by_omega, ?_, fun r hr _ => by_simp_all, rfl, rfl, rfl, rfl⟩)
    zumb
  zubv
  obtain ⟨c₁, k₁, e₁, hk₁, v14, v13, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 70210 30001 30001, .addN 70210 70210 30001, .addN 70210 70210 70216,
        .constN 70214 2, .addN 70210 70210 70214, .loadN 70214 70210]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 70214 = c.nmem zteof ∧ c₁.nreg 70213 = x2 ∧
      (∀ r, zthjy → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hb]; omega)
    refine ztfwy
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hb, h13]
    grind
  zud
  zugar
  by_cases c5 : c.nmem zteof < x2
  · refine spec_ifLtN_true by_omega (spec_instr (Exec.constN w₁ _ _
      ztbg) fun _ => ⟨by_omega, ?_, fun r hr hr' => ?_, by zvmxn, by zunkd,
        by zunkf, by zuoyb⟩)
    · simp_all
    simp_all
  · refine spec_ifLtN_false by_omega (spec_instr ztgdo
      fun _ => ⟨by_omega, ?_, fun r hr hr' => ?_, by zvmxn, by zunkd, by zunkf,
        by zuoyb⟩)
    · zumb
    simp_all
set_option maxHeartbeats 4000000 in
/-- **The contract of the comparator.** -/
theorem cmp3_ok {m₀ : ℕ → ℕ} {A₀ T K : ℕ} {g : ℕ → ℕ} (hTK : T + 3 * K ≤ A₀)
    (hW : 1 ≤ W) (hAW : A₀ ≤ W) :
    SortR.CmpOK P W cmp3 {bFuse} ztowm (le3 m₀ T K) 40 := by
  zufhy
  have hwr : wr (fun r => decide ztkdj || decide (70210 ≤ r ∧ r ≤ 70215)) cmp3 = true := by
    decide
  suffices H : ∃ c' k, Exec P W cmp3 c c' k ∧ k ≤ 40 ∧
      c'.nreg 30002 = (if le3 m₀ T K ztjry ztjrz then 1 else 0) by
    zubcs

    refine ⟨c', k, ex, hk, ⟨?_, ?_, fun a ha => by zunkg; simp_all,
      fun r a b => by rw [f.1 r by_grind]
                      simp_all⟩, hbit,
      fun r h0 h1 h2 hb => f.1 r ?_, fun r _ => fr r rfl, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · zudjx
    · zuhlg
    · zuhou

      zucor
      · exact hb (by rw [Finset.mem_singleton]; unfold bandOf bFuse; omega)
      · zugik
  have h1 : c.nreg 70217 = K := j2
  unfold cmp3 le3
  zuirl
  · zudd
    zucur
    · zudd
      obtain ⟨a, ha'⟩ : ∃ a, c.nreg 30000 = a := zths
      obtain ⟨b, hb'⟩ : ∃ b, c.nreg 30001 = b := zths
      have haK : ztsdg := ha' ▸ ha
      have hbK : b < K := hb' ▸ hb
      obtain ⟨c₁, k₁, e₁, hk₁, v11, v12, v13, v14, v15, r₁, m₁, -, -, -⟩ :=
        ld3_exec (P := P) c hw j1 ha' hb' by_omega by_omega
      obtain ⟨c₂, k₂, e₂, hk₂, v2, -⟩ := cmpT_exec (P := P) (T := T) (b := b) c₁ e₁.wb_right hW
        ((r₁ _ by_omega).trans j1) ((r₁ _ by_omega).trans hb') by_omega
        v11 v12 v13 v14 v15
      refine ztkkk
      rw [v2, m₁, j3 _ by_omega, j3 _ by_omega, j3 _ by_omega, j3 _ by_omega,
        j3 _ by_omega, j3 _ by_omega, ha', hb']
      by_cases ht : tle (m₀ ztjmz, m₀ zthcr, m₀ zthcs)
          (m₀ ztqcw, m₀ ztnpp, m₀ zteof)
      · have ht' : tle ztrxo ztrxp := ht
        simp_all
      · have ht' : ¬ tle ztrxo ztrxp := ht
        simp_all
    · refine spec_ifLtN_false by_omega (spec_instr ztcsz
        fun _ => zteh)
      simp_all
  · zubv
    zucur
    · refine spec_ifLtN_true by_omega (spec_instr ztbbp
        fun _ => zteh)
      simp_all
    · zubv
      zuhsy
      · refine spec_ifLtN_true hc (spec_instr ztbbp fun _ =>
          ⟨by_omega, ?_⟩)
        simp_all
      · zulol
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
variable {α : Type*} [DecidableEq α]

/-- The entries kept by the scan: the first one and those differing from their predecessor. -/
def keep (l : List α) (d : α) (j : ℕ) : Bool := j = 0 ∨ l.getD j d ≠ l.getD zthv d

/-- The scan applied to the first `n` entries. -/
def ddp (l : List α) (d : α) (n : ℕ) : List α :=
  ((List.range n).filter (keep l d)).map fun j => l.getD j d

/-- The scan. -/
def dd (l : List α) (d : α) : List α := ddp l d l.length
variable (l : List α) (d : α)
theorem ddp_succ (n : ℕ) :
    ddp l d ztkk = ddp l d n ++ (if keep l d n then [l.getD n d] else []) := by
  unfold ddp
  rw [List.range_succ, List.filter_append, List.map_append]
  grind
theorem mem_dd (x : α) : x ∈ dd l d ↔ x ∈ l := by
  unfold dd ddp
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · grind
  · zuetb
    zufyn
    -- the first occurrence
    classical
    let P : ℕ → Prop := fun i => i < l.length ∧ l.getD i d = l[j]
    have hP : ∃ i, P i := ⟨j, hj, by_simp_all⟩
    let i := Nat.find hP
    have hi : P i := Nat.find_spec hP
    refine ⟨i, ztooh, hi.2⟩
    unfold keep
    zufqt
    · simp_all
    · have hmin := Nat.find_min hP (show i - 1 < i by omega)
      grind

/-- **The scan of a sorted list has no repetitions.** -/
theorem dd_nodup {r : α → α → Prop} (hanti : ∀ x y, r x y → r y x → x = y) {l : List α}
    (hs : l.Pairwise r) (d : α) : (dd l d).Nodup := by
  unfold dd ddp
  refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
  zubgs
  simp only [List.mem_filter, List.mem_range] at hi hj
  zuct
  -- wlog `i < j`
  have key : ∀ a b, a < b → b < l.length → keep l d b = true → l.getD a d = l.getD b d → False := by
    intro a b hab hb hk heq
    have hb0 : b ≠ 0 := by_omega
    unfold keep at hk
    simp only [hb0, false_or, decide_eq_true_eq, decide_eq_true_eq] at hk
    apply hk
    -- `l[a] = l[b]` and `a ≤ b - 1 < b`: sorted, so `l[b - 1] = l[b]`
    have ga : l.getD a d = l[a] := by
      grind
    have gb : l.getD b d = l[b] := by
      simp_all
    have gc : l.getD zteow d = l[b - 1] := by
      grind
    rw [gb, gc]
    rw [ga, gb] at heq
    rcases Nat.lt_or_ge a zteow with h | h
    · have h1 : r l[a] l[b - 1] := List.pairwise_iff_getElem.1 hs _ _ by_omega by_omega h
      have h2 : r l[b - 1] l[b] := List.pairwise_iff_getElem.1 hs _ _ by_omega hb by_omega
      grind
    grind
  grind

/-! ## The index loop -/

/-- Write the index and advance. -/
def ixBody : Stmt := block [.storeN ALLOC 70200, .addN ALLOC ALLOC 70105, .addN 70200 70200 70105]

/-- Write the indices `0 … K - 1` at the allocator. -/
def ixLoop : Stmt := .whileLtN 70200 70201 ixBody

/-- The invariant of the index loop. -/
structure IXI (W K S : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 70200 ≤ K
  alloc : c.nreg ALLOC = S + c.nreg 70200
  regs : ∀ r, r ≠ 70200 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : ∀ a, a < S → c.nmem a = c₀.nmem a
  done : ∀ j, j < c.nreg 70200 → c.nmem zthck = j
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
set_option maxHeartbeats 2000000 in
theorem ixLoop_exec {P : Polygon} {W K S : ℕ} {c₀ : Config} (h05 : c₀.nreg 70105 = 1)
    (h01 : c₀.nreg 70201 = K) (hW : S + K + 1 ≤ W) :
    ∀ (n : ℕ) (c : Config), IXI W K S c₀ c → c.nreg 70200 + n = K →
      ∃ c' k, Exec P W ixLoop c c' k ∧ k ≤ 5 * n + 2 ∧ n ≤ k ∧ IXI W K S c₀ c' ∧ c'.nreg 70200 = K
  | 0, c, hI, hn => by
    zudxw
    exact ztdiz
  | n + 1, c, hI, hn => by
    zudxw
    have h05' : ztplz := by rw [hI.regs 70105 by_decide by_decide, h05]
    obtain ⟨i, hi⟩ : ∃ i, c.nreg 70200 = i := zths
    have hA : c.nreg 9999 = S + i := by rw [← hi]; exact hI.alloc
    zudpm
    obtain ⟨c', k, e, hk, q⟩ : ∃ c' k, Exec P W ixBody c c' k ∧ k = 3 ∧
        (c'.nreg 70200 = i + 1 ∧ c'.nreg ALLOC = S + ztg ∧
        (∀ r, r ≠ 70200 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c'.nmem = upd c.nmem ztbat i ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
      unfold ixBody
      exec_block
      all_goals try (simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hA, hi, h05', ALLOC]; omega)
      refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, ?_, rfl, rfl, rfl⟩
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hi,
          h05', ALLOC]
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA,
          h05', ALLOC]; ring
      · simp_all
      · simp (disch := omega) only [hA, hi, ALLOC]
    obtain ⟨q0, qA, qr, qm, qrr, qrm, qo⟩ := q
    have hI' : IXI W K S c₀ c' := by
      refine ⟨e.wb_right, by_omega, by_omega, fun r a1 a2 => by rw [qr r a1 a2,
        hI.regs r a1 a2], fun a ha => by rw [qm, upd_other _ _ _ by_omega, hI.low a ha],
        fun j hj => ?_, by rw [qrr, hI.rr], by rw [qrm, hI.rm], by rw [qo, hI.out]⟩
      rw [q0] at hj
      zujlh
      rcases Nat.lt_or_ge j i with h | h
      · zumya; exact hI.done j by_omega
      · have : ztsjr := by_omega
        simp_all
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := ixLoop_exec h05 h01 hW n c' hI' by_omega
    exact ztfjw
theorem seg_range {m : ℕ → ℕ} {S K : ℕ} (h : ∀ j, j < K → m zthck = j) :
    SortL.seg m S K = List.range K := by
  zulda
  zumgy
  simp only [SortL.seg, List.getElem_map, List.getElem_range]
  simp_all
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def neqS (a b : ℕ) : Stmt :=
  .seq (.ifLtN a b ztiga .skip) (.ifLtN b a ztiga .skip)

/-- Load the item and its triple; clear the flag. -/
def dsLoad : Stmt := block [.loadN 70222 70221, .addN 70229 70222 70222,
  .addN 70229 70229 70222, .addN 70229 70229 70216, .loadN 70224 70229,
  .addN 70229 70229 70105, .loadN 70225 70229, .addN 70229 70229 70105, .loadN 70226 70229,
  .constN 70228 0]

/-- Compare with the triple of the previous item. -/
def dsPrev : Stmt :=
  .seq (block [.addN 70229 70223 70223, .addN 70229 70229 70223, .addN 70229 70229 70216,
      .loadN 70227 70229])
    (.seq (neqS 70224 70227) (.seq ztepk
      (.seq (neqS 70225 70227) (.seq ztepk
        (neqS 70226 70227)))))

/-- The flag: the first item, or a new triple. -/
def dsFlag : Stmt := .ifLtN 70220 70105 ztiga dsPrev

/-- Append the triple. -/
def dsCopy : Stmt := block [.storeN ALLOC 70224, .addN ALLOC ALLOC 70105, .storeN ALLOC 70225,
  .addN ALLOC ALLOC 70105, .storeN ALLOC 70226, .addN ALLOC ALLOC 70105,
  .addN 70219 70219 70105]

/-- One item. -/
def dsBody : Stmt :=
  .seq dsLoad (.seq dsFlag (.seq ztprs
    ztgqx))

/-- The scan. -/
def dsLoop : Stmt := .whileLtN 70220 70230 dsBody

/-! ## Pieces -/
variable {P : Polygon} {W : ℕ}
theorem neqS_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (a b : ℕ) (ha : a ≠ 70228) (hb : b ≠ 70228) :
    ∃ c' k, Exec P W (neqS a b) c c' k ∧ k ≤ 6 ∧
      c'.nreg 70228 = (if c.nreg a ≠ c.nreg b then 1 else c.nreg 70228) ∧
      ztivg ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have step : ∀ (x y : ℕ) (c : Config), WordsBounded W c → x ≠ 70228 → y ≠ 70228 →
      ∃ c' k, Exec P W (.ifLtN x y _ .skip) c c' k ∧ k ≤ 3 ∧
        c'.nreg 70228 = (if c.nreg x < c.nreg y then 1 else c.nreg 70228) ∧
        ztivg ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := fun x y c hw _ _ => by
    by_cases h : c.nreg x < c.nreg y
    · have e := Exec.constN (P := P) hw 70228 1 hW
      exact ⟨_, _, .ifLtN_true h e, by_omega, by zumxk, by_simp_all, rfl, rfl,
        rfl, rfl⟩
    · exact ⟨c, _, .ifLtN_false h ztjd, by_omega, by zumxk, by_omega, rfl, rfl,
        rfl, rfl⟩
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁, m₁, rr₁, rm₁, o₁⟩ := step a b c hw ha hb
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := step b a c₁ e₁.wb_right hb ha
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, ?_, by_grind,
    by grind, by_grind, by_grind, by_grind⟩
  grind
set_option maxHeartbeats 4000000 in
theorem dsLoad_exec (c : Config) (hw : WordsBounded W c) {T x : ℕ}
    (hT : c.nreg 70216 = T) (h05 : c.nreg 70105 = 1) (hx : c.nmem (c.nreg 70221) = x)
    (hxW : T + 3 * x + 2 ≤ W) :
    ∃ c' k, Exec P W dsLoad c c' k ∧ k = 10 ∧ c'.nreg 70222 = x ∧
      c'.nreg 70224 = c.nmem ztjnc ∧ c'.nreg 70225 = c.nmem (T + 3 * x + 1) ∧
      c'.nreg 70226 = c.nmem (T + 3 * x + 2) ∧ c'.nreg 70228 = 0 ∧
      (∀ r, r ≠ 70222 → r ≠ 70224 → r ≠ 70225 → r ≠ 70226 → r ≠ 70228 → r ≠ 70229 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dsLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, hx, h05]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hT, hx, h05]
  all_goals first | rfl | (congr 1; ring)
set_option maxHeartbeats 4000000 in
theorem dsPrev_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    {T p : ℕ} (hT : c.nreg 70216 = T) (h05 : c.nreg 70105 = 1) (hp : c.nreg 70223 = p)
    (hpW : T + 3 * p + 2 ≤ W) (h28 : c.nreg 70228 = 0) :
    ∃ c' k, Exec P W dsPrev c c' k ∧ k ≤ 30 ∧
      c'.nreg 70228 = (if (c.nreg 70224, c.nreg 70225, c.nreg 70226) ≠
        (c.nmem ztjna, c.nmem zthct, c.nmem ztnpq) then 1 else 0) ∧
      (∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- first component
  obtain ⟨c₁, k₁, e₁, hk₁, v27, v29, r₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 70229 70223 70223, .addN 70229 70229 70223, .addN 70229 70229 70216,
        .loadN 70227 70229]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 70227 = c.nmem (T + 3 * p) ∧
      c₁.nreg 70229 = T + 3 * p ∧ (∀ r, r ≠ 70227 → r ≠ 70229 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hp]; omega)
    zuloy
    all_goals simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hT, hp]
    all_goals first | rfl | ring
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, r₂, m₂, rr₂, rm₂, o₂⟩ :=
    neqS_exec (P := P) c₁ e₁.wb_right hW 70224 70227 by_decide by_decide
  -- second component
  have load : ∀ (d : Config) (v : ℕ), WordsBounded W d → d.nreg 70229 = v → d.nreg 70105 = 1 →
      v + 1 ≤ W → ∃ d' k, Exec P W ztepk d d' k ∧
        k = 2 ∧ d'.nreg 70227 = d.nmem ztsp ∧ d'.nreg 70229 = v + 1 ∧
        (∀ r, r ≠ 70227 → r ≠ 70229 → d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem ∧
        d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
    intro d v hwd hv h1 hvW
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hv, h1]; omega)
    simp_all
  have g2 : ∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₂.nreg r = c.nreg r := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, u27, u29, r₃, m₃, rr₃, rm₃, o₃⟩ := load c₂ ztjna e₂.wb_right
    by_grind by_grind
    by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, r₄, m₄, rr₄, rm₄, o₄⟩ :=
    neqS_exec (P := P) c₃ e₃.wb_right hW 70225 70227 by_decide by_decide
  have g4 : ∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₄.nreg r = c.nreg r := fun r a b d => by
    rw [r₄ r b, r₃ r a d, g2 r a b d]
  obtain ⟨c₅, k₅, e₅, hk₅, w27, w29, r₅, m₅, rr₅, rm₅, o₅⟩ := load c₄ zthct
    e₄.wb_right by_grind by_grind by_omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, r₆, m₆, rr₆, rm₆, o₆⟩ :=
    neqS_exec (P := P) c₅ e₅.wb_right hW 70226 70227 by_decide by_decide
  have ex : Exec P W dsPrev c c₆ _ :=
    .seq e₁ ztfv
  refine ⟨c₆, _, ex, by_omega, ?_, fun r a b d => by rw [r₆ r b, r₅ r a d, g4 r a b d], ?_, ?_,
    ?_, ?_⟩
  · have mm : ∀ x, c₅.nmem x = c.nmem x := fun x => by_grind
    have A2 : c₂.nreg 70228 = if c.nreg 70224 ≠ c.nmem ztjna then 1 else 0 := by
      rw [f₂, r₁ _ by_decide by_decide, v27, h28.symm.trans (r₁ _ by_decide by_decide).symm]
    have A4 : c₄.nreg 70228 = if c.nreg 70225 ≠ c.nmem zthct then 1
        else c₂.nreg 70228 := by
      rw [f₄, r₃ _ by_decide by_decide, u27, g2 _ by_decide by_decide by_decide,
        r₃ _ by_decide by_decide, m₂, m₁]
    have A6 : c₆.nreg 70228 = if c.nreg 70226 ≠ c.nmem ztnpq then 1
        else c₄.nreg 70228 := by
      rw [f₆, r₅ _ by_decide by_decide, w27, g4 _ by_decide by_decide by_decide,
        r₅ _ by_decide by_decide, m₄, m₃, m₂, m₁]
    rw [A6, A4, A2]
    simp only [ne_eq, Prod.mk.injEq, not_and_or]
    split_ifs <;> tauto
  · grind
  · grind
  · grind
  grind
set_option maxHeartbeats 4000000 in
theorem dsCopy_exec (c : Config) (hw : WordsBounded W c) {a : ℕ}
    (hA : c.nreg ALLOC = a) (h05 : c.nreg 70105 = 1) (ha : a + 3 ≤ W) {n : ℕ}
    (h19 : c.nreg 70219 = n) (hn : n + 1 ≤ W) :
    ∃ c' k, Exec P W dsCopy c c' k ∧ k = 7 ∧ c'.nreg ALLOC = a + 3 ∧
      ztfjr ∧
      c'.nmem a = c.nreg 70224 ∧ c'.nmem ztdf = c.nreg 70225 ∧ c'.nmem ztvj = c.nreg 70226 ∧
      c'.nreg 70219 = n + 1 ∧ (∀ r, r ≠ ALLOC → r ≠ 70219 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dsCopy
  zubtg
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h05, h19, ALLOC]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h05, h19, ALLOC])
  · have a1' : zteif := a1
    simp_all

/-! ## The loop -/

/-- The triples of the sorted items. -/
def stl (m₀ : ℕ → ℕ) (T B K : ℕ) : List zte := (SortL.seg m₀ B K).map (trip m₀ T)
theorem stl_getD {m₀ : ℕ → ℕ} {T B K j : ℕ} (hj : j < K) :
    (stl m₀ T B K).getD j ztt = trip m₀ T (m₀ ztelw) := by
  simp [stl, SortL.seg, List.getD_eq_getElem?_getD, hj]

/-- The invariant of the scan. -/
structure DSI (W K T B LB : ℕ) (m₀ : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  j_le : c.nreg 70220 ≤ K
  cur : c.nreg 70221 = B + c.nreg 70220
  prev : 0 < c.nreg 70220 → c.nreg 70223 = m₀ (B + (c.nreg 70220 - 1))
  alloc : c.nreg ALLOC = LB + 3 * (ddp ztbby ztt ztqhz).length
  list : ChordListAt c.nmem LB (ddp ztbby ztt ztqhz)
  cnt : c.nreg 70219 = (ddp ztbby ztt ztqhz).length
  low : ∀ a, a < LB → c.nmem a = m₀ a
  regs : ∀ r, ztofy → r ≠ ALLOC → c.nreg r = c₀.nreg r
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
theorem ddp_length_le {α : Type*} [DecidableEq α] (l : List α) (d : α) (n : ℕ) :
    (ddp l d n).length ≤ n := by
  unfold ddp; grind
set_option maxHeartbeats 8000000 in
theorem dsBody_step {W K T B LB : ℕ} {m₀ : ℕ → ℕ} {c₀ c : Config}
    (hI : DSI W K T B LB m₀ c₀ c) (ht : c.nreg 70220 < K) (h05 : c₀.nreg 70105 = 1)
    (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70216 = T)
    (hitems : ∀ j, j < K → m₀ ztelw < K) (hTB : T + 3 * K ≤ LB) (hBL : B + K ≤ LB)
    (hW : LB + 3 * K + 3 ≤ W) :
    ∃ c' k, Exec P W dsBody c c' k ∧ DSI W K T B LB m₀ c₀ c' ∧ k ≤ 58 ∧ 3 ≤ k ∧
      c'.nreg 70220 = c.nreg 70220 + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, c.nreg 70220 = j := by_simp_all
  zukuk
  zumeq
  have r05 : ztplz := by rw [hreg _ by_norm_num by_decide, h05]
  have r08 : ztuoa := by rw [hreg _ by_norm_num by_decide, h08]
  have r16 : c.nreg 70216 = T := by rw [hreg _ by_norm_num by_decide, h16]
  obtain ⟨x, hx⟩ : ∃ x, m₀ (B + j) = x := by_simp_all
  have hxK : ztpql := by_grind
  zudk
  -- load
  obtain ⟨c₁, k₁, e₁, hk₁, v22, v24, v25, v26, v28, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dsLoad_exec (P := P) c hI.wb r16 r05 (x := x)
      (by rw [hI.cur, hj, hI.low _ by_omega, hx]) by_omega
  have mT : ∀ k, k < 3 → c.nmem _ = m₀ (T + 3 * x + k) := fun k hk =>
    hI.low _ by_omega
  have mT0 : c.nmem ztjnc = m₀ ztjnc := by simpa using mT 0 by_omega
  -- flag
  have hkeep : keep ztbby ztt j = true ↔
      (j = 0 ∨ trip m₀ T x ≠ trip m₀ T (m₀ ztyoo)) := by
    unfold keep
    rw [stl_getD ht, hx]
    zujsj
    · grind
    · rw [stl_getD by_omega]; simp
  obtain ⟨c₂, k₂, e₂, hk₂, v2, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W dsFlag c₁ c₂ k₂ ∧
      k₂ ≤ 32 ∧ (c₂.nreg 70228 = if keep ztbby ztt j then 1 else 0) ∧
      (∀ r, r ≠ 70227 → r ≠ 70228 → r ≠ 70229 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q20 : c₁.nreg 70220 = j := by
      grind
    have q05 : ztpmw := by
      grind
    unfold dsFlag
    zujsj
    · have e := Exec.constN (P := P) e₁.wb_right 70228 1 hW1
      refine ⟨_, _, .ifLtN_true by_omega e, by_omega, ?_, fun r _ hr _ => by
        zumwy, rfl, rfl, rfl, rfl⟩
      zufb
      grind
    · have hp : c₁.nreg 70223 = m₀ ztyoo := by
        rw [r₁ _ by_decide by_decide by_decide by_decide by_decide by_decide]
        zuorx; exact hI.prev by_omega
      have hpK : m₀ ztyoo < K := by_grind
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dsPrev_exec c₁ e₁.wb_right hW1
        ((r₁ _ by_decide by_decide by_decide by_decide by_decide by_decide).trans r16)
        q05 hp by_omega v28
      refine ⟨c₂, _, .ifLtN_false by_omega e₂, by_omega, ?_,
        by omega, m₂, rr₂, rm₂, o₂⟩
      rw [f₂, v24, v25, v26, m₁, mT0, mT 1 by_omega, mT 2 by_omega,
        hI.low _ by_omega, hI.low _ by_omega, hI.low _ by_omega]
      zuhbp
      · have := (hkeep.1 hk).resolve_left h0
        rw [ite_eq_left hk, ite_eq_left]
        simpa [trip] using this
      · rw [ite_eq_right hk, ite_eq_right]
        intro hne; exact hk (hkeep.2 (Or.inr (by simpa [trip] using hne)))
  -- copy
  have g2 : ∀ r, (r < 70220 ∨ 70229 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [r₂ r by_omega by_omega by_omega, r₁ r by_omega by_omega by_omega by_omega
      by_omega by_omega]
  have q28 : c₂.nreg 70108 = 0 := by_grind
  have hAc : c₂.nreg ALLOC = LB + 3 * (ddp ztbby ztt j).length := by
    rw [g2 _ by_decide]; zuoko
  have hdl := ddp_length_le ztbby ztt j
  zugmp

  have h19 : c₂.nreg 70219 = (ddp ztbby ztt j).length := by
    rw [g2 _ by_norm_num]; zuokp
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, m₃, l₃, n₃, q₃, rr₃, rm₃, o₃⟩ : ∃ c₃ k₃, Exec P W
      ztprs c₂ c₃ k₃ ∧ k₃ ≤ 9 ∧
      c₃.nreg ALLOC = LB + 3 * (ddp ztbby ztt ztl).length ∧
      (∀ a, a < LB + 3 * (ddp ztbby ztt j).length → c₃.nmem a = c.nmem a) ∧
      ChordListAt c₃.nmem LB (ddp ztbby ztt ztl) ∧
      c₃.nreg 70219 = (ddp ztbby ztt ztl).length ∧
      (∀ r, r ≠ ALLOC → r ≠ 70219 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    rw [ddp_succ]
    zuhbp
    · rw [ite_eq_left hk] at v2 ⊢
      obtain ⟨c₃, k₃, e₃, hk₃, a₃, mo, n0, n1, n2, n19, R₃, rr₃, rm₃, o₃⟩ := dsCopy_exec
        c₂ e₂.wb_right hAc by_grind by_omega h19 by_omega
      refine ⟨c₃, _, .ifLtN_true by_omega e₃, by_omega, ?_, fun a ha => ?_, ?_,
        by rw [n19, List.length_append]; simp, R₃, rr₃, rm₃, o₃⟩
      · rw [a₃, List.length_append]; rfl
      · grind
      · zuknk
        · zufir
          zusk
          · grind
          · grind
          grind
        · rw [n0, r₂ _ by_decide by_decide by_decide, v24, stl_getD ht, mT0, hx]; rfl
        · rw [n1, r₂ _ by_decide by_decide by_decide, v25, stl_getD ht, mT 1 by_omega,
            hx]; rfl
        · rw [n2, r₂ _ by_decide by_decide by_decide, v26, stl_getD ht, mT 2 by_omega,
            hx]; rfl
    · rw [ite_eq_right hk] at v2 ⊢
      rw [List.append_nil]
      refine ⟨c₂, _, .ifLtN_false by_omega ztdyc, by_omega, hAc,
        by grind, ?_, h19, by_omega, rfl, rfl, rfl⟩
      grind
  -- advance
  have g3 : ∀ r, ztofy → r ≠ ALLOC → c₃.nreg r = c.nreg r := fun r hr ha => by
    rw [q₃ r ha by_omega, g2 r by_omega]
  have q22 : c₃.nreg 70222 = x := by
    grind
  have q21 : c₃.nreg 70221 = B + j := by
    rw [q₃ _ by_decide by_decide, r₂ _ by_decide by_decide by_decide,
      r₁ _ by_decide by_decide by_decide by_decide by_decide by_decide, hI.cur, hj]
  have q20 : c₃.nreg 70220 = j := by
    rw [q₃ _ by_decide by_decide, r₂ _ by_decide by_decide by_decide,
      r₁ _ by_decide by_decide by_decide by_decide by_decide by_decide, hj]
  have q05 : ztusj := by_grind
  zubj
  obtain ⟨c₄, k₄, e₄, hk₄, u23, u21, u20, r₄, m₄, rr₄, rm₄, o₄⟩ : ∃ c₄ k₄, Exec P W
      ztgqx c₃ c₄ k₄ ∧
      k₄ = 3 ∧ c₄.nreg 70223 = x ∧ c₄.nreg 70221 = B + ztl ∧ c₄.nreg 70220 = j + 1 ∧
      (∀ r, r ≠ 70220 → r ≠ 70221 → r ≠ 70223 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem ∧
      c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, q21, q20, q05]; omega)
    refine ztbfo
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      q22, q21, q20, q05]
    omega
  have ex : Exec P W dsBody c c₄ _ := .seq e₁ ztcb
  refine ⟨c₄, _, ex, ⟨e₄.wb_right, by_omega, by_omega, fun _ => by rw [u23, u20, Nat.add_sub_cancel, hx],
    by rw [u20, ← a₃, r₄ _ by_decide by_decide by_decide], by_grind,
    by grind,
    fun a ha => by rw [m₄, m₃ a by_omega, hI.low a ha],
    fun r hr ha => by rw [r₄ r by_omega by_omega by_omega, g3 r hr ha, hreg r hr ha],
    by zunlv, by zunlw,
    by zunlx⟩, by_omega, by_omega, by_omega⟩
set_option maxHeartbeats 2000000 in
/-- **The scan.** -/
theorem dsLoop_exec {W K T B LB : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config}
    (h05 : c₀.nreg 70105 = 1) (h08 : c₀.nreg 70108 = 0) (h16 : c₀.nreg 70216 = T)
    (h30 : c₀.nreg 70230 = K)
    (hitems : ∀ j, j < K → m₀ ztelw < K) (hTB : T + 3 * K ≤ LB) (hBL : B + K ≤ LB)
    (hW : LB + 3 * K + 3 ≤ W) :
    ∀ (n : ℕ) (c : Config), DSI W K T B LB m₀ c₀ c → c.nreg 70220 + n = K →
      ∃ c' k, Exec P W dsLoop c c' k ∧ k ≤ 60 * n + 2 ∧ 3 * n ≤ k ∧ DSI W K T B LB m₀ c₀ c' ∧
        c'.nreg 70220 = K
  | 0, c, hI, hn => by
    zudya
    exact ztdiz
  | n + 1, c, hI, hn => by
    zudya
    have ht : c.nreg 70220 < K := by_omega
    obtain ⟨c', k, e, hI', hk, hk3, hc'⟩ := dsBody_step (P := P) hI ht h05 h08 h16 hitems hTB hBL hW
    obtain ⟨c'', k₂, e₂, hk₂, hk₂', hI'', hK⟩ := dsLoop_exec h05 h08 h16 h30 hitems hTB hBL hW n c' hI'
      by_omega
    exact ztfjw
end
end FuseAsm
end Chazelle.Core
namespace Chazelle.Core
namespace FuseAsm
open Machine Machine.Stmt Programs SignK
@[expose] public section
def ddInit : Stmt := block [.constN 70105 1, .constN 70108 0, .copyN 70216 70240,
  .copyN 70217 70241, .copyN 70201 70241, .copyN 70230 70241, .constN 70200 0,
  .copyN 70202 ALLOC]

/-- The arguments of the sort. -/
def ddMid : Stmt := block [.copyN 30003 70202, .copyN 30004 70241]

/-- The start of the scan. -/
def ddPost : Stmt := block [.copyN 70242 ALLOC, .constN 70220 0, .copyN 70221 30005,
  .constN 70219 0, .constN 70105 1, .constN 70108 0, .copyN 70230 70217]

/-- **The deduplication.** -/
def ddRun : Stmt :=
  .seq ddInit (.seq ixLoop (.seq ddMid (.seq (SortR.sortStmt cmp3) (.seq ddPost dsLoop))))

/-- The stored triples. -/
def tlist (m : ℕ → ℕ) (T K : ℕ) : List zte := (List.range K).map (trip m T)
variable {m : ℕ → ℕ}
theorem tle_of_le3 {T K a b : ℕ} (ha : a < K) (hb : b < K)
    (h : le3 m T K a b = true) : tle ztrxm ztrxn := by
  unfold le3 at h; simp_all

/-- The scanned list of a sorted permutation of the indices: same elements, no repetition. -/
theorem dd_spec {T K : ℕ} {L' : List ℕ} (hp : L'.Perm ztpzt)
    (hs : L'.Pairwise fun a b => le3 m T K a b = true) :
    (∀ x, x ∈ dd ztihg ztt ↔ x ∈ tlist m T K) ∧
      (dd ztihg ztt).Nodup ∧
      (dd ztihg ztt).length ≤ K := by
  have hlt : ∀ a ∈ L', a < K := by_grind
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [mem_dd, tlist]
    grind
  · refine dd_nodup (fun x y h1 h2 => tle_antisymm h1 h2) ?_ _
    zuczn
    exact hs.imp_of_mem fun {a b} ha hb h => tle_of_le3 by_simp_all by_simp_all h
  · unfold dd
    refine (ddp_length_le _ _ _).trans ?_
    rw [List.length_map, hp.length_eq, List.length_range]

/-- The cost bound of `ddRun`. -/
def ddCost (K : ℕ) : ℕ := SortR.sortCost 40 K + 70 * K + 30
theorem frameFS_of_regs {c c' : Config} {k : ℕ}
    (hr : ∀ r, (r < 30000 ∨ (40000 ≤ r ∧ r < 70000) ∨ 80000 ≤ r) → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ ({bFuse, bSort} : Finset ℕ) → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hrm : ∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) (ho : c'.output = c.output)
    (ha1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (ha2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bFuse, bSort} c c' k := by
  refine ⟨fun r hb hra => hr r ?_ hra, hrr, hm, hrm, ho, ha1, ha2⟩
  zubq

  apply hb
  simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bFuse, bSort]
  omega
set_option maxHeartbeats 8000000 in
/-- **The deduplication procedure.** -/
theorem ddRun_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {T K : ℕ}
    (h40 : c.nreg 70240 = T) (h41 : c.nreg 70241 = K) (hT : T + 3 * K ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + ddCost K ≤ W) :
    ∃ c' k, Exec P W ddRun c c' k ∧ k ≤ ddCost K ∧ Frame {bFuse, bSort} c c' k ∧
      (∀ r, 70000 ≤ r → r < 70105 → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg 70242 ∧ c'.nreg 70242 + 3 * c'.nreg 70219 ≤ c'.nreg ALLOC ∧
      ∃ D : List zte, ChordListAt c'.nmem (c'.nreg 70242) D ∧
        c'.nreg 70219 = D.length ∧ D.length ≤ K ∧
        (∀ x, x ∈ D ↔ x ∈ tlist c.nmem T K) ∧ D.Nodup := by
  obtain ⟨A₀, hA₀⟩ : ztcgh := by_simp_all
  zujyw
  have hsc := SortR.sortCost_room 40 K
  unfold ddCost at hroom
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W ddInit c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 70105 = 1 ∧ c₁.nreg 70108 = 0 ∧ c₁.nreg 70216 = T ∧ c₁.nreg 70217 = K ∧
        c₁.nreg 70201 = K ∧ c₁.nreg 70230 = K ∧ c₁.nreg 70200 = 0 ∧ c₁.nreg 70202 = A₀ ∧
        c₁.nreg ALLOC = A₀ ∧
        (∀ r, (r < 70105 ∨ 70230 < r) → r ≠ ALLOC → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold ddInit
    exec_block
    all_goals try omega
    zubee
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h40, h41, hA', ALLOC]
    and_intros
    all_goals first | trivial | rfl |
      (intro r hr ha; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨q05, q08, q16, q17, q01, q30, q00, q02, qA, qr, qm, qrr, qrm, qo⟩ := q
  -- the indices
  have I0 : IXI W K A₀ c₁ c₁ := ⟨e₁.wb_right, by_omega, by_omega, by_omega,
    by omega, by_simp_all, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := ixLoop_exec (P := P) q05 q01 by_omega K c₁ I0
    by_omega
  have hseg : SortL.seg c₂.nmem A₀ K = List.range K := seg_range fun j hj => I₂.done j by_omega
  have a₂ : c₂.nreg ALLOC = A₀ + K := by rw [I₂.alloc, h₂]
  have g₂ := I₂.regs
  -- the sort
  obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W ddMid c₂ c₃ k₃ ∧ k₃ = 2 ∧
      (c₃.nreg 30003 = A₀ ∧ c₃.nreg 30004 = K ∧
        ztgsm ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    have hw₂ := I₂.wb
    have r02 : c₂.nreg 70202 = A₀ := by rw [g₂ _ by_decide by_decide, q02]
    have r41 : c₂.nreg 70241 = K := by
      grind
    unfold ddMid
    exec_block
    simp_all
  obtain ⟨s03, s04, sr₃, sm₃, srr₃, srm₃, so₃⟩ := q3
  have a₃ : c₃.nreg ALLOC = A₀ + K := by rw [sr₃ _ by_decide by_decide, a₂]
  have cmp := cmp3_ok (P := P) (W := W) (m₀ := c₃.nmem) (A₀ := A₀ + K) (T := T) (K := K)
    (g := c₃.nreg)
    by_omega by_omega by_omega
  have hJ : Cmp3J c₃.nmem ztnjc T K c₃.nreg c₃ := ⟨by
      grind,
    by grind,
    by omega, by_omega⟩
  obtain ⟨c₄, k₄, e₄, hk₄, hJ₄, fr₄, b₄, b₄', L', hL', hperm, hsorted⟩ :=
    SortR.sortStmt_exec (P := P) cmp by_decide (le3_trans c₃.nmem T K)
      (le3_total c₃.nmem T K) e₃.wb_right hJ (by rw [a₃]; exact cmp3J_stable _ _ _ _ _)
      ztpzt by_simp_all
      by_simp_all by_simp_all
      by_grind
  rw [List.length_range] at hk₄ b₄' hL'
  -- the scan
  obtain ⟨B', hB'⟩ : ∃ x, c₄.nreg 30005 = x := by_simp_all
  obtain ⟨LB, hLB⟩ : ∃ x, c₄.nreg ALLOC = x := by_simp_all
  zubwq
  obtain ⟨j16, j17, j4, j5⟩ := hJ₄
  obtain ⟨c₅, k₅, e₅, hk₅, q5⟩ : ∃ c₅ k₅, Exec P W ddPost c₄ c₅ k₅ ∧ k₅ = 7 ∧
      (c₅.nreg 70242 = LB ∧ c₅.nreg 70220 = 0 ∧ c₅.nreg 70221 = B' ∧ c₅.nreg 70219 = 0 ∧
        c₅.nreg 70105 = 1 ∧ c₅.nreg 70108 = 0 ∧ c₅.nreg 70230 = K ∧ c₅.nreg 70216 = T ∧
        (∀ r, (r < 70105 ∨ 70242 < r) → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have hLB' := hLB
    unfold ddPost
    exec_block
    all_goals try omega
    zubee
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hLB', hB', j16, j17, ALLOC]
    and_intros
    all_goals first | trivial | rfl | (intro r h1; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨t42, t20, t21, t19, t05, t08, t30, t16, tr₅, tm₅, trr₅, trm₅, to₅⟩ := q5
  have hitems : ∀ j, j < K → c₅.nmem ztsvd < K := by
    zun
    have hmem : c₅.nmem ztsvd ∈ L' := by
      rw [← hL', tm₅, ← hB']
      simp only [SortL.seg, List.mem_map, List.mem_range]
      grind
    grind
  have a₅ : c₅.nreg ALLOC = LB := by rw [tr₅ _ by_decide, hLB]
  have hK4 := hk₄
  have hLBb : LB ≤ A₀ + K + k₄ := by rw [← hLB, ← a₃]; exact fr₄.2.2.2.2.2.2
  have hBL : B' + K ≤ LB := by_grind
  have D0 : DSI W K T B' LB c₅.nmem c₅ c₅ := by
    refine ⟨e₅.wb_right, by_grind, by_omega, by_grind,
      by rw [a₅, t20]; rfl, by rw [t20]; intro i hi; simp [ddp] at hi,
      by rw [t19, t20]; rfl, by_omega, by_omega, rfl, rfl, rfl⟩
  obtain ⟨c₆, k₆, e₆, hk₆, hk₆', D₆, h₆⟩ := dsLoop_exec (P := P) (m₀ := c₅.nmem) t05 t08 t16 t30
    hitems by_omega hBL by_omega K c₅ D0 by_omega
  -- assembling
  have ex : Exec P W ddRun c c₆ _ :=
    .seq e₁ ztfv
  set D := ddp (stl c₅.nmem T B' K) ztt K with hD
  have hDdd : D = dd (L'.map ztuca) ztt := by
    have e1 : stl c₅.nmem T B' K = L'.map ztuca := by
      unfold stl
      rw [tm₅, ← hB', hL']
      zucfh
      zuge
      zukax
      unfold trip
      have hm : ∀ x, x < A₀ → c₄.nmem x = c.nmem x := fun x hx => by
        rw [fr₄.2.2.1 x by_grind, sm₃, I₂.low x hx, qm]
      zueme
    rw [hD, e1]; unfold dd; rw [List.length_map, hperm.length_eq, List.length_range]
  have hsorted' : L'.Pairwise fun a b => le3 c.nmem T K a b = true := by
    refine hsorted.imp_of_mem fun {a b} ha hb h => ?_
    zukax
    have hbK : b < K := by_grind
    have hm : ∀ x, x < A₀ → c₃.nmem x = c.nmem x := fun x hx => by rw [sm₃, I₂.low x hx, qm]
    have ht : ∀ y, y < K → trip c₃.nmem T y = trip c.nmem T y := fun y hy => by
      unfold trip; rw [hm _ by_omega, hm _ by_omega, hm _ by_omega]
    unfold le3 at h ⊢
    grind
  obtain ⟨hmemD, hnodD, hlenD⟩ := dd_spec (m := c.nmem) (T := T) hperm hsorted'
  rw [← hDdd] at hmemD hnodD hlenD
  have hc6 := D₆.cnt
  rw [h₆] at hc6
  have hl6 := D₆.list
  rw [h₆] at hl6
  have ha6 := D₆.alloc
  rw [h₆] at ha6
  have r42 : c₆.nreg 70242 = LB := by rw [D₆.regs _ by_norm_num by_decide, t42]
  refine ⟨c₆, _, ex, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, D, by_grind, hc6, hlenD,
    hmemD, hnodD⟩
  · have := hlenD; unfold ddCost; omega
  · have a4 : A₀ + K ≤ LB := by_grind
    have hA6 := ha6
    refine frameFS_of_regs (fun r hr ha => ?_) ztez ztts ztts
      ?_ by_omega by_grind
    · rw [D₆.regs r by_omega ha, tr₅ r by_omega,
        fr₄.1 r (by simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bFuse]; omega)
          ha, sr₃ r by_omega by_omega, g₂ r by_omega ha, qr r by_omega ha]
    · rw [D₆.rr, trr₅, fr₄.2.1 r (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto), srr₃, I₂.rr, qrr]
    · zuksh
      rw [D₆.low a by_omega, tm₅, fr₄.2.2.1 a by_grind, sm₃, I₂.low a ha, qm]
    · zuksh
      rw [D₆.rm, trm₅, fr₄.2.2.2.1 a by_grind, srm₃, I₂.rm, qrm]
    · rw [D₆.out, to₅, fr₄.2.2.2.2.1, so₃, I₂.out, qo]
  · zucvq
    rw [D₆.regs r by_omega hA, tr₅ r by_omega, j5 r h1 h2, sr₃ r by_omega by_omega,
      g₂ r by_omega hA, qr r by_omega hA]
  · grind
  omega
