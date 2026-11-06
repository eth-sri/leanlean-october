module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepPrimArrMath
public import Chazelle.Core.SweepLabelJ
public import Chazelle.Core.SweepLabelJL

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

/-! ## The tour offsets -/

/-- **The tour offset** `tpos C J = (J + 2m - S) mod 2m` is the candidate index. -/
theorem tpos_eq_cand (C : Chain) {J : ℕ} (hJ : J < 2 * C.m) :
    WalkEmbed.tpos C J = candIdx C.m (C.sideS C.sideBeta) J := by
  have hS := C.sideS_lt C.sideBeta
  unfold WalkEmbed.tpos WalkEmbed.bS candIdx
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show J + 2 * C.m - C.sideS C.sideBeta = (J - C.sideS C.sideBeta) + 2 * C.m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Reading a descriptor -/

/-- Read the number of edges (`50101`), `2m` (`50108`) and the tour position `S = sideS` of the
box (`50102`) of the chain descriptor at the address in `50100`. -/
def readS : Stmt :=
  .seq (block [.constN 50104 2, .addN 50105 50100 50104, .loadN 50101 50105,
      .constN 50104 3, .addN 50105 50100 50104, .loadN 50106 50105,
      .constN 50104 4, .addN 50105 50100 50104, .loadN 50107 50105,
      .addN 50108 50101 50101, .constN 50109 1])
    (.ifLtN 50107 50109 (.instr (.subN 50102 50108 50106))
      (.ifLtN 50109 50107 (.instr (.subN 50102 50108 50106)) (.instr (.copyN 50102 50106))))

theorem readS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {X : ℕ}
    (hX : c.nreg 50100 = X) {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem X Q H C) (hXW : X + 5 ≤ W) (hmW : 2 * C.m ≤ W) :
    ∃ c' k, Exec P W readS c c' k ∧ k ≤ 16 ∧ c'.nreg 50101 = C.m ∧
      c'.nreg 50102 = C.sideS C.sideBeta ∧ c'.nreg 50108 = 2 * C.m ∧
      (∀ r, (r < 50101 ∨ 50109 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨-, -, -, hm, hT, hb⟩ := hC
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50104 2,
      .addN 50105 50100 50104, .loadN 50101 50105, .constN 50104 3, .addN 50105 50100 50104,
      .loadN 50106 50105, .constN 50104 4, .addN 50105 50100 50104, .loadN 50107 50105,
      .addN 50108 50101 50101, .constN 50109 1]) c c₁ k₁ ∧ k₁ = 11 ∧
      (c₁.nreg 50101 = C.m ∧ c₁.nreg 50106 = C.topIdx ∧ c₁.nreg 50107 = c.nmem (X + 4) ∧
        c₁.nreg 50108 = 2 * C.m ∧ c₁.nreg 50109 = 1 ∧
        (∀ r, (r < 50101 ∨ 50109 < r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; grind)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · config_simp; simp_all
    · simp_all
    · simp_all
    · config_simp; grind
    · config_simp
    · intro r hr; simp only [upd]; grind
  obtain ⟨q01, q06, q07, q08, q09, r₁, m₁⟩ := q
  have w₁ := e₁.wb_right
  have hsS : C.sideS C.sideBeta = if C.sideBeta = true then C.topIdx else 2 * C.m - C.topIdx := by
    grind [Chain.sideS]
  obtain ⟨c₂, k₂, e₂, hk₂, q02, r₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 50107 50109 (.instr (.subN 50102 50108 50106))
        (.ifLtN 50109 50107 (.instr (.subN 50102 50108 50106)) (.instr (.copyN 50102 50106))))
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50102 = C.sideS C.sideBeta ∧
      ∀ r, r ≠ 50102 → c₂.nreg r = c₁.nreg r := by
    by_cases h0 : c.nmem (X + 4) < 1
    · have hβ : C.sideBeta = false := by
        simp_all
      refine spec_ifLtN_true (by omega) (spec_instr (Exec.subN w₁ _ _ _)
        fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      simp_all
    · refine spec_ifLtN_false (by omega) ?_
      by_cases h2 : 1 < c.nmem (X + 4)
      · have hβ : C.sideBeta = false := by
          grind
        refine spec_ifLtN_true (by omega) (spec_instr (Exec.subN w₁ _ _ _)
          fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
        simp_all
      · have hβ : C.sideBeta = true := hb.1 (by omega)
        refine spec_ifLtN_false (by omega) (spec_instr (Exec.copyN w₁ _ _)
          fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
        simp_all
  refine ⟨c₂, _, .seq e₁ e₂, by omega, by simp_all, q02,
    by simp_all, fun r hr => by grind,
    by rw [(exec_frameB e₂ (B := fun r => r == 50102) (by decide)).2.2.1, m₁]⟩

/-! ## Generic arithmetic blocks -/

/-- `dst := candIdx`-style: `if j < s then j + d else j - s`. -/
def candR (j s d dst : ℕ) : Stmt := .ifLtN j s (.instr (.addN dst j d)) (.instr (.subN dst j s))

theorem candR_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {j s d dst : ℕ}
    (hjd : c.nreg j < c.nreg s → c.nreg j + c.nreg d ≤ W) :
    ∃ c' k, Exec P W (candR j s d dst) c c' k ∧ k ≤ 3 ∧
      c'.nreg dst = (if c.nreg j < c.nreg s then c.nreg j + c.nreg d else c.nreg j - c.nreg s) ∧
      ∀ r, r ≠ dst → c'.nreg r = c.nreg r := by
  unfold candR
  by_cases h : c.nreg j < c.nreg s
  · exact spec_ifLtN_true h (spec_instr (Exec.addN hw _ _ _ (hjd h)) fun _ =>
      ⟨by omega, by simp [h], fun r hr => by simp [hr]⟩)
  · exact spec_ifLtN_false h (spec_instr (Exec.subN hw _ _ _) fun _ =>
      ⟨by omega, by simp [h], fun r hr => by simp [hr]⟩)

/-- The right lengths `rL1, rL2, rδ` from `A = 2m - τ` (`50130`), `B = 2m₂ - τ'` (`50131`), `2m₂` (`50115`). -/
def selR : Stmt :=
  .ifLtN 50130 50115 (block [.addN 50212 50115 50160, .constN 50213 0, .constN 50214 0])
    (.ifLtN 50131 50115 (block [.copyN 50212 50131, .subN 50213 50115 50131, .constN 50214 7])
      (block [.copyN 50212 50115, .constN 50213 0, .constN 50214 0]))

theorem selR_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
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
    exec_block
    all_goals simp_all
  · refine spec_ifLtN_false ha ?_
    by_cases hb : c.nreg 50131 < c.nreg 50115
    · refine spec_ifLtN_true hb ?_
      exec_block
      all_goals (simp_all +zetaDelta <;> omega)
    · refine spec_ifLtN_false hb ?_
      exec_block
      all_goals try omega
      ram_simp

/-- The left lengths `lL1, lL2, lδ` from `A' = 2m - τL` (`50132`), `B' = 2m₁ - τ'L` (`50133`), `2m₁` (`50118`). -/
def selL : Stmt :=
  .ifLtN 50132 50118 (block [.addN 50217 50118 50160, .constN 50218 0, .constN 50219 0])
    (.ifLtN 50133 50118 (block [.copyN 50217 50133, .subN 50218 50118 50133, .constN 50219 7])
      (block [.copyN 50217 50118, .constN 50218 0, .constN 50219 0]))

theorem selL_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
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
    exec_block
    all_goals simp_all
  · refine spec_ifLtN_false ha ?_
    by_cases hb : c.nreg 50133 < c.nreg 50118
    · refine spec_ifLtN_true hb ?_
      exec_block
      all_goals (simp_all +zetaDelta <;> omega)
    · refine spec_ifLtN_false hb ?_
      exec_block
      all_goals try omega
      ram_simp


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

theorem wr_junConst : wr Bjun junConst = true := by decide

/-- The machine value of a candidate. -/
theorem cand_val {m S j : ℕ} :
    (if j < S then j + (2 * m - S) else j - S) = candIdx m S j := rfl

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

theorem junHead_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {H : Host}
    {J : Merge.Junction}
    (hJ : JunctionAt c.nmem (c.nreg 50200) (c.nreg 50201) (c.nreg 50202) (Qof P) H J)
    (hXl : c.nreg 50200 + 5 ≤ W) (hXr : c.nreg 50201 + 5 ≤ W) (hXw : c.nreg 50202 + 5 ≤ W)
    (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junHead c c' k ∧ k ≤ 70 ∧ HeadVals J c' ∧ c'.nmem = c.nmem ∧
      ∀ r, (r < 50100 ∨ 50200 ≤ r) → c'.nreg r = c.nreg r := by
  obtain ⟨hCl, hCr, hCw⟩ := hJ
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hlm : J.left.m = J.m₁ := rfl
  have hrm : J.right.m = J.m₂ := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50119 6, .constN 50160 7,
      .copyN 50100 50202]) c c₁ k₁ ∧ k₁ = 3 ∧ (c₁.nreg 50119 = 6 ∧ c₁.nreg 50160 = 7 ∧
      c₁.nreg 50100 = c.nreg 50202 ∧
      (∀ r, r ≠ 50119 → r ≠ 50160 → r ≠ 50100 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    exec_block
    all_goals try omega
    simp_all
  obtain ⟨p19, p60, p00, r₁, m₁⟩ := q
  obtain ⟨c₂, k₂, e₂, hk₂, a01, a02, a08, r₂, m₂⟩ := readS_exec (P := P) c₁ e₁.wb_right p00
    (by simp_all +zetaDelta <;> omega) hXw (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50110 50101,
      .copyN 50111 50102, .copyN 50112 50108, .copyN 50100 50201]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 50110 = J.whole.m ∧ c₃.nreg 50111 = J.whole.sideS J.whole.sideBeta ∧
        c₃.nreg 50112 = 2 * J.whole.m ∧ c₃.nreg 50100 = c.nreg 50201 ∧
        (∀ r, r ≠ 50110 → r ≠ 50111 → r ≠ 50112 → r ≠ 50100 → c₃.nreg r = c₂.nreg r)) := by
    have hw₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, by ram_simp, by ram_simp, by ram_simp,
      ?_, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩
    ram_simp
  obtain ⟨p10, p11, p12, p00', r₃⟩ := q
  have m₃ : c₃.nmem = c.nmem := by
    rw [(exec_frameB e₃ (B := fun r => decide (50100 ≤ r ∧ r < 50113)) (by decide)).2.2.1, m₂, m₁]
  obtain ⟨c₄, k₄, e₄, hk₄, b01, b02, b08, r₄, m₄⟩ := readS_exec (P := P) c₃ e₃.wb_right p00'
    (by rw [m₃]; exact hCr) hXr (by omega)
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 50113 50101,
      .copyN 50114 50102, .copyN 50115 50108, .copyN 50100 50200]) c₄ c₅ k₅ ∧ k₅ = 4 ∧
      (c₅.nreg 50113 = J.right.m ∧ c₅.nreg 50114 = J.right.sideS J.right.sideBeta ∧
        c₅.nreg 50115 = 2 * J.right.m ∧ c₅.nreg 50100 = c.nreg 50200 ∧
        (∀ r, r ≠ 50113 → r ≠ 50114 → r ≠ 50115 → r ≠ 50100 → c₅.nreg r = c₄.nreg r)) := by
    have hw₄ := e₄.wb_right
    exec_block <;> (config_simp; simp_all [Chazelle.upd] <;> omega_nf)
  obtain ⟨p13, p14, p15, p00'', r₅⟩ := q
  have m₅ : c₅.nmem = c.nmem := by
    rw [(exec_frameB e₅ (B := fun r => decide (50100 ≤ r ∧ r < 50116)) (by decide)).2.2.1, m₄, m₃]
  obtain ⟨c₆, k₆, e₆, hk₆, d01, d02, d08, r₆, m₆⟩ := readS_exec (P := P) c₅ e₅.wb_right p00''
    (by rw [m₅]; exact hCl) hXl (by omega)
  have ex : Exec P W junHead c c₆ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have k₅₆ : ∀ r, (r < 50101 ∨ 50109 < r) → r ≠ 50113 → r ≠ 50114 → r ≠ 50115 → r ≠ 50100 →
      c₆.nreg r = c₄.nreg r := fun r h0 h1 h2 h3 h4 => by grind
  ram_grind

/-- The tour offsets computed by `junMid`. -/
structure MidVals (J : Merge.Junction) (c : Config) : Prop where
  t20 : c.nreg 50120 = WalkEmbed.tpos J.whole J.m₁
  t22 : c.nreg 50122 = WalkEmbed.tpos J.right 0
  t25 : c.nreg 50125 = WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂)
  t27 : c.nreg 50127 = WalkEmbed.tpos J.left J.m₁
  v12 : c.nreg 50112 = 2 * J.whole.m
  v15 : c.nreg 50115 = 2 * J.right.m
  v18 : c.nreg 50118 = 2 * J.left.m
  v19 : c.nreg 50119 = 6
  v60 : c.nreg 50160 = 7

section
variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {J : Merge.Junction}
include hw
theorem junMid_exec (hv : HeadVals J c) (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junMid c c' k ∧ k ≤ 20 ∧ MidVals J c' ∧
      ∀ r, (r < 50100 ∨ 50200 ≤ r) → c'.nreg r = c.nreg r := by
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hlm : J.left.m = J.m₁ := rfl
  have hrm : J.right.m = J.m₂ := rfl
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hSw := J.whole.sideS_lt J.whole.sideBeta
  have hSr := J.right.sideS_lt J.right.sideBeta
  
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
    exec_block <;> (config_simp; grind [Chazelle.upd, Chazelle.Chain.sideBeta, Chazelle.WordsBounded, Chazelle.Core.SweepPrim.HeadVals])
  obtain ⟨u16, u17, u18, u21, u23, u24, u26, u28, r₁⟩ := q
  have k1 : ∀ r, r = 50110 ∨ r = 50111 ∨ r = 50112 ∨ r = 50113 ∨ r = 50114 ∨ r = 50115 ∨
      r = 50119 ∨ r = 50160 → c₁.nreg r = c.nreg r := fun r hr => by
    grind
  obtain ⟨c₂, k₂, e₂, hk₂, t20, r₂⟩ := candR_exec (P := P) (j := 50116) (s := 50111) (d := 50121)
    (dst := 50120) c₁ e₁.wb_right (by
      ram_grind)
  obtain ⟨c₃, k₃, e₃, hk₃, t22, r₃⟩ := candR_exec (P := P) (j := 50123) (s := 50114) (d := 50124)
    (dst := 50122) c₂ e₂.wb_right (by
      grind)
  obtain ⟨c₄, k₄, e₄, hk₄, t25, r₄⟩ := candR_exec (P := P) (j := 50126) (s := 50111) (d := 50121)
    (dst := 50125) c₃ e₃.wb_right (by
      grind [Chazelle.Core.SweepPrim.HeadVals.v11])
  obtain ⟨c₅, k₅, e₅, hk₅, t27, r₅⟩ := candR_exec (P := P) (j := 50116) (s := 50117) (d := 50128)
    (dst := 50127) c₄ e₄.wb_right (by
      grind)
  have k5 : ∀ r, r ≠ 50120 → r ≠ 50122 → r ≠ 50125 → r ≠ 50127 → c₅.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 h4 => by grind
  have ex : Exec P W junMid c c₅ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_⟩
  · rw [r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide), t20, u16, k1 _ (by omega), hv.v11,
      u21, cand_val, tpos_eq_cand _ (by omega)]
  · rw [r₅ _ (by decide), r₄ _ (by decide), t22, r₂ _ (by decide), r₂ _ (by decide),
      r₂ _ (by decide), u23, k1 _ (by omega), hv.v14, u24, cand_val, tpos_eq_cand _ (by omega)]
  · rw [r₅ _ (by decide), t25, r₃ _ (by decide), r₃ _ (by decide), r₃ _ (by decide),
      r₂ _ (by decide), r₂ _ (by decide), r₂ _ (by decide), u26, k1 _ (by omega), hv.v11, u21,
      cand_val, tpos_eq_cand _ (by omega)]
  · rw [t27, r₄ _ (by decide), r₄ _ (by decide), r₄ _ (by decide), r₃ _ (by decide),
      r₃ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), r₂ _ (by decide), r₂ _ (by decide),
      u16, u17, u28, cand_val, ← hlm, tpos_eq_cand _ (by omega)]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide), k1 _ (by omega), hv.v12]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide), k1 _ (by omega), hv.v15]
  · grind
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide), k1 _ (by omega), hv.v19]
  · rw [k5 _ (by decide) (by decide) (by decide) (by decide), k1 _ (by omega), hv.v60]
  · rw [k5 r (by omega) (by omega) (by omega) (by omega),
      r₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]

theorem junOut_exec (hv : MidVals J c) (hWm : 2 * J.whole.m + 7 ≤ W) :
    ∃ c' k, Exec P W junOut c c' k ∧ k = 8 ∧
      c'.nreg 50210 = 6 + WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50211 = 6 + WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50130 = 2 * J.whole.m - WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50131 = 2 * J.right.m - WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50215 = 6 + WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂) ∧
      c'.nreg 50216 = 6 + WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50132 = 2 * J.whole.m - WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂) ∧
      c'.nreg 50133 = 2 * J.left.m - WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50115 = 2 * J.right.m ∧ c'.nreg 50118 = 2 * J.left.m ∧ c'.nreg 50160 = 7 ∧
      ∀ r, (r < 50100 ∨ 50220 ≤ r) → c'.nreg r = c.nreg r := by
  have tR := WalkEmbed.tpos_lt J.whole J.m₁
  have tR' := WalkEmbed.tpos_lt J.right 0
  have tL := WalkEmbed.tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  have tL' := WalkEmbed.tpos_lt J.left J.m₁
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hlm : J.left.m = J.m₁ := rfl
  have hrm : J.right.m = J.m₂ := rfl
  unfold junOut
  exec_block
  all_goals try (config_simp; ram_grind)
  all_goals try (config_simp; rw [hv.v19, hv.t22]; omega)
  all_goals try (config_simp; rw [hv.v19, hv.t25]; omega)
  all_goals try (config_simp; rw [hv.v19, hv.t27]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; ram_grind
  · config_simp; exact hv.v15
  · config_simp; exact hv.v18
  · config_simp; exact hv.v60
  grind [upd]


end

/-- **Contract of `junConst`** (at most `120` steps). -/
theorem junConst_meets : Meets junConst {bLocate}
    (fun P W c => c.nreg 50200 + 5 ≤ W ∧ c.nreg 50201 + 5 ≤ W ∧ c.nreg 50202 + 5 ≤ W ∧
      ∃ H J, JunctionAt c.nmem (c.nreg 50200) (c.nreg 50201) (c.nreg 50202) (Qof P) H J ∧
        2 * J.whole.m + 7 ≤ W)
    (fun P c c' => ∀ H J, JunctionAt c.nmem (c.nreg 50200) (c.nreg 50201) (c.nreg 50202)
      (Qof P) H J →
      c'.nreg 50210 = 6 + WalkEmbed.tpos J.whole J.m₁ ∧
      c'.nreg 50211 = 6 + WalkEmbed.tpos J.right 0 ∧
      c'.nreg 50212 = Sweep.rL1 J ∧ c'.nreg 50213 = Sweep.rL2 J ∧ c'.nreg 50214 = Sweep.rδ J ∧
      c'.nreg 50215 = 6 + WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂) ∧
      c'.nreg 50216 = 6 + WalkEmbed.tpos J.left J.m₁ ∧
      c'.nreg 50217 = Sweep.lL1 J ∧ c'.nreg 50218 = Sweep.lL2 J ∧ c'.nreg 50219 = Sweep.lδ J)
    (fun _ _ => 120) := by
  intro P W c hw ⟨hXl, hXr, hXw, H, J, hJ, hWm⟩ hroom
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hlm : J.left.m = J.m₁ := rfl
  have hrm : J.right.m = J.m₂ := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, hv₁, -, -⟩ := junHead_exec c hw hJ hXl hXr hXw hWm
  obtain ⟨c₂, k₂, e₂, hk₂, hv₂, -⟩ := junMid_exec c₁ e₁.wb_right hv₁ hWm
  obtain ⟨c₃, k₃, e₃, hk₃, o10, o11, a30, a31, o15, o16, a32, a33, a15, a18, a60, -⟩ :=
    junOut_exec c₂ e₂.wb_right hv₂ hWm
  obtain ⟨c₄, k₄, e₄, hk₄, s12, s13, s14, r₄⟩ := selR_exec (P := P) c₃ e₃.wb_right a60
    (by omega)
  have k4 : ∀ r, r ≠ 50212 → r ≠ 50213 → r ≠ 50214 → c₄.nreg r = c₃.nreg r := r₄
  obtain ⟨c₅, k₅, e₅, hk₅, s17, s18, s19, r₅⟩ := selL_exec (P := P) c₄ e₄.wb_right
    (by grind)
    (by grind)
  have k5 : ∀ r, r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → c₅.nreg r = c₄.nreg r := r₅
  have ex : Exec P W junConst c c₅ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, by grind, ?_, ?_⟩
  · intro H' J' ⟨hCl', hCr', hCw'⟩
    obtain ⟨hCl, hCr, hCw⟩ := hJ
    have eL : J'.left = J.left := NFLoc.chain_eq_of_desc hCl' hCl
    have eR : J'.right = J.right := NFLoc.chain_eq_of_desc hCr' hCr
    have eW : J'.whole = J.whole := NFLoc.chain_eq_of_desc hCw' hCw
    have e1 : J'.m₁ = J.m₁ := congrArg Chain.m eL
    have e2 : J'.m₂ = J.m₂ := congrArg Chain.m eR
    
    
    have tR' := WalkEmbed.tpos_lt J.right 0
    
    have tL' := WalkEmbed.tpos_lt J.left J.m₁
    have w12 : c₅.nreg 50212 = c₄.nreg 50212 := k5 _ (by decide) (by decide) (by decide)
    have w13 : c₅.nreg 50213 = c₄.nreg 50213 := k5 _ (by decide) (by decide) (by decide)
    have w14 : c₅.nreg 50214 = c₄.nreg 50214 := k5 _ (by decide) (by decide) (by decide)
    have x32 : c₄.nreg 50132 = c₃.nreg 50132 := k4 _ (by decide) (by decide) (by decide)
    have x33 : c₄.nreg 50133 = c₃.nreg 50133 := k4 _ (by decide) (by decide) (by decide)
    have x18 : c₄.nreg 50118 = c₃.nreg 50118 := k4 _ (by decide) (by decide) (by decide)
    grind [Sweep.rL1, Sweep.rL2, Sweep.rδ, Sweep.lL1, Sweep.lL2, Sweep.lδ]
  · exact NFLoc.frame_of_frameB (exec_frameB ex wr_junConst) (fun r hr => by
      simp only [Bjun, Bool.or_eq_true, decide_eq_true_eq] at hr
      grind [ALLOC, bandOf, bLocate, Finset.mem_singleton]) _

end

end SweepPrim

end Chazelle.Core
