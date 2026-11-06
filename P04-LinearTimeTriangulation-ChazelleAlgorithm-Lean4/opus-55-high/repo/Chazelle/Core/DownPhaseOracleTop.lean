module

public import Chazelle.Core.DownPhaseOracleTopM
public import Chazelle.Core.DownPhaseOracleRamC

/-!
# WP-M (E7-B, RAM part 4): the top of a chain by the grade table (O5)

`topLoop` runs the bottom-up dyadic cover of the vertex range `[x, y]` of `Q`
(`y ≤ n - 1`), one grade per iteration (registers `170050` `q_l`, `170051` `q_r`, `170052` the
grade `g`, `170053` `2^g`, `170054` `lo = q_l 2^g`, `170055` `hi = q_r 2^g`): an odd `q_l`
contributes the block `(g, q_l)` (its top from the grade table, or its end vertex for `g = 0`),
an odd `q_r` the block `(g, q_r - 1)`; the running maximum `170046` (a vertex index of `Q`) is
kept by one sign test per block (`cmpUpd`).  Invariant (`TopI`): every vertex of `[x, lo]` and of
`[hi, y]` is at most as high as the running maximum.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The programs -/

/-- `170058 := q_l mod 2` (`170057 := q_l / 2` from the halving table). -/
def parL : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170057 170056, .subN 170058 170050 170057,
    .subN 170058 170058 170057]

/-- `170058 := q_r mod 2`. -/
def parR : Stmt :=
  block [.addN 170056 170017 170051, .loadN 170057 170056, .subN 170058 170051 170057,
    .subN 170058 170058 170057]

/-- The candidate of the block `(g, q_l)` starting at `lo`: its end vertex for `g = 0`, else its top read from the grade table. -/
def candL : Stmt :=
  .ifLtN 170052 170011 (block [.addN 170059 170054 170011])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170050,
      .addN 170056 170056 170050, .addN 170056 170056 170050, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170054 170056])

/-- The right candidate for `g = 0` is the start of the block (its end is covered). -/
def candR : Stmt :=
  .ifLtN 170052 170011 (block [.copyN 170059 170055])
    (block [.addN 170056 170016 170052, .loadN 170056 170056, .addN 170056 170056 170051,
      .addN 170056 170056 170051, .addN 170056 170056 170051, .loadN 170056 170056,
      .constN 170067 3, .addN 170056 170056 170067, .loadN 170056 170056,
      .addN 170059 170055 170056])

/-- The running maximum: `170046 := 170059` if it is higher. -/
def cmpUpd : Stmt :=
  .seq (block [.constN 170060 0, .copyN 170061 170046, .constN 170063 0, .copyN 170064 170059])
    (.seq (SweepPrim.kbit 170060 170063 170060 1 170066)
      (.ifLtN 170012 170066 (block [.copyN 170046 170059]) .skip))

/-- The left block of a grade (if `q_l` is odd). -/
def stepL : Stmt :=
  .ifLtN 170012 170058
    (.seq candL (.seq cmpUpd (block [.addN 170050 170050 170011, .addN 170054 170054 170053])))
    .skip

/-- The right block of a grade (if `q_r` is odd). -/
def stepR : Stmt :=
  .ifLtN 170012 170058
    (.seq (block [.subN 170051 170051 170011, .subN 170055 170055 170053]) (.seq candR cmpUpd))
    .skip

/-- The next grade. -/
def halve : Stmt :=
  block [.addN 170056 170017 170050, .loadN 170050 170056, .addN 170056 170017 170051,
    .loadN 170051 170056, .addN 170052 170052 170011, .addN 170053 170053 170053]

/-- One grade of the cover. -/
def topBody : Stmt := .seq parL (.seq stepL (.seq parR (.seq stepR halve)))

/-- **The cover of `[x, y]`** (`x` in `170050`, `y` in `170051` on entry; the maximum already
covers both ends). -/
def topLoop : Stmt :=
  .seq (block [.constN 170052 0, .constN 170053 1, .copyN 170054 170050, .copyN 170055 170051])
    (.whileLtN 170050 170051 topBody)

/-- The registers the top computation writes. -/
def Btop (r : ℕ) : Bool := decide (170046 ≤ r ∧ r < 170070) || Bk r

theorem wr_kbit_top (a b d op dst : ℕ) (h1 : 170046 ≤ dst) (h2 : dst < 170070) :
    wr Btop (SweepPrim.kbit a b d op dst) = true :=
  SweepPrim.wr_mono (SweepPrim.wr_kbit a b d op dst) (fun r hr => by
    simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
    unfold Btop; rcases hr with hr | hr
    · simp [hr]
    · subst hr; simp; omega)

theorem wr_cmpUpd : wr Btop cmpUpd = true := by
  simp only [cmpUpd, wr, block, wrOK, wr_kbit_top _ _ _ _ 170066 (by norm_num) (by norm_num),
    Bool.and_true, Bool.true_and]
  decide

theorem wr_topLoop : wr Btop topLoop = true := by
  simp only [topLoop, topBody, stepL, stepR, halve, parL, parR, candL, candR, wr, block, wrOK, wr_cmpUpd,
    Bool.and_true, Bool.true_and]
  decide

/-! ## The steps -/

section steps

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The height of vertex `v` of `Q`. -/
noncomputable abbrev Y (P : Polygon) (v : ℕ) : ℝ := ((Qof P).vtx v).2

/-- **The parity of `q_l`.** -/
theorem parL_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hq : c.nreg 170050 ≤ P.n) :
    ∃ c' k, Exec P W parL c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170050 % 2 ∧
      (∀ r, r ≠ 170056 → r ≠ 170057 → r ≠ 170058 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have hlow := ShootCut.grade_low hS.grade
  have hhalf := (hS.grade.holds).2.2.1 (c.nreg 170050) hq
  have hm : c.nmem (s.m₀ (s.h + 3) + c.nreg 170050) = c.nreg 170050 / 2 := by
    rw [hS.mem _ (hlow.2.2 _ hq)]; exact hhalf
  have hW := hS.hW
  unfold hostWords at hW
  unfold parL
  exec_block
  · config_simp; rw [hS.r17]; have := hlow.2.2 _ hq; have := hS.alloc; have := hw.1 ALLOC
    omega
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl⟩
  · config_simp; rw [hS.r17, hm]; omega
  · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The parity of `q_r`.** -/
theorem parR_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hq : c.nreg 170051 ≤ P.n) :
    ∃ c' k, Exec P W parR c c' k ∧ k = 4 ∧ c'.nreg 170058 = c.nreg 170051 % 2 ∧
      (∀ r, r ≠ 170056 → r ≠ 170057 → r ≠ 170058 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have hlow := ShootCut.grade_low hS.grade
  have hhalf := (hS.grade.holds).2.2.1 (c.nreg 170051) hq
  have hm : c.nmem (s.m₀ (s.h + 3) + c.nreg 170051) = c.nreg 170051 / 2 := by
    rw [hS.mem _ (hlow.2.2 _ hq)]; exact hhalf
  unfold parR
  exec_block
  · config_simp; rw [hS.r17]; have := hlow.2.2 _ hq; have := hS.alloc; have := hw.1 ALLOC
    omega
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl⟩
  · config_simp; rw [hS.r17, hm]; omega
  · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- The top index read from the descriptor of the block `(g, b)`. -/
def blkT (m : ℕ → ℕ) (h g b : ℕ) : ℕ := m (blkD m h g b + 3)

/-- **The left candidate**: the end vertex `lo + 1` of an edge (`g = 0`), else the top of the
block `(g, q_l)` from the grade table. -/
theorem candL_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      (c.nreg 170050 + 1) * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hlo : c.nreg 170054 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W candL c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170054 + 1 else
        c.nreg 170054 + blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170050)) ∧
      (∀ r, r ≠ 170056 → r ≠ 170059 → r ≠ 170067 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have hW := hS.hW
  unfold hostWords at hW
  have hA := hw.1 ALLOC
  have hal := hS.alloc
  unfold candL
  by_cases hg : c.nreg 170052 < c.nreg 170011
  · refine spec_ifLtN_true hg ?_
    have hg0 : c.nreg 170052 = 0 := by rw [hS.r11] at hg; omega
    exec_block
    · config_simp; rw [hS.r11]; rw [hg0] at hlo; simp at hlo; omega
    refine ⟨by omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; rw [ite_eq_left hg0, hS.r11]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false hg ?_
    have hg1 : 1 ≤ c.nreg 170052 := by rw [hS.r11] at hg; omega
    obtain ⟨hgΛ, hb⟩ := hblk hg1
    obtain ⟨a2, ar, ae, ad, hTb, -⟩ := block_top hS.grade hgΛ hb
    have m1 : c.nmem (s.m₀ (s.h + 2) + c.nreg 170052) = s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) :=
      hS.mem _ ar
    have m2 : c.nmem (s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + 3 * c.nreg 170050) =
        blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170050) := hS.mem _ ae
    have m3 : c.nmem (blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170050) + 3) =
        blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170050) := hS.mem _ ad
    have hpow : 1 ≤ 2 ^ c.nreg 170052 := Nat.one_le_two_pow
    have m2' : c.nmem (s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + c.nreg 170050 + c.nreg 170050 +
        c.nreg 170050) = blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170050) := by
      rw [show s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + c.nreg 170050 + c.nreg 170050 +
        c.nreg 170050 = s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + 3 * c.nreg 170050 by ring]
      exact m2
    have hTb' : blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170050) ≤ 2 ^ c.nreg 170052 := hTb
    exec_block
    all_goals first | omega | skip
    all_goals first | (config_simp; rw [hS.r16]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1, m2']; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1, m2', m3]; omega) | skip
    refine ⟨by omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; rw [ite_eq_right (by omega), hS.r16, m1, m2', m3]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The right candidate**: the start vertex `hi` of an edge (`g = 0`), else the top of the
block `(g, q_r)` (after the decrement). -/
theorem candR_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      (c.nreg 170051 + 1) * 2 ^ c.nreg 170052 ≤ P.n - 1)
    (hhi : c.nreg 170055 + 2 ^ c.nreg 170052 ≤ P.n) :
    ∃ c' k, Exec P W candR c c' k ∧ k ≤ 12 ∧
      c'.nreg 170059 = (if c.nreg 170052 = 0 then c.nreg 170055 else
        c.nreg 170055 + blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170051)) ∧
      (∀ r, r ≠ 170056 → r ≠ 170059 → r ≠ 170067 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have hW := hS.hW
  unfold hostWords at hW
  have hA := hw.1 ALLOC
  have hal := hS.alloc
  unfold candR
  by_cases hg : c.nreg 170052 < c.nreg 170011
  · refine spec_ifLtN_true hg ?_
    have hg0 : c.nreg 170052 = 0 := by rw [hS.r11] at hg; omega
    exec_block
    refine ⟨by omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; rw [ite_eq_left hg0]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false hg ?_
    have hg1 : 1 ≤ c.nreg 170052 := by rw [hS.r11] at hg; omega
    obtain ⟨hgΛ, hb⟩ := hblk hg1
    obtain ⟨a2, ar, ae, ad, hTb, -⟩ := block_top hS.grade hgΛ hb
    have m1 : c.nmem (s.m₀ (s.h + 2) + c.nreg 170052) = s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) :=
      hS.mem _ ar
    have m2 : c.nmem (s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + 3 * c.nreg 170051) =
        blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170051) := hS.mem _ ae
    have m3 : c.nmem (blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170051) + 3) =
        blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170051) := hS.mem _ ad
    have hpow : 1 ≤ 2 ^ c.nreg 170052 := Nat.one_le_two_pow
    have m2' : c.nmem (s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + c.nreg 170051 + c.nreg 170051 +
        c.nreg 170051) = blkD s.m₀ s.h (c.nreg 170052) (c.nreg 170051) := by
      rw [show s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + c.nreg 170051 + c.nreg 170051 +
        c.nreg 170051 = s.m₀ (s.m₀ (s.h + 2) + c.nreg 170052) + 3 * c.nreg 170051 by ring]
      exact m2
    have hTb' : blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170051) ≤ 2 ^ c.nreg 170052 := hTb
    exec_block
    all_goals first | omega | skip
    all_goals first | (config_simp; rw [hS.r16]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1]; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1, m2']; omega) | skip
    all_goals first | (config_simp; rw [hS.r16, m1, m2', m3]; omega) | skip
    refine ⟨by omega, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; rw [ite_eq_right (by omega), hS.r16, m1, m2', m3]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The running maximum.** -/
theorem cmpUpd_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hv : c.nreg 170046 < P.n) (hc : c.nreg 170059 < P.n) :
    ∃ c' k, Exec P W cmpUpd c c' k ∧ k ≤ 250 ∧
      c'.nreg 170046 = (if Y P (c.nreg 170046) < Y P (c.nreg 170059) then c.nreg 170059
        else c.nreg 170046) ∧
      (∀ r, r ≠ 170046 → (r < 170060 ∨ 170067 ≤ r) → (r < 10000 ∨ 10500 ≤ r) →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  have hW := hS.nW
  obtain ⟨c₁, k₁, e₁, hk₁, h60, h61, h63, h64, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 170060 0, .copyN 170061 170046, .constN 170063 0, .copyN 170064 170059])
      c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 170060 = 0 ∧ c₁.nreg 170061 = c.nreg 170046 ∧
      c₁.nreg 170063 = 0 ∧ c₁.nreg 170064 = c.nreg 170059 ∧
      (∀ r, r ≠ 170060 → r ≠ 170061 → r ≠ 170063 → r ≠ 170064 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp,
      fun r a b d e => ?_, rfl⟩
    simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  have s1 : SymPtIn c₁ 170060 (.vtx (c.nreg 170046)) := ⟨h60, h61⟩
  have s2 : SymPtIn c₁ 170063 (.vtx (c.nreg 170059)) := ⟨h63, h64⟩
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec (P := P) hS.good hW c₁ e₁.wb_right
    (a := 170060) (b := 170063) (d := 170060) (op := 1) (dst := 170066) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sa := .vtx (c.nreg 170046))
    (sb := .vtx (c.nreg 170059)) (sd := .vtx (c.nreg 170046)) hv hc hv s1 s2 s1
  simp only [SignTest, SymPt.eval] at t₂
  have k2 : ∀ r, 10500 ≤ r → r ≠ 170066 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; exact ⟨by omega, h2⟩)
  have w₂ := e₂.wb_right
  have hfr : ∀ r, r ≠ 170046 → (r < 170060 ∨ 170067 ≤ r) → (r < 10000 ∨ 10500 ≤ r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; exact ⟨by omega, by omega⟩), r₁ r (by omega) (by omega) (by omega)
      (by omega)]
  have c12 : c₂.nreg 170012 = 0 := by rw [hfr _ (by decide) (by decide) (by decide)]; exact hS.r12
  have c59 : c₂.nreg 170059 = c.nreg 170059 := by
    rw [k2 _ (by norm_num) (by norm_num), r₁ _ (by decide) (by decide) (by decide) (by decide)]
  have c46 : c₂.nreg 170046 = c.nreg 170046 := by
    rw [k2 _ (by norm_num) (by norm_num), r₁ _ (by decide) (by decide) (by decide) (by decide)]
  by_cases hb : c₂.nreg 170012 < c₂.nreg 170066
  · have hy : Y P (c.nreg 170046) < Y P (c.nreg 170059) := t₂.1 (by omega)
    have e₃ := exec_copyN_upd (P := P) w₂ 170046 170059
    refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true hb e₃)), by omega, ?_, fun r h1 h2 h3 => ?_, ?_⟩
    · simp only [upd_same]; rw [ite_eq_left hy, c59]
    · simp only [upd, ite_eq_right h1]; exact hfr r h1 h2 h3
    · show c₂.nmem = c.nmem; rw [F₂.2.2.1, m₁]
  · have hy : ¬ Y P (c.nreg 170046) < Y P (c.nreg 170059) := fun h => by
      have := t₂.2 h; omega
    refine ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_false hb (.skip w₂))), by omega, ?_,
      fun r h1 h2 h3 => hfr r h1 h2 h3, ?_⟩
    · rw [ite_eq_right hy, c46]
    · rw [F₂.2.2.1, m₁]

/-! ## The invariant of the cover -/

/-- **The invariant of the cover of `[x, y]`**: the grade registers, the covered ranges `[x, lo]`
and `[hi, y]` below the running maximum, which is a good vertex. -/
structure TopI (P : Polygon) (W : ℕ) (O : OracleIface) (s : Stat) (x y : ℕ) (G : ℕ → Prop)
    (c : Config) : Prop where
  env : SEnv P W O s c
  pw : c.nreg 170053 = 2 ^ c.nreg 170052
  lo : c.nreg 170054 = c.nreg 170050 * c.nreg 170053
  hi : c.nreg 170055 = c.nreg 170051 * c.nreg 170053
  xlo : x ≤ c.nreg 170054
  qq : c.nreg 170050 ≤ c.nreg 170051
  hiy : c.nreg 170055 ≤ y
  yn : y ≤ P.n - 1
  cap : y - x ≤ 2 ^ (s.m₀ s.h - 1)
  vbG : G (c.nreg 170046)
  vbn : c.nreg 170046 < P.n
  cov : ∀ v, (x ≤ v ∧ v ≤ c.nreg 170054) ∨ (c.nreg 170055 ≤ v ∧ v ≤ y) →
    Y P v ≤ Y P (c.nreg 170046)
  good : ∀ v, x ≤ v → v ≤ y → G v

theorem TopI.keep {x y : ℕ} {G : ℕ → Prop} {c c' : Config} (hI : TopI P W O s x y G c)
    (hk : ∀ r, (170000 ≤ r ∧ r < 170030) ∨ (170046 ≤ r ∧ r < 170056) → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) (hA : c'.nreg ALLOC = c.nreg ALLOC) : TopI P W O s x y G c' := by
  have k : ∀ r, 170046 ≤ r → r < 170056 → c'.nreg r = c.nreg r := fun r h1 h2 =>
    hk r (Or.inr ⟨h1, h2⟩)
  have k46 := k 170046 (by norm_num) (by norm_num)
  have k50 := k 170050 (by norm_num) (by norm_num)
  have k51 := k 170051 (by norm_num) (by norm_num)
  have k52 := k 170052 (by norm_num) (by norm_num)
  have k53 := k 170053 (by norm_num) (by norm_num)
  have k54 := k 170054 (by norm_num) (by norm_num)
  have k55 := k 170055 (by norm_num) (by norm_num)
  refine ⟨hI.env.keep (fun r h1 h2 => hk r (Or.inl ⟨h1, h2⟩)) (fun a _ => by rw [hm])
    (by rw [hA]), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩
  all_goals simp only [k46, k50, k51, k52, k53, k54, k55]
  · exact hI.pw
  · exact hI.lo
  · exact hI.hi
  · exact hI.xlo
  · exact hI.qq
  · exact hI.hiy
  · exact hI.vbG
  · exact hI.vbn
  · exact hI.cov

theorem pow_le_of_cap {g Λ d : ℕ} (hg : 1 ≤ g) (h1 : 2 ^ g ≤ d) (h2 : d ≤ 2 ^ (Λ - 1)) :
    g < Λ := by
  have h3 : 2 ^ g ≤ 2 ^ (Λ - 1) := h1.trans h2
  have h4 : g ≤ Λ - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have h5 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have : 1 ≤ Λ - 1 := by
    by_contra h
    have : Λ - 1 = 0 := by omega
    rw [this] at h3; simp at h3; omega
  omega

theorem Y_max_le {P : Polygon} {a b : ℕ} :
    Y P a ≤ Y P (if Y P a < Y P b then b else a) ∧ Y P b ≤ Y P (if Y P a < Y P b then b else a) := by
  split_ifs with h
  · exact ⟨h.le, le_rfl⟩
  · exact ⟨le_rfl, not_lt.1 h⟩

/-- **The left block of a grade.** -/
theorem stepL_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170050 % 2)
    (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W stepL c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 + c.nreg 170050 % 2 ∧ c'.nreg 170051 = c.nreg 170051 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem := by
  have hS := hI.env
  have hpw := hI.pw
  have hlo := hI.lo
  have hhi := hI.hi
  have hp1 : 1 ≤ 2 ^ c.nreg 170052 := Nat.one_le_two_pow
  have hprod : (c.nreg 170050 + 1) * 2 ^ c.nreg 170052 = c.nreg 170054 + c.nreg 170053 := by
    rw [hlo, hpw, Nat.add_mul, Nat.one_mul]
  have hloHi : c.nreg 170054 + c.nreg 170053 ≤ c.nreg 170055 := by
    rw [hlo, hhi]
    have : (c.nreg 170050 + 1) * c.nreg 170053 ≤ c.nreg 170051 * c.nreg 170053 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hxlo := hI.xlo
  have hhiy := hI.hiy
  have hyn := hI.yn
  have hqlo : c.nreg 170050 ≤ c.nreg 170054 := by
    rw [hlo, hpw]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hblk : 1 ≤ c.nreg 170052 → c.nreg 170052 < s.m₀ s.h ∧
      (c.nreg 170050 + 1) * 2 ^ c.nreg 170052 ≤ P.n - 1 := fun hg1 =>
    ⟨pow_le_of_cap hg1 (d := y - x) (by rw [← hpw]; omega) hI.cap, by omega⟩
  unfold stepL
  by_cases hodd : c.nreg 170012 < c.nreg 170058
  · refine spec_ifLtN_true hodd ?_
    have h1 : c.nreg 170050 % 2 = 1 := by rw [hS.r12, hpar] at hodd; omega
    -- the candidate
    obtain ⟨c₁, k₁, e₁, hk₁, v59, r₁, m₁⟩ := candL_exec c hw hS hblk (by rw [← hpw]; omega)
    have hcand : c₁.nreg 170059 < P.n ∧ x ≤ c₁.nreg 170059 ∧ c₁.nreg 170059 ≤ y := by
      rw [v59]
      split_ifs with hg0
      · have : c.nreg 170053 = 1 := by rw [hpw, hg0]; rfl
        omega
      · obtain ⟨hgΛ, hb⟩ := hblk (by omega)
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.1
        have : blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170050) ≤ 2 ^ c.nreg 170052 := hT
        omega
    -- every vertex of the block is below the candidate
    have hblkv : ∀ v, c.nreg 170054 < v → v ≤ c.nreg 170054 + c.nreg 170053 →
        Y P v ≤ Y P (c₁.nreg 170059) := by
      intro v hv1 hv2
      rw [v59]
      split_ifs with hg0
      · have : c.nreg 170053 = 1 := by rw [hpw, hg0]; rfl
        rw [show v = c.nreg 170054 + 1 by omega]
      · obtain ⟨hgΛ, hb⟩ := hblk (by omega)
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.2 (v - c.nreg 170054) (by rw [← hpw]; omega)
        have e1 : c.nreg 170050 * 2 ^ c.nreg 170052 = c.nreg 170054 := by rw [hlo, hpw]
        rw [e1, show c.nreg 170054 + (v - c.nreg 170054) = v by omega] at hT
        exact hT
    have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => r₁ r (by omega) (by omega) (by omega))
      (fun a _ => by rw [m₁]) (by rw [r₁ _ (by decide) (by decide) (by decide)])
    have v46 : c₁.nreg 170046 = c.nreg 170046 := r₁ _ (by decide) (by decide) (by decide)
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      (by rw [v46]; exact hI.vbn) hcand.1
    have k2 : ∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) →
        c₂.nreg r = c.nreg r := fun r h1 h2 => by
      rw [r₂ r (by omega) (by omega) h2, r₁ r (by omega) (by omega) (by omega)]
    have k2' : ∀ r, 170050 ≤ r → r < 170056 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
      rw [r₂ r (by omega) (by omega) (by omega), r₁ r (by omega) (by omega) (by omega)]
    have S₂ : SEnv P W O s c₂ := S₁.keep (fun r h1 h2 => by
        rw [r₂ r (by omega) (by omega) (by omega)]) (fun a _ => by rw [m₂]) (by
        rw [r₂ _ (by decide) (by decide) (by decide)])
    have w₂ := e₂.wb_right
    have hmx := Y_max_le (P := P) (a := c.nreg 170046) (b := c₁.nreg 170059)
    rw [← v46] at hmx
    rw [← v46'] at hmx
    refine spec_seq ⟨c₁, k₁, e₁, spec_seq ⟨c₂, k₂, e₂, ?_⟩⟩
    have hW := hS.hW
    unfold hostWords at hW
    exec_block
    · config_simp; rw [k2' _ (by norm_num) (by norm_num), S₂.r11]; omega
    · config_simp; rw [k2' _ (by norm_num) (by norm_num), k2' _ (by norm_num) (by norm_num)]
      omega
    refine ⟨by omega, ⟨S₂.keep (fun r h1 h2 => by
          simp only [Config.nreg_mk, upd]; rw [ite_eq_right (by omega), ite_eq_right (by omega)])
        (fun a _ => rfl) (by simp [upd, ALLOC]), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_,
        hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    all_goals config_simp
    all_goals try rw [S₂.r11]
    all_goals try rw [k2' 170050 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170051 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170052 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170053 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170054 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170055 (by norm_num) (by norm_num)]
    · exact hpw
    · rw [hlo]; ring
    · exact hhi
    · omega
    · omega
    · omega
    · rw [v46']; split_ifs
      · exact hI.good _ hcand.2.1 hcand.2.2
      · rw [v46]; exact hI.vbG
    · rw [v46']; split_ifs
      · exact hcand.1
      · rw [v46]; exact hI.vbn
    · intro v hv
      by_cases hv1 : v ≤ c.nreg 170054
      · exact (hI.cov v (Or.inl ⟨hv.elim (fun h => h.1) (fun h => by omega), hv1⟩)).trans (v46 ▸ hmx.1)
      by_cases hv2 : c.nreg 170055 ≤ v
      · exact (hI.cov v (Or.inr ⟨hv2, hv.elim (fun h => by omega) (fun h => h.2)⟩)).trans (v46 ▸ hmx.1)
      · exact (hblkv v (by omega) (hv.elim (fun h => h.2) (fun h => by omega))).trans hmx.2
    · omega
    · simp only [upd]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact k2 r h1 h2
    · rw [v46] at hmx; exact hmx.1
  · refine spec_ifLtN_false hodd ?_
    have h0 : c.nreg 170050 % 2 = 0 := by rw [hS.r12, hpar] at hodd; omega
    refine spec_skip hw ⟨by omega, hI, by omega, rfl, rfl, fun r _ _ => rfl, le_rfl, rfl⟩

/-- The configuration after the decrement of `q_r` and `hi`. -/
def decCfg (c : Config) : Config :=
  { c with nreg := upd (upd c.nreg 170051 (c.nreg 170051 - c.nreg 170011)) 170055
                          (c.nreg 170055 - c.nreg 170053) }

/-- **The right block of a grade.** -/
theorem stepR_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hpar : c.nreg 170058 = c.nreg 170051 % 2)
    (hlt : c.nreg 170051 % 2 = 1 → c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W stepR c c' k ∧ k ≤ 280 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170051 = c.nreg 170051 - c.nreg 170051 % 2 ∧ c'.nreg 170050 = c.nreg 170050 ∧
      c'.nreg 170052 = c.nreg 170052 ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem := by
  have hS := hI.env
  have hpw := hI.pw
  have hlo := hI.lo
  have hhi := hI.hi
  have hp1 : 1 ≤ 2 ^ c.nreg 170052 := Nat.one_le_two_pow
  have hxlo := hI.xlo
  have hhiy := hI.hiy
  have hyn := hI.yn
  unfold stepR
  by_cases hodd : c.nreg 170012 < c.nreg 170058
  · refine spec_ifLtN_true hodd ?_
    have h1 : c.nreg 170051 % 2 = 1 := by rw [hS.r12, hpar] at hodd; omega
    have hlt' := hlt h1
    have hprod : c.nreg 170051 * c.nreg 170053 = (c.nreg 170051 - 1) * c.nreg 170053 +
        c.nreg 170053 := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : c.nreg 170053 ≤ c.nreg 170051 * c.nreg 170053 :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hloHi : c.nreg 170054 + c.nreg 170053 ≤ c.nreg 170055 := by
      rw [hlo, hhi]
      have : (c.nreg 170050 + 1) * c.nreg 170053 ≤ c.nreg 170051 * c.nreg 170053 :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    refine spec_seq ?_
    exec_block
    -- the configuration after the decrement
    set c₀ : Config := decCfg c with hc₀
    have w₀ : WordsBounded W c₀ := ‹_›
    have k0 : ∀ r, r ≠ 170051 → r ≠ 170055 → c₀.nreg r = c.nreg r := fun r a b => by
      rw [hc₀]; simp [decCfg, upd, a, b]
    have c51 : c₀.nreg 170051 = c.nreg 170051 - 1 := by rw [hc₀]; simp only [decCfg]; config_simp; rw [hS.r11]
    have c55 : c₀.nreg 170055 = c.nreg 170055 - c.nreg 170053 := by rw [hc₀]; simp only [decCfg]; config_simp
    have S₀ : SEnv P W O s c₀ := hS.keep (fun r h1 h2 => k0 r (by omega) (by omega))
      (fun a _ => rfl) (by rw [k0 _ (by decide) (by decide)])
    have hblk : 1 ≤ c₀.nreg 170052 → c₀.nreg 170052 < s.m₀ s.h ∧
        (c₀.nreg 170051 + 1) * 2 ^ c₀.nreg 170052 ≤ P.n - 1 := fun hg1 => by
      rw [k0 _ (by decide) (by decide)] at hg1 ⊢
      refine ⟨pow_le_of_cap hg1 (d := y - x) (by rw [← hpw]; omega) hI.cap, ?_⟩
      rw [c51, show c.nreg 170051 - 1 + 1 = c.nreg 170051 by omega, ← hpw, ← hhi]; omega
    obtain ⟨c₁, k₁, e₁, hk₁, v59, r₁, m₁⟩ := candR_exec c₀ w₀ S₀ hblk (by
      rw [c55, k0 _ (by decide) (by decide), ← hpw]; omega)
    rw [c55, k0 170052 (by decide) (by decide), c51] at v59
    have hcand : c₁.nreg 170059 < P.n ∧ x ≤ c₁.nreg 170059 ∧ c₁.nreg 170059 ≤ y := by
      rw [v59]
      split_ifs with hg0
      · omega
      · obtain ⟨hgΛ, hb⟩ := hblk (by rw [k0 _ (by decide) (by decide)]; omega)
        rw [k0 170052 (by decide) (by decide)] at hgΛ hb; rw [c51] at hb
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.1
        have : blkT s.m₀ s.h (c.nreg 170052) (c.nreg 170051 - 1) ≤ 2 ^ c.nreg 170052 := hT
        omega
    have hblkv : ∀ v, c.nreg 170055 - c.nreg 170053 ≤ v → v < c.nreg 170055 →
        Y P v ≤ Y P (c₁.nreg 170059) := by
      intro v hv1 hv2
      rw [v59]
      split_ifs with hg0
      · have : c.nreg 170053 = 1 := by rw [hpw, hg0]; rfl
        rw [show v = c.nreg 170055 - c.nreg 170053 by omega]
      · obtain ⟨hgΛ, hb⟩ := hblk (by rw [k0 _ (by decide) (by decide)]; omega)
        rw [k0 170052 (by decide) (by decide)] at hgΛ hb; rw [c51] at hb
        have hT := (block_top hS.grade hgΛ hb).2.2.2.2.2 (v - (c.nreg 170055 - c.nreg 170053))
          (by rw [← hpw]; omega)
        have e1 : (c.nreg 170051 - 1) * 2 ^ c.nreg 170052 = c.nreg 170055 - c.nreg 170053 := by
          rw [← hpw, hhi]; omega
        rw [e1, show c.nreg 170055 - c.nreg 170053 + (v - (c.nreg 170055 - c.nreg 170053)) = v by
          omega] at hT
        exact hT
    have S₁ : SEnv P W O s c₁ := S₀.keep (fun r h1 h2 => r₁ r (by omega) (by omega) (by omega))
      (fun a _ => by rw [m₁]) (by rw [r₁ _ (by decide) (by decide) (by decide)])
    have v46 : c₁.nreg 170046 = c.nreg 170046 := by
      rw [r₁ _ (by decide) (by decide) (by decide), k0 _ (by decide) (by decide)]
    obtain ⟨c₂, k₂, e₂, hk₂, v46', r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
      (by rw [v46]; exact hI.vbn) hcand.1
    have hmx := Y_max_le (P := P) (a := c.nreg 170046) (b := c₁.nreg 170059)
    rw [← v46, ← v46'] at hmx
    rw [v46] at hmx
    have k2' : ∀ r, 170050 ≤ r → r < 170056 → c₂.nreg r = c₀.nreg r := fun r h1 h2 => by
      rw [r₂ r (by omega) (by omega) (by omega), r₁ r (by omega) (by omega) (by omega)]
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ⟨S₁.keep (fun r h1 h2 =>
        r₂ r (by omega) (by omega) (by omega)) (fun a _ => by rw [m₂]) (by
        rw [r₂ _ (by decide) (by decide) (by decide)]), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_,
        ?_, ?_, hI.good⟩, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, m₂.trans m₁⟩
    all_goals try rw [k2' 170050 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170051 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170052 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170053 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170054 (by norm_num) (by norm_num)]
    all_goals try rw [k2' 170055 (by norm_num) (by norm_num)]
    all_goals try rw [c51]
    all_goals try rw [c55]
    all_goals try rw [k0 170050 (by decide) (by decide)]
    all_goals try rw [k0 170052 (by decide) (by decide)]
    all_goals try rw [k0 170053 (by decide) (by decide)]
    all_goals try rw [k0 170054 (by decide) (by decide)]
    · exact hpw
    · exact hlo
    · rw [hhi, Nat.sub_mul, Nat.one_mul]
    · exact hxlo
    · omega
    · omega
    · rw [v46']; split_ifs
      · exact hI.good _ hcand.2.1 hcand.2.2
      · rw [v46]; exact hI.vbG
    · rw [v46']; split_ifs
      · exact hcand.1
      · rw [v46]; exact hI.vbn
    · intro v hv
      by_cases hv1 : v ≤ c.nreg 170054
      · exact (hI.cov v (Or.inl ⟨hv.elim (fun h => h.1) (fun h => by omega), hv1⟩)).trans hmx.1
      by_cases hv2 : c.nreg 170055 ≤ v
      · exact (hI.cov v (Or.inr ⟨hv2, hv.elim (fun h => by omega) (fun h => h.2)⟩)).trans hmx.1
      · exact (hblkv v (hv.elim (fun h => by omega) (fun h => h.1)) (by omega)).trans hmx.2
    · omega
    · rw [r₂ r (by omega) (by omega) h2, r₁ r (by omega) (by omega) (by omega),
        k0 r (by omega) (by omega)]
    · exact hmx.1
  · refine spec_ifLtN_false hodd ?_
    have h0 : c.nreg 170051 % 2 = 0 := by rw [hS.r12, hpar] at hodd; omega
    refine spec_skip hw ⟨by omega, hI, by omega, rfl, rfl, fun r _ _ => rfl, le_rfl, rfl⟩

/-- **The next grade**: halve `q_l`, `q_r` (both even), double `2^g`. -/
theorem halve_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hl : c.nreg 170050 % 2 = 0) (hr : c.nreg 170051 % 2 = 0)
    (hpn : c.nreg 170053 ≤ P.n) :
    ∃ c' k, Exec P W halve c c' k ∧ k = 6 ∧ TopI P W O s x y G c' ∧
      c'.nreg 170050 = c.nreg 170050 / 2 ∧ c'.nreg 170051 = c.nreg 170051 / 2 ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nreg 170046 = c.nreg 170046 ∧ c'.nmem = c.nmem := by
  have hS := hI.env
  have hlow := ShootCut.grade_low hS.grade
  have hpw := hI.pw
  have hlo := hI.lo
  have hhi := hI.hi
  have hp1 : 1 ≤ c.nreg 170053 := by rw [hpw]; exact Nat.one_le_two_pow
  have hqlo : c.nreg 170050 ≤ c.nreg 170054 := by rw [hlo]; exact Nat.le_mul_of_pos_right _ hp1
  have hqhi : c.nreg 170051 ≤ c.nreg 170055 := by rw [hhi]; exact Nat.le_mul_of_pos_right _ hp1
  have hxlo := hI.xlo
  have hhiy := hI.hiy
  have hyn := hI.yn
  have hqq := hI.qq
  have hql : c.nreg 170050 ≤ P.n := by omega
  have hqr : c.nreg 170051 ≤ P.n := by omega
  have h50 : c.nmem (s.m₀ (s.h + 3) + c.nreg 170050) = c.nreg 170050 / 2 := by
    rw [hS.mem _ (hlow.2.2 _ hql)]; exact (hS.grade.holds).2.2.1 _ hql
  have h51 : c.nmem (s.m₀ (s.h + 3) + c.nreg 170051) = c.nreg 170051 / 2 := by
    rw [hS.mem _ (hlow.2.2 _ hqr)]; exact (hS.grade.holds).2.2.1 _ hqr
  have hg : c.nreg 170052 < c.nreg 170053 := by rw [hpw]; exact Nat.lt_two_pow_self
  have hW := hS.hW
  unfold hostWords at hW
  have hA := hw.1 ALLOC
  have hal := hS.alloc
  have b1 := hlow.2.2 _ hql
  have b2 := hlow.2.2 _ hqr
  unfold halve
  exec_block
  all_goals first
    | (config_simp; rw [hS.r17]; omega)
    | (config_simp; rw [hS.r17, h50]; omega)
    | (config_simp; rw [hS.r11]; omega)
    | (config_simp; omega)
    | skip
  refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
      simp only [Config.nreg_mk, upd]; split_ifs <;> first | omega | rfl) (fun a _ => rfl)
      (by simp [upd, ALLOC]), ?_, ?_, ?_, ?_, ?_, ?_, hI.yn, hI.cap, ?_, ?_, ?_, hI.good⟩,
    ?_, ?_, fun r h1 => ?_, ?_, rfl⟩
  all_goals config_simp
  all_goals try rw [hS.r17]
  all_goals try rw [h50]
  all_goals try rw [h51]
  all_goals try rw [hS.r11]
  · rw [hpw, pow_succ]; ring
  · rw [hlo]
    obtain ⟨q, hq⟩ : ∃ q, c.nreg 170050 = 2 * q := ⟨c.nreg 170050 / 2, by omega⟩
    rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]; ring
  · rw [hhi]
    obtain ⟨q, hq⟩ : ∃ q, c.nreg 170051 = 2 * q := ⟨c.nreg 170051 / 2, by omega⟩
    rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]; ring
  · exact hxlo
  · omega
  · exact hhiy
  · exact hI.vbG
  · exact hI.vbn
  · exact hI.cov
  · simp only [upd]; split_ifs <;> first | omega | rfl

/-- **One grade of the cover.** -/
theorem topBody_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hI : TopI P W O s x y G c) (hlt : c.nreg 170050 < c.nreg 170051) :
    ∃ c' k, Exec P W topBody c c' k ∧ k ≤ 600 ∧ TopI P W O s x y G c' ∧
      2 * (c'.nreg 170051 - c'.nreg 170050) ≤ c.nreg 170051 - c.nreg 170050 ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem := by
  have hS := hI.env
  have hpw := hI.pw
  have hlo := hI.lo
  have hhi := hI.hi
  have hp1 : 1 ≤ c.nreg 170053 := by rw [hpw]; exact Nat.one_le_two_pow
  have hqlo : c.nreg 170050 ≤ c.nreg 170054 := by rw [hlo]; exact Nat.le_mul_of_pos_right _ hp1
  have hqhi : c.nreg 170051 ≤ c.nreg 170055 := by rw [hhi]; exact Nat.le_mul_of_pos_right _ hp1
  have hpn : c.nreg 170053 ≤ P.n := by
    have : (c.nreg 170050 + 1) * c.nreg 170053 ≤ c.nreg 170051 * c.nreg 170053 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul, ← hlo, ← hhi] at this
    have := hI.hiy; have := hI.yn; omega
  -- `q_l`
  obtain ⟨c₁, k₁, e₁, hk₁, p₁, r₁, m₁⟩ := parL_exec c hw hS (by have := hI.hiy; have := hI.yn; omega)
  have I₁ : TopI P W O s x y G c₁ := hI.keep (fun r h => r₁ r (by omega) (by omega) (by omega))
    m₁ (r₁ _ (by decide) (by decide) (by decide))
  have e50 : c₁.nreg 170050 = c.nreg 170050 := r₁ _ (by decide) (by decide) (by decide)
  have e51 : c₁.nreg 170051 = c.nreg 170051 := r₁ _ (by decide) (by decide) (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, I₂, q50, q51, q52, r₂, y₂, m₂⟩ := stepL_exec c₁ e₁.wb_right I₁
    (by rw [p₁, e50]) (by rw [e50, e51]; exact hlt)
  -- `q_r`
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, r₃, m₃⟩ := parR_exec c₂ e₂.wb_right I₂.env
    (by have := I₂.hiy; have := I₂.yn; have := I₂.hi; have := I₂.pw
        have : c₂.nreg 170051 ≤ c₂.nreg 170055 := by
          rw [I₂.hi]; exact Nat.le_mul_of_pos_right _ (by rw [I₂.pw]; exact Nat.one_le_two_pow)
        omega)
  have I₃ : TopI P W O s x y G c₃ := I₂.keep (fun r h => r₃ r (by omega) (by omega) (by omega))
    m₃ (r₃ _ (by decide) (by decide) (by decide))
  have f50 : c₃.nreg 170050 = c₂.nreg 170050 := r₃ _ (by decide) (by decide) (by decide)
  have f51 : c₃.nreg 170051 = c₂.nreg 170051 := r₃ _ (by decide) (by decide) (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, I₄, s51, s50, s52, r₄, y₄, m₄⟩ := stepR_exec c₃ e₃.wb_right I₃
    (by rw [p₃, f51]) (by
      intro h1
      have hq : c₂.nreg 170050 ≤ c₂.nreg 170051 := I₂.qq
      simp only [f50, f51, q50, q51, e50, e51] at hq h1 ⊢
      omega)
  have hpn4 : c₄.nreg 170053 ≤ P.n := by
    have g3 : c₃.nreg 170052 = c.nreg 170052 := by
      rw [r₃ _ (by decide) (by decide) (by decide), q52, r₁ _ (by decide) (by decide) (by decide)]
    rw [I₄.pw, s52, g3, ← hpw]; exact hpn
  obtain ⟨c₅, k₅, e₅, hk₅, I₅, t50, t51, r₅, y₅, m₅⟩ := halve_exec c₄ e₄.wb_right I₄
    (by rw [s50, f50, q50, e50]; exact (fun a : ℕ => by omega : ∀ a : ℕ, (a + a % 2) % 2 = 0) _)
    (by rw [s51, f51, q51, e51]; exact (fun a : ℕ => by omega : ∀ a : ℕ, (a - a % 2) % 2 = 0) _)
    hpn4
  rw [r₁ _ (by decide) (by decide) (by decide)] at y₂
  rw [r₃ _ (by decide) (by decide) (by decide)] at y₄
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, I₅, ?_, fun r h1 h2 => ?_,
    by rw [y₅]; exact y₂.trans y₄, by rw [m₅, m₄, m₃, m₂, m₁]⟩
  · rw [t50, t51, s50, s51, f50, f51, q50, q51, e50, e51]; omega
  · rw [r₅ r h1, r₄ r h1 h2, r₃ r (by omega) (by omega) (by omega), r₂ r h1 h2,
      r₁ r (by omega) (by omega) (by omega)]

/-- The potential of the cover drops under halving: `2 d' ≤ d`, `0 < d` give
`log (2 d') < log (2 d)`. -/
theorem log_half_lt {d d' : ℕ} (h : 2 * d' ≤ d) (hd : 0 < d) :
    Nat.log 2 (2 * d') < Nat.log 2 (2 * d) := by
  have e : Nat.log 2 (2 * d) = Nat.log 2 d + 1 := by
    rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
  rw [e]
  have := Nat.log_mono_right (b := 2) h
  omega

/-- **The cover of `[x, y]`.**  From `q_l = x ≤ y = q_r` (`y ≤ n - 1`, `y - x` within the cap)
and a running maximum `170046` at least as high as both ends, `topLoop` ends with a running
maximum at least as high as every vertex of `[x, y]`, within `602 size (y - x) + 6` steps. -/
theorem topLoop_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (hx : c.nreg 170050 = x) (hy : c.nreg 170051 = y) (hxy : x ≤ y)
    (hyn : y ≤ P.n - 1) (hcap : y - x ≤ 2 ^ (s.m₀ s.h - 1)) (hvG : G (c.nreg 170046))
    (hvn : c.nreg 170046 < P.n) (hvx : Y P x ≤ Y P (c.nreg 170046))
    (hvy : Y P y ≤ Y P (c.nreg 170046)) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W topLoop c c' k ∧ k ≤ 602 * Nat.log 2 (2 * (y - x)) + 6 ∧ SEnv P W O s c' ∧
      G (c'.nreg 170046) ∧ c'.nreg 170046 < P.n ∧
      (∀ v, x ≤ v → v ≤ y → Y P v ≤ Y P (c'.nreg 170046)) ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem := by
  obtain ⟨c₀, k₀, e₀, hk₀, I₀, h50, h51, h46, r₀, m₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.constN 170052 0, .constN 170053 1, .copyN 170054 170050, .copyN 170055 170051])
      c c₀ k₀ ∧ k₀ = 4 ∧ TopI P W O s x y G c₀ ∧ c₀.nreg 170050 = x ∧ c₀.nreg 170051 = y ∧
      c₀.nreg 170046 = c.nreg 170046 ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → c₀.nreg r = c.nreg r) ∧ c₀.nmem = c.nmem := by
    have hn := hS.nW
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ⟨hS.keep (fun r h1 h2 => by
        simp only [Config.nreg_mk, upd]; split_ifs <;> first | omega | rfl) (fun a _ => rfl)
        (by simp [upd, ALLOC]), ?_, ?_, ?_, ?_, ?_, ?_, hyn, hcap, ?_, ?_, ?_, hgood⟩,
      ?_, ?_, ?_, fun r h1 => ?_, rfl⟩
    all_goals config_simp
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try (first | exact hvG | exact hvn | omega | simp; done)
    · intro v hv
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [show v = x by omega]; exact hvx
      · rw [show v = y by omega]; exact hvy
    · simp only [upd]; split_ifs <;> first | omega | rfl
  let I : Config → Prop := fun c' => TopI P W O s x y G c' ∧ WordsBounded W c' ∧
    (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
    Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem
  obtain ⟨c', k, e, ⟨I', w', f', y', m'⟩, hex, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 170050) (b := 170051) (body := topBody) I
    (fun c' => 602 * Nat.log 2 (2 * (c'.nreg 170051 - c'.nreg 170050))) (fun _ h => h.2.1)
    (fun c₁ ⟨I₁, w₁, f₁, y₁, m₁⟩ hlt => by
      obtain ⟨c₂, k₂, e₂, hk₂, I₂, hd, f₂, y₂, m₂⟩ := topBody_exec c₁ w₁ I₁ hlt
      refine ⟨c₂, k₂, e₂, ⟨I₂, e₂.wb_right, fun r h1 h2 => (f₂ r h1 h2).trans (f₁ r h1 h2),
        y₁.trans y₂, m₂.trans m₁⟩, ?_⟩
      have := log_half_lt hd (by omega)
      have : 602 * (Nat.log 2 (2 * (c₂.nreg 170051 - c₂.nreg 170050)) + 1) ≤
          602 * Nat.log 2 (2 * (c₁.nreg 170051 - c₁.nreg 170050)) := Nat.mul_le_mul_left _ this
      omega)
    (c := c₀) ⟨I₀, e₀.wb_right, fun r h1 _ => r₀ r h1, by rw [h46], m₀⟩
  rw [h50, h51] at hk
  have hq := I'.qq
  have heq : c'.nreg 170050 = c'.nreg 170051 := by omega
  have hlh : c'.nreg 170054 = c'.nreg 170055 := by rw [I'.lo, I'.hi, heq]
  refine ⟨c', _, .seq e₀ e, by omega, I'.env, I'.vbG, I'.vbn, fun v h1 h2 => I'.cov v ?_, f', y', m'⟩
  by_cases hv : v ≤ c'.nreg 170054
  · exact Or.inl ⟨h1, hv⟩
  · exact Or.inr ⟨by omega, h2⟩

end steps

end

end IOrc

end Chazelle.Core
