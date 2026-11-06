module

public import Chazelle.Core.RestoreTIntKey
public import Chazelle.Core.ShootCutOrig
public import Chazelle.Core.SweepPrimAbs

/-!
# WP-E, the candidate test on the RAM: abscissa records in the interior model

The running minimum of the shot wrapper compares two hits by abscissa with `absCmp`, which reads
**abscissa records** (`AbsRec`: kind `1` and a symbolic point with that abscissa).  In a chain
model `absKey` computes them; in the interior model of `Q` every walk position is a symbolic point
of `Q`:

* `⟨e, 0⟩` is the vertex `iIdx bit n e` of `Q`;
* `⟨e, h + 1⟩` is the point `onEdge E h` of the edge `E = iEdgeIdx bit n e` of `Q` carrying the
  walk edge `e` (`ShootCut.pos_eq_onEdge`).

`iRec a b` writes that record into `50210 … 50213` (`iRec_exec`), with the radius
`coordBound Q + 1`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {P : Polygon} {W : ℕ}

/-! ## Mathematics -/

/-- The index of the edge of `Q` carrying the edge `e` of the interior walk. -/
def iEdgeIdx (bit n e : ℕ) : ℕ := if bit = 1 then e else if e + 1 < n then n - 2 - e else n - 1

/-- The symbolic point of the position `⟨e, h⟩` of the interior walk. -/
def iSym (bit n e h : ℕ) : SymPt :=
  if h = 0 then .vtx (iIdx bit n e) else .onEdge (iEdgeIdx bit n e) (h - 1)

theorem iEdgeIdx_lt {bit n e : ℕ} (hn : 3 ≤ n) (he : e < n) : iEdgeIdx bit n e < n := by
  unfold iEdgeIdx; split_ifs <;> omega

theorem iSym_lt {bit n e h : ℕ} (hn : 3 ≤ n) (he : e < n) (hh : h ≤ n) : (iSym bit n e h).Lt n := by
  unfold iSym; split_ifs with h0
  · exact iIdx_lt he
  · exact ⟨iEdgeIdx_lt hn he, by omega⟩

/-- The walk edge `e` joins consecutive vertices of `Q`. -/
theorem iIdx_edgeOK {bit n e : ℕ} (hn : 3 ≤ n) (he : e < n) :
    HostEdgeOK n (.vtx (iIdx bit n e)) (.vtx (iIdx bit n ((e + 1) % n))) := by
  simp only [HostEdgeOK, iIdx]
  rcases Nat.lt_or_ge (e + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs
    · left; rw [Nat.mod_eq_of_lt h1]
    · right; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have : e + 1 = n := by omega
    rw [this, Nat.mod_self]
    split_ifs
    · left; rw [← this, Nat.mod_self]
    · right; rw [show n - 1 - 0 + 1 = n by omega, Nat.mod_self]; omega

theorem iIdx_ne {bit n e : ℕ} (hn : 3 ≤ n) (he : e < n) :
    iIdx bit n e ≠ iIdx bit n ((e + 1) % n) := by
  unfold iIdx
  rcases Nat.lt_or_ge (e + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; split_ifs <;> omega
  · rw [show e + 1 = n by omega, Nat.mod_self]; split_ifs <;> omega

/-- **The edge of `Q` carrying the walk edge** is `iEdgeIdx`. -/
theorem edgeOf_iIdx {bit n e : ℕ} (hn : 3 ≤ n) (he : e < n) :
    ShootCut.edgeOf n (.vtx (iIdx bit n e)) (.vtx (iIdx bit n ((e + 1) % n))) = iEdgeIdx bit n e := by
  have hmod : (e + 1) % n = if e + 1 < n then e + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show e + 1 = n by omega, Nat.mod_self]
  by_cases hb : bit = 1
  · simp [ShootCut.edgeOf, iEdgeIdx, iIdx, hb]
  · have hne : n - 1 - (e + 1) % n ≠ (n - 1 - e + 1) % n := by
      rw [hmod]
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; rw [ite_eq_left (by omega), show n - 1 - 0 + 1 = n by omega, Nat.mod_self]; omega
      · rw [Nat.mod_eq_of_lt (show n - 1 - e + 1 < n by omega)]; split_ifs <;> omega
    simp only [ShootCut.edgeOf, iEdgeIdx, iIdx, hb, ite_false, ite_eq_right hne]
    rw [hmod]; split_ifs <;> omega

/-- **The point of a position of the interior walk** is its symbolic point. -/
theorem interior_pos_sym (hG : GoodEnv P) {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    {e h : ℕ} (he : e < P.n) :
    (interiorModel (Qof P)).pos (Qof P) ⟨e, h⟩ = (iSym bit P.n e h).eval (Qof P) := by
  have hn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ P.n := hG.1.1
  rcases h with _ | k
  · simp only [Model.pos, Model.param, iSym, ite_true, SymPt.eval, Geometry.lerp_zero]
    exact interior_wa hbit he
  · have hD := ShootCut.goodEnv_distinct hG
    have ha := interior_wa (P := P) hbit he
    have hb := interior_wb (P := P) hbit he
    have hi := iIdx_lt (bit := bit) he
    have hj := iIdx_lt (bit := bit) (Nat.mod_lt (e + 1) (show 0 < P.n by omega))
    have := ShootCut.pos_eq_onEdge (interiorModel (Qof P)) hD (by rw [hn]; omega)
      (p := e) (h := k) (sp₁ := .vtx (iIdx bit P.n e)) (sp₂ := .vtx (iIdx bit P.n ((e + 1) % P.n)))
      ha hb (by show _ < _; rwa [hn]) (by show _ < _; rwa [hn])
      (by rw [hn]; exact iIdx_edgeOK hn3 he)
      (by rw [ha, hb]; exact hD _ _ (by rwa [hn]) (by rwa [hn]) (iIdx_ne hn3 he))
    rw [this, hn, edgeOf_iIdx hn3 he]
    simp [iSym]

/-- **The abscissa of a proper position of the interior walk** is below `coordBound Q + 1`. -/
theorem interior_abs_lt (hG : GoodEnv P) {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    {x : WPos} (he : x.edge < P.n) (hp : ProperPos (interiorModel (Qof P)) (Qof P) P.n x) :
    |((interiorModel (Qof P)).pos (Qof P) x).1| < Jordan.coordBound (Qof P) + 1 := by
  have hn : (Qof P).n = P.n := shear_n _ _
  have ha := interior_wa (P := P) hbit he
  have hb := interior_wb (P := P) hbit he
  have hi := iIdx_lt (bit := bit) he
  have hj := iIdx_lt (bit := bit) (Nat.mod_lt (x.edge + 1) (show 0 < P.n by
    have := hG.1.1; omega))
  have b1 := Jordan.abs_fst_vtx_le_coordBound (Qof P) (i := iIdx bit P.n x.edge) (by rwa [hn])
  have b2 := Jordan.abs_fst_vtx_le_coordBound (Qof P) (i := iIdx bit P.n ((x.edge + 1) % P.n))
    (by rwa [hn])
  obtain ⟨t0, t1, -⟩ := hp
  simp only [Model.pos, Geometry.lerp_fst]
  rw [ha, hb]
  set t := (interiorModel (Qof P)).param (Qof P) x
  set u := ((Qof P).vtx (iIdx bit P.n x.edge)).1
  set v := ((Qof P).vtx (iIdx bit P.n ((x.edge + 1) % P.n))).1
  have : u + t * (v - u) = (1 - t) * u + t * v := by ring
  rw [this]
  have h1 : |(1 - t) * u + t * v| ≤ (1 - t) * |u| + t * |v| := by
    calc |(1 - t) * u + t * v| ≤ |(1 - t) * u| + |t * v| := abs_add_le _ _
      _ = (1 - t) * |u| + t * |v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_of_nonneg t0]
  have h2 : (1 - t) * |u| + t * |v| ≤ Jordan.coordBound (Qof P) := by
    have := mul_le_mul_of_nonneg_left b1 (by linarith : (0 : ℝ) ≤ 1 - t)
    have := mul_le_mul_of_nonneg_left b2 t0
    nlinarith
  linarith

/-! ## The machine -/

/-- The edge index for the reversed orientation: `n - 2 - e`, or `n - 1` at the last edge. -/
def iNxt (a : ℕ) : Stmt :=
  .seq (.instr (.addN 50217 a 50216))
    (.ifLtN 50217 50215 (block [.subN 50212 50215 50217, .subN 50212 50212 50216])
      (.instr (.subN 50212 50215 50216)))

/-- The index for the reversed orientation (`bit ≠ 1`). -/
def iFix (a b : ℕ) : Stmt :=
  .ifLtN 83022 b (iNxt a) (block [.subN 50212 50215 50216, .subN 50212 50212 a])

/-- **The abscissa record of an interior position** `(a, b)` into `50210 … 50213`. -/
def iRec (a b : ℕ) : Stmt :=
  .seq (block [.loadN 50214 83020, .inputSize 50215, .constN 50216 1, .constN 50210 1,
      .copyN 50212 a, .constN 50211 0])
    (.seq (.ifLtN 83022 b (block [.constN 50211 1, .subN 50213 b 50216]) .skip)
      (.ifLtN 50214 50216 (iFix a b) (.ifLtN 50216 50214 (iFix a b) .skip)))

/-- The registers written by `iRec`. -/
def BiR (r : ℕ) : Bool := decide (50210 ≤ r ∧ r < 50218)

theorem wr_iRec (a b : ℕ) : wr BiR (iRec a b) = true := by
  simp only [iRec, iFix, iNxt, wr, block, wrOK, BiR]
  decide

/-- The registers written by `iFix`. -/
def Bfx (r : ℕ) : Bool := r == 50212 || r == 50217

theorem bfx_sub {r : ℕ} (h : Bfx r = true) : BiR r = true := by
  simp only [Bfx, Bool.or_eq_true, beq_iff_eq] at h
  simp only [BiR, decide_eq_true_eq]; omega

/-- **The reversed index**: `iFix` puts `n - 1 - e` (vertex) or `iEdgeIdx` (edge) into `50212`. -/
theorem iFix_exec {c : Config} (hw : WordsBounded W c) {a b : ℕ} (hW : P.n + 3 ≤ W)
    (h15 : c.nreg 50215 = P.n) (h16 : c.nreg 50216 = 1) (h22 : c.nreg 83022 = 0)
    (ha : c.nreg a < P.n) (_hn3 : 3 ≤ P.n) (hab : a ≠ 50212 ∧ a ≠ 50217) :
    ∃ c' k, Exec P W (iFix a b) c c' k ∧ k ≤ 6 ∧
      c'.nreg 50212 = (if c.nreg b = 0 then P.n - 1 - c.nreg a
        else if c.nreg a + 1 < P.n then P.n - 2 - c.nreg a else P.n - 1) ∧
      FrameB Bfx c c' := by
  unfold iFix
  by_cases hb : c.nreg 83022 < c.nreg b
  · have hb0 : c.nreg b ≠ 0 := by omega
    have e₁ := Exec.addN (P := P) hw 50217 a 50216 (by rw [h16]; have := hw.1 ALLOC; omega)
    set c₁ : Config := { c with nreg := upd c.nreg 50217 (c.nreg a + c.nreg 50216) } with hc₁
    have w₁ := e₁.wb_right
    have v17 : c₁.nreg 50217 = c.nreg a + 1 := by rw [hc₁]; simp [h16]
    have v15 : c₁.nreg 50215 = P.n := by rw [hc₁]; simp [upd, h15]
    have v16 : c₁.nreg 50216 = 1 := by rw [hc₁]; simp [upd, h16]
    by_cases hl : c₁.nreg 50217 < c₁.nreg 50215
    · obtain ⟨c', k, e, hk, v12, fr⟩ : ∃ c' k, Exec P W
          (block [.subN 50212 50215 50217, .subN 50212 50212 50216]) c₁ c' k ∧ k = 2 ∧
          c'.nreg 50212 = c₁.nreg 50215 - c₁.nreg 50217 - c₁.nreg 50216 ∧
          FrameB Bfx c₁ c' := by
        have ea := Exec.subN (P := P) w₁ 50212 50215 50217
        have eb := Exec.subN (P := P) ea.wb_right 50212 50212 50216
        refine ⟨_, _, Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right)), rfl,
          ?_, ?_⟩
        · simp [upd]
        · exact exec_frameB (Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right)))
            (by simp only [wr, block, wrOK, Bfx]; decide)
      have ex : Exec P W (.ifLtN 83022 b (iNxt a) (block [.subN 50212 50215 50216,
          .subN 50212 50212 a])) c c' _ := .ifLtN_true hb (.seq e₁ (.ifLtN_true hl e))
      refine ⟨c', _, ex, by omega, ?_, exec_frameB ex (by
        simp only [iNxt, wr, block, wrOK, Bfx]; decide)⟩
      rw [v12, v15, v17, v16, ite_eq_right hb0, ite_eq_left (by rwa [v17, v15] at hl)]
      omega
    · have e₂ := Exec.subN (P := P) w₁ 50212 50215 50216
      have ex : Exec P W (.ifLtN 83022 b (iNxt a) (block [.subN 50212 50215 50216,
          .subN 50212 50212 a])) c _ _ := .ifLtN_true hb (.seq e₁ (.ifLtN_false hl e₂))
      refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by
        simp only [iNxt, wr, block, wrOK, Bfx]; decide)⟩
      simp only [upd_same]
      rw [v15, v16, ite_eq_right hb0, ite_eq_right (by rwa [v17, v15] at hl)]
  · have hb0 : c.nreg b = 0 := by omega
    have ea := Exec.subN (P := P) hw 50212 50215 50216
    have eb := Exec.subN (P := P) ea.wb_right 50212 50212 a
    have ex : Exec P W (.ifLtN 83022 b (iNxt a) (block [.subN 50212 50215 50216,
        .subN 50212 50212 a])) c _ _ :=
      .ifLtN_false hb (Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right)))
    refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (by
      simp only [iNxt, wr, block, wrOK, Bfx]; decide)⟩
    simp only [upd_same, ite_eq_left hb0]
    rw [upd_other _ _ _ hab.1, h15, h16]

/-- **The abscissa record of an interior position.** -/
theorem iRec_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    (hmd : c.nmem (c.nreg 83020) = bit) (h22 : c.nreg 83022 = 0)
    (ha8 : 80000 ≤ a ∧ a < 90000) (hb8 : 80000 ≤ b ∧ b < 90000)
    (hp : ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c.nreg a, c.nreg b⟩)
    (he : c.nreg a < P.n) :
    ∃ c' k, Exec P W (iRec a b) c c' k ∧ k ≤ 20 ∧
      AbsRec P c' 50210 ((interiorModel (Qof P)).pos (Qof P) ⟨c.nreg a, c.nreg b⟩).1
        (Jordan.coordBound (Qof P) + 1) ∧ FrameB BiR c c' := by
  have hn3 : 3 ≤ P.n := hG.1.1
  have hbn : c.nreg b ≤ P.n := hp.2.2
  set e := c.nreg a with he_def
  set h := c.nreg b with hh_def
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q14, q15, q16, q10, q12, q11, g₁, hm₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.loadN 50214 83020, .inputSize 50215, .constN 50216 1, .constN 50210 1,
        .copyN 50212 a, .constN 50211 0]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 50214 = bit ∧
      c₁.nreg 50215 = P.n ∧ c₁.nreg 50216 = 1 ∧ c₁.nreg 50210 = 1 ∧ c₁.nreg 50212 = e ∧
      c₁.nreg 50211 = 0 ∧ (∀ r, 80000 ≤ r → r < 90000 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    · omega
    · omega
    · refine ⟨rfl, ?_, by config_simp, by config_simp, by config_simp, ?_, by config_simp,
        fun r h1 h2 => ?_, rfl⟩
      · simp [upd, hmd]
      · simp [upd, he_def, show a ≠ 50214 by omega, show a ≠ 50215 by omega,
          show a ≠ 50216 by omega, show a ≠ 50210 by omega]
      · simp [upd, show r ≠ 50210 by omega, show r ≠ 50211 by omega, show r ≠ 50212 by omega,
          show r ≠ 50214 by omega, show r ≠ 50215 by omega, show r ≠ 50216 by omega]
  have w₁ := e₁.wb_right
  have gb := g₁ b hb8.1 hb8.2
  have g22 := g₁ 83022 (by norm_num) (by norm_num)
  have F₁ : FrameB BiR c c₁ := exec_frameB e₁ (by simp only [wr, block, wrOK, BiR]; decide)
  -- the kind of the symbolic point
  obtain ⟨c₂, k₂, e₂, hk₂, r10, r11, r13, r12, r14, r15, r16, g₂, F₂⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 83022 b (block [.constN 50211 1, .subN 50213 b 50216]) .skip) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 50210 = 1 ∧ c₂.nreg 50211 = (if h = 0 then 0 else 1) ∧
      (h ≠ 0 → c₂.nreg 50213 = h - 1) ∧ c₂.nreg 50212 = e ∧ c₂.nreg 50214 = bit ∧
      c₂.nreg 50215 = P.n ∧ c₂.nreg 50216 = 1 ∧
      (∀ r, 80000 ≤ r → r < 90000 → c₂.nreg r = c.nreg r) ∧ FrameB BiR c₁ c₂ := by
    by_cases hb : c₁.nreg 83022 < c₁.nreg b
    · have h0 : h ≠ 0 := by rw [gb, g22, h22] at hb; omega
      have ea := Exec.constN (P := P) w₁ 50211 1 (by omega)
      have eb := Exec.subN (P := P) ea.wb_right 50213 b 50216
      have ex := Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right))
      refine ⟨_, _, .ifLtN_true hb ex, by omega, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_,
        fun r h1 h2 => ?_, exec_frameB ex (by simp only [wr, block, wrOK, BiR]; decide)⟩
      all_goals simp only [upd]
      all_goals try simp only [show (50210 : ℕ) ≠ 50213 by norm_num,
        show (50210 : ℕ) ≠ 50211 by norm_num, ite_false]
      · exact q10
      · simp [h0]
      · simp [show b ≠ 50211 by omega, q16, gb, ← hh_def]
      · simp; exact q12
      · simp; exact q14
      · simp; exact q15
      · simp; exact q16
      · simp [show r ≠ 50213 by omega, show r ≠ 50211 by omega]; exact g₁ r h1 h2
    · have h0 : h = 0 := by rw [gb, g22, h22] at hb; omega
      refine ⟨c₁, _, .ifLtN_false hb (.skip w₁), by omega, q10, by simp [h0, q11],
        fun h' => absurd h0 h', q12, q14, q15, q16, g₁, FrameB.refl _ _⟩
  have w₂ := e₂.wb_right
  have ga2 := g₂ a ha8.1 ha8.2
  have gb2 := g₂ b hb8.1 hb8.2
  have g222 := g₂ 83022 (by norm_num) (by norm_num)
  -- the index
  have hidx : ∃ c' k, Exec P W (.ifLtN 50214 50216 (iFix a b) (.ifLtN 50216 50214 (iFix a b)
      .skip)) c₂ c' k ∧ k ≤ 10 ∧ c'.nreg 50212 = (if h = 0 then iIdx bit P.n e
        else iEdgeIdx bit P.n e) ∧ FrameB Bfx c₂ c' := by
    have fix := iFix_exec (P := P) w₂ (a := a) (b := b) hW r15 r16 (by rw [g222, h22])
      (by rwa [ga2]) hn3 ⟨by omega, by omega⟩
    rw [ga2, gb2] at fix
    obtain ⟨c', k, ex, hk, v12, fr⟩ := fix
    have val : bit ≠ 1 → c'.nreg 50212 = (if h = 0 then iIdx bit P.n e
        else iEdgeIdx bit P.n e) := fun hb1 => by
      rw [v12, ← he_def, ← hh_def]; unfold iIdx iEdgeIdx; simp only [hb1, ite_false]
    by_cases g1 : c₂.nreg 50214 < c₂.nreg 50216
    · exact ⟨c', _, .ifLtN_true g1 ex, by omega, val (by rw [r14, r16] at g1; omega), fr⟩
    by_cases g2 : c₂.nreg 50216 < c₂.nreg 50214
    · exact ⟨c', _, .ifLtN_false g1 (.ifLtN_true g2 ex), by omega,
        val (by rw [r14, r16] at g2; omega), fr⟩
    · have hb1 : bit = 1 := by rw [r14, r16] at g1 g2; omega
      refine ⟨c₂, _, .ifLtN_false g1 (.ifLtN_false g2 (.skip w₂)), by omega, ?_, FrameB.refl _ _⟩
      rw [r12]; unfold iIdx iEdgeIdx; simp [hb1]
  obtain ⟨c₃, k₃, e₃, hk₃, v12, F₃⟩ := hidx
  have k3 : ∀ r, Bfx r = false → c₃.nreg r = c₂.nreg r := F₃.1
  have ex : Exec P W (iRec a b) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ?_,
    F₁.trans (F₂.trans (frameB_mono F₃ (fun r hr => bfx_sub hr)))⟩
  have v10 : c₃.nreg 50210 = 1 := by rw [k3 _ (by decide), r10]
  have v11 : c₃.nreg 50211 = (if h = 0 then 0 else 1) := by rw [k3 _ (by decide), r11]
  have v13 : h ≠ 0 → c₃.nreg 50213 = h - 1 := fun h0 => by rw [k3 _ (by decide), r13 h0]
  have hpos := interior_pos_sym (P := P) hG hbit (e := e) (h := h) he
  refine ⟨by
    have : 0 ≤ Jordan.coordBound (Qof P) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    linarith, Or.inr (Or.inr
    ⟨v10, interior_abs_lt hG hbit he hp, iSym bit P.n e h, ?_,
      iSym_lt hn3 he hbn, by rw [hpos]⟩)⟩
  unfold iSym
  by_cases h0 : h = 0
  · simp only [h0, ite_true] at v11 v12 ⊢
    exact ⟨v11, v12⟩
  · simp only [h0, ite_false] at v11 v12 ⊢
    exact ⟨v11, v12, v13 h0⟩

end

end Restore

end Chazelle.Core
