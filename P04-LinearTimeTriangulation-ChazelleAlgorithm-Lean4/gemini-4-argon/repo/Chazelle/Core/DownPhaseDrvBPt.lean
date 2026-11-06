module

public import Chazelle.Core.DownPhaseDrvBRegM

/-!
# Down-phase base (D9), RAM: one point of a region

The points of the region are in the point array at `PA = r212015` (`PtArr`: three words per
point, kind `0` vertex / `1` edge point, then the indices), `NP = r212016` points, the current
point `k = r212017`.  One point (`ptS`):

1. `loadS`: the previous, current and next points (cyclically) into the register triples
   `212060`, `212063`, `212066`;
2. `vtxS`: the vertex test (`qvx`): a vertex `.vtx i`, or an edge point at the abscissa of its
   height vertex (two sign tests); flag `r212043`, vertex `i` into `212070`;
3. if a vertex: the corner test `cornerS` (bits `212084`, `212085` for the directions `+1`,
   `-1`), and for each direction code `d` whose bit is set (`dirS`): the far-end scan `farS` and
   the append `emitS`;
4. `k := k + 1`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (ivB qE)

@[expose] public section

/-! ## The point array -/

/-- A symbolic point at `a` in memory (kind `0` vertex, `1` edge point, then its indices). -/
def PtAt (m : ℕ → ℕ) (a : ℕ) : SymPt → Prop
  | .vtx i => m a = 0 ∧ m (a + 1) = i
  | .onEdge e h => m a = 1 ∧ m (a + 1) = e ∧ m (a + 2) = h

/-- **The point array** at `PA`. -/
def PtArr (m : ℕ → ℕ) (PA : ℕ) (l : List SymPt) : Prop :=
  ∀ k, k < l.length → PtAt m (PA + 3 * k) (l.getD k (.vtx 0))

/-! ## The records of a point -/

open Classical in
/-- The emitted indices at point `k`. -/
noncomputable def emAt (Q : Polygon) (l : List SymPt) (k : ℕ) : List (ℕ × ℕ) :=
  (List.range 2).filterMap fun d =>
    if (qvx Q (l.getD k (.vtx 0))).isSome ∧ emitAt Q l k d then some (k, d) else none

theorem emIdx_eq (Q : Polygon) (l : List SymPt) :
    emIdx Q l = (List.range l.length).flatMap (emAt Q l) := rfl

/-- **The records of point `k`.** -/
noncomputable def ptRecs (li : Bool) (Q : Polygon) (l : List SymPt) (k : ℕ) :
    List (ℕ × ℕ × ℕ) :=
  (emAt Q l k).map (recAt li Q l)

theorem regList_eq_flatMap (li : Bool) (Q : Polygon) (l : List SymPt) :
    regList li Q l = (List.range l.length).flatMap (ptRecs li Q l) := by
  unfold regList ptRecs; rw [emIdx_eq, List.map_flatMap]

open Classical in
theorem emAt_eq (Q : Polygon) (l : List SymPt) (k : ℕ) :
    emAt Q l k = (if (qvx Q (l.getD k (.vtx 0))).isSome ∧ emitAt Q l k 0 then [(k, 0)] else []) ++
      (if (qvx Q (l.getD k (.vtx 0))).isSome ∧ emitAt Q l k 1 then [(k, 1)] else []) := by
  unfold emAt
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp

/-! ## The program -/

/-- Load the point with index in `ir` into the register triple `x`. -/
def ldPtS (ir x : ℕ) : Stmt :=
  block [.addN 212042 ir ir, .addN 212042 212042 ir, .addN 212042 212042 212015,
    .loadN x 212042, .addN 212042 212042 212000, .loadN (x + 1) 212042,
    .addN 212042 212042 212000, .loadN (x + 2) 212042]

/-- The indices of the neighbours, `k - 1` and `k + 1` cyclically. -/
def nbS : Stmt :=
  .seq (.ifLtN 212001 212017 (.instr (.subN 212040 212017 212000))
      (.instr (.subN 212040 212016 212000)))
    (.seq (.instr (.addN 212041 212017 212000))
      (.ifLtN 212041 212016 .skip (.instr (.constN 212041 0))))

/-- The three points of the corner. -/
def loadS : Stmt :=
  .seq nbS (.seq (ldPtS 212040 212060) (.seq (ldPtS 212017 212063) (ldPtS 212041 212066)))

/-- **The vertex test**: flag `212043` (`1` iff the point is a vertex of `Q`), the vertex into
`212070`. -/
def vtxS : Stmt :=
  .ifLtN 212063 212000
    (block [.constN 212043 1, .copyN 212070 212064])
    (.seq (block [.constN 212056 0, .copyN 212057 212065])
      (.seq (tstR 0 212063 212056 212056 212044)
        (.seq (tstR 0 212056 212063 212063 212045)
          (block [.subN 212043 212000 212044, .subN 212043 212043 212045,
            .copyN 212070 212065]))))

/-- One direction: if the bit `b` is set, the far-end scan and the append. -/
def dirS (d b : ℕ) : Stmt :=
  .ifLtN 212001 b (.seq (.instr (.constN 212086 d)) (.seq farS emitS)) .skip

/-- **One point of the region.** -/
def ptS : Stmt :=
  .seq loadS (.seq vtxS (.seq (.ifLtN 212001 212043
    (.seq cornerS (.seq (dirS 0 212084) (dirS 1 212085))) .skip)
    (.instr (.addN 212017 212017 212000))))

/-- The registers `dirS` writes. -/
def Bdir (r : ℕ) : Bool := decide (r = 212086) || Bfar r || Bemit r

/-- The registers `ptS` writes. -/
def Bpt (r : ℕ) : Bool :=
  Bk r || decide (r = 212017) || decide (212036 ≤ r ∧ r ≤ 212112) || Bemit r

theorem bpt_of_bk {q : ℕ} (h : Bk q = true) : Bpt q = true := by simp [Bpt, h]

theorem bpt_of_range {q : ℕ} (h : 212036 ≤ q ∧ q ≤ 212112) : Bpt q = true := by
  simp [Bpt, h]

theorem bpt_of_emit {q : ℕ} (h : Bemit q = true) : Bpt q = true := by simp [Bpt, h]

theorem bpt_dir {q : ℕ} (h : Bdir q = true) : Bpt q = true := by
  unfold Bdir Bfar at h
  cases hk : Bk q
  · cases he : Bemit q
    · simp only [hk, he, Bool.or_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h
      exact bpt_of_range (by omega)
    · exact bpt_of_emit he
  · exact bpt_of_bk hk

/-- The registers fixed during the points of a region. -/
def FixP (q : ℕ) : Prop :=
  FixB q ∨ q = 216031 ∨ q = 212033 ∨ q = 212034 ∨ q = 212015 ∨ q = 212016

theorem bdir_fix {q : ℕ} (h : FixP q) : Bdir q = false := by
  unfold FixP FixB at h
  simp only [Bdir, Bfar, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
    Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- The step bound of one direction. -/
def dirK (C : ℕ) : ℕ := ((visK + 2) * C + 24) * 5 + 2 * (DrvD.scanK + 2) * 5 + 60

/-- **The state at a point of region `r`**: the fixed registers, the region registers, the point
array at `PA` (above the output area), the output `T` so far. -/
structure PtSt (E : BEnv) (r PA : ℕ) (c : Config) (T : List (ℕ × (ℕ × ℕ × ℕ))) : Prop where
  wb : WordsBounded E.W c
  regs : BRegs E c
  p31 : c.nreg 216031 = E.RP r
  lp : 0 < E.K → c.nreg 212033 = E.LP r
  nR : c.nreg 212034 = E.nRg r
  pa : c.nreg 212015 = PA
  np : c.nreg 212016 = (E.pts r).length
  arr : PtArr c.nmem PA (E.pts r)
  hPA : E.B₂ + 10 * E.P.n ≤ PA
  hPAW : PA + 3 * (E.pts r).length ≤ E.W
  out : OutSt E c T

/-- The state survives a change of the registers outside `FixP` and of the output area. -/
theorem PtSt.step {E : BEnv} {r PA : ℕ} {c c' : Config} {T T' : List (ℕ × (ℕ × ℕ × ℕ))}
    (h : PtSt E r PA c T) (hw : WordsBounded E.W c') (hr : ∀ q, FixP q → c'.nreg q = c.nreg q)
    (hm : ∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c'.nmem a = c.nmem a)
    (hout : OutSt E c' T') : PtSt E r PA c' T' := by
  refine ⟨hw, h.regs.congr fun q hq => hr q (Or.inl hq), by rw [hr _ (by simp [FixP]), h.p31],
    fun hK => by rw [hr _ (by simp [FixP]), h.lp hK], by rw [hr _ (by simp [FixP]), h.nR],
    by rw [hr _ (by simp [FixP]), h.pa], by rw [hr _ (by simp [FixP]), h.np], fun k hk => ?_,
    h.hPA, h.hPAW, hout⟩
  have := h.arr k hk
  have hp := h.hPA
  cases hs : (E.pts r).getD k (.vtx 0) with
  | vtx i =>
    rw [hs] at this
    exact ⟨(hm _ (Or.inr (by omega))).trans this.1, (hm _ (Or.inr (by omega))).trans this.2⟩
  | onEdge e g =>
    rw [hs] at this
    exact ⟨(hm _ (Or.inr (by omega))).trans this.1, (hm _ (Or.inr (by omega))).trans this.2.1,
      (hm _ (Or.inr (by omega))).trans this.2.2⟩

/-- The step bound of one point. -/
def ptK (C : ℕ) : ℕ := 2 * dirK C + 2900

/-- The state survives a register-only change outside the fixed and output registers. -/
theorem PtSt.regStep {E : BEnv} {r PA : ℕ} {c c' : Config} {T : List (ℕ × (ℕ × ℕ × ℕ))}
    (h : PtSt E r PA c T) (hw : WordsBounded E.W c')
    (hr : ∀ q, (FixP q ∨ (216020 ≤ q ∧ q ≤ 216022)) → c'.nreg q = c.nreg q)
    (hm : c'.nmem = c.nmem) : PtSt E r PA c' T := by
  refine h.step hw (fun q hq => hr q (Or.inl hq)) (fun a _ => by rw [hm]) ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h.out
  refine ⟨by rwa [hr _ (Or.inr ⟨le_rfl, by norm_num⟩)],
    by rwa [hr _ (Or.inr ⟨by norm_num, by norm_num⟩)],
    by rwa [hr _ (Or.inr ⟨by norm_num, le_rfl⟩)], by rwa [hm],
    fun hK => by rw [hm]; exact a5 hK, fun hK => by rw [hm]; exact a6 hK,
    fun a ha => by rw [hm]; exact a7 a ha⟩

/-- The registers `vtxS` writes. -/
def Bvt (r : ℕ) : Bool :=
  Bk r || decide (212043 ≤ r ∧ r ≤ 212045) || decide (r = 212056 ∨ r = 212057 ∨ r = 212070)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Loading a point.** -/
theorem ldPtS_exec (c : Config) (hw : WordsBounded W c) {ir x idx PA : ℕ} {s : SymPt}
    (hir : c.nreg ir = idx) (hPA : c.nreg 212015 = PA) (c0 : c.nreg 212000 = 1)
    (hpt : PtAt c.nmem (PA + 3 * idx) s) (hb : PA + 3 * idx + 2 ≤ W) (hir' : ir ≠ 212042)
    (hx : 212043 ≤ x) :
    ∃ c' k, Exec P W (ldPtS ir x) c c' k ∧ k = 8 ∧ SymPtIn c' x s ∧
      FrameB (fun r => decide (r = 212042) || decide (x ≤ r ∧ r ≤ x + 2)) c c' := by
  obtain ⟨c', k, ex, hk, v0, v1, v2⟩ : ∃ c' k, Exec P W (ldPtS ir x) c c' k ∧ k = 8 ∧
      c'.nreg x = c.nmem (PA + 3 * idx) ∧ c'.nreg (x + 1) = c.nmem (PA + 3 * idx + 1) ∧
      c'.nreg (x + 2) = c.nmem (PA + 3 * idx + 2) := by
    unfold ldPtS
    exec_block
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hir, hPA, c0]
    all_goals try omega
    refine ⟨trivial, ?_, ?_, ?_⟩ <;> congr 1 <;> omega
  refine ⟨c', k, ex, hk, ?_, ?_⟩
  · cases s with
    | vtx i => exact ⟨v0.trans hpt.1, v1.trans hpt.2⟩
    | onEdge e h => exact ⟨v0.trans hpt.1, v1.trans hpt.2.1, v2.trans hpt.2.2⟩
  · refine exec_frameB ex ?_
    simp [ldPtS, block, wr, wrOK]

/-- **The neighbours.** -/
theorem nbS_exec (c : Config) (hw : WordsBounded W c) {k NP : ℕ} (hk : c.nreg 212017 = k)
    (hNP : c.nreg 212016 = NP) (hkN : k < NP) (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k', Exec P W nbS c c' k' ∧ k' ≤ 7 ∧ c'.nreg 212040 = (k + NP - 1) % NP ∧
      c'.nreg 212041 = (k + 1) % NP ∧
      FrameB (fun r => decide (r = 212040) || decide (r = 212041)) c c' := by
  have hNW : NP ≤ W := hNP ▸ hw.1 212016
  -- `k - 1`
  obtain ⟨c₁, k₁, e₁, hk₁, v40, g₁⟩ : ∃ c₁ k₁, Exec P W (.ifLtN 212001 212017
      (.instr (.subN 212040 212017 212000)) (.instr (.subN 212040 212016 212000))) c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 212040 = (k + NP - 1) % NP ∧ ∀ r, r ≠ 212040 → c₁.nreg r = c.nreg r := by
    by_cases h0 : 0 < k
    · have e := Exec.subN (P := P) hw 212040 212017 212000
      refine ⟨_, _, .ifLtN_true (by rwa [c1, hk]) e, by omega, ?_, fun r h => by simp [h]⟩
      simp only [Machine.upd_same, hk, c0]
      rw [show k + NP - 1 = (k - 1) + NP by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have e := Exec.subN (P := P) hw 212040 212016 212000
      refine ⟨_, _, .ifLtN_false (by rwa [c1, hk]) e, by omega, ?_, fun r h => by simp [h]⟩
      simp only [Machine.upd_same, hNP, c0]
      rw [show k = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  have w₁ := e₁.wb_right
  have k1 : c₁.nreg 212017 = k := by rw [g₁ _ (by norm_num), hk]
  have n1 : c₁.nreg 212016 = NP := by rw [g₁ _ (by norm_num), hNP]
  have c0' : c₁.nreg 212000 = 1 := by rw [g₁ _ (by norm_num), c0]
  have e₂ := Exec.addN (P := P) w₁ 212041 212017 212000 (by rw [k1, c0']; omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 212041 (c₁.nreg 212017 + c₁.nreg 212000) }
    with hc₂
  have w₂ := e₂.wb_right
  have v41 : c₂.nreg 212041 = k + 1 := by simp [hc₂, k1, c0']
  have n2 : c₂.nreg 212016 = NP := by simp [hc₂, n1]
  by_cases h1 : k + 1 < NP
  · have ex : Exec P W nbS c c₂ (k₁ + (1 + (0 + 1))) :=
      .seq e₁ (.seq e₂ (.ifLtN_true (by rwa [v41, n2]) (.skip w₂)))
    refine ⟨c₂, _, ex, by omega, by simp [hc₂, v40], by rw [v41, Nat.mod_eq_of_lt h1],
      exec_frameB ex (by decide)⟩
  · have e₃ := Exec.constN (P := P) w₂ 212041 0 (Nat.zero_le _)
    have ex : Exec P W nbS c _ (k₁ + (1 + (1 + 2))) :=
      .seq e₁ (.seq e₂ (.ifLtN_false (by rwa [v41, n2]) e₃))
    refine ⟨_, _, ex, by omega, by simp [hc₂, v40], ?_, exec_frameB ex (by decide)⟩
    simp only [Machine.upd_same]
    rw [show k + 1 = NP by omega, Nat.mod_self]

/-- The registers `loadS` writes. -/
def Bld (r : ℕ) : Bool := decide (212040 ≤ r ∧ r ≤ 212042) || decide (212060 ≤ r ∧ r ≤ 212068)

set_option maxHeartbeats 2000000 in
/-- **The three points of the corner.** -/
theorem loadS_exec (c : Config) (hw : WordsBounded W c) {k PA : ℕ} {l : List SymPt}
    (hk : c.nreg 212017 = k) (hNP : c.nreg 212016 = l.length) (hkN : k < l.length)
    (hPA : c.nreg 212015 = PA) (hb : PA + 3 * l.length ≤ W) (harr : PtArr c.nmem PA l)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k', Exec P W loadS c c' k' ∧ k' ≤ 32 ∧
      SymPtIn c' 212060 (l.getD ((k + l.length - 1) % l.length) (.vtx 0)) ∧
      SymPtIn c' 212063 (l.getD k (.vtx 0)) ∧
      SymPtIn c' 212066 (l.getD ((k + 1) % l.length) (.vtx 0)) ∧ FrameB Bld c c' := by
  have hpos : 0 < l.length := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, v40, v41, f₁⟩ := nbS_exec (P := P) c hw hk hNP hkN c0 c1
  have g₁ : ∀ r, r ≠ 212040 → r ≠ 212041 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r (by simp [a, b])
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  have i1 : (k + l.length - 1) % l.length < l.length := Nat.mod_lt _ hpos
  have i2 : (k + 1) % l.length < l.length := Nat.mod_lt _ hpos
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, f₂⟩ := ldPtS_exec (P := P) c₁ e₁.wb_right (ir := 212040)
    (x := 212060) v40 (by rw [g₁ _ (by norm_num) (by norm_num), hPA])
    (by rw [g₁ _ (by norm_num) (by norm_num), c0]) (by rw [m₁]; exact harr _ i1) (by omega)
    (by norm_num) (by norm_num)
  have g₂ : ∀ r, r ≠ 212042 → (r < 212060 ∨ 212062 < r) → c₂.nreg r = c₁.nreg r := fun r a b =>
    f₂.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, f₃⟩ := ldPtS_exec (P := P) c₂ e₂.wb_right (ir := 212017)
    (x := 212063) (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by norm_num) (by norm_num), hk])
    (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by norm_num) (by norm_num), hPA])
    (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by norm_num) (by norm_num), c0])
    (by rw [f₂.2.2.1, m₁]; exact harr _ hkN) (by omega) (by norm_num) (by norm_num)
  have g₃ : ∀ r, r ≠ 212042 → (r < 212063 ∨ 212065 < r) → c₃.nreg r = c₂.nreg r := fun r a b =>
    f₃.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  obtain ⟨c₄, k₄, e₄, hk₄, s₄, f₄⟩ := ldPtS_exec (P := P) c₃ e₃.wb_right (ir := 212041)
    (x := 212066) (by rw [g₃ _ (by norm_num) (by norm_num), g₂ _ (by norm_num) (by norm_num), v41])
    (by rw [g₃ _ (by norm_num) (by norm_num), g₂ _ (by norm_num) (by norm_num),
      g₁ _ (by norm_num) (by norm_num), hPA])
    (by rw [g₃ _ (by norm_num) (by norm_num), g₂ _ (by norm_num) (by norm_num),
      g₁ _ (by norm_num) (by norm_num), c0])
    (by rw [f₃.2.2.1, f₂.2.2.1, m₁]; exact harr _ i2) (by omega) (by norm_num) (by norm_num)
  have g₄ : ∀ r, r ≠ 212042 → (r < 212066 ∨ 212068 < r) → c₄.nreg r = c₃.nreg r := fun r a b =>
    f₄.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have ex : Exec P W loadS c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have hBld : ∀ {B : ℕ → Bool} {c c' : Config}, FrameB B c c' →
      (∀ r, B r = true → Bld r = true) → FrameB Bld c c' := fun f h => fbMono f h
  refine ⟨c₄, _, ex, by omega, ?_, ?_, s₄, ?_⟩
  · refine symPtIn_copy s₂ ?_ ?_ ?_ <;>
      rw [g₄ _ (by norm_num) (by norm_num), g₃ _ (by norm_num) (by norm_num)]
  · refine symPtIn_copy s₃ ?_ ?_ ?_ <;> rw [g₄ _ (by norm_num) (by norm_num)]
  · refine fbTrans (hBld f₁ ?_) (fbTrans (hBld f₂ ?_) (fbTrans (hBld f₃ ?_) (hBld f₄ ?_))) <;>
      intro r h <;> simp only [Bld, Bool.or_eq_true, decide_eq_true_eq] at h ⊢ <;> omega

set_option maxHeartbeats 4000000 in
/-- **The vertex test.** -/
theorem vtxS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {s : SymPt} (hs : SymPtIn c 212063 s) (hsl : s.Lt P.n) (c0 : c.nreg 212000 = 1) :
    ∃ c' k, Exec P W vtxS c c' k ∧ k ≤ 500 ∧ FrameB Bvt c c' ∧ c'.nreg 212043 ≤ 1 ∧
      (c'.nreg 212043 = 1 → qvx (Qof P) s = some (c'.nreg 212070)) ∧
      (c'.nreg 212043 = 1 ↔ (qvx (Qof P) s).isSome) := by
  cases s with
  | vtx i =>
    obtain ⟨k0, k1⟩ := hs
    obtain ⟨c', k, e, hk, v43, v70⟩ : ∃ c' k, Exec P W (block [.constN 212043 1,
        .copyN 212070 212064]) c c' k ∧ k = 2 ∧ c'.nreg 212043 = 1 ∧ c'.nreg 212070 = i := by
      exec_block
      · have := hw.1 212000; omega
      · refine ⟨rfl, ?_, ?_⟩ <;> config_simp; exact k1
    have ex : Exec P W vtxS c c' _ := .ifLtN_true (by rw [k0, c0]; omega) e
    refine ⟨c', _, ex, by omega, exec_frameB ex (by decide), by omega, fun _ => ?_, ?_⟩
    · rw [v70]; rfl
    · simp [v43, qvx]
  | onEdge e h =>
    obtain ⟨k0, k1, k2⟩ := hs
    obtain ⟨c₁, k₁, e₁, hk₁, v56, v57, g₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 212056 0,
        .copyN 212057 212065]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212056 = 0 ∧ c₁.nreg 212057 = h ∧
        ∀ r, r ≠ 212056 → r ≠ 212057 → c₁.nreg r = c.nreg r := by
      exec_block
      · omega
      · refine ⟨rfl, ?_, ?_, fun r a b => ?_⟩ <;> config_simp
        · exact k2
        · simp [a, b]
    have hv : SymPtIn c₁ 212056 (.vtx h) := ⟨v56, v57⟩
    have hp : SymPtIn c₁ 212063 (.onEdge e h) :=
      ⟨by rw [g₁ _ (by norm_num) (by norm_num), k0], by rw [g₁ _ (by norm_num) (by norm_num), k1],
        by rw [g₁ _ (by norm_num) (by norm_num), k2]⟩
    have o63 : OutK 212063 := Or.inr (by norm_num)
    have o56 : OutK 212056 := Or.inr (by norm_num)
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
      o63 o56 o56 (d := 212044) c₁ e₁.wb_right hp hv hv hsl hsl.2 hsl.2
    have hv₂ : SymPtIn c₂ 212056 (.vtx h) := symPtIn_copy hv (keep_bt f₂ (by norm_num)
      (by norm_num)) (keep_bt f₂ (by norm_num) (by norm_num)) (keep_bt f₂ (by norm_num) (by norm_num))
    have hp₂ : SymPtIn c₂ 212063 (.onEdge e h) := symPtIn_copy hp (keep_bt f₂ (by norm_num)
      (by norm_num)) (keep_bt f₂ (by norm_num) (by norm_num)) (keep_bt f₂ (by norm_num) (by norm_num))
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := tstR_exec (P := P) hG hW (op := 0) (by norm_num)
      o56 o63 o63 (d := 212045) c₂ e₂.wb_right hv₂ hp₂ hp₂ hsl.2 hsl hsl
    have v44 : c₃.nreg 212044 = c₂.nreg 212044 := keep_bt f₃ (by norm_num) (by norm_num)
    have c0₃ : c₃.nreg 212000 = 1 := by
      rw [keep_bt f₃ (by norm_num) (by norm_num), keep_bt f₂ (by norm_num) (by norm_num),
        g₁ _ (by norm_num) (by norm_num), c0]
    have h65 : c₃.nreg 212065 = h := by
      rw [keep_bt f₃ (by norm_num) (by norm_num), keep_bt f₂ (by norm_num) (by norm_num),
        g₁ _ (by norm_num) (by norm_num), k2]
    obtain ⟨c₄, k₄, e₄, hk₄, v43, v70⟩ : ∃ c₄ k₄, Exec P W (block [.subN 212043 212000 212044,
        .subN 212043 212043 212045, .copyN 212070 212065]) c₃ c₄ k₄ ∧ k₄ = 3 ∧
        c₄.nreg 212043 = 1 - c₃.nreg 212044 - c₃.nreg 212045 ∧ c₄.nreg 212070 = h := by
      have w₃ := e₃.wb_right
      exec_block
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp
      · rw [c0₃]
      · exact h65
    have ex : Exec P W vtxS c c₄ _ :=
      .ifLtN_false (by rw [k0, c0]; omega) (.seq e₁ (.seq e₂ (.seq e₃ e₄)))
    have fr : FrameB Bvt c c₄ := by
      refine fbTrans (exec_frameB e₁ (by decide)) (fbTrans (fbMono f₂ fun r hr => ?_)
        (fbTrans (fbMono f₃ fun r hr => ?_) (exec_frameB e₄ (by decide))))
      · simp only [Brute.Bt, Bvt, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
        rcases hr with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inl (Or.inr (by omega))
      · simp only [Brute.Bt, Bvt, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
        rcases hr with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inl (Or.inr (by omega))
    have hx1 : c₃.nreg 212044 = 1 ↔ edgeXAt (Qof P) e h < ((Qof P).vtx h).1 := by
      rw [v44, t₂]; simp [SignTest, SymPt.eval]
    have hx2 : c₃.nreg 212045 = 1 ↔ ((Qof P).vtx h).1 < edgeXAt (Qof P) e h := by
      rw [t₃]; simp [SignTest, SymPt.eval]
    have hq : (c₄.nreg 212043 = 1) ↔ edgeXAt (Qof P) e h = ((Qof P).vtx h).1 := by
      rw [v43]
      constructor
      · intro h1
        have a1 : c₃.nreg 212044 = 0 := by omega
        have a2 : c₃.nreg 212045 = 0 := by omega
        rcases lt_trichotomy (edgeXAt (Qof P) e h) ((Qof P).vtx h).1 with hl | heq | hl
        · have := hx1.2 hl; omega
        · exact heq
        · have := hx2.2 hl; omega
      · intro heq
        have a1 : c₃.nreg 212044 ≠ 1 := fun h' => absurd (hx1.1 h') (by rw [heq]; exact lt_irrefl _)
        have a2 : c₃.nreg 212045 ≠ 1 := fun h' => absurd (hx2.1 h') (by rw [heq]; exact lt_irrefl _)
        omega
    refine ⟨c₄, _, ex, by omega, fr, by rw [v43]; omega, fun h1 => ?_, ?_⟩
    · rw [v70]; simp only [qvx]; rw [ite_eq_left (hq.1 h1)]
    · rw [hq]; simp only [qvx]; split_ifs with hx <;> simp [hx]

set_option maxHeartbeats 8000000 in
/-- The direction code and the far-end scan of `dirS`. -/
theorem dirS_far {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List (ℕ × (ℕ × ℕ × ℕ))} (hS : PtSt E r PA c T) {k d i : ℕ} (hd : d ≤ 1)
    (hi : c.nreg 212070 = i) (hkd : (k, d) ∈ emIdx E.Q (E.pts r))
    (hqi : qvx E.Q ((E.pts r).getD k (.vtx 0)) = some i) :
    ∃ c₁ c₂ k₂, Exec E.P E.W (.instr (.constN 212086 d)) c c₁ 1 ∧ Exec E.P E.W farS c₁ c₂ k₂ ∧
      k₂ ≤ ((visK + 2) * E.Cm + 24) * E.nRg r + 4 ∧
      FrameB (fun q => decide (q = 212086) || Bfar q) c c₂ ∧
      c₂.nreg 212097 = farW E.li E.Q i d ∧ c₂.nreg 212086 = d ∧ i < E.P.n := by
  have R := hS.regs
  have O := hS.out
  have hW3 : E.P.n + 3 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  have hn3 := hE.hn3
  have hBW := hE.hBW
  obtain ⟨i', hi', hin, hdir, hES⟩ := hE.far_ok hr hkd
  rw [hqi, Option.some.injEq] at hi'
  subst hi'
  have e₁ := Exec.constN (P := E.P) hS.wb 212086 d (by omega)
  have g₁ : ∀ q, q ≠ 212086 → (upd c.nreg 212086 d) q = c.nreg q := fun q h =>
    Machine.upd_other _ _ _ h
  have v₁ : (upd c.nreg 212086 d) 212086 = d := Machine.upd_same _ _ _
  set c₁ : Config := { c with nreg := upd c.nreg 212086 d }
  have R₁ : BRegs E c₁ := R.congr fun q hq => g₁ q (by unfold FixB at hq; omega)
  have hld : ∀ t, t < E.nRg r → LdOK c₁ E.P.n t (E.stF r t) (E.cntF r t) ∧
      (0 < c₁.nreg 212012 → c₁.nreg 216014 + 5 * c₁.nmem (c₁.nreg 212033 + t) + 3 ≤ E.W) ∧
      (0 < c₁.nreg 212012 → c₁.nreg 212033 + E.nRg r ≤ E.W) := fun t ht =>
    hE.ld_ok hr c₁ O.low R₁.K R₁.d14 (fun hK => by
      show (upd c.nreg 212086 d) 212033 = _
      rw [g₁ _ (by norm_num)]; exact hS.lp hK) ht
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂⟩ := farS_exec (P := E.P) hE.hG hW3 (by omega) c₁
    e₁.wb_right (stF := E.stF r) (cntF := E.cntF r) (nR := E.nRg r) (i := i) (d := d)
    (Cm := E.Cm) (li := E.li) R₁.n
    (by show (upd c.nreg 212086 d) 212034 = _; rw [g₁ _ (by norm_num)]; exact hS.nR)
    (fun t ht => (hld t ht).1) (hE.hCm r hr) (fun t ht => (hld t ht).2.1)
    (fun hK => by
      rcases Nat.eq_zero_or_pos (E.nRg r) with h0 | h0
      · rw [h0, Nat.add_zero]; exact e₁.wb_right.1 _
      · exact (hld 0 h0).2.2 hK) R₁.li
    (by show (upd c.nreg 212086 d) 212070 = _; rwa [g₁ _ (by norm_num)]) hin v₁ hd
    R₁.c0 R₁.c1 R₁.c2
  have hQn := hE.hQn
  have hb₂' : BestOK E.Q E.Q.n i (sgnD d) E.li (ESr E.P.n (E.stF r) (E.cntF r) (E.nRg r) 0)
      (c₂.nreg 212099) (c₂.nreg 212097) (c₂.nreg 212098) := by rwa [hQn]
  obtain ⟨-, hbw⟩ := far_found hE.hQ hE.hDH (by rwa [hQn]) hdir hES hb₂'
  have f₁ : FrameB (fun q => decide (q = 212086)) c c₁ :=
    ⟨fun q hq => g₁ q (by simpa using hq), fun _ _ => rfl, rfl, rfl, rfl⟩
  refine ⟨c₁, c₂, k₂, e₁, e₂, hk₂, ?_, hbw, ?_, hin⟩
  · exact fbTrans (fbMono f₁ fun q h => by simp [h]) (fbMono f₂ fun q h => by simp [h])
  · rwa [f₂.1 _ (by unfold Bfar Bk; simp)]

set_option maxHeartbeats 8000000 in
/-- **One direction of a vertex point**: if the corner bit `b` is set, the far end is `farW`
and the record `recAt (k, d)` is appended. -/
theorem dirS_on {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List (ℕ × (ℕ × ℕ × ℕ))} (hS : PtSt E r PA c T) {k d b i : ℕ}
    (_hb : c.nreg b ≤ 1) (hd : d ≤ 1)
    (hi : c.nreg 212070 = i)
    (hem : c.nreg b = 1 → (k, d) ∈ emIdx E.Q (E.pts r))
    (hqi : c.nreg b = 1 → qvx E.Q ((E.pts r).getD k (.vtx 0)) = some i)
    (hT : c.nreg b = 1 → T.length < 2 * E.P.n) (h1 : c.nreg b = 1) :
    ∃ c' k', Exec E.P E.W (dirS d b) c c' k' ∧ k' ≤ dirK E.Cm ∧
      PtSt E r PA c' (T ++ [(r, recAt E.li E.Q (E.pts r) (k, d))]) ∧
      FrameM Bdir c c' ∧ (∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c'.nmem a = c.nmem a) := by
  have R := hS.regs
  have O := hS.out
  have hn3 := hE.hn3
  have hBW := hE.hBW
  · have hkd := hem h1
    obtain ⟨c₁, c₂, k₂, e₁, e₂, hk₂, f₂, hbw, h86, hin⟩ := dirS_far hE hr c hS hd hi hkd (hqi h1)
    have hQn := hE.hQn
    have R₂ : BRegs E c₂ := R.congr fun q hq => f₂.1 q (by
      unfold FixB at hq; simp only [Bfar, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
    have k₂' : ∀ q, q ≠ 212086 → Bfar q = false → c₂.nreg q = c.nreg q := fun q a b =>
      f₂.1 q (by simp [a, b])
    -- the record
    have hrec : recAt E.li E.Q (E.pts r) (k, d) = vtrip E.li E.P.n i d (farW E.li E.Q i d) := by
      unfold recAt; rw [hqi h1, hQn]; rfl
    have hxm : vtrip E.li E.P.n i d (farW E.li E.Q i d) ∈ E.recs r := by
      rw [← hrec]; exact List.mem_map_of_mem hkd
    have hm₂ : ∀ a, a < E.B₂ → c₂.nmem a = E.m₀ a := fun a ha => by
      rw [f₂.2.2.1]; exact O.low a ha
    obtain ⟨a1, a2⟩ := hE.areas hr
    have hBK : E.BK = E.B₂ + 3 * (2 * E.P.n) := by unfold BEnv.BK; ring
    have hlist : ChordListAt c₂.nmem E.B₂ (T.map Prod.snd) := by rw [f₂.2.2.1]; exact O.list
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, w₃, hm₃, d20, d21, d22, hL₃, hbk₃, hbk0₃⟩ := emitS_exec (P := E.P)
      hE.hG hE.hWh c₂ e₂.wb_right (li := E.li) (i := i) (d := d) (w := farW E.li E.Q i d) (r := r)
      (K := E.K) (MD := E.MD) (H := E.H) (A₀ := E.B₂) (B₂ := E.B₂) (Kmax := 2 * E.P.n)
      (m₀ := E.m₀) (N := E.N) (T := T)
      (by rwa [k₂' _ (by norm_num) (by decide)]) hin
      h86 hd hbw R₂.li R₂.n R₂.K R₂.c0 R₂.c1 R₂.d02 R₂.d03
      R₂.d05 R₂.d14 R₂.d16 R₂.d17
      (by rw [k₂' _ (by norm_num) (by decide), hS.p31]; rfl) R₂.md
      (by rw [k₂' _ (by norm_num) (by decide)]; exact O.cnt)
      (by rw [k₂' _ (by norm_num) (by decide)]; exact O.dst)
      (by rw [k₂' _ (by norm_num) (by decide), O.dstB, hBK])
      hm₂ le_rfl (hT h1) (by omega) (by omega)
      (by have := hE.LP_lt hr; unfold BEnv.LP at this; omega)
      hlist (fun hK => by rw [f₂.2.2.1, ← hBK]; exact O.bk hK)
      (fun hK q hq => by rw [f₂.2.2.1, ← hBK]; exact O.bk0 hK q hq) (hE.nA_eq hr)
      (fun hK m hm hmW s hs => hE.scan_ok hK hr hxm hm hmW hs)
      (fun hK s hs => hE.hex_ok hK hr hxm hs)
    have ex : Exec E.P E.W (dirS d b) c c₃ (k₂ + k₃ + 2) := by
      have := Exec.ifLtN_true (P := E.P) (W := E.W) (a := 212001) (b := b)
        (t := .seq (.instr (.constN 212086 d)) (.seq farS emitS)) (e := .skip)
        (by rw [R.c1, h1]; omega) (.seq e₁ (.seq e₂ e₃))
      have e : 1 + (k₂ + k₃) + 1 = k₂ + k₃ + 2 := by ring
      rwa [e] at this
    have hn5 := hE.nRg_le5 hr
    have ha5 := hE.arcs_le5 hr
    have FM : FrameM Bdir c c₃ :=
      ((FrameB.toM f₂).mono fun q h => by unfold Bdir; rw [h]; rfl).trans
        (f₃.mono fun q h => by simp [Bdir, h])
    have hmem : ∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
      rw [hm₃ a (by omega), f₂.2.2.1]
    refine ⟨c₃, _, ex, ?_, ?_, FM, hmem⟩
    · have m1 := Nat.mul_le_mul_left ((visK + 2) * E.Cm + 24) hn5
      have m2 := Nat.mul_le_mul_left (2 * (DrvD.scanK + 2)) ha5
      unfold dirK; omega
    · refine hS.step w₃ (fun q hq => ?_) hmem ⟨?_, ?_, ?_, ?_, fun hK => ?_, fun hK => ?_, fun a ha => ?_⟩
      · rw [FM.1 q (bdir_fix hq)]
      · rw [d20, List.length_append, List.length_singleton]
      · rw [d21, List.length_append, List.length_singleton]
      · rw [d22, List.length_append, List.length_singleton, hBK]
      · rwa [hrec]
      · rw [hrec, hBK]; exact hbk₃ hK
      · intro q hq; rw [hBK]; exact hbk0₃ hK q (by simpa using hq)
      · rw [hmem a (Or.inl ha)]; exact O.low a ha

set_option maxHeartbeats 8000000 in
/-- **One direction of a vertex point**: if the corner bit `b` is set, the far end is `farW`
and the record `recAt (k, d)` is appended. -/
theorem dirS_exec {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List (ℕ × (ℕ × ℕ × ℕ))} (hS : PtSt E r PA c T) {k d b i : ℕ}
    (hb : c.nreg b ≤ 1) (hd : d ≤ 1)
    (hi : c.nreg 212070 = i)
    (hem : c.nreg b = 1 → (k, d) ∈ emIdx E.Q (E.pts r))
    (hqi : c.nreg b = 1 → qvx E.Q ((E.pts r).getD k (.vtx 0)) = some i)
    (hT : c.nreg b = 1 → T.length < 2 * E.P.n) :
    ∃ c' k', Exec E.P E.W (dirS d b) c c' k' ∧ k' ≤ dirK E.Cm ∧
      PtSt E r PA c' (T ++ if c.nreg b = 1 then [(r, recAt E.li E.Q (E.pts r) (k, d))] else []) ∧
      FrameM Bdir c c' ∧ (∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c'.nmem a = c.nmem a) := by
  have R := hS.regs
  by_cases h1 : c.nreg b = 1
  · rw [ite_eq_left h1]
    exact dirS_on hE hr c hS hb hd hi hem hqi hT h1
  · have h0 : c.nreg b = 0 := by omega
    rw [ite_eq_right h1, List.append_nil]
    have ex : Exec E.P E.W (dirS d b) c c 2 :=
      .ifLtN_false (by rw [R.c1, h0]; omega) (.skip hS.wb)
    refine ⟨c, 2, ex, by unfold dirK; omega, hS, FrameM.refl _ _, fun _ _ => rfl⟩

set_option maxHeartbeats 8000000 in
/-- **One point of a region**: its records `ptRecs k` are appended. -/
theorem ptS_exec {E : BEnv} (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List (ℕ × (ℕ × ℕ × ℕ))} (hS : PtSt E r PA c T) {k : ℕ} (hk : c.nreg 212017 = k)
    (hkn : k < (E.pts r).length)
    (hT : T.length + (ptRecs E.li E.Q (E.pts r) k).length ≤ 2 * E.P.n) :
    ∃ c' k', Exec E.P E.W ptS c c' k' ∧ k' ≤ ptK E.Cm ∧
      PtSt E r PA c' (T ++ (ptRecs E.li E.Q (E.pts r) k).map fun x => (r, x)) ∧
      c'.nreg 212017 = k + 1 ∧ FrameM Bpt c c' ∧
      (∀ a, (a < E.B₂ ∨ E.B₂ + 10 * E.P.n ≤ a) → c'.nmem a = c.nmem a) := by
  have R := hS.regs
  have hW3 : E.P.n + 3 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  have hQn := hE.hQn
  set l := E.pts r
  have hlt : ∀ s ∈ l, s.Lt E.P.n := by rw [← hQn]; exact hE.pts_lt hr
  have hgetD : ∀ j, j < l.length → (l.getD j (.vtx 0)).Lt E.P.n := fun j hj => by
    apply hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  have hpos : 0 < l.length := by omega
  -- 1. the three points
  obtain ⟨c₁, k₁, e₁, hk₁, sa, sv, sb, f₁⟩ := loadS_exec (P := E.P) c hS.wb hk hS.np hkn hS.pa
    hS.hPAW hS.arr R.c0 R.c1
  have S₁ : PtSt E r PA c₁ T := hS.regStep e₁.wb_right (fun q hq => f₁.1 q (by
    unfold FixP FixB at hq; simp only [Bld, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    f₁.2.2.1
  -- 2. the vertex test
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hq₂, hs₂⟩ := vtxS_exec (P := E.P) hE.hG hW3 c₁ e₁.wb_right sv
    (hgetD k hkn) S₁.regs.c0
  have fx₂ : ∀ q, (FixP q ∨ (216020 ≤ q ∧ q ≤ 216022)) → c₂.nreg q = c₁.nreg q := fun q hq =>
    f₂.1 q (by unfold FixP FixB at hq; simp only [Bvt, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have S₂ : PtSt E r PA c₂ T := S₁.regStep e₂.wb_right fx₂ f₂.2.2.1
  have keep₂ : ∀ q, 212060 ≤ q → q ≤ 212068 → c₂.nreg q = c₁.nreg q := fun q a b =>
    f₂.1 q (by simp only [Bvt, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  set C : Prop := (qvx E.Q (l.getD k (.vtx 0))).isSome = true with hC
  -- the records of the point
  have hrecs : ∀ (b0 b1 : Prop) [Decidable b0] [Decidable b1],
      (b0 ↔ C ∧ emitAt E.Q l k 0) → (b1 ↔ C ∧ emitAt E.Q l k 1) →
      (ptRecs E.li E.Q l k).map (fun x => (r, x)) =
        (if b0 then [(r, recAt E.li E.Q l (k, 0))] else []) ++
          (if b1 then [(r, recAt E.li E.Q l (k, 1))] else []) := by
    intro b0 b1 _ _ h0 h1
    classical
    unfold ptRecs
    rw [emAt_eq]
    by_cases g0 : b0 <;> by_cases g1 : b1
    · rw [ite_eq_left (h0.1 g0), ite_eq_left (h1.1 g1), ite_eq_left g0, ite_eq_left g1]; rfl
    · rw [ite_eq_left (h0.1 g0), ite_eq_right (h1.not.1 g1), ite_eq_left g0, ite_eq_right g1]; rfl
    · rw [ite_eq_right (h0.not.1 g0), ite_eq_left (h1.1 g1), ite_eq_right g0, ite_eq_left g1]; rfl
    · rw [ite_eq_right (h0.not.1 g0), ite_eq_right (h1.not.1 g1), ite_eq_right g0, ite_eq_right g1]; rfl
  have hw₂ : WordsBounded E.W c₂ := e₂.wb_right
  have FM₁ : FrameM Bpt c c₁ := (FrameB.toM f₁).mono fun q hq => bpt_of_range (by
    simp only [Bld, Bool.or_eq_true, decide_eq_true_eq] at hq; omega)
  have FM₂ : FrameM Bpt c₁ c₂ := (FrameB.toM f₂).mono fun q hq => by
    unfold Bvt at hq
    cases hk : Bk q
    · simp only [hk, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hq
      exact bpt_of_range (by omega)
    · exact bpt_of_bk hk
  have hk₂ : c₂.nreg 212017 = k := by rw [f₂.1 _ (by decide), f₁.1 _ (by decide), hk]
  have c1₂ : c₂.nreg 212001 = 0 := S₂.regs.c1
  have c0₂ : c₂.nreg 212000 = 1 := S₂.regs.c0
  have hlenT : ∀ (b0 b1 : Prop) [Decidable b0] [Decidable b1],
      (b0 ↔ C ∧ emitAt E.Q l k 0) → (b1 ↔ C ∧ emitAt E.Q l k 1) →
      (ptRecs E.li E.Q l k).length = (if b0 then 1 else 0) + (if b1 then 1 else 0) := by
    intro b0 b1 _ _ h0 h1
    have := congrArg List.length (hrecs b0 b1 h0 h1)
    rw [List.length_map] at this
    rw [this, List.length_append]
    split_ifs <;> rfl
  by_cases hf : c₂.nreg 212043 = 1
  · have hqv := hq₂ hf
    set i := c₂.nreg 212070
    have hCt : C := by rw [hC, hqv]; rfl
    -- the corner
    have i1 : (k + l.length - 1) % l.length < l.length := Nat.mod_lt _ hpos
    have i2 : (k + 1) % l.length < l.length := Nat.mod_lt _ hpos
    have sa₂ := symPtIn_copy sa (keep₂ _ (by norm_num) (by norm_num))
      (keep₂ _ (by norm_num) (by norm_num)) (keep₂ _ (by norm_num) (by norm_num))
    have sv₂ := symPtIn_copy sv (keep₂ _ (by norm_num) (by norm_num))
      (keep₂ _ (by norm_num) (by norm_num)) (keep₂ _ (by norm_num) (by norm_num))
    have sb₂ := symPtIn_copy sb (keep₂ _ (by norm_num) (by norm_num))
      (keep₂ _ (by norm_num) (by norm_num)) (keep₂ _ (by norm_num) (by norm_num))
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, b84, b85, t84, t85⟩ := cornerS_exec (P := E.P) hE.hG hW3 c₂ hw₂
      sa₂ sv₂ sb₂ (hgetD _ i1) (hgetD _ hkn) (hgetD _ i2) c0₂ c1₂
    have hw₃ : WordsBounded E.W c₃ := e₃.wb_right
    have S₃ : PtSt E r PA c₃ T := S₂.regStep hw₃ (fun q hq => f₃.1 q (by
      unfold FixP FixB at hq; simp only [Bcor, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega)) f₃.2.2.1
    have FM₃ : FrameM Bpt c₂ c₃ := (FrameB.toM f₃).mono fun q hq => by
      unfold Bcor at hq
      cases hk : Bk q
      · simp only [hk, Bool.false_or, decide_eq_true_eq] at hq
        exact bpt_of_range (by omega)
      · exact bpt_of_bk hk
    have e0 : emitAt E.Q l k 0 ↔ c₃.nreg 212084 = 1 := by
      rw [t84]; unfold emitAt; rw [show sgnD 0 = 1 by simp [sgnD]]
    have e1 : emitAt E.Q l k 1 ↔ c₃.nreg 212085 = 1 := by
      rw [t85]; unfold emitAt; rw [show sgnD 1 = -1 by simp [sgnD]]
    have i₃ : c₃.nreg 212070 = i := f₃.1 _ (by decide)
    have k₃' : c₃.nreg 212017 = k := by rw [f₃.1 _ (by decide), hk₂]
    -- the length of the records
    have hL := hlenT (c₃.nreg 212084 = 1) (c₃.nreg 212085 = 1)
      ⟨fun h => ⟨hCt, e0.2 h⟩, fun h => e0.1 h.2⟩ ⟨fun h => ⟨hCt, e1.2 h⟩, fun h => e1.1 h.2⟩
    -- direction `+1`
    obtain ⟨c₄, k₄, e₄, hk₄, S₄, F₄, M₄⟩ := dirS_exec hE hr c₃ S₃ (k := k) (d := 0) (b := 212084)
      (i := i) b84 (by norm_num) i₃ (fun h => mem_emIdx.2 ⟨hkn, by norm_num, hCt, e0.2 h⟩)
      (fun _ => hqv) (fun h => by rw [ite_eq_left h] at hL; omega)
    have b85' : c₄.nreg 212085 = c₃.nreg 212085 := F₄.1 _ (by decide)
    have i₄ : c₄.nreg 212070 = i := by rw [F₄.1 _ (by decide), i₃]
    -- direction `-1`
    obtain ⟨c₅, k₅, e₅, hk₅, S₅, F₅, M₅⟩ := dirS_exec hE hr c₄ S₄ (k := k) (d := 1) (b := 212085)
      (i := i) (by rwa [b85']) (by norm_num) i₄
      (fun h => mem_emIdx.2 ⟨hkn, by norm_num, hCt, e1.2 (b85' ▸ h)⟩)
      (fun _ => hqv) (fun h => by
        rw [b85'] at h
        rw [List.length_append]
        by_cases hA : c₃.nreg 212084 = 1
        · simp only [hA, h, ite_true] at hL ⊢; simp; omega
        · simp only [hA, h, ite_true, ite_false] at hL ⊢; simp; omega)
    -- the counter
    have k₅' : c₅.nreg 212017 = k := by rw [F₅.1 _ (by decide), F₄.1 _ (by decide), k₃']
    have c0₅ : c₅.nreg 212000 = 1 := S₅.regs.c0
    have hkW : k + 1 ≤ E.W := by
      have h1 : PA + 3 * l.length ≤ E.W := hS.hPAW; omega
    have e₆ := Exec.addN (P := E.P) S₅.wb 212017 212017 212000 (by rwa [k₅', c0₅])
    have f₆ : FrameB (fun q => decide (q = 212017)) c₅ _ := exec_frameB e₆ (by decide)
    have ex : Exec E.P E.W ptS c _ (k₁ + (k₂ + ((k₃ + (k₄ + k₅) + 1) + 1))) :=
      .seq e₁ (.seq e₂ (.seq (.ifLtN_true (by rw [c1₂, hf]; omega) (.seq e₃ (.seq e₄ e₅))) e₆))
    have hT₂ : T ++ (ptRecs E.li E.Q l k).map (fun x => (r, x)) =
        (T ++ if c₃.nreg 212084 = 1 then [(r, recAt E.li E.Q l (k, 0))] else []) ++
          (if c₄.nreg 212085 = 1 then [(r, recAt E.li E.Q l (k, 1))] else []) := by
      rw [List.append_assoc, hrecs (c₃.nreg 212084 = 1) (c₄.nreg 212085 = 1)
        ⟨fun h => ⟨hCt, e0.2 h⟩, fun h => e0.1 h.2⟩
        ⟨fun h => ⟨hCt, e1.2 (b85' ▸ h)⟩, fun h => b85' ▸ e1.1 h.2⟩]
    refine ⟨_, _, ex, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · unfold ptK; omega
    · rw [hT₂]
      refine S₅.regStep e₆.wb_right (fun q hq => f₆.1 q ?_) f₆.2.2.1
      rcases hq with hq | hq
      · unfold FixP FixB at hq; simp only [decide_eq_false_iff_not]; omega
      · simp only [decide_eq_false_iff_not]; omega
    · simp only [Machine.upd_same, k₅', c0₅]
    · refine FM₁.trans (FM₂.trans (FM₃.trans ((F₄.mono fun q hq => bpt_dir hq).trans
        ((F₅.mono fun q hq => bpt_dir hq).trans ((FrameB.toM f₆).mono fun q hq => ?_)))))
      simp only [decide_eq_true_eq] at hq; subst hq; decide
    · show c₅.nmem a = c.nmem a
      rw [M₅ a ha, M₄ a ha, f₃.2.2.1, f₂.2.2.1, f₁.2.2.1]
  · -- not a vertex: no records
    have hf0 : ¬ C := fun h => hf (hs₂.2 h)
    have hnil : (ptRecs E.li E.Q l k).map (fun x => (r, x)) = [] := by
      rw [hrecs False False ⟨False.elim, fun h => hf0 h.1⟩ ⟨False.elim, fun h => hf0 h.1⟩]
      simp
    have hf' : c₂.nreg 212043 = 0 := by omega
    have e₆ := Exec.addN (P := E.P) hw₂ 212017 212017 212000 (by
      rw [hk₂, c0₂]; have h1 : PA + 3 * l.length ≤ E.W := hS.hPAW; omega)
    have f₆ : FrameB (fun q => decide (q = 212017)) c₂ _ := exec_frameB e₆ (by decide)
    have ex : Exec E.P E.W ptS c _ (k₁ + (k₂ + (2 + 1))) :=
      .seq e₁ (.seq e₂ (.seq (.ifLtN_false (by rw [c1₂, hf']; omega) (.skip hw₂)) e₆))
    refine ⟨_, _, ex, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · unfold ptK; omega
    · rw [hnil, List.append_nil]
      refine S₂.regStep e₆.wb_right (fun q hq => f₆.1 q ?_) f₆.2.2.1
      rcases hq with hq | hq
      · unfold FixP FixB at hq; simp only [decide_eq_false_iff_not]; omega
      · simp only [decide_eq_false_iff_not]; omega
    · simp only [Machine.upd_same, hk₂, c0₂]
    · exact FM₁.trans (FM₂.trans ((FrameB.toM f₆).mono fun q hq => by
        simp only [decide_eq_true_eq] at hq; subst hq; decide))
    · show c₂.nmem a = c.nmem a
      rw [f₂.2.2.1, f₁.2.2.1]

end exec

end

end DrvB

end Chazelle.Core
