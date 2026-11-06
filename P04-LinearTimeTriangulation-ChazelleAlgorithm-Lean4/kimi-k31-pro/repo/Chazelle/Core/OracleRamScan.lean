module

public import Chazelle.Core.OracleHitSem
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Lemma 3.6 (WP-H), RAM part 3: the constants of the query, and the scan of one walk edge

The query program keeps its constants in the registers `120010 … 120049` (`QConst`, for the
values `QV`); every kernel writes only registers `≥ 120050` (and the kernel bands), so the
constants survive (`QConst.congr`).

`wstep` scans the walk edge `w` (register `120070`): a tour edge `w = i + 6` (`i < 2 m`) is the
chain edge `tci i` (computed from `u = (sideS + i) mod 2m`), tested by `edgeT`; box and slit
edges are skipped.  `wstep_exec`: the new best is `wupd`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## The constants -/

/-- **The values of the constants of the query.** -/
structure QV where
  /-- The chain descriptor. -/
  D : ℕ
  /-- The normal-form handle. -/
  NB : ℕ
  /-- Start of the chain. -/
  s : ℕ
  /-- Number of edges. -/
  m : ℕ
  /-- Top index. -/
  tIdx : ℕ
  /-- Orientation bit. -/
  β : ℕ
  /-- `sideS`. -/
  sS : ℕ
  /-- Index in `Q` of the top vertex. -/
  tv : ℕ
  /-- Height vertex of the ray. -/
  hz : ℕ
  /-- Direction bit. -/
  σb : ℕ
  /-- The origin (`none`: box). -/
  zo : Option Point
  /-- Number of arcs. -/
  A : ℕ
  /-- Base of the inverse sequence table. -/
  POS : ℕ
  /-- Base of the `D*` flags. -/
  FL : ℕ
  /-- Base of the labels. -/
  LAB : ℕ
  /-- Base of the `D*` list. -/
  DL : ℕ
  /-- Length of the `D*` list. -/
  nD : ℕ
  /-- Base of the nodes sorted by label. -/
  ORD : ℕ
  /-- Base of the ranks. -/
  RK : ℕ
  /-- Base of the sorted chords. -/
  CH : ℕ
  /-- Number of chords. -/
  K : ℕ
  /-- Model descriptor. -/
  MD : ℕ
  /-- Table of powers. -/
  TB : ℕ
  /-- Its length. -/
  L : ℕ
  /-- Chord area. -/
  CB : ℕ
  /-- Arc area. -/
  AB : ℕ
  /-- Region area. -/
  RB : ℕ
  /-- Sequence table. -/
  SB : ℕ
  /-- List area. -/
  LB : ℕ
  /-- Number of nodes of the book. -/
  μ : ℕ

/-- **The constants of the query in the registers `120010 … 120049`.** -/
structure QConst (P : Polygon) (V : QV) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  D : c.nreg 120013 = V.D
  NB : c.nreg 120014 = V.NB
  s : c.nreg 120015 = V.s
  m : c.nreg 120016 = V.m
  tIdx : c.nreg 120017 = V.tIdx
  β : c.nreg 120018 = V.β
  twoM : c.nreg 120019 = 2 * V.m
  nW : c.nreg 120020 = 2 * V.m + 7
  sS : c.nreg 120021 = V.sS
  tv : c.nreg 120022 = V.tv
  hz : c.nreg 120023 = V.hz
  σb : c.nreg 120024 = V.σb
  org : OriginOK P c V.zo
  six : c.nreg 120028 = 6
  tEnd : c.nreg 120029 = 2 * V.m + 6
  A : c.nreg 120030 = V.A
  POS : c.nreg 120031 = V.POS
  FL : c.nreg 120032 = V.FL
  LAB : c.nreg 120033 = V.LAB
  DL : c.nreg 120034 = V.DL
  nD : c.nreg 120035 = V.nD
  ORD : c.nreg 120036 = V.ORD
  RK : c.nreg 120037 = V.RK
  CH : c.nreg 120038 = V.CH
  K : c.nreg 120039 = V.K
  MD : c.nreg 120040 = V.MD
  TB : c.nreg 120041 = V.TB
  L : c.nreg 120042 = V.L
  CB : c.nreg 120043 = V.CB
  AB : c.nreg 120044 = V.AB
  RB : c.nreg 120045 = V.RB
  SB : c.nreg 120046 = V.SB
  LB : c.nreg 120047 = V.LB
  two : c.nreg 120048 = 2
  μ : c.nreg 120049 = V.μ

/-- The constants survive a statement that does not write the registers `120010 … 120049`. -/
theorem QConst.congr {P : Polygon} {V : QV} {c c' : Config} (h : QConst P V c)
    (hr : ∀ r, 120010 ≤ r → r ≤ 120049 → c'.nreg r = c.nreg r) : QConst P V c' := by
  have g : ∀ r, 120010 ≤ r → r ≤ 120049 → ∀ v, c.nreg r = v → c'.nreg r = v :=
    fun r h1 h2 v hv => (hr r h1 h2).trans hv
  exact ⟨g _ (by norm_num) (by norm_num) _ h.n, g _ (by norm_num) (by norm_num) _ h.one,
    g _ (by norm_num) (by norm_num) _ h.zero, g _ (by norm_num) (by norm_num) _ h.D,
    g _ (by norm_num) (by norm_num) _ h.NB, g _ (by norm_num) (by norm_num) _ h.s,
    g _ (by norm_num) (by norm_num) _ h.m, g _ (by norm_num) (by norm_num) _ h.tIdx,
    g _ (by norm_num) (by norm_num) _ h.β, g _ (by norm_num) (by norm_num) _ h.twoM,
    g _ (by norm_num) (by norm_num) _ h.nW, g _ (by norm_num) (by norm_num) _ h.sS,
    g _ (by norm_num) (by norm_num) _ h.tv, g _ (by norm_num) (by norm_num) _ h.hz,
    g _ (by norm_num) (by norm_num) _ h.σb,
    originOK_congr (fun r h1 h2 => hr r (by omega) (by omega)) h.org,
    g _ (by norm_num) (by norm_num) _ h.six, g _ (by norm_num) (by norm_num) _ h.tEnd,
    g _ (by norm_num) (by norm_num) _ h.A, g _ (by norm_num) (by norm_num) _ h.POS,
    g _ (by norm_num) (by norm_num) _ h.FL, g _ (by norm_num) (by norm_num) _ h.LAB,
    g _ (by norm_num) (by norm_num) _ h.DL, g _ (by norm_num) (by norm_num) _ h.nD,
    g _ (by norm_num) (by norm_num) _ h.ORD, g _ (by norm_num) (by norm_num) _ h.RK,
    g _ (by norm_num) (by norm_num) _ h.CH, g _ (by norm_num) (by norm_num) _ h.K,
    g _ (by norm_num) (by norm_num) _ h.MD, g _ (by norm_num) (by norm_num) _ h.TB,
    g _ (by norm_num) (by norm_num) _ h.L, g _ (by norm_num) (by norm_num) _ h.CB,
    g _ (by norm_num) (by norm_num) _ h.AB, g _ (by norm_num) (by norm_num) _ h.RB,
    g _ (by norm_num) (by norm_num) _ h.SB, g _ (by norm_num) (by norm_num) _ h.LB,
    g _ (by norm_num) (by norm_num) _ h.two, g _ (by norm_num) (by norm_num) _ h.μ⟩

/-- A statement whose written registers (natural and real) lie outside `120010 … 120049`. -/
theorem QConst.frame {P : Polygon} {V : QV} {c c' : Config} {B : ℕ → Bool} (h : QConst P V c)
    (hf : FrameB B c c') (hB : ∀ r, 120010 ≤ r → r ≤ 120049 → B r = false) : QConst P V c' :=
  h.congr fun r h1 h2 => hf.1 r (hB r h1 h2)

/-- **The facts about the values** used by the scan. -/
structure QVOK (P : Polygon) (C : Chain) (V : QV) : Prop where
  CQ : C.P = Qof P
  s : V.s = C.s
  m : V.m = C.m
  sS : V.sS = C.sideS C.sideBeta
  hz_lt : V.hz < P.n
  σb_le : V.σb ≤ 1
  s_lt : V.s < P.n

/-- The edge test's constants from the query's. -/
theorem QConst.econst {P : Polygon} {C : Chain} {V : QV} {c : Config} (h : QConst P V c)
    (hv : QVOK P C V) : EConst P V.s V.hz V.σb V.zo c :=
  ⟨h.n, h.one, h.two, h.s, h.hz, h.σb, hv.σb_le, h.org, hv.s_lt, hv.hz_lt⟩

/-! ## One walk edge -/

/-- **The scan of walk edge `w`** (register `120070`). -/
def wstep : Stmt :=
  .ifLtN 120070 120028 .skip
    (.ifLtN 120070 120029
      (.seq (block [.subN 120071 120070 120028, .addN 120071 120071 120021])
        (.seq (modSub 120071 120019)
          (.seq (.ifLtN 120071 120016 (.instr (.copyN 120060 120071))
                  (block [.subN 120060 120019 120011, .subN 120060 120060 120071]))
            edgeT)))
      .skip)

/-- The registers written by `wstep`. -/
def BW (r : ℕ) : Bool := BE r || decide (r = 120071) || decide (r = 120060)

theorem wr_wstep : wr BW wstep = true := by decide

theorem BW_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BW r = false := by
  sio only [BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]

open Classical in
/-- **The new best after walk edge `w`.** -/
noncomputable def wupd (Q : Polygon) (C : Chain) (s hz : ℕ) (σ : ℝ) (zo : Option Point)
    (best : Option ℕ) (w : ℕ) : Option ℕ :=
  if 6 ≤ w ∧ w < 2 * C.m + 6 then upd1 Q s hz σ zo best (tci C (w - 6)) else best

theorem wstep_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 4 * P.n + 8 ≤ W)
    (hD : DistinctHeights (Qof P)) {C : Chain} {V : QV} (hv : QVOK P C V) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) :
    ∃ c' k, Exec P W wstep c c' k ∧ k ≤ 1120 ∧ FrameB BW c c' ∧ BestOK P.n V.s V.m c' ∧
      bestOf c' = wupd (Qof P) C V.s V.hz (sgnOf V.σb) V.zo (bestOf c) (c.nreg 120070) := by
  have hmn : C.m < P.n := by
    have := C.m_lt; rw [hv.CQ, show (Qof P).n = P.n from shear_n _ _] at this; exact this
  have hm1 := C.one_le
  suffices H : ∃ c' k, Exec P W wstep c c' k ∧ k ≤ 1120 ∧ BestOK P.n V.s V.m c' ∧
      bestOf c' = wupd (Qof P) C V.s V.hz (sgnOf V.σb) V.zo (bestOf c) (c.nreg 120070) by
    obtain ⟨c', k, ex, hk, hb', hv'⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_wstep, hb', hv'⟩
  set w := c.nreg 120070 with hw_def
  by_cases h6 : w < 6
  · refine ⟨c, _, .ifLtN_true (by rwx [hq.six]) (.skip hw), by omega, hb, ?_⟩
    unfold wupd; rw [ite_eq_right (by omega)]
  by_cases hE : w < 2 * C.m + 6
  swap
  · refine ⟨c, _, .ifLtN_false (by rwx [hq.six])
      (.ifLtN_false (by rwx [hq.tEnd, hv.m]) (.skip hw)), by omega, hb, ?_⟩
    unfold wupd; rw [ite_eq_right (by omega)]
  -- the tour edge `i = w - 6`
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 120071 120070 120028, .addN 120071 120071 120021]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 120071 = w - 6 + V.sS ∧ (∀ r, r ≠ 120071 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hq.six, hq.sS, hv.sS]
      have := C.sideS_lt C.sideBeta; omega
    · refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp; rw [hq.six, hq.sS]
      · config_simp; upd_solve
  have hsS : V.sS ≤ 2 * C.m := by rw [hv.sS]; exact C.sideS_lt C.sideBeta
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120071) (nr := 120019)
    (by decide) c₁ e₁.wb_right (by rwo [v₁, r₁ _ (by decide), hq.twoM, hv.m])
  rw [v₁, r₁ _ (by decide), hq.twoM, hv.m] at v₂
  have htj : c₂.nreg 120071 = tj C (w - 6) := by
    rw [v₂]; unfold tj; rw [← hv.sS, Nat.add_comm]
  have hu := tj_lt C (w - 6)
  have R₂ : ∀ r, r ≠ 120071 → c₂.nreg r = c.nreg r := fun r h => (r₂ r h).trans (r₁ r h)
  -- the chain edge
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
      (.ifLtN 120071 120016 (.instr (.copyN 120060 120071))
        (block [.subN 120060 120019 120011, .subN 120060 120060 120071])) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 120060 = tci C (w - 6) ∧ (∀ r, r ≠ 120060 → c₃.nreg r = c₂.nreg r) := by
    have hm2 : c₂.nreg 120016 = C.m := by rw [R₂ _ (by decide), hq.m, hv.m]
    by_cases hlt : tj C (w - 6) < C.m
    · refine ⟨_, _, .ifLtN_true (by rwx [htj, hm2]) (Exec.copyN e₂.wb_right _ _),
        by omega, ?_, fun r hr => ?_⟩
      · config_simp; rw [htj]; unfold tci; rw [ite_eq_left hlt]
      · config_simp; upd_solve
    · have w₂ := e₂.wb_right
      obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃⟩ : ∃ c₃ k₃, Exec P W
          (block [.subN 120060 120019 120011, .subN 120060 120060 120071]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
          c₃.nreg 120060 = 2 * C.m - 1 - tj C (w - 6) ∧
          (∀ r, r ≠ 120060 → c₃.nreg r = c₂.nreg r) := by
        exec_block
        refine ⟨rfl, ?_, fun r hr => ?_⟩
        · config_simp
          rw [R₂ _ (by decide), R₂ _ (by decide), hq.twoM, hq.one, htj, hv.m]
        · config_simp; upd_solve
      refine ⟨c₃, _, .ifLtN_false (by rwx [htj, hm2]) e₃, by omega, ?_, r₃⟩
      rw [v₃]; unfold tci; rw [ite_eq_right hlt]
  have R₃ : ∀ r, r ≠ 120071 → r ≠ 120060 → c₃.nreg r = c.nreg r := fun r h1 h2 =>
    (r₃ r h2).trans (R₂ r h1)
  have hq₃ : QConst P V c₃ := hq.congr fun r h1 h2 => R₃ r (by omega) (by omega)
  have hb₃ : BestOK P.n V.s V.m c₃ := by
    unfold BestOK
    rw [R₃ 120050 (by decide) (by decide), R₃ 120051 (by decide) (by decide),
      R₃ 120052 (by decide) (by decide)]
    exact hb
  obtain ⟨c₄, k₄, e₄, hk₄, -, hb₄, v₄⟩ := edgeT_exec (P := P) hG (by omega) hD c₃ e₃.wb_right
    (hq₃.econst hv) (by rw [v₃]; have := tci_lt C (w - 6); omega) (mb := V.m)
    (by rw [v₃, hv.m]; exact tci_lt C (w - 6)) hb₃
  have hbo₃ : bestOf c₃ = bestOf c := by
    unfold bestOf
    rw [R₃ 120050 (by decide) (by decide), R₃ 120052 (by decide) (by decide)]
  rw [v₃, hbo₃] at v₄
  refine ⟨c₄, _, .ifLtN_false (by rwx [hq.six])
    (.ifLtN_true (by rwx [hq.tEnd, hv.m]) (.seq e₁ (.seq e₂ (.seq e₃ e₄)))),
    by omega, hb₄, ?_⟩
  rw [v₄]; unfold wupd; rw [ite_eq_left ⟨by omega, hE⟩]

/-! ## The semantic context -/

/-- **The geometric context of the scan**: the ray from `z` at the height of vertex `hz`, in
direction `σ = sgnOf σb`, the origin data `zo` of the registers. -/
structure SemOK (P : Polygon) (C : Chain) (V : QV) (z : Point) : Prop where
  hv : QVOK P C V
  hD : DistinctHeights (Qof P)
  zy : z.2 = ((Qof P).vtx V.hz).2
  σ : sgnOf V.σb = 1 ∨ sgnOf V.σb = -1
  zo : ZoOK C (sgnOf V.σb) z V.zo

theorem sgnOf_cases (b : ℕ) : sgnOf b = 1 ∨ sgnOf b = -1 := by
  unfold sgnOf; split_ifs <;> simp

/-- **One walk edge, semantically.** -/
theorem wupd_step {P : Polygon} {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z)
    {S : Set Point} {best : Option ℕ}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z best))
    (w : ℕ) :
    Sweep.FirstHitOpt (S ∪ wseg C w) z (sgnOf V.σb)
      (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z
        (wupd (Qof P) C V.s V.hz (sgnOf V.σb) V.zo best w)) := by
  unfold wupd wseg
  by_cases h : 6 ≤ w ∧ w < 2 * C.m + 6
  · rw [ite_eq_left h, ite_eq_left h]
    exact fold_step hs.hv.CQ hs.hv.s.symm hs.hD (tci_lt C _) hs.zy hs.σ hs.zo hS
  · rwx [ite_eq_right h, ite_eq_right h, Set.union_empty]

end

end OracleR

end Chazelle.Core
