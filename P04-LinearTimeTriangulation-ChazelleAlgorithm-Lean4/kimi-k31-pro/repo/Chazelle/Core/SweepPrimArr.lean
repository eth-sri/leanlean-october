module

public import Chazelle.Core.SweepPrimArrMath
public import Chazelle.Core.SweepDetect2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Sweep RAM primitives (WP-D2), part 8: `arrivalPos`

`arrivalPos` (design-merge-v2 §9.6 item 1).  Input: the walk position `x = (e, h)` of
`chainModel C` in `50201, 50202` (a proper position whose point `w` is strictly inside the
height range of the box) and, in `50203`, the code `ρ` of the **reversed** ray direction: the ray
arrives at `w` in direction `σ = -dirOf ρ` (so its left-sector test is in direction `dirOf ρ`; for
a shot in direction `dirOf v` pass `ρ = 1 - v` if `v ≤ 1`, see `neg_dirOf_flip`).  Output:
`50210 = 1` and a proper position `(p, h')` in `50211, 50212` with
`Sweep.Arrival W w σ p (param (p, h'))`, or `50210 = 0` if no position of `w` is an arrival
position (`ArrRes`).

The machine classifies `x` like `leftSec` (inside an edge, or at a tour vertex), then

* inside an edge: tests the edge; if the test fails, the answer is the twin edge (a slit edge or a
  tour edge; `twin_left`), or none on a vertical side of the box (`wall_none`);
* at the chain vertex `v_k`: tests the candidates `candIdx m S k`, `candIdx m S (2m - k)` and, if
  `k` is the top, `2m` (`cand_complete`, `vertex_positions`).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE sideLeft sidePt)

@[expose] public section

/-! ## The result -/

/-- **The result of `arrivalPos`** for the input position `(e, h)` and reversed direction code
`ρ`. -/
def ArrRes (P : Polygon) (C : Chain) (e h ρ : ℕ) (c' : Config) : Prop :=
  c'.nreg 50210 ≤ 1 ∧
    (c'.nreg 50210 = 1 → c'.nreg 50211 < (chainModel C).W.n ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c'.nreg 50211, c'.nreg 50212⟩ ∧
      Sweep.Arrival (chainModel C).W ((chainModel C).pos (Qof P) ⟨e, h⟩) (-dirOf ρ)
        (c'.nreg 50211) ((chainModel C).param (Qof P) ⟨c'.nreg 50211, c'.nreg 50212⟩)) ∧
    (c'.nreg 50210 ≠ 1 → ∀ p t, ¬ Sweep.Arrival (chainModel C).W
      ((chainModel C).pos (Qof P) ⟨e, h⟩) (-dirOf ρ) p t)

/-- Reversing a direction code. -/
theorem neg_dirOf_flip (v : ℕ) : -dirOf (if v = 1 then 0 else 1) = dirOf v := by
  unfold dirOf; split_ifs <;> simp_all

/-! ## Mathematics of the answers -/

/-- An arrival position at the point of a proper position. -/
theorem arrival_iff (M : Model) (Q : Polygon) {y : WPos} (hy : y.edge < M.W.n)
    (h0 : 0 ≤ M.param Q y) (h1 : M.param Q y < 1) (σ : ℝ) :
    Sweep.Arrival M.W (M.pos Q y) σ y.edge (M.param Q y) ↔
      sideLeft M.W y.edge (M.param Q y) (Visibility.rayPt (M.pos Q y) (-σ) 1) :=
  ⟨fun h => h.2.2.2.2, fun h => ⟨hy, h0, h1, rfl, h⟩⟩

/-- **The twin edge takes over** when the arriving ray is not in the half-plane of the edge. -/
theorem twin_left (M : Model) (Q : Polygon) {p p' h : ℕ} (hh : 1 ≤ h)
    (h1 : M.wa p' = M.wb p) (h2 : M.wb p' = M.wa p) (ht : 0 < M.param Q ⟨p, h⟩)
    (ht1 : M.param Q ⟨p, h⟩ < 1) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hn : ¬ sideLeft M.W p (M.param Q ⟨p, h⟩) (Visibility.rayPt (M.pos Q ⟨p, h⟩) s 1)) :
    sideLeft M.W p' (M.param Q ⟨p', h⟩) (Visibility.rayPt (M.pos Q ⟨p', h⟩) s 1) ∧
      M.pos Q ⟨p', h⟩ = M.pos Q ⟨p, h⟩ ∧ 0 < M.param Q ⟨p', h⟩ ∧ M.param Q ⟨p', h⟩ < 1 := by
  have hne := ne_of_param_pos ht
  obtain ⟨hpos, hpar⟩ := twin_pos_param M Q hh h1 h2 hne
  have ht' : 0 < M.param Q ⟨p', h⟩ := by rwli [hpar]
  have ht1' : M.param Q ⟨p', h⟩ < 1 := by rwli [hpar]
  refine ⟨?_, hpos, ht', ht1'⟩
  have hne' : (M.W.vtx p').2 ≠ (M.W.vtx ((p' + 1) % M.W.n)).2 := by
    have := ne_of_param_pos ht'; exact this
  rw [pos_eq_sidePt] at hn ⊢
  rw [sideLeft_interior ht' ht1' hne']
  rw [sideLeft_interior ht ht1 hne] at hn
  have e1 : M.W.vtx p' = M.wa p' := rfl
  have e2 : M.W.vtx ((p' + 1) % M.W.n) = M.wb p' := rfl
  have e3 : M.W.vtx p = M.wa p := rfl
  have e4 : M.W.vtx ((p + 1) % M.W.n) = M.wb p := rfl
  rw [e1, e2, h1, h2]
  rw [e3, e4] at hn
  have hd : (M.wb p).2 - (M.wa p).2 ≠ 0 := sub_ne_zero.2 hne.symm
  rcases hs with rfl | rfl
  · push Not at hn
    rcases lt_or_gt_of_ne hd with hd | hd <;> nlinarith
  · push Not at hn
    rcases lt_or_gt_of_ne hd with hd | hd <;> nlinarith

/-- **No arrival position on a vertical side of the box** when the edge test fails. -/
theorem wall_none (C : Chain) (hP : C.P.Simple) {Q : Polygon} {e h : ℕ} (he : e = 1 ∨ e = 3)
    (ht : 0 < (chainModel C).param Q ⟨e, h⟩) (ht1 : (chainModel C).param Q ⟨e, h⟩ < 1) {σ : ℝ}
    (hn : ¬ sideLeft (chainModel C).W e ((chainModel C).param Q ⟨e, h⟩)
      (Visibility.rayPt ((chainModel C).pos Q ⟨e, h⟩) (-σ) 1)) :
    ∀ p t, ¬ Sweep.Arrival (chainModel C).W ((chainModel C).pos Q ⟨e, h⟩) σ p t := by
  rintro p t ⟨hp, ht0, ht1', hpt, hl⟩
  rw [pos_eq_sidePt] at hpt hl hn
  obtain ⟨rfl, rfl⟩ := wall_unique C hP he ht ht1 hp ht0 ht1' hpt
  exact hn (by rwx [← hpt])

/-- **An arrival position at a tour vertex.** -/
theorem arrival_vertex (C : Chain) {Q : Polygon} {x : WPos} {i : ℕ} (hi : i ≤ 2 * C.m)
    (hv : (chainModel C).W.vtx (i + 6) = (chainModel C).pos Q x) {σ : ℝ}
    (hl : sideLeft (chainModel C).W (i + 6) 0
      (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (-σ) 1)) :
    Sweep.Arrival (chainModel C).W ((chainModel C).pos Q x) σ (i + 6)
      ((chainModel C).param Q ⟨i + 6, 0⟩) := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  refine ⟨by omega, le_refl _, by rwn [Model.param], ?_, ?_⟩
  · rw [show (chainModel C).param Q ⟨i + 6, 0⟩ = 0 from rfl, Chazelle.Chain.sidePt_zero, hv]
  · rwx [show (chainModel C).param Q ⟨i + 6, 0⟩ = 0 from rfl, ← hv]

/-- **No arrival position at a chain vertex** when all candidates fail. -/
theorem vertex_none (C : Chain) (hP : C.P.Simple) {Q : Polygon} {x : WPos} {k : ℕ}
    (hk : k ≤ C.m) (hv : (chainModel C).pos Q x = C.vertex k) {σ : ℝ}
    (hn : ∀ i, i ≤ 2 * C.m → (i = candIdx C.m (C.sideS C.sideBeta) k ∨
        i = candIdx C.m (C.sideS C.sideBeta) (2 * C.m - k) ∨ (i = 2 * C.m ∧ k = C.topIdx)) →
      ¬ sideLeft (chainModel C).W (i + 6) 0
        (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (-σ) 1)) :
    ∀ p t, ¬ Sweep.Arrival (chainModel C).W ((chainModel C).pos Q x) σ p t := by
  rintro p t ⟨hp, ht0, ht1, hpt, hl⟩
  rw [hv] at hpt hl
  obtain ⟨rfl, i, hi, rfl, hik⟩ := vertex_positions C hP hk hp ht0 ht1 hpt
  have hcand := cand_complete C C.sideBeta hi hik
  refine hn i hi ?_ ?_
  · rcases hcand with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨h, ?_⟩)
      rw [← hik, h, C.sideIdx_two_m]
  · rw [Chazelle.Chain.sidePt_zero] at hpt
    rwx [hpt]


/-- Inside an edge, the edge test is the turning code `1`. -/
theorem interior_iff (M : Model) (Q : Polygon) {x : WPos} (ht : 0 < M.param Q x)
    (ht1 : M.param Q x < 1) (ρ : ℕ) :
    turnCode (dirCode M x.edge) ρ = 1 ↔
      sideLeft M.W x.edge (M.param Q x) (Visibility.rayPt (M.pos Q x) (dirOf ρ) 1) := by
  rw [← interior_bit, pos_eq_sidePt]
  exact (sideLeft_interior ht ht1 (ne_of_param_pos ht)).symm

/-! ## The machine -/

/-- Found at the input position (the flag is already `1`). -/
def foundIn : Stmt := block [.copyN 50211 50201, .copyN 50212 50202]
/-- Found at the up-slit edge `2m + 6`, same height code. -/
def foundTop : Stmt :=
  block [.constN 50210 1, .addN 50211 50053 50053, .addN 50211 50211 50081, .copyN 50212 50202]
/-- Found at the down-slit edge `5`, same height code. -/
def found5 : Stmt := block [.constN 50210 1, .constN 50211 5, .copyN 50212 50202]
/-- Found at the tour edge `50121 + 6`, same height code. -/
def foundT : Stmt := block [.constN 50210 1, .addN 50211 50121 50081, .copyN 50212 50202]
/-- Found at the tour vertex `50121 + 6`. -/
def foundV : Stmt := block [.constN 50210 1, .addN 50211 50121 50081, .constN 50212 0]
/-- No arrival position. -/
def noneS : Stmt := .instr (.constN 50210 0)

/-- Inside an edge of the box block. -/
def boxArr : Stmt := .seq intOut (.ifLtN 50210 50032 (.ifLtN 50201 50085 .skip foundTop) foundIn)

/-- The twin of a tour or up-slit edge. -/
def twinT : Stmt :=
  .seq (.instr (.subN 50120 50201 50081)) (.seq tvIdx
    (.ifLtN 50120 50058
      (.seq (block [.subN 50224 50058 50032, .subN 50224 50224 50077])
        (.seq (.ifLtN 50224 50059 (.instr (.addN 50121 50224 50089))
          (.instr (.subN 50121 50224 50059))) foundT))
      found5))

/-- Inside an edge of the tour or the up-slit edge. -/
def intArr : Stmt := .seq intOut (.ifLtN 50210 50032 twinT foundIn)

/-- The candidate tour step `candIdx m S (r)` into `50121`. -/
def candS (r : ℕ) : Stmt :=
  .ifLtN r 50221 (.instr (.addN 50121 r 50223)) (.instr (.subN 50121 r 50221))

/-- Test the sector of the candidate `50121`; answer or continue. -/
def tryS (rest : Stmt) : Stmt := .seq secAt (.ifLtN 50110 50032 rest foundV)

/-- At a tour vertex: all tour vertices of the same chain vertex. -/
def vtxArr : Stmt :=
  .seq (.instr (.subN 50120 50201 50081)) (.seq tvIdx
    (.seq (block [.copyN 50220 50091, .copyN 50221 50059, .copyN 50222 50058, .copyN 50223 50089])
      (.seq (candS 50220) (tryS
        (.seq (.instr (.subN 50224 50222 50220)) (.seq (candS 50224) (tryS
          (.ifLtN 50220 50054 noneS (.ifLtN 50054 50220 noneS
            (.seq (.instr (.copyN 50121 50222)) (tryS noneS)))))))))))

/-- **`arrivalPos`**: the classification of `leftSec`, then the cases. -/
def arrCore : Stmt :=
  .seq (.instr (.copyN 50002 50201)) (.seq dirAt
    (.ifLtN 50201 50081 boxArr
      (.ifLtN 50202 50032 vtxArr
        (.ifLtN 10502 50032 vtxArr
          (.seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50133)
            (.seq (block [.constN 50160 0, .subN 50161 50202 50032])
              (.seq (kbit 50133 50160 50133 1 50170) (.seq (kbit 50160 50133 50160 1 50171)
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxArr intArr) intArr))))))))))

/-- **The primitive `arrivalPos`.** -/
def arrivalPos : Stmt := .seq pHead arrCore

theorem wr_arrivalPos : wr Bprim arrivalPos = true := by decide


/-! ## The vertex case -/

/-- **Testing one candidate tour vertex.** -/
theorem tryS_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {rest : Stmt} {K : ℕ}
    (c : Config) (hE : CEnv P W H C c) {e hc ρ i : ℕ} (h03 : c.nreg 50203 = ρ)
    (h121 : c.nreg 50121 = i) (hi : i ≤ 2 * C.m) (hWn : 2 * C.m + 7 ≤ W)
    (hv : (chainModel C).W.vtx (i + 6) = (chainModel C).pos (Qof P) ⟨e, hc⟩)
    (hrest : ∀ c₁ : Config, CEnv P W H C c₁ → FrameB Bsec c c₁ →
      ¬ sideLeft (chainModel C).W (i + 6) 0
        (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (dirOf ρ) 1) →
      ∃ c' k, Exec P W rest c₁ c' k ∧ k ≤ K ∧ ArrRes P C e hc ρ c') :
    ∃ c' k, Exec P W (tryS rest) c c' k ∧ k ≤ K + 81 * H.length + 3205 ∧
      ArrRes P C e hc ρ c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hE₁, b₁⟩ := secAt_exec c hE h121 hi
  rw [h03] at b₁
  have w₁ := e₁.wb_right
  by_cases h0 : c₁.nreg 50110 < c₁.nreg 50032
  · rw [hE₁.r32] at h0
    have hn : ¬ sideLeft (chainModel C).W (i + 6) 0
        (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (dirOf ρ) 1) := fun h => by
      have := b₁.2.2 h; omega
    obtain ⟨c', k, ex, hk, hr⟩ := hrest c₁ hE₁ f₁ hn
    exact ⟨c', _, .seq e₁ (.ifLtN_true (by rwx [hE₁.r32]) ex), by omega, hr⟩
  · have h0' : ¬ c₁.nreg 50110 < 1 := by rw [hE₁.r32] at h0; exact h0
    have hl : sideLeft (chainModel C).W (i + 6) 0
        (Visibility.rayPt ((chainModel C).W.vtx (i + 6)) (dirOf ρ) 1) :=
      b₁.2.1 (by have := b₁.1; omega)
    have q121 : c₁.nreg 50121 = i := by rw [f₁.1 _ (by decide), h121]
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W foundV c₁ c₂ k₂ ∧ k₂ = 3 ∧
        (c₂.nreg 50210 = 1 ∧ c₂.nreg 50211 = i + 6 ∧ c₂.nreg 50212 = 0) := by
      unfold foundV
      exec_block
      · omega
      · config_simp; rwo [q121, hE₁.r81]
      · omega
      · refine ⟨rfl, ?_⟩
        config_simp
        rw [q121, hE₁.r81]
    obtain ⟨q10, q11, q12⟩ := q
    have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false h0 e₂), by omega,
      by rw [q10], fun _ => ?_, fun h => absurd q10 h⟩
    rw [q11, q12]
    refine ⟨by omega, ⟨le_refl _, by rwn [Model.param], by simp⟩, ?_⟩
    exact arrival_vertex C hi hv (by rwx [neg_neg])

/-- The candidate computation. -/
theorem candS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {r m S j : ℕ}
    (_hr : r ≠ 50121) (h221 : c.nreg 50221 = S) (h223 : c.nreg 50223 = 2 * m - S)
    (hrj : c.nreg r = j) (hS : S ≤ 2 * m) (_hj : j ≤ 2 * m) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W (candS r) c c' k ∧ k ≤ 3 ∧ c'.nreg 50121 = candIdx m S j ∧
      ∀ r', r' ≠ 50121 → c'.nreg r' = c.nreg r' := by
  unfold candS candIdx
  by_cases h : j < S
  · refine spec_ifLtN_true (by rwx [hrj, h221]) (spec_instr (Exec.addN hw _ _ _
      (by rwo [hrj, h223])) fun _ => ⟨by omega, ?_, fun r' hr' => by simp [hr']⟩)
    config_simp; rw [hrj, h223, ite_eq_left h]
  · refine spec_ifLtN_false (by rwx [hrj, h221]) (spec_instr (Exec.subN hw _ _ _)
      fun _ => ⟨by omega, ?_, fun r' hr' => by simp [hr']⟩)
    config_simp; rw [hrj, h221, ite_eq_right h]

/-- The walk vertex of a candidate is the chain vertex. -/
theorem walk_vtx_cand (C : Chain) {i k : ℕ} (hi : i ≤ 2 * C.m) (hk : C.sideIdx C.sideBeta i = k) :
    (chainModel C).W.vtx (i + 6) = C.vertex k := by
  rw [walk_vtx_tour C hi, hk]

/-- **The vertex case of `arrivalPos`.** -/
theorem vtxArr_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hP : C.P.Simple) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h03 : c.nreg 50203 = ρ) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7) (hWn : 2 * C.m + 7 ≤ W)
    (hpar : (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) :
    ∃ c' k, Exec P W vtxArr c c' k ∧ k ≤ 26000 ∧ ArrRes P C e hc ρ c' := by
  have hlen := hE.hlen
  have hm1 := C.one_le
  have hT := C.topIdx_le
  have hS := C.sideS_lt C.sideBeta
  set S := C.sideS C.sideBeta with hSdef
  -- the chain vertex
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  set c₁ : Config := { c with nreg := upd c.nreg 50120 (c.nreg 50201 - c.nreg 50081) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, k91, k58, k59, k89, -⟩ := tvIdx_exec c₁ hE₁ (i := e - 6)
    (by rw [hc₁]; simp [h01, hE.r81]) (by omega)
  have hE₂ : CEnv P W H C c₂ := hE₁.frame f₂ e₂.wb_right (by decide)
  set k := C.sideIdx C.sideBeta (e - 6) with hkdef
  have hkm : k ≤ C.m := C.sideIdx_le _ _
  have hposx : (chainModel C).pos (Qof P) ⟨e, hc⟩ = C.vertex k := by
    rw [pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero]
    rw [show e = (e - 6) + 6 by omega, walk_vtx_tour C (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50220 50091, .copyN 50221 50059,
      .copyN 50222 50058, .copyN 50223 50089]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 50220 = k ∧ c₃.nreg 50221 = S ∧ c₃.nreg 50222 = 2 * C.m ∧
        c₃.nreg 50223 = 2 * C.m - S ∧
        ∀ r, r ≠ 50220 → r ≠ 50221 → r ≠ 50222 → r ≠ 50223 → c₃.nreg r = c₂.nreg r) := by
    have hw₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, by config_simp; exact k91, by config_simp; exact k59, by config_simp; exact k58,
      by config_simp; exact k89, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩
  obtain ⟨q20, q21, q22, q23, r₃⟩ := q
  have hE₃ : CEnv P W H C c₃ := hE₂.keep e₃.wb_right
    (exec_frameB e₃ (B := fun r => decide (50220 ≤ r ∧ r < 50224)) (by decide)).2.2.1
    (fun r hr => r₃ r (ne_of_mem_of_not_mem hr (by decide))
      (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      (ne_of_mem_of_not_mem hr (by decide)))
  have s₃ : c₃.nreg 50203 = ρ := by
    rw [r₃ _ (by decide) (by decide) (by decide) (by decide), f₂.1 _ (by decide), hc₁]
    simp [h03]
  -- the candidates
  obtain ⟨⟨ca1, ca2⟩, ⟨cb1, cb2⟩⟩ := cand_vertex C C.sideBeta hkm
  have hmW : 2 * C.m ≤ W := by omega
  obtain ⟨c₄, k₄, e₄, hk₄, q121, r₄⟩ := candS_exec (P := P) c₃ e₃.wb_right (by decide) q21 q23
    q20 hS (by omega) hmW
  have hE₄ : CEnv P W H C c₄ := hE₃.keep e₄.wb_right
    (exec_frameB e₄ (B := fun r => r == 50121) (by decide)).2.2.1
    (fun r hr => r₄ r (ne_of_mem_of_not_mem hr (by decide)))
  -- registers kept by the sector procedure
  have kS : ∀ {ca cb : Config}, FrameB Bsec ca cb → ∀ r, 50200 ≤ r → r < 50230 → r ≠ 50210 →
      r ≠ 50211 → r ≠ 50212 → cb.nreg r = ca.nreg r := fun hf r h1 h2 h3 h4 h5 => hf.1 r (by
        interval_cases r <;> first | decide)
  have hn7 : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  obtain ⟨c', k', ex', hk', res⟩ := tryS_exec (K := 17000) (e := e) (hc := hc) (ρ := ρ)
      (i := candIdx C.m S k) (rest := .seq
      (.instr (.subN 50224 50222 50220)) (.seq (candS 50224) (tryS
        (.ifLtN 50220 50054 noneS (.ifLtN 50054 50220 noneS
          (.seq (.instr (.copyN 50121 50222)) (tryS noneS))))))) c₄ hE₄
      (by rw [r₄ _ (by decide), s₃]) q121 ca1 hWn (by rw [walk_vtx_cand C ca1 ca2, hposx]) (by
    intro c₅ hE₅ f₅ hn₁
    have g₅ := kS f₅
    have w₅ := hE₅.wb
    have e₆ := Exec.subN (P := P) w₅ 50224 50222 50220
    set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50224 (c₅.nreg 50222 - c₅.nreg 50220) }
      with hc₆
    have hE₆ : CEnv P W H C c₆ := hE₅.frame (exec_frameB e₆ (B := fun r => r == 50224)
      (by decide)) e₆.wb_right (by decide)
    have r₆ : ∀ r, r ≠ 50224 → c₆.nreg r = c₅.nreg r := fun r hr => by rw [hc₆]; simp [hr]
    have v20 : c₅.nreg 50220 = k := by
      rw [g₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        r₄ _ (by decide), q20]
    have v21 : c₅.nreg 50221 = S := by
      rw [g₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        r₄ _ (by decide), q21]
    have v22 : c₅.nreg 50222 = 2 * C.m := by
      rw [g₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        r₄ _ (by decide), q22]
    have v23 : c₅.nreg 50223 = 2 * C.m - S := by
      rw [g₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        r₄ _ (by decide), q23]
    have v03 : c₅.nreg 50203 = ρ := by
      rw [g₅ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        r₄ _ (by decide), s₃]
    obtain ⟨c₇, k₇, e₇, hk₇, q121', r₇⟩ := candS_exec (P := P) (r := 50224) (j := 2 * C.m - k) c₆
      e₆.wb_right (by decide)
      (by rw [r₆ _ (by decide), v21]) (by rw [r₆ _ (by decide), v23])
      (by rw [hc₆]; simp [v22, v20]) hS (by omega) hmW
    have hE₇ : CEnv P W H C c₇ := hE₆.keep e₇.wb_right
      (exec_frameB e₇ (B := fun r => r == 50121) (by decide)).2.2.1
      (fun r hr => r₇ r (ne_of_mem_of_not_mem hr (by decide)))
    have t7 : ∀ r, r ≠ 50121 → r ≠ 50224 → c₇.nreg r = c₅.nreg r := fun r h1 h2 => by
      rw [r₇ r h1, r₆ r h2]
    obtain ⟨c'', k'', ex'', hk'', res'⟩ := tryS_exec (K := 8500) (e := e) (hc := hc) (ρ := ρ)
        (i := candIdx C.m S (2 * C.m - k)) (rest := .ifLtN 50220 50054
        noneS (.ifLtN 50054 50220 noneS (.seq (.instr (.copyN 50121 50222)) (tryS noneS)))) c₇
        hE₇ (by rw [t7 _ (by decide) (by decide), v03]) q121' cb1 hWn
        (by rw [walk_vtx_cand C cb1 cb2, hposx]) (by
      intro c₈ hE₈ f₈ hn₂
      have g₈ := kS f₈
      have w₈ := hE₈.wb
      have u20 : c₈.nreg 50220 = k := by
        rw [g₈ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          t7 _ (by decide) (by decide), v20]
      have u22 : c₈.nreg 50222 = 2 * C.m := by
        rw [g₈ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          t7 _ (by decide) (by decide), v22]
      have u03 : c₈.nreg 50203 = ρ := by
        rw [g₈ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
          t7 _ (by decide) (by decide), v03]
      -- the final answer when no candidate is left
      have none_res : ∀ c₉ : Config, c₉.nreg 50210 = 0 →
          (k = C.topIdx → ¬ sideLeft (chainModel C).W (2 * C.m + 6) 0
            (Visibility.rayPt ((chainModel C).W.vtx (2 * C.m + 6)) (dirOf ρ) 1)) →
          ArrRes P C e hc ρ c₉ := by
        intro c₉ h10 hn₃
        refine ⟨by rwo [h10], fun h => by omega, fun _ => ?_⟩
        refine vertex_none C hP hkm hposx ?_
        intro i hi hic
        rw [neg_neg]
        rcases hic with rfl | rfl | ⟨rfl, hkT⟩
        · exact hn₁
        · exact hn₂
        · exact hn₃ hkT
      have noneS_exec : ∀ c₉ : Config, WordsBounded W c₉ →
          (k = C.topIdx → ¬ sideLeft (chainModel C).W (2 * C.m + 6) 0
            (Visibility.rayPt ((chainModel C).W.vtx (2 * C.m + 6)) (dirOf ρ) 1)) →
          ∃ c' k, Exec P W noneS c₉ c' k ∧ k = 1 ∧ ArrRes P C e hc ρ c' := fun c₉ hw₉ hn₃ =>
        ⟨_, 1, Exec.constN hw₉ _ _ (by omega), rfl, none_res _ (by simp) hn₃⟩
      by_cases hk1 : c₈.nreg 50220 < c₈.nreg 50054
      · obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₈ w₈ (fun h => by
          rwo [u20, hE₈.r54] at hk1)
        exact ⟨c', _, .ifLtN_true hk1 ex, by omega, r⟩
      by_cases hk2 : c₈.nreg 50054 < c₈.nreg 50220
      · obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₈ w₈ (fun h => by
          rwo [u20, hE₈.r54] at hk2)
        exact ⟨c', _, .ifLtN_false hk1 (.ifLtN_true hk2 ex), by omega, r⟩
      have hkT : k = C.topIdx := by rwo [u20, hE₈.r54] at hk1 hk2
      have e₉ := Exec.copyN (P := P) w₈ 50121 50222
      set c₉ : Config := { c₈ with nreg := upd c₈.nreg 50121 (c₈.nreg 50222) } with hc₉
      have hE₉ : CEnv P W H C c₉ := hE₈.frame (exec_frameB e₉ (B := fun r => r == 50121)
        (by decide)) e₉.wb_right (by decide)
      have hv₃ : (chainModel C).W.vtx (2 * C.m + 6) = (chainModel C).pos (Qof P) ⟨e, hc⟩ := by
        rw [walk_vtx_cand C le_rfl (C.sideIdx_two_m _), hposx, hkT]
      obtain ⟨c', k', ex, hk, r⟩ := tryS_exec (K := 1) (rest := noneS) (e := e) (hc := hc)
        (ρ := ρ) (i := 2 * C.m) c₉ hE₉
        (by rw [hc₉]; simp [u03]) (by rw [hc₉]; simp [u22]) le_rfl hWn hv₃ (by
          intro c₁₀ hE₁₀ f₁₀ hn₃
          obtain ⟨c', k', ex, hk, r⟩ := noneS_exec c₁₀ hE₁₀.wb (fun _ => hn₃)
          exact ⟨c', k', ex, by omega, r⟩)
      exact ⟨c', _, .ifLtN_false hk1 (.ifLtN_false hk2 (.seq e₉ ex)), by omega, r⟩)
    exact ⟨c'', _, .seq e₆ (.seq e₇ ex''), by omega, res'⟩)
  refine ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ ex'))), by omega, res⟩


/-! ## The interior cases -/

theorem hgt_pos_of_param_pos {M : Model} {Q : Polygon} {e h : ℕ} (ht : 0 < M.param Q ⟨e, h⟩) :
    1 ≤ h := by
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · exact absurd (show M.param Q ⟨e, 0⟩ = 0 from rfl) (ne_of_gt ht)
  · exact h0

/-- The answer at the input position. -/
theorem found_here {P : Polygon} {C : Chain} {e hc ρ : ℕ} (hen : e < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param (Qof P) ⟨e, hc⟩) (h1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) (hl : sideLeft (chainModel C).W e ((chainModel C).param (Qof P) ⟨e, hc⟩)
      (Visibility.rayPt ((chainModel C).pos (Qof P) ⟨e, hc⟩) (dirOf ρ) 1))
    {c' : Config} (q10 : c'.nreg 50210 = 1) (q11 : c'.nreg 50211 = e) (q12 : c'.nreg 50212 = hc) :
    ArrRes P C e hc ρ c' := by
  refine ⟨by rw [q10], fun _ => ?_, fun h => absurd q10 h⟩
  rw [q11, q12]
  exact ⟨hen, ⟨h0, h1, hhn⟩, (arrival_iff _ _ (y := ⟨e, hc⟩) hen h0 h1 _).2 (by rwx [neg_neg])⟩

/-- The answer at a twin position. -/
theorem found_twin {P : Polygon} {C : Chain} {e hc ρ p' : ℕ} (hp' : p' < (chainModel C).W.n)
    (hhn : hc ≤ P.n)
    (htw : sideLeft (chainModel C).W p' ((chainModel C).param (Qof P) ⟨p', hc⟩)
      (Visibility.rayPt ((chainModel C).pos (Qof P) ⟨p', hc⟩) (dirOf ρ) 1) ∧
      (chainModel C).pos (Qof P) ⟨p', hc⟩ = (chainModel C).pos (Qof P) ⟨e, hc⟩ ∧
      0 < (chainModel C).param (Qof P) ⟨p', hc⟩ ∧ (chainModel C).param (Qof P) ⟨p', hc⟩ < 1)
    {c' : Config} (q10 : c'.nreg 50210 = 1) (q11 : c'.nreg 50211 = p') (q12 : c'.nreg 50212 = hc) :
    ArrRes P C e hc ρ c' := by
  obtain ⟨hl, hpos, ht0, ht1⟩ := htw
  refine ⟨by rw [q10], fun _ => ?_, fun h => absurd q10 h⟩
  rw [q11, q12]
  refine ⟨hp', ⟨ht0.le, ht1, hhn⟩, ?_⟩
  rw [← hpos]
  exact (arrival_iff _ _ (y := ⟨p', hc⟩) hp' ht0.le ht1 _).2 (by rwx [neg_neg])

theorem dirOf_cases' (ρ : ℕ) : dirOf ρ = 1 ∨ dirOf ρ = -1 := dirOf_cases ρ

/-- The block `foundTop`. -/
theorem foundTop_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {m hc : ℕ}
    (h53 : c.nreg 50053 = m) (h81 : c.nreg 50081 = 6) (h02 : c.nreg 50202 = hc)
    (hmW : 2 * m + 7 ≤ W) :
    ∃ c' k, Exec P W foundTop c c' k ∧ k = 4 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = 2 * m + 6 ∧ c'.nreg 50212 = hc) := by
  unfold foundTop
  exec_block
  all_goals try omega
  all_goals try (config_simp; rwo [h53])

/-- **Inside an edge of the box block.** -/
theorem boxArr_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hP : C.P.Simple) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (h03 : c.nreg 50203 = ρ)
    (hd : c.nreg 10502 = dirCode (chainModel C) e) (he : e < 6)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (ht1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) (hWn : 2 * C.m + 7 ≤ W) :
    ∃ c' k, Exec P W boxArr c c' k ∧ k ≤ 30 ∧ ArrRes P C e hc ρ c' := by
  have hn7 : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁⟩ := intOut_exec (P := P) c hE.wb (by omega) hE.r32
    (by rw [hd]; exact dirCode_le_two _ _)
  rw [hd, h03, interior_iff _ _ (x := ⟨e, hc⟩) ht ht1] at b₁
  have w₁ := e₁.wb_right
  have p32 : c₁.nreg 50032 = 1 := by rw [r₁ _ (by decide), hE.r32]
  by_cases h0 : c₁.nreg 50210 < c₁.nreg 50032
  · rw [p32] at h0
    have hn : ¬ sideLeft (chainModel C).W e ((chainModel C).param (Qof P) ⟨e, hc⟩)
        (Visibility.rayPt ((chainModel C).pos (Qof P) ⟨e, hc⟩) (dirOf ρ) 1) := fun h => by
      have := b₁.2.2 h; omega
    have hne := ne_of_param_pos ht
    have hdir : dirCode (chainModel C) e ≠ 0 := by
      unfold dirCode; split_ifs with h1 h2
      · omega
      · omega
      · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) hne
    rw [chain_dirCode_small C he] at hdir
    by_cases h5 : c₁.nreg 50201 < c₁.nreg 50085
    · rw [r₁ _ (by decide), r₁ _ (by decide), h01, hE.r85] at h5
      have he13 : e = 1 ∨ e = 3 := by split_ifs at hdir <;> omega
      refine ⟨c₁, _, .seq e₁ (.ifLtN_true (by rwx [p32])
        (.ifLtN_true (by rwx [r₁ _ (by decide), r₁ _ (by decide), h01, hE.r85])
          (.skip w₁))), by omega, by omega, fun h => by omega, fun _ => ?_⟩
      exact wall_none C hP he13 ht ht1 (by rwx [neg_neg])
    · rw [r₁ _ (by decide), r₁ _ (by decide), h01, hE.r85] at h5
      have he5 : e = 5 := by omega
      subst he5
      obtain ⟨c₂, k₂, e₂, hk₂, q⟩ := foundTop_exec (P := P) c₁ w₁
        (by rw [r₁ _ (by decide), hE.r53]) (by rw [r₁ _ (by decide), hE.r81])
        (by rw [r₁ _ (by decide), h02]) hWn
      obtain ⟨q10, q11, q12⟩ := q
      refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by rwx [p32])
        (.ifLtN_false (by rwo [r₁ _ (by decide), r₁ _ (by decide), h01, hE.r85]) e₂)),
        by omega, found_twin (by omega) hhn ?_ q10 q11 q12⟩
      exact twin_left _ _ (hgt_pos_of_param_pos ht) (slit_twin' C).1 (slit_twin' C).2 ht ht1
        (dirOf_cases ρ) hn
  · have hl := b₁.2.1 (by have := b₁.1; rwo [p32] at h0)
    obtain ⟨c₂, k₂, e₂, hk₂, q11, q12, r₂⟩ : ∃ c₂ k₂, Exec P W foundIn c₁ c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50211 = e ∧ c₂.nreg 50212 = hc ∧ c₂.nreg 50210 = c₁.nreg 50210 := by
      unfold foundIn
      exec_block
      refine ⟨rfl, ?_, ?_, by config_simp⟩
      · config_simp; rw [r₁ _ (by decide), h01]
      · config_simp; rw [r₁ _ (by decide), h02]
    have q10 : c₂.nreg 50210 = 1 := by rw [r₂]; have := b₁.1; rwo [p32] at h0
    exact ⟨c₂, _, .seq e₁ (.ifLtN_false h0 e₂), by omega,
      found_here (by omega) ht.le ht1 hhn hl q10 q11 q12⟩

/-- The generic candidate computation `50121 := candIdx` with registers `rs` (`S`) and `rd`
(`2m - S`). -/
theorem candGen_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {r rs rd m S j : ℕ}
    (_hr : r ≠ 50121) (hs : c.nreg rs = S) (hd : c.nreg rd = 2 * m - S) (hrj : c.nreg r = j)
    (hS : S ≤ 2 * m) (_hj : j ≤ 2 * m) (hmW : 2 * m ≤ W) :
    ∃ c' k, Exec P W (.ifLtN r rs (.instr (.addN 50121 r rd)) (.instr (.subN 50121 r rs))) c c' k ∧
      k ≤ 3 ∧ c'.nreg 50121 = candIdx m S j ∧ ∀ r', r' ≠ 50121 → c'.nreg r' = c.nreg r' := by
  unfold candIdx
  by_cases h : j < S
  · refine spec_ifLtN_true (by rwx [hrj, hs]) (spec_instr (Exec.addN hw _ _ _
      (by rwo [hrj, hd])) fun _ => ⟨by omega, ?_, fun r' hr' => by simp [hr']⟩)
    config_simp; rw [hrj, hd, ite_eq_left h]
  · refine spec_ifLtN_false (by rwx [hrj, hs]) (spec_instr (Exec.subN hw _ _ _)
      fun _ => ⟨by omega, ?_, fun r' hr' => by simp [hr']⟩)
    config_simp; rw [hrj, hs, ite_eq_right h]


/-- The block `found5`. -/
theorem found5_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {hc : ℕ}
    (h02 : c.nreg 50202 = hc) (hW : 5 ≤ W) :
    ∃ c' k, Exec P W found5 c c' k ∧ k = 3 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = 5 ∧ c'.nreg 50212 = hc) := by
  unfold found5
  exec_block
  all_goals try omega
  all_goals try (refine ⟨rfl, ?_⟩; config_simp; rw [h02])

/-- The block `foundT`. -/
theorem foundT_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {i hc : ℕ}
    (h121 : c.nreg 50121 = i) (h81 : c.nreg 50081 = 6) (h02 : c.nreg 50202 = hc)
    (hW : i + 6 ≤ W) :
    ∃ c' k, Exec P W foundT c c' k ∧ k = 3 ∧
      (c'.nreg 50210 = 1 ∧ c'.nreg 50211 = i + 6 ∧ c'.nreg 50212 = hc) := by
  unfold foundT
  exec_block
  all_goals try omega
  all_goals try (config_simp; rwo [h121, h81])

/-- The block `foundIn`. -/
theorem foundIn_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W foundIn c c' k ∧ k = 2 ∧ c'.nreg 50211 = c.nreg 50201 ∧
      c'.nreg 50212 = c.nreg 50202 ∧ c'.nreg 50210 = c.nreg 50210 := by
  unfold foundIn
  exec_block
  exact ⟨rfl, by config_simp, by config_simp, by config_simp⟩

/-- **Inside an edge of the tour or the up-slit edge.** -/
theorem intArr_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc ρ : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (h03 : c.nreg 50203 = ρ)
    (hd : c.nreg 10502 = dirCode (chainModel C) e) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (ht1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) (hWn : 2 * C.m + 7 ≤ W) :
    ∃ c' k, Exec P W intArr c c' k ∧ k ≤ 60 ∧ ArrRes P C e hc ρ c' := by
  have hn7 : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hm1 := C.one_le
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁⟩ := intOut_exec (P := P) c hE.wb (by omega) hE.r32
    (by rw [hd]; exact dirCode_le_two _ _)
  rw [hd, h03, interior_iff _ _ (x := ⟨e, hc⟩) ht ht1] at b₁
  have w₁ := e₁.wb_right
  have p32 : c₁.nreg 50032 = 1 := by rw [r₁ _ (by decide), hE.r32]
  have hE₁ : CEnv P W H C c₁ := hE.keep w₁
    (exec_frameB e₁ (B := fun r => r == 50210) (by decide)).2.2.1
    (fun r hr => r₁ r (ne_of_mem_of_not_mem hr (by decide)))
  by_cases h0 : c₁.nreg 50210 < c₁.nreg 50032
  · rw [p32] at h0
    have hn : ¬ sideLeft (chainModel C).W e ((chainModel C).param (Qof P) ⟨e, hc⟩)
        (Visibility.rayPt ((chainModel C).pos (Qof P) ⟨e, hc⟩) (dirOf ρ) 1) := fun h => by
      have := b₁.2.2 h; omega
    have hh := hgt_pos_of_param_pos ht
    -- the tour position of the edge
    have e₂ := Exec.subN (P := P) w₁ 50120 50201 50081
    set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50120 (c₁.nreg 50201 - c₁.nreg 50081) }
      with hc₂
    have hE₂ : CEnv P W H C c₂ := hE₁.step e₂ (by decide)
    have q120 : c₂.nreg 50120 = e - 6 := by
      rw [hc₂]; simp only [upd_same]; rw [r₁ _ (by decide), h01, hE₁.r81]
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, -, k58, k59, k89, k77⟩ := tvIdx_exec c₂ hE₂ (i := e - 6) q120
      (by omega)
    have hE₃ : CEnv P W H C c₃ := hE₂.frame f₃ e₃.wb_right (by decide)
    have w₃ := e₃.wb_right
    have s₃ : c₃.nreg 50202 = hc := by
      rw [f₃.1 _ (by decide), hc₂]; simp only
      rw [upd_other _ _ _ (by decide), r₁ _ (by decide), h02]
    have i₃ : c₃.nreg 50120 = e - 6 := by rw [f₃.1 _ (by decide), q120]
    by_cases hlt : c₃.nreg 50120 < c₃.nreg 50058
    · rw [i₃, k58] at hlt
      set i := e - 6 with hi
      have hS := C.sideS_lt C.sideBeta
      set S := C.sideS C.sideBeta with hSdef
      have hjx : (if i < 2 * C.m - S then S + i else i - (2 * C.m - S)) = (S + i) % (2 * C.m) :=
        (tour_mod hS hlt).symm
      rw [hjx] at k77
      have hjlt := Nat.mod_lt (S + i) (show 0 < 2 * C.m by omega)
      obtain ⟨c₄, k₄, e₄, hk₄, q⟩ : ∃ c₄ k₄, Exec P W
          (block [.subN 50224 50058 50032, .subN 50224 50224 50077]) c₃ c₄ k₄ ∧ k₄ = 2 ∧
          (c₄.nreg 50224 = 2 * C.m - 1 - (S + i) % (2 * C.m) ∧
            ∀ r, r ≠ 50224 → c₄.nreg r = c₃.nreg r) := by
        exec_block
        refine ⟨rfl, ?_, fun r hr => by simp [hr]⟩
        config_simp; rw [k58, hE₃.r32, k77]
      obtain ⟨q224, r₄⟩ := q
      obtain ⟨c₅, k₅, e₅, hk₅, q121, r₅⟩ := candGen_exec (P := P) (r := 50224) (rs := 50059)
        (rd := 50089) (m := C.m) (S := S) (j := 2 * C.m - 1 - (S + i) % (2 * C.m)) c₄
        e₄.wb_right (by decide) (by rw [r₄ _ (by decide), k59]) (by rw [r₄ _ (by decide), k89])
        q224 hS (by omega) (by omega)
      obtain ⟨tw1, tw2, tw3⟩ := tour_twin C hlt
      have htw : tourTwin C i = candIdx C.m S (2 * C.m - 1 - (S + i) % (2 * C.m)) := rfl
      rw [← htw] at q121
      obtain ⟨c₆, k₆, e₆, hk₆, q10, q11, q12⟩ := foundT_exec (P := P) c₅ e₅.wb_right q121
        (by rw [r₅ _ (by decide), r₄ _ (by decide), hE₃.r81])
        (by rw [r₅ _ (by decide), r₄ _ (by decide), s₃]) (by omega)
      refine ⟨c₆, _, .seq e₁ (.ifLtN_true (by rwx [p32]) (.seq e₂ (.seq e₃
        (.ifLtN_true (by rwx [i₃, k58]) (.seq e₄ (.seq e₅ e₆)))))), by omega,
        found_twin (by omega) hhn ?_ q10 q11 q12⟩
      have he' : e = i + 6 := by omega
      rw [he'] at hn ht ht1 ⊢
      exact twin_left _ _ hh tw2 tw3 ht ht1 (dirOf_cases ρ) hn
    · rw [i₃, k58] at hlt
      have he' : e = 2 * C.m + 6 := by omega
      subst he'
      obtain ⟨c₄, k₄, e₄, hk₄, q10, q11, q12⟩ := found5_exec (P := P) c₃ w₃ s₃ (by omega)
      refine ⟨c₄, _, .seq e₁ (.ifLtN_true (by rwx [p32]) (.seq e₂ (.seq e₃
        (.ifLtN_false (by rwx [i₃, k58]) e₄)))), by omega,
        found_twin (by omega) hhn ?_ q10 q11 q12⟩
      exact twin_left _ _ hh (slit_twin C).1 (slit_twin C).2 ht ht1 (dirOf_cases ρ) hn
  · have hl := b₁.2.1 (by have := b₁.1; rwo [p32] at h0)
    obtain ⟨c₂, k₂, e₂, hk₂, q11, q12, q10⟩ := foundIn_exec (P := P) c₁ w₁
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false h0 e₂), by omega,
      found_here (by omega) ht.le ht1 hhn hl ?_ ?_ ?_⟩
    · rw [q10]; have := b₁.1; rwo [p32] at h0
    · rw [q11, r₁ _ (by decide), h01]
    · rw [q12, r₁ _ (by decide), h02]


/-! ## The contract -/

/-- The input condition of `arrivalPos`: that of `leftSec`, a simple host polygon, and the walk
indices within the word bound. -/
def ArrIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  LeftIn P W C c ∧ C.P.Simple ∧ 2 * C.m + 7 ≤ W

/-- The output condition of `arrivalPos`. -/
def ArrOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  ArrRes P C (c.nreg 50201) (c.nreg 50202) (c.nreg 50203) c'

/-- **Contract of `arrivalPos`** (at most `35000` steps): an arrival position of the point of
`(e, h)` for the ray arriving in direction `-dirOf ρ`, as a proper position, or the flag `0` if
there is none (`ArrRes`). -/
theorem arrivalPos_meets : Meets arrivalPos primBands (PrimPre ArrIn) (PrimPost ArrOut)
    (fun _ _ => 35000) := by
  refine prim_meets (K := 34200) (fun _ => id) wr_arrivalPos ?_
  intro P W H C c₀ c _hC hE ⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hP, hWn⟩ hinp
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  have i03 := hinp 50203 (by norm_num) (by norm_num)
  unfold ArrOut
  set e := c₀.nreg 50201 with he_def
  set hc := c₀.nreg 50202 with hc_def
  set σ := c₀.nreg 50203 with hσ_def
  set M := chainModel C with hM
  set x : WPos := ⟨e, hc⟩ with hx
  have hn : M.W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  have hW := hE.hW
  -- the edge direction
  have e₁ := Exec.copyN (P := P) hE.wb 50002 50201
  set c₁ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 50201) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    (by decide)) e₁.wb_right (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    (by rw [hc₁]; simp [i01]) (by omega)
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [f₂.1 r (by sio only [Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]),
      hc₁]
    simp only
    rw [upd_other _ _ _ (by omega), hinp r h1 h2]
  have q01 := g₂ 50201 (by norm_num) (by norm_num)
  have q02 := g₂ 50202 (by norm_num) (by norm_num)
  have q03 := g₂ 50203 (by norm_num) (by norm_num)
  have hd2 : c₂.nreg 10502 ≤ 2 := by rw [d₂]; exact dirCode_le_two _ _
  by_cases hsm : e < 6
  · -- the box block
    have hpos : 0 < M.param (Qof P) x := box_param_pos C hsm hp0 hy
    obtain ⟨c', k, ex, hk, b⟩ := boxArr_exec c₂ hE₂ hP q01 q02 q03 d₂ hsm hpos hp1 hhn hWn
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwx [q01, hE₂.r81]) ex)),
      by omega, b⟩
  have t1 : ¬ c₂.nreg 50201 < c₂.nreg 50081 := by rwx [q01, hE₂.r81]
  by_cases hh0 : hc < 1
  · obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec (hc := hc) c₂ hE₂ hP q01 q03 (by omega) (by omega) hWn
      ((param_eq_zero_iff _ _ _).2 (Or.inl (by sio)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      (by rwx [q02, hE₂.r32]) ex))), by omega, b⟩
  have t2 : ¬ c₂.nreg 50202 < c₂.nreg 50032 := by rwx [q02, hE₂.r32]
  by_cases hd0 : c₂.nreg 10502 < 1
  · have hdir : dirCode M e = 0 := by rwo [← d₂]
    have hhor : (M.wa x.edge).2 = (M.wb x.edge).2 := by
      unfold dirCode at hdir
      split_ifs at hdir with h1 h2
      exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec (hc := hc) c₂ hE₂ hP q01 q03 (by omega) (by omega) hWn
      ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inl hhor)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      (by rwx [hE₂.r32]) ex)))), by omega, b⟩
  have t3 : ¬ c₂.nreg 10502 < c₂.nreg 50032 := by rwx [hE₂.r32]
  -- the start vertex of the edge and the height vertex
  have e₃ := Exec.subN (P := P) w₂ 50120 50201 50081
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50201 - c₂.nreg 50081) }
    with hc₃
  have hE₃ : CEnv P W H C c₃ := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    (by decide)) e₃.wb_right (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    (by rw [hc₃]; simp only [upd_same]; rw [q01, hE₂.r81]) (by omega)
    (dst := 50133) (by norm_num)
  have w₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 (by decide), f₄.1 50032 (by decide), hc₃]
      simp only
      rw [upd_other _ _ _ (by decide), upd_other _ _ _ (by decide), q02, hE₂.r32]
  obtain ⟨q60, q61, r₅⟩ := q
  have w₅ := e₅.wb_right
  have ih : SymPtIn c₅ 50160 (.vtx (hc - 1)) := ⟨q60, q61⟩
  have hhn' : hc ≤ P.n := hhn
  have lh : (SymPt.vtx (hc - 1)).Lt P.n := by show hc - 1 < P.n; omega
  have ia₅ : SymPtIn c₅ 50133 sa := symPtIn_of_eq ia fun j h1 h2 => r₅ j (by omega) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) la lh la ia₅ ih ia₅
  have ia₆ := symPtIn_keep ia₅ f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have ih₆ := symPtIn_keep ih f₆ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lh la lh
    ih₆ ia₆ ih₆
  have w₇ := e₇.wb_right
  have hE₅ : CEnv P W H C c₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) (by decide)).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      (by intro h; subst h; revert hr; decide))
  have hE₆ := hE₅.frame f₆ e₆.wb_right (by decide)
  have hE₇ := hE₆.frame f₇ w₇ (by decide)
  -- registers kept since `c₂`
  have g₇ : ∀ r, r = 50201 ∨ r = 50203 ∨ r = 10502 ∨ r = 50202 → c₇.nreg r = c₂.nreg r := by
    intro r hr
    rw [f₇.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      f₆.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      r₅ r (by omega) (by omega), f₄.1 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide), hc₃]
    simp only
    rw [upd_other _ _ _ (by omega)]
  have b70 : BitIs c₇ 50170 ((SymPt.eval (Qof P) sa).2 < ((SymPt.vtx (hc - 1)).eval (Qof P)).2) :=
    BitIs.keep ⟨b₆, t₆⟩ f₇ (by decide)
  have b71 : BitIs c₇ 50171 (((SymPt.vtx (hc - 1)).eval (Qof P)).2 < (SymPt.eval (Qof P) sa).2) :=
    ⟨b₇, t₇⟩
  rw [va, show e - 6 + 6 = e by omega] at b70 b71
  have hwa : M.wa x.edge = M.W.vtx e := rfl
  have hQ : ((SymPt.vtx (hc - 1)).eval (Qof P)) = (Qof P).vtx (x.hgt - 1) := rfl
  rw [hQ] at b70 b71
  by_cases hlt : c₇.nreg 50170 < c₇.nreg 50032
  · rw [hE₇.r32] at hlt
    have n70 : ¬ (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := fun h => by
      have := b70.2.2 h; omega
    by_cases hlt2 : c₇.nreg 50171 < c₇.nreg 50032
    · rw [hE₇.r32] at hlt2
      have n71 : ¬ ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := fun h => by
        have := b71.2.2 h; omega
      have heq : ((Qof P).vtx (x.hgt - 1)).2 = (M.wa x.edge).2 := by
        rw [hwa]; linarith [not_lt.1 n70, not_lt.1 n71]
      obtain ⟨c', k, ex, hk, b⟩ := vtxArr_exec (hc := hc) c₇ hE₇ hP (by rw [g₇ _ (Or.inl rfl), q01])
        (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03]) (by omega) (by omega) hWn
        ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inr heq)))
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwx [hE₇.r32])
          (.ifLtN_true (by rwx [hE₇.r32]) ex))))))))))), by omega, b⟩
    · have p71 : ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := b71.2.1 (by
        have := b71.1; rwo [hE₇.r32] at hlt2)
      have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
        rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
        · sio [hx] at h'
        · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
            ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
        · rwli [hwa] at h')
      obtain ⟨c', k, ex, hk, b⟩ := intArr_exec c₇ hE₇ (by rw [g₇ _ (Or.inl rfl), q01])
        (by rw [g₇ _ (Or.inr (Or.inr (Or.inr rfl))), q02]) (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03])
        (by rw [g₇ _ (Or.inr (Or.inr (Or.inl rfl))), d₂]) (by omega) (by omega) hpos hp1 hhn hWn
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwx [hE₇.r32])
          (.ifLtN_false hlt2 ex))))))))))), by omega, b⟩
  · have p70 : (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := b70.2.1 (by
      have := b70.1; rwo [hE₇.r32] at hlt)
    have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
      rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
      · sio [hx] at h'
      · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
          ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
      · rwli [hwa] at h')
    obtain ⟨c', k, ex, hk, b⟩ := intArr_exec c₇ hE₇ (by rw [g₇ _ (Or.inl rfl), q01])
      (by rw [g₇ _ (Or.inr (Or.inr (Or.inr rfl))), q02]) (by rw [g₇ _ (Or.inr (Or.inl rfl)), q03])
      (by rw [g₇ _ (Or.inr (Or.inr (Or.inl rfl))), d₂]) (by omega) (by omega) hpos hp1 hhn hWn
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_false hlt ex)))))))))), by omega, b⟩


end

end SweepPrim

end Chazelle.Core
