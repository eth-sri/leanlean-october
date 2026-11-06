module

public import Chazelle.Core.SweepPrimAbs
public import Chazelle.Core.ShootCutBox

/-!
# WP-G, part 40: the point record of a walk position (`ptKey`)

The ray-shooter compares the points of walk positions of a chain model with the origin of the
ray: abscissae and ordinates.  The primitive `ptKey` (calling convention of the sweep primitives,
`SweepPrim.prim_meets`) takes a walk position `x = (e, h)` of `chainModel C` (`50201`, `50202`)
and returns in `50210 …` a **point record** of its point `z`:

* `50210 … 50213`: an abscissa record of `z.1` (`SweepPrim.AbsRec`);
* `50214`, `50215`: an **ordinate record** of `z.2` (`HRec`): kind `0` (`-R`), `2` (`R`), or `1`
  and a vertex of `Q` at the height of `z` (`|z.2| < R`);
* `50216 … 50219`: flag `1` and a symbolic point of `Q` whose point is `z` (for a vertex of the
  chain and a point inside a tour edge), or flag `0` (the box and the slit).

The input may be a vertex of the box (height code `0`), or any position of the walk proper
strictly inside the height range of the box.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sidePt)

@[expose] public section

/-! ## Records -/

/-- **An ordinate record** at `r`: kind `0` (`y = -R`), `2` (`y = R`), or `1` and a vertex of
`Q` at height `y`, `|y| < R`. -/
def HRec (P : Polygon) (c : Config) (r : ℕ) (y R : ℝ) : Prop :=
  (c.nreg r = 0 ∧ y = -R) ∨ (c.nreg r = 2 ∧ y = R) ∨
    (c.nreg r = 1 ∧ |y| < R ∧ c.nreg (r + 1) < P.n ∧ y = ((Qof P).vtx (c.nreg (r + 1))).2)

/-- **A symbolic record** at `r`: flag `1` and a symbolic point of `Q` whose point is `z`. -/
def FRec (P : Polygon) (c : Config) (r : ℕ) (z : Point) : Prop :=
  c.nreg r = 1 → ∃ s : SymPt, SymPtIn c (r + 1) s ∧ s.Lt P.n ∧ s.eval (Qof P) = z

/-- The point record of `z` at `50210`. -/
def PtRec (P : Polygon) (c : Config) (z : Point) (R : ℝ) : Prop :=
  AbsRec P c 50210 z.1 R ∧ HRec P c 50214 z.2 R ∧ FRec P c 50216 z

theorem absRec_copy' {P : Polygon} {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) (h3 : c'.nreg (r' + 3) = c.nreg (r + 3)) :
    AbsRec P c' r' x R := by
  obtain ⟨hR, hk⟩ := h
  refine ⟨hR, ?_⟩
  rcases hk with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
  · exact Or.inl ⟨h0.trans k, hx⟩
  · exact Or.inr (Or.inl ⟨h0.trans k, hx⟩)
  · refine Or.inr (Or.inr ⟨h0.trans k, hx, s, ?_, hl, he⟩)
    have e1 : r' + 1 + 1 = r' + 2 := by omega
    have e2 : r + 1 + 1 = r + 2 := by omega
    have e3 : r' + 1 + 2 = r' + 3 := by omega
    have e4 : r + 1 + 2 = r + 3 := by omega
    exact NFLoc.symPtIn_copy hs h1 (by rwa [e1, e2]) (by rwa [e3, e4])

/-! ## The machine -/

/-- The ordinate kind and the symbolic flag of a box vertex. -/
def hyV (k : ℕ) : Stmt := block [.constN 50214 k, .constN 50216 0]

/-- A vertex of the box on the line of the slit (`0` or `5`). -/
def ptTopV : Stmt := .seq absTop (hyV 2)

/-- A box corner: constant abscissa and ordinate kinds. -/
def hxy (x y : ℕ) : Stmt := block [.constN 50210 x, .constN 50214 y, .constN 50216 0]

/-- The vertices of the box (`e < 6`, code `0`). -/
def ptBoxV : Stmt :=
  .ifLtN 50201 50032 ptTopV
    (.ifLtN 50201 50082 (hxy 0 2)
      (.ifLtN 50201 50083 (hxy 0 0)
        (.ifLtN 50201 50084 (hxy 2 0)
          (.ifLtN 50201 50085 (hxy 2 2) ptTopV))))

/-- A position inside a vertical edge of the box block (`1`, `3`, `5`). -/
def ptBoxS : Stmt :=
  .seq (block [.constN 50214 1, .subN 50215 50202 50032, .constN 50216 0])
    (.ifLtN 50201 50082 (.instr (.constN 50210 0))
      (.ifLtN 50201 50084 (.instr (.constN 50210 2)) absTop))

/-- A vertex of the tour. -/
def ptVtx : Stmt :=
  .seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50211)
    (.seq (block [.constN 50210 1, .copyN 50217 50211, .copyN 50218 50212, .copyN 50219 50213,
        .constN 50216 1, .constN 50214 1])
      (.ifLtN 50211 50032 (.instr (.copyN 50215 50212)) (.instr (.copyN 50215 50213)))))

/-- The ordinate of a position inside a walk edge, and its symbolic flag. -/
def hyI (f : ℕ) : Stmt := block [.constN 50214 1, .subN 50215 50202 50032, .constN 50216 f]

/-- Inside a tour edge. -/
def ptTour : Stmt :=
  .seq absTour (.seq (hyI 1)
    (block (copies [(50217, 50211), (50218, 50212), (50219, 50213)])))

/-- Inside a tour edge or the up-slit edge. -/
def ptInt : Stmt :=
  .seq (block [.subN 50120 50201 50081, .addN 50143 50053 50053])
    (.ifLtN 50120 50143 ptTour (.seq absTop (hyI 0)))

/-- **The primitive `ptKey`.** -/
def ptKey : Stmt :=
  .seq pHead (.ifLtN 50201 50081 (.ifLtN 50202 50032 ptBoxV ptBoxS) (classify .skip ptVtx ptInt))

theorem wr_ptKey : wr Bprim ptKey = true := by decide

/-! ## The box vertices -/

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain}

theorem hyV_exec (c : Config) (hw : WordsBounded W c) (hW : 3 ≤ W) {k : ℕ} (hk : k ≤ 2) :
    ∃ c' k', Exec P W (hyV k) c c' k' ∧ k' = 2 ∧ c'.nreg 50214 = k ∧ c'.nreg 50216 = 0 ∧
      ∀ r, r ≠ 50214 → r ≠ 50216 → c'.nreg r = c.nreg r := by
  unfold hyV
  exec_block
  all_goals first | omega | skip
  refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_⟩
  simp only [upd]; split_ifs <;> first | rfl | omega

theorem abs_top_lt (C : Chain) : |C.top.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set C.top_mem_set).1 C.coordBound_lt_radius

/-- The point of a box vertex. -/
theorem pos_box_vtx (C : Chain) (Q : Polygon) (e : ℕ) :
    (chainModel C).pos Q ⟨e, 0⟩ = (C.sideWalk C.sideBeta).vtx e := by
  rw [pos_eq_sidePt, show (chainModel C).param Q ⟨e, 0⟩ = 0 from rfl,
    Chazelle.Chain.sidePt_zero]; rfl

theorem ptTopV_exec (c : Config) (hE : CEnv P W H C c) :
    ∃ c' k, Exec P W ptTopV c c' k ∧ k ≤ 27 * H.length + 47 ∧
      PtRec P c' (C.top.1, C.radius) C.radius := by
  obtain ⟨c₁, k₁, e₁, hk₁, a₁⟩ := absTop_exec c hE
  obtain ⟨c₂, k₂, e₂, hk₂, y₂, f₂, r₂⟩ := hyV_exec (P := P) c₁ e₁.wb_right (by have := hE.hW; omega)
    (k := 2) (by norm_num)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, absRec_copy' a₁ (r₂ _ (by decide) (by decide))
    (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide)),
    Or.inr (Or.inl ⟨y₂, rfl⟩), fun h => by rw [f₂] at h; exact absurd h (by norm_num)⟩

theorem hxy_exec (c : Config) (hw : WordsBounded W c) (hW : 3 ≤ W) {x y : ℕ} (hx : x = 0 ∨ x = 2)
    (hy : y = 0 ∨ y = 2) {pt : Point} (hR : 0 < C.radius) (px0 : x = 0 → pt.1 = -C.radius)
    (px2 : x = 2 → pt.1 = C.radius) (py0 : y = 0 → pt.2 = -C.radius)
    (py2 : y = 2 → pt.2 = C.radius) :
    ∃ c' k, Exec P W (hxy x y) c c' k ∧ k = 3 ∧ PtRec P c' pt C.radius := by
  obtain ⟨c', k, ex, hk, v0, v4, v6⟩ : ∃ c' k, Exec P W (hxy x y) c c' k ∧ k = 3 ∧
      c'.nreg 50210 = x ∧ c'.nreg 50214 = y ∧ c'.nreg 50216 = 0 := by
    unfold hxy
    exec_block
    all_goals first | omega | skip
    exact ⟨rfl, by config_simp, by config_simp, by config_simp⟩
  refine ⟨c', k, ex, hk, ⟨hR, ?_⟩, ?_, fun h => by rw [v6] at h; exact absurd h (by norm_num)⟩
  · rcases hx with rfl | rfl
    · exact Or.inl ⟨v0, px0 rfl⟩
    · exact Or.inr (Or.inl ⟨v0, px2 rfl⟩)
  · rcases hy with rfl | rfl
    · exact Or.inl ⟨v4, py0 rfl⟩
    · exact Or.inr (Or.inl ⟨v4, py2 rfl⟩)

theorem ptBoxV_exec (c : Config) (hE : CEnv P W H C c) {e : ℕ} (h01 : c.nreg 50201 = e)
    (he : e < 6) :
    ∃ c' k, Exec P W ptBoxV c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ((C.sideWalk C.sideBeta).vtx e) C.radius := by
  have hR := C.radius_pos
  have hW := hE.hW
  have hw := hE.wb
  have W3 : 3 ≤ W := by omega
  unfold ptBoxV
  have v1 := C.sideWalk_vtx_one C.sideBeta
  have v2 := C.sideWalk_vtx_two C.sideBeta
  have v3 := C.sideWalk_vtx_three C.sideBeta
  have v4 := C.sideWalk_vtx_four C.sideBeta
  by_cases h0 : e < 1
  · obtain rfl : e = 0 := by omega
    obtain ⟨c', k, ex, hk, pr⟩ := ptTopV_exec c hE
    exact ⟨c', _, .ifLtN_true (by rw [h01, hE.r32]; omega) ex, by omega, by
      rwa [C.sideWalk_vtx_zero]⟩
  have t0 : ¬ c.nreg 50201 < c.nreg 50032 := by rw [h01, hE.r32]; omega
  by_cases h2 : e < 2
  · obtain rfl : e = 1 := by omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec (P := P) (C := C) c hw W3 (x := 0) (y := 2) (Or.inl rfl)
      (Or.inr rfl) (pt := (C.sideWalk C.sideBeta).vtx 1) hR (fun _ => by rw [v1])
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)) (fun _ => by rw [v1])
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_true (by rw [h01, hE.r82]; omega) ex), by omega, pr⟩
  have t1 : ¬ c.nreg 50201 < c.nreg 50082 := by rw [h01, hE.r82]; omega
  by_cases h3 : e < 3
  · obtain rfl : e = 2 := by omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec (P := P) (C := C) c hw W3 (x := 0) (y := 0) (Or.inl rfl)
      (Or.inl rfl) (pt := (C.sideWalk C.sideBeta).vtx 2) hR (fun _ => by rw [v2])
      (fun h => absurd h (by norm_num)) (fun _ => by rw [v2]) (fun h => absurd h (by norm_num))
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_true (by rw [h01, hE.r83]; omega)
      ex)), by omega, pr⟩
  have t2 : ¬ c.nreg 50201 < c.nreg 50083 := by rw [h01, hE.r83]; omega
  by_cases h4 : e < 4
  · obtain rfl : e = 3 := by omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec (P := P) (C := C) c hw W3 (x := 2) (y := 0) (Or.inr rfl)
      (Or.inl rfl) (pt := (C.sideWalk C.sideBeta).vtx 3) hR (fun h => absurd h (by norm_num))
      (fun _ => by rw [v3]) (fun _ => by rw [v3]) (fun h => absurd h (by norm_num))
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      (by rw [h01, hE.r84]; omega) ex))), by omega, pr⟩
  have t3 : ¬ c.nreg 50201 < c.nreg 50084 := by rw [h01, hE.r84]; omega
  by_cases h5 : e < 5
  · obtain rfl : e = 4 := by omega
    obtain ⟨c', k, ex, hk, pr⟩ := hxy_exec (P := P) (C := C) c hw W3 (x := 2) (y := 2) (Or.inr rfl)
      (Or.inr rfl) (pt := (C.sideWalk C.sideBeta).vtx 4) hR (fun h => absurd h (by norm_num))
      (fun _ => by rw [v4]) (fun h => absurd h (by norm_num)) (fun _ => by rw [v4])
    exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      (.ifLtN_true (by rw [h01, hE.r85]; omega) ex)))), by omega, pr⟩
  have t4 : ¬ c.nreg 50201 < c.nreg 50085 := by rw [h01, hE.r85]; omega
  obtain rfl : e = 5 := by omega
  obtain ⟨c', k, ex, hk, pr⟩ := ptTopV_exec c hE
  exact ⟨c', _, .ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
    (.ifLtN_false t4 ex)))), by omega, by rwa [C.sideWalk_vtx_five]⟩

/-! ## Positions inside a vertical edge of the box block -/

/-- A positive parameter: the point is not a box vertex. -/
theorem box_param_pos' (C : Chain) (Q : Polygon) {e hc : ℕ} (he : e < 6)
    (hp : 0 ≤ (chainModel C).param Q ⟨e, hc⟩)
    (hy : |((chainModel C).pos Q ⟨e, hc⟩).2| < C.radius) :
    0 < (chainModel C).param Q ⟨e, hc⟩ := by
  rcases hp.lt_or_eq with h | h
  · exact h
  · exfalso
    have hv : (chainModel C).pos Q ⟨e, hc⟩ = (chainModel C).W.vtx e := by
      rw [pos_eq_sidePt, ← h, Chazelle.Chain.sidePt_zero]
    rw [hv] at hy
    rcases walk_vtx_box C (q := e) (by omega) with h1 | h1 <;> rw [h1] at hy
    · rw [abs_of_pos C.radius_pos] at hy; exact lt_irrefl _ hy
    · rw [abs_neg, abs_of_pos C.radius_pos] at hy; exact lt_irrefl _ hy

theorem ptBoxS_exec (c : Config) (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he : e < 6) (hc1 : 1 ≤ hc) (hhn : hc ≤ P.n)
    (hp : 0 ≤ (chainModel C).param (Qof P) ⟨e, hc⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨e, hc⟩).2| < C.radius) :
    ∃ c' k, Exec P W ptBoxS c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ((chainModel C).pos (Qof P) ⟨e, hc⟩) C.radius := by
  have hR := C.radius_pos
  have hW := hE.hW
  have hw := hE.wb
  have hpos := box_param_pos' C (Qof P) he hp hy
  have hne := ne_of_param_pos hpos
  -- the ordinate
  have hY : ((chainModel C).pos (Qof P) ⟨e, hc⟩).2 = ((Qof P).vtx (hc - 1)).2 := by
    rw [Model.pos_snd hne]
    obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
    rfl
  obtain ⟨c₁, k₁, e₁, hk₁, o14, o15, o16, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50214 1,
      .subN 50215 50202 50032, .constN 50216 0]) c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 50214 = 1 ∧
      c₁.nreg 50215 = hc - 1 ∧ c₁.nreg 50216 = 0 ∧
      ∀ r, r ≠ 50214 → r ≠ 50215 → r ≠ 50216 → c₁.nreg r = c.nreg r := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, ?_, by config_simp, fun r h1 h2 h3 => ?_⟩
    · config_simp; rw [h02, hE.r32]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50214 ||
    r == 50215 || r == 50216) (by decide)) e₁.wb_right (by decide)
  have q01 : c₁.nreg 50201 = e := by rw [r₁ _ (by decide) (by decide) (by decide), h01]
  have hHR : ∀ c' : Config, (∀ r, 50214 ≤ r → r < 50217 → c'.nreg r = c₁.nreg r) →
      HRec P c' 50214 ((chainModel C).pos (Qof P) ⟨e, hc⟩).2 C.radius ∧
        FRec P c' 50216 ((chainModel C).pos (Qof P) ⟨e, hc⟩) := fun c' hk =>
    ⟨Or.inr (Or.inr ⟨by rw [hk _ le_rfl (by norm_num), o14], hy,
      by rw [hk _ (by norm_num) (by norm_num), o15]; omega,
      by rw [hk _ (by norm_num) (by norm_num), o15, hY]⟩),
     fun h => by rw [hk _ (by norm_num) (by norm_num), o16] at h; exact absurd h (by norm_num)⟩
  obtain ⟨-, b1, -, b3, -, b5, -⟩ := C.sidePt_box C.sideBeta
    ((chainModel C).param (Qof P) ⟨e, hc⟩)
  have hpt : (chainModel C).pos (Qof P) ⟨e, hc⟩ =
      sidePt (C.sideWalk C.sideBeta) e ((chainModel C).param (Qof P) ⟨e, hc⟩) := rfl
  have hnot : e ≠ 0 ∧ e ≠ 2 ∧ e ≠ 4 := by
    refine ⟨fun h => hne ?_, fun h => hne ?_, fun h => hne ?_⟩ <;> subst h <;>
      exact box_horizontal C (by norm_num)
  by_cases h2 : e < 2
  · obtain rfl : e = 1 := by omega
    have e₂ := Exec.constN (P := P) e₁.wb_right 50210 0 (by omega)
    refine ⟨_, _, .seq e₁ (.ifLtN_true (by rw [q01, hE₁.r82]; omega) e₂), by omega,
      ⟨hR, Or.inl ⟨by simp, by rw [hpt, b1]⟩⟩, hHR _ fun r h1 h2 => by simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by omega)]⟩
  by_cases h4 : e < 4
  · obtain rfl : e = 3 := by omega
    have e₂ := Exec.constN (P := P) e₁.wb_right 50210 2 (by omega)
    refine ⟨_, _, .seq e₁ (.ifLtN_false (by rw [q01, hE₁.r82]; omega)
      (.ifLtN_true (by rw [q01, hE₁.r84]; omega) e₂)), by omega,
      ⟨hR, Or.inr (Or.inl ⟨by simp, by rw [hpt, b3]⟩)⟩, hHR _ fun r h1 h2 => by simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by omega)]⟩
  obtain rfl : e = 5 := by omega
  obtain ⟨c₂, k₂, e₂, hk₂, a₂⟩ := absTop_exec c₁ hE₁
  have f₂ := exec_frameB e₂ (B := fun r => Btv 50211 r || r == 50120 || r == 50210)
    (by decide)
  refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by rw [q01, hE₁.r82]; omega)
    (.ifLtN_false (by rw [q01, hE₁.r84]; omega) e₂)), by omega, by rwa [hpt, b5],
    hHR _ fun r h1 h2 => f₂.1 r (by interval_cases r <;> decide)⟩

/-! ## Tour vertices -/

/-- The height index of a symbolic point. -/
def hIdx : SymPt → ℕ
  | .vtx k => k
  | .onEdge _ h => h

theorem hIdx_lt {n : ℕ} {s : SymPt} (h : s.Lt n) : hIdx s < n := by
  cases s with
  | vtx k => exact h
  | onEdge e h' => exact h.2

theorem hIdx_snd (Q : Polygon) (s : SymPt) : (s.eval Q).2 = (Q.vtx (hIdx s)).2 := by
  cases s <;> rfl

theorem ptVtx_exec (c : Config) (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) :
    ∃ c' k, Exec P W ptVtx c c' k ∧ k ≤ 27 * H.length + 60 ∧
      PtRec P c' ((chainModel C).pos (Qof P) ⟨e, hc⟩) C.radius ∧ c'.nreg 50216 = 1 := by
  have hW := hE.hW
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50081
  have hE₁ : CEnv P W H C _ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    (by simp [h01, hE.r81]) (by omega) (dst := 50211) (by norm_num)
  have hv : (chainModel C).pos (Qof P) ⟨e, hc⟩ = (chainModel C).W.vtx (e - 6 + 6) := by
    rw [pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero, show e - 6 + 6 = e by omega]
  have hmem : (chainModel C).W.vtx (e - 6 + 6) ∈ C.set := by
    rw [walk_vtx_tour C (by omega)]; exact C.vertex_mem_set (C.sideIdx_le _ _)
  have hb := C.abs_le_coordBound_of_mem_set hmem
  have hlt := C.coordBound_lt_radius
  have s32 : c₂.nreg 50032 = 1 := hE₂.r32
  obtain ⟨c₃, k₃, e₃, hk₃, q10, q17, q18, q19, q16, q14, r₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.constN 50210 1, .copyN 50217 50211, .copyN 50218 50212, .copyN 50219 50213,
        .constN 50216 1, .constN 50214 1]) c₂ c₃ k₃ ∧ k₃ = 6 ∧ c₃.nreg 50210 = 1 ∧
      c₃.nreg 50217 = c₂.nreg 50211 ∧ c₃.nreg 50218 = c₂.nreg 50212 ∧
      c₃.nreg 50219 = c₂.nreg 50213 ∧ c₃.nreg 50216 = 1 ∧ c₃.nreg 50214 = 1 ∧
      ∀ r, r ≠ 50210 → r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → r ≠ 50216 → r ≠ 50214 →
        c₃.nreg r = c₂.nreg r := by
    have hw₂ := e₂.wb_right
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, fun r h1 h2 h3 h4 h5 h6 => ?_⟩
    simp only [upd]; split_ifs <;> first | rfl | omega
  have g : ∀ r, 50211 ≤ r → r < 50214 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    r₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have isp₃ : SymPtIn c₃ 50211 sp := symPtIn_of_eq isp fun j h1 h2 => g j h1 h2
  have fsp₃ : SymPtIn c₃ 50217 sp := NFLoc.symPtIn_copy isp q17 q18 q19
  have c32 : c₃.nreg 50032 = 1 := by rw [r₃ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), s32]
  have hw₃ := e₃.wb_right
  -- the height index
  obtain ⟨c₄, k₄, e₄, hk₄, q15, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50211 50032
      (.instr (.copyN 50215 50212)) (.instr (.copyN 50215 50213))) c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 50215 = hIdx sp ∧ ∀ r, r ≠ 50215 → c₄.nreg r = c₃.nreg r := by
    cases sp with
    | vtx k =>
      obtain ⟨i0, i1⟩ := isp₃
      exact ⟨_, _, .ifLtN_true (by rw [i0, c32]; omega) (Exec.copyN hw₃ _ _), by norm_num,
        by simp [i1, hIdx], fun r hr => by simp [hr]⟩
    | onEdge e' h' =>
      obtain ⟨i0, i1, i2⟩ := isp₃
      exact ⟨_, _, .ifLtN_false (by rw [i0, c32]; omega) (Exec.copyN hw₃ _ _), by norm_num,
        by simp [i2, hIdx], fun r hr => by simp [hr]⟩
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ⟨⟨C.radius_pos, Or.inr (Or.inr
    ⟨by rw [r₄ _ (by decide), q10], by rw [hv]; exact lt_of_le_of_lt hb.1 hlt, sp,
      symPtIn_of_eq isp₃ fun j h1 h2 => r₄ j (by omega), lsp, by rw [vsp, hv]⟩)⟩,
    Or.inr (Or.inr ⟨by rw [r₄ _ (by decide), q14], by rw [hv]; exact lt_of_le_of_lt hb.2 hlt,
      by rw [q15]; exact hIdx_lt lsp, by rw [q15, hv, ← vsp, hIdx_snd]⟩),
    fun _ => ⟨sp, symPtIn_of_eq fsp₃ fun j h1 h2 => r₄ j (by omega), lsp, by rw [vsp, hv]⟩⟩,
    by rw [r₄ _ (by decide), q16]⟩

/-! ## Positions inside a tour edge or the up-slit edge -/

theorem hyI_exec (c : Config) (hw : WordsBounded W c) (hW : 3 ≤ W) (h32 : c.nreg 50032 = 1)
    {f : ℕ} (hf : f ≤ 1) :
    ∃ c' k, Exec P W (hyI f) c c' k ∧ k = 3 ∧ c'.nreg 50214 = 1 ∧
      c'.nreg 50215 = c.nreg 50202 - 1 ∧ c'.nreg 50216 = f ∧
      ∀ r, r ≠ 50214 → r ≠ 50215 → r ≠ 50216 → c'.nreg r = c.nreg r := by
  unfold hyI
  exec_block
  all_goals first | omega | skip
  refine ⟨rfl, by config_simp, ?_, by config_simp, fun r h1 h2 h3 => ?_⟩
  · config_simp; rw [h32]
  · simp only [upd]; split_ifs <;> first | rfl | omega

/-- **The symbolic point inside a tour edge.** -/
theorem absTour_exec' (c : Config) (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {i hc : ℕ}
    (h20 : c.nreg 50120 = i) (h02 : c.nreg 50202 = hc) (hi : i < 2 * C.m)
    (ht : 0 < (chainModel C).param (Qof P) ⟨i + 6, hc⟩) (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absTour c c' k ∧ k ≤ 60 * H.length + 150 ∧ c'.nreg 50210 = 1 ∧
      c'.nreg 50202 = hc ∧ c'.nreg 50032 = 1 ∧ ∃ E, E < P.n ∧
        SymPtIn c' 50211 (.onEdge E (hc - 1)) ∧
        (SymPt.onEdge E (hc - 1)).eval (Qof P) = (chainModel C).pos (Qof P) ⟨i + 6, hc⟩ := by
  have hW := hE.hW
  have hNn := hE.n_eq
  have hNW := hE.NW
  have hmN := C.m_lt
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c hE (i := i) h20
    hi.le (dst := 50130) (by norm_num)
  have w₂ := e₂.wb_right
  have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
    (by rw [f₂.1 _ (by decide), h20, hE₂.r32]; omega)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50120 + c₂.nreg 50032) }
    with hc₃
  have hE₃ : CEnv P W H C c₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
    (by rw [hc₃]; simp [f₂.1 _ (by decide : Btv 50130 50120 = false) ▸ h20, hE₂.r32])
    (by omega) (dst := 50136) (by norm_num)
  have i₁' : SymPtIn c₄ 50130 s₁ := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
    rw [hc₃]; simp [show j ≠ 50120 by omega]) f₄
    (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right (by omega)
    hE₄.r32 i₁' i₂ l₁ l₂
  have q02 : c₅.nreg 50202 = hc := by
    rw [r₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), hc₃]
    simp only [Config.nreg_mk]
    rw [upd_other _ _ _ (by decide), f₂.1 _ (by decide), h02]
  have q32 : c₅.nreg 50032 = 1 := by
    rw [r₅ _ (by decide) (by decide) (by decide), hE₄.r32]
  obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hi x₁ x₂ l₁ l₂ v₁ v₂ (hc := hc) ht
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨i + 6, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
      (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 (.onEdge (hostEdgeIdx P.n s₁ s₂) (hc - 1)) ∧
        c₆.nreg 50202 = hc ∧ c₆.nreg 50032 = 1) := by
    unfold outE
    have hw₅ := e₅.wb_right
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, ⟨by config_simp, by config_simp; exact v₅, ?_⟩, ?_, ?_⟩
    · config_simp; rw [q02, q32]
    · config_simp; exact q02
    · config_simp; exact q32
  obtain ⟨q10, q11, q02', q32'⟩ := q
  -- the ordinate of the point
  have hne := ne_of_param_pos ht
  have hY : ((chainModel C).pos (Qof P) ⟨i + 6, hc⟩).2 = ((Qof P).vtx (hc - 1)).2 := by
    rw [Model.pos_snd hne]
    obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
    rfl
  refine ⟨c₆, _, .seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))), by omega, q10, q02', q32', _, hEi,
    q11, ?_⟩
  ext
  · exact hx.symm
  · rw [hY]; rfl

theorem ptInt_exec (c : Config) (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ}
    (h01 : c.nreg 50201 = e) (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param (Qof P) ⟨e, hc⟩) (ht1 : (chainModel C).param (Qof P) ⟨e, hc⟩ < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W ptInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      PtRec P c' ((chainModel C).pos (Qof P) ⟨e, hc⟩) C.radius ∧
      (e < 2 * C.m + 6 → c'.nreg 50216 = 1) := by
  have hW := hE.hW
  have hR := C.radius_pos
  have hNW := hE.NW
  have hNn := hE.n_eq
  have hmN := C.m_lt
  have hne := ne_of_param_pos ht
  have hc1 : 1 ≤ hc := by
    rcases Nat.eq_zero_or_pos hc with rfl | h
    · exact absurd (show (chainModel C).param (Qof P) ⟨e, 0⟩ = 0 from rfl) (ne_of_gt ht)
    · exact h
  have hY : ((chainModel C).pos (Qof P) ⟨e, hc⟩).2 = ((Qof P).vtx (hc - 1)).2 := by
    rw [Model.pos_snd hne]
    obtain ⟨h', rfl⟩ : ∃ h', hc = h' + 1 := ⟨hc - 1, by omega⟩
    rfl
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    have hw := hE.wb
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; rw [h01, hE.r81], by config_simp; rw [hE.r53]; ring,
        fun r h1 h2 => by simp [h1, h2]⟩
  obtain ⟨q20, q43, r₁⟩ := q
  have hE₁ : CEnv P W H C c₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) (by decide)).2.2.1
    (fun r hr => r₁ r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide)))
  have q02 : c₁.nreg 50202 = hc := by rw [r₁ _ (by decide) (by decide), h02]
  by_cases hlt : e - 6 < 2 * C.m
  · obtain ⟨c₂, k₂, e₂, hk₂, o10, o02, o32, E, hE', o11, hv⟩ := absTour_exec' c₁ hE₁ hreg
      (i := e - 6) q20 q02 hlt (by rwa [show e - 6 + 6 = e by omega]) hhn
    rw [show e - 6 + 6 = e by omega] at hv
    obtain ⟨c₃, k₃, e₃, hk₃, y14, y15, y16, r₃⟩ := hyI_exec (P := P) c₂ e₂.wb_right (by omega)
      o32 (f := 1) le_rfl
    have o11' : SymPtIn c₃ 50211 (.onEdge E (hc - 1)) :=
      symPtIn_of_eq o11 fun j h1 h2 => r₃ j (by omega) (by omega) (by omega)
    obtain ⟨c₄, e₄, v₄, f₄⟩ := copies_exec (P := P) [(50217, 50211), (50218, 50212),
      (50219, 50213)] c₃ e₃.wb_right (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₄
    obtain ⟨v17, v18, v19⟩ := v₄
    have k₄ : ∀ r, r ≠ 50217 → r ≠ 50218 → r ≠ 50219 → c₄.nreg r = c₃.nreg r := fun r h1 h2 h3 =>
      f₄.1 r (by simp [h1, h2, h3])
    have hmem : (chainModel C).pos (Qof P) ⟨e, hc⟩ ∈ C.set := by
      have hei : e = e - 6 + 6 := by omega
      rw [pos_eq_sidePt]
      rw [hei] at ht ht1 ⊢
      exact C.sideWalk_tour_pt_mem _ hlt.le (fun h => absurd h (by omega)) ht.le ht1
    have hb := C.abs_le_coordBound_of_mem_set hmem
    have hl := C.coordBound_lt_radius
    have o11'' : SymPtIn c₄ 50211 (.onEdge E (hc - 1)) :=
      symPtIn_of_eq o11' fun j h1 h2 => k₄ j (by omega) (by omega) (by omega)
    have lt : (SymPt.onEdge E (hc - 1)).Lt P.n := ⟨hE', by omega⟩
    refine ⟨c₄, _, .seq e₁ (.ifLtN_true (by rwa [q20, q43]) (.seq e₂ (.seq e₃ e₄))),
      by simp only [List.length_cons, List.length_nil]; omega,
      ⟨⟨hR, Or.inr (Or.inr ⟨by rw [k₄ _ (by decide) (by decide) (by decide),
        r₃ _ (by decide) (by decide) (by decide), o10], lt_of_le_of_lt hb.1 hl, _, o11'', lt,
        by rw [hv]⟩)⟩,
      Or.inr (Or.inr ⟨by rw [k₄ _ (by decide) (by decide) (by decide), y14],
        lt_of_le_of_lt hb.2 hl, by rw [k₄ _ (by decide) (by decide) (by decide), y15, o02]; omega,
        by rw [k₄ _ (by decide) (by decide) (by decide), y15, o02, hY]⟩),
      fun _ => ⟨_, NFLoc.symPtIn_copy o11' v17 v18 v19, lt, hv⟩⟩,
      fun _ => by rw [k₄ _ (by decide) (by decide) (by decide), y16]⟩
  · have he' : e = 2 * C.m + 6 := by omega
    obtain ⟨c₂, k₂, e₂, hk₂, hrec⟩ := absTop_exec c₁ hE₁
    have f₂ := exec_frameB e₂ (B := fun r => Btv 50211 r || r == 50120 || r == 50210)
      (by decide)
    have o02 : c₂.nreg 50202 = hc := by rw [f₂.1 _ (by decide), q02]
    have o32 : c₂.nreg 50032 = 1 := by rw [f₂.1 _ (by decide), hE₁.r32]
    obtain ⟨c₃, k₃, e₃, hk₃, y14, y15, y16, r₃⟩ := hyI_exec (P := P) c₂ e₂.wb_right (by omega)
      o32 (f := 0) (by norm_num)
    -- the point on the up-slit edge
    subst he'
    obtain ⟨-, -, -, -, -, -, e6⟩ := C.sidePt_box C.sideBeta
      ((chainModel C).param (Qof P) ⟨2 * C.m + 6, hc⟩)
    have hpt : (chainModel C).pos (Qof P) ⟨2 * C.m + 6, hc⟩ =
        (C.top.1, C.top.2 + (chainModel C).param (Qof P) ⟨2 * C.m + 6, hc⟩ *
          (C.radius - C.top.2)) := by
      rwa [pos_eq_sidePt]
    have htop := C.top_snd_lt_radius
    have htop' := (abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2).1
    have hl := C.coordBound_lt_radius
    have hy : |((chainModel C).pos (Qof P) ⟨2 * C.m + 6, hc⟩).2| < C.radius := by
      rw [hpt, abs_lt]
      constructor <;> nlinarith
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rwa [q20, q43]) (.seq e₂ e₃)),
      by omega, ⟨?_, Or.inr (Or.inr ⟨y14, hy, by rw [y15, o02]; omega, by rw [y15, o02, hY]⟩),
      fun h => by rw [y16] at h; exact absurd h (by norm_num)⟩, fun h => absurd h (by omega)⟩
    rw [hpt]
    exact absRec_copy' hrec (r₃ _ (by decide) (by decide) (by decide))
      (r₃ _ (by decide) (by decide) (by decide)) (r₃ _ (by decide) (by decide) (by decide))
      (r₃ _ (by decide) (by decide) (by decide))

/-! ## The contract -/

/-- The input condition of `ptKey`: a position of the walk proper, a box vertex or strictly inside
the height range of the box, and a regular host. -/
def PtIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 50201, c.nreg 50202⟩ ∧
    (c.nreg 50202 = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩).2| < C.radius) ∧
    ∀ H', HostAt c.nmem (c.nmem (c.nreg 50200)) H' → HostRegular P.n H'

/-- The output condition of `ptKey`. -/
def PtOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  PtRec P c' ((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩) C.radius ∧
    (6 ≤ c.nreg 50201 → (c.nreg 50201 < 2 * C.m + 6 ∨
      (chainModel C).param (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩ = 0) → c'.nreg 50216 = 1)

/-- **Contract of `ptKey`** (at most `15800` steps). -/
theorem ptKey_meets : Meets ptKey primBands (PrimPre PtIn) (PrimPost PtOut)
    (fun _ _ => 15800) := by
  refine prim_meets (K := 15000) (fun r h => h) wr_ptKey ?_
  intro P W H C c₀ c hC hE ⟨hen, ⟨hp0, hp1, hhn⟩, hy, hreg⟩ hinp
  have hregH := hreg H hC.1
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  set e := c₀.nreg 50201
  set hc := c₀.nreg 50202
  by_cases h6 : e < 6
  · have t0 : c.nreg 50201 < c.nreg 50081 := by rwa [i01, hE.r81]
    by_cases hh : hc < 1
    · have hc0 : hc = 0 := by omega
      obtain ⟨c', k, ex, hk, pr⟩ := ptBoxV_exec c hE i01 h6
      refine ⟨c', _, .ifLtN_true t0 (.ifLtN_true (by rwa [i02, hE.r32]) ex), by omega, ?_⟩
      refine ⟨?_, fun h => absurd h (by omega)⟩
      show PtRec P c' ((chainModel C).pos (Qof P) ⟨e, hc⟩) C.radius
      rwa [hc0, pos_box_vtx]
    · have hy' : |((chainModel C).pos (Qof P) ⟨e, hc⟩).2| < C.radius := by
        rcases hy with h | h
        · exact absurd h (by omega)
        · exact h
      obtain ⟨c', k, ex, hk, pr⟩ := ptBoxS_exec c hE i01 i02 h6 (by omega) hhn hp0 hy'
      exact ⟨c', _, .ifLtN_true t0 (.ifLtN_false (by rwa [i02, hE.r32]) ex), by omega,
        pr, fun h => absurd h (by omega)⟩
  · have t0 : ¬ c.nreg 50201 < c.nreg 50081 := by rwa [i01, hE.r81]
    have hen' : e < 2 * C.m + 7 := by rwa [← hn]
    -- the ordinate is inside the box
    have hy' : |((chainModel C).pos (Qof P) ⟨e, hc⟩).2| < C.radius := by
      rcases hy with h | h
      · have hv : (chainModel C).pos (Qof P) ⟨e, hc⟩ = (chainModel C).W.vtx (e - 6 + 6) := by
          show (chainModel C).pos (Qof P) ⟨e, hc⟩ = _
          rw [show hc = 0 from h, pos_box_vtx, show e - 6 + 6 = e by omega]; rfl
        have hmem : (chainModel C).W.vtx (e - 6 + 6) ∈ C.set := by
          rw [walk_vtx_tour C (by omega)]; exact C.vertex_mem_set (C.sideIdx_le _ _)
        rw [hv]
        exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).2 C.coordBound_lt_radius
      · exact h
    obtain ⟨c', k, ex, hk, pr⟩ := classify_exec (Kb := 0) (Kv := 27 * H.length + 60)
      (Ki := 60 * H.length + 200)
      (R := fun c' => PtRec P c' ((chainModel C).pos (Qof P) ⟨e, hc⟩) C.radius ∧
        (6 ≤ e → (e < 2 * C.m + 6 ∨ (chainModel C).param (Qof P) ⟨e, hc⟩ = 0) →
          c'.nreg 50216 = 1)) c₀ c hE hinp hen
      hp0 hp1 hhn hy'
      (fun _ _ _ _ he _ => absurd he h6)
      (fun c₂ hE₂ g₂ h6' hpar => by
        obtain ⟨c', k, ex, hk, pr, fl⟩ := ptVtx_exec c₂ hE₂ (g₂ 50201 (by norm_num) (by norm_num))
          h6' hen' hpar
        exact ⟨c', k, ex, hk, pr, fun _ _ => fl⟩)
      (fun c₂ hE₂ g₂ _ h6' hpos => by
        obtain ⟨c', k, ex, hk, pr, fl⟩ := ptInt_exec c₂ hE₂ hregH
          (g₂ 50201 (by norm_num) (by norm_num)) (g₂ 50202 (by norm_num) (by norm_num)) h6' hen'
          hpos hp1 hhn
        refine ⟨c', k, ex, hk, pr, fun _ h => fl ?_⟩
        rcases h with h | h
        · exact h
        · exact absurd h (ne_of_gt hpos))
    exact ⟨c', _, .ifLtN_false t0 ex, by omega, pr⟩

end

end ShootCut

end Chazelle.Core
