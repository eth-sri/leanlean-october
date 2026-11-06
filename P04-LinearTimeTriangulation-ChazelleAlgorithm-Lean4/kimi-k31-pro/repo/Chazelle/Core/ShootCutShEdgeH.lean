module

public import Chazelle.Core.ShootCutShEdgeR
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-G, part 45: the segment machine `edgeH`

The decision tree of `edgeSel` on the RAM (see `ShootCutShEdgeR`).  `eqTree`: the ends at one
height; `neTree`: the ends at different heights, with `midTree` for the origin strictly between.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The ends at one height. -/
def eqTree : Stmt :=
  .ifLtN 140312 K1 cand0
    (.seq (aheadT 140270 140314) (.ifLtN 140314 K1 cand0
      (.seq (nearT 140316) (.ifLtN 140316 K1 (candFrom 140270 140263 140264)
        (candFrom 140281 140265 140266)))))

/-- The point at the height of the origin, strictly inside the segment. -/
def xTree : Stmt :=
  .seq (.instr (.addN 140304 140236 K1)) (.seq (ptLoad 140262 140304 140292)
    (.seq (aheadT 140292 140314) (.ifLtN 140314 K1 cand0 (candFrom 140292 140262 140304))))

/-- The origin neither at the height of `U` nor at the one of `V`. -/
def midTree : Stmt :=
  .seq (hLess 140274 140234 140317) (.seq (hLess 140234 140285 140318)
    (.seq (hLess 140285 140234 140319) (.seq (hLess 140234 140274 140320)
      (.ifLtN 140317 K1 (.ifLtN 140319 K1 cand0 (.ifLtN 140320 K1 cand0 xTree))
        (.ifLtN 140318 K1 (.ifLtN 140319 K1 cand0 (.ifLtN 140320 K1 cand0 xTree)) xTree)))))

/-- The ends at different heights. -/
def neTree : Stmt :=
  .ifLtN 140312 K1
    (.ifLtN 140313 K1 midTree
      (.seq (aheadT 140281 140314) (.ifLtN 140314 K1 cand0 (candFrom 140281 140265 140266))))
    (.seq (aheadT 140270 140314) (.ifLtN 140314 K1 cand0 (candFrom 140270 140263 140264)))

/-- **The segment machine.** -/
def edgeH : Stmt :=
  .seq (ptLoad 140263 140264 140270) (.seq (ptLoad 140265 140266 140281)
    (.seq (hEq 140274 140285 140311) (.seq (hEq 140234 140274 140312)
      (.seq (hEq 140234 140285 140313) (.ifLtN 140311 K1 neTree eqTree)))))

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## Frames -/

theorem PtRecB.keep {c c' : Config} {B : ℕ} {q : Point} {R : ℝ} (h : PtRecB P c B q R)
    (hk : ∀ r, B ≤ r → r < B + 11 → c'.nreg r = c.nreg r) : PtRecB P c' B q R := by
  obtain ⟨ax, hy, fr⟩ := h
  refine ⟨absRec_copy' ax (hk _ le_rfl (by omega)) (hk _ (by omega) (by omega))
    (hk _ (by omega) (by omega)) (hk _ (by omega) (by omega)),
    hy.copy (hk _ (by omega) (by omega)) (by rw [hk _ (by omega) (by omega)])
      (by rw [hk _ (by omega) (by omega)]), fun h7 => ?_⟩
  obtain ⟨s, hs, hl, hv⟩ := fr (by rwx [← hk _ (by omega) (by omega)])
  exact ⟨s, NFLoc.symPtIn_copy hs (hk _ (by omega) (by omega)) (by rw [hk _ (by omega) (by omega)])
    (by rw [hk _ (by omega) (by omega)]), hl, hv⟩

theorem Bkb_bedge {dst : ℕ} (hd : Bedge dst = true) (r : ℕ) (h : Bkb dst r = true) :
    Bedge r = true := by
  simp [Bkb, Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | rfl
  · sio [Bedge, Bprim]
  · exact hd

theorem Bld_bedge {B : ℕ} (hB : 140262 ≤ B ∧ B + 11 ≤ 140330) (r : ℕ) (h : Bld B r = true) :
    Bedge r = true := by
  simp [Bld, Bool.or_eq_true, decide_eq_true_eq] at h
  simp [Bedge, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inr (by omega)

/-! ## The ends at one height -/

/-- The walk position in `e`, `h` has the point `q`, is proper, on a walk edge. -/
def PosAt (P : Polygon) (C : Chain) (c : Config) (e h : ℕ) (q : Point) : Prop :=
  (chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ = q ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩ ∧ c.nreg e < (chainModel C).W.n

theorem PosAt.keep {c c' : Config} {e h : ℕ} {q : Point} (hp : PosAt P C c e h q)
    (he : c'.nreg e = c.nreg e) (hh : c'.nreg h = c.nreg h) : PosAt P C c' e h q := by
  unfold PosAt at *; rwx [he, hh]

theorem ne_of_seg {U V z X : Point} (hz : z ∉ seg U V) (hX : X ∈ seg U V) (hy : z.2 = X.2) :
    X.1 ≠ z.1 := fun h => hz (by
  have : z = X := Prod.ext h.symm hy
  rwx [this])

theorem eqTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} (rU : PtRecB P c 140270 pU C.radius) (rV : PtRecB P c 140281 pV C.radius)
    (pU' : PosAt P C c 140263 140264 pU) (pV' : PosAt P C c 140265 140266 pV)
    (hUV : pU.2 = pV.2) (b12 : BitIs c 140312 (z.2 = pU.2)) (hz : z ∉ seg pU pV) :
    ∃ c' k, Exec P W eqTree c c' k ∧ k ≤ 600 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; ufo hostWords at this
  have hc := edge_cand (U := pU) (V := pV) (X := pU) E.hσ hz (fun h => by
    exfalso; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)
  dsimp at hc
  unfold eqTree
  by_cases t0 : c.nreg 140312 < c.nreg K1
  · have hzU : ¬ z.2 = pU.2 := fun h => by have := b12.2.2 h; rwo [E.k1] at t0
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_right hzU]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) (z := z) (σ := σ) c hw
      (hc.2 (by norm_num))
    exact ⟨c', _, .ifLtN_true t0 ex, by omega, ca, f⟩
  have hzU : z.2 = pU.2 := b12.2.1 (by have := b12.1; rwo [E.k1] at t0)
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec (P := P) c hw E (A := 140270) (dst := 140314)
    (by norm_num) (by norm_num) rU.1 (ne_of_seg hz (U_mem_seg pU pV) hzU)
  have E₁ := E.frame f₁ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140314 r
    · rfl
    · exact absurd (Bkb_bedge (by decide) r h) (by rwd [this])
  have kp : ∀ r, 140260 ≤ r → r < 140300 → r ≠ 140314 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    f₁.1 r (by sio [Bkb, Bk])
  have rU₁ := rU.keep fun r h1 h2 => kp r (by omega) (by omega) (by omega)
  have rV₁ := rV.keep fun r h1 h2 => kp r (by omega) (by omega) (by omega)
  have pU₁ := pU'.keep (kp _ (by norm_num) (by norm_num) (by norm_num))
    (kp _ (by norm_num) (by norm_num) (by norm_num))
  have pV₁ := pV'.keep (kp _ (by norm_num) (by norm_num) (by norm_num))
    (kp _ (by norm_num) (by norm_num) (by norm_num))
  have fe₁ : FrameB Bedge c c₁ := FrameB.wk f₁ (Bkb_bedge (by decide))
  have w₁ := e₁.wb_right
  have t0'  := t0
  by_cases t1 : c₁.nreg 140314 < c₁.nreg K1
  · have hA : ¬ 0 < σ * (pU.1 - z.1) := fun h => by
      have := a₁.2.2 h; rwo [E₁.k1] at t1
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_left hzU, ite_eq_right hA]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) (z := z) (σ := σ) c₁ w₁
      (hc.2 (by norm_num))
    exact ⟨c', _, .ifLtN_false t0' (.seq e₁ (.ifLtN_true t1 ex)), by omega, ca, fe₁.trans f⟩
  have hA : 0 < σ * (pU.1 - z.1) := a₁.2.1 (by have := a₁.1; rwo [E₁.k1] at t1)
  obtain ⟨c₂, k₂, e₂, hk₂, a₂, f₂⟩ := nearT_exec (P := P) c₁ w₁ E₁ (dst := 140316) (by norm_num)
    rU₁.1 rV₁.1
  have E₂ := E₁.frame f₂ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140316 r
    · rfl
    · exact absurd (Bkb_bedge (by decide) r h) (by rwd [this])
  have kp₂ : ∀ r, 140260 ≤ r → r < 140300 → r ≠ 140316 → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => f₂.1 r (by sio [Bkb, Bk])
  have rU₂ := rU₁.keep fun r h1 h2 => kp₂ r (by omega) (by omega) (by omega)
  have rV₂ := rV₁.keep fun r h1 h2 => kp₂ r (by omega) (by omega) (by omega)
  have pU₂ := pU₁.keep (kp₂ _ (by norm_num) (by norm_num) (by norm_num))
    (kp₂ _ (by norm_num) (by norm_num) (by norm_num))
  have pV₂ := pV₁.keep (kp₂ _ (by norm_num) (by norm_num) (by norm_num))
    (kp₂ _ (by norm_num) (by norm_num) (by norm_num))
  have fe₂ : FrameB Bedge c₁ c₂ := FrameB.wk f₂ (Bkb_bedge (by decide))
  have w₂ := e₂.wb_right
  have t1'  := t1
  by_cases t2 : c₂.nreg 140316 < c₂.nreg K1
  · have hn : σ * pU.1 ≤ σ * pV.1 := by
      by_contra h; have := a₂.2.2 h; rwo [E₂.k1] at t2
    rw [show edgeSel _ _ _ _ _ _ _ _ = 1 by unfold edgeSel; rw [ite_eq_left hUV,
      ite_eq_left hzU, ite_eq_left hA, ite_eq_left hn]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₂ w₂
      (by omega) (A := 140270) (e := 140263) (h := 140264) (by norm_num) (by norm_num)
      (by norm_num) rU₂.1 (hc.1 rfl) pU₂.2.1 pU₂.2.2 (by rw [pU₂.1, hzU])
    exact ⟨c', _, .ifLtN_false t0' (.seq e₁ (.ifLtN_false t1' (.seq e₂ (.ifLtN_true t2 ex)))),
      by omega, ca, (fe₁.trans fe₂).trans f⟩
  have hn : ¬ σ * pU.1 ≤ σ * pV.1 := a₂.2.1 (by have := a₂.1; rwo [E₂.k1] at t2)
  rw [show edgeSel _ _ _ _ _ _ _ _ = 2 by unfold edgeSel; rw [ite_eq_left hUV,
    ite_eq_left hzU, ite_eq_left hA, ite_eq_right hn]] at hc
  obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₂ w₂
    (by omega) (A := 140281) (e := 140265) (h := 140266) (by norm_num) (by norm_num)
    (by norm_num) rV₂.1 (hc.1 rfl) pV₂.2.1 pV₂.2.2 (by rw [pV₂.1, hzU, hUV])
  exact ⟨c', _, .ifLtN_false t0' (.seq e₁ (.ifLtN_false t1' (.seq e₂ (.ifLtN_false t2 ex)))),
    by omega, ca, (fe₁.trans fe₂).trans f⟩

/-! ## The point at the height of the origin -/

/-- A step framed by `Bkb dst` keeps the environment. -/
theorem ShEnv.bkb {c c' : Config} (E : ShEnv P W H C z σ c) {dst : ℕ} (hd : Bedge dst = true)
    (f : FrameB (Bkb dst) c c') : ShEnv P W H C z σ c' :=
  E.frame f fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb dst r
    · rfl
    · exact absurd (Bkb_bedge hd r h) (by rwd [this])

theorem xTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p i : ℕ} (h62 : c.nreg 140262 = p) (h36 : c.nreg 140236 = i)
    (hq : (chainModel C).pos (Qof P) ⟨p, i + 1⟩ ∈ seg pU pV)
    (hqy : ((chainModel C).pos (Qof P) ⟨p, i + 1⟩).2 = z.2)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨p, i + 1⟩) (hpn : p < (chainModel C).W.n)
    (hqR : |((chainModel C).pos (Qof P) ⟨p, i + 1⟩).2| < C.radius)
    (hUV : pU.2 ≠ pV.2) (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W xTree c c' k ∧ k ≤ 16200 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; ufo hostWords at this
  have hin : i + 1 ≤ P.n := hpp.2.2
  have e₁ := Exec.addN (P := P) hw 140304 140236 K1 (by rwo [h36, E.k1])
  set c₁ : Config := { c with nreg := upd c.nreg 140304 (c.nreg 140236 + c.nreg K1) } with hc₁
  have g₁ : ∀ r, r ≠ 140304 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [hr]
  have fe₁ : FrameB Bedge c c₁ := frameB_upd c _ (by decide)
  have E₁ := E.frame fe₁ Bedge_env
  have q04 : c₁.nreg 140304 = i + 1 := by rw [hc₁]; simp [h36, E.k1]
  have q62 : c₁.nreg 140262 = p := by rw [g₁ _ (by decide), h62]
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, f₂⟩ := ptLoad_exec (P := P) c₁ e₁.wb_right E₁ (e := 140262)
    (h := 140304) (B := 140292) (by norm_num) (by norm_num) (by norm_num) (by rwx [q62])
    (by rwx [q62, q04]) (Or.inr (by rwx [q62, q04])) (by rwx [hA₁])
  rw [q62, q04] at r₂
  have fe₂ : FrameB Bedge c₁ c₂ := FrameB.wk f₂ (Bld_bedge (by norm_num))
  have E₂ := E₁.frame fe₂ Bedge_env
  have k₂' : ∀ r, (r = 140262 ∨ r = 140304) → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r (by rcases hr with rfl | rfl <;> decide)
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, f₃⟩ := aheadT_exec (P := P) c₂ e₂.wb_right E₂ (A := 140292)
    (dst := 140314) (by norm_num) (by norm_num) r₂.1 (ne_of_seg hz hq hqy.symm)
  have fe₃ : FrameB Bedge c₂ c₃ := FrameB.wk f₃ (Bkb_bedge (by decide))
  have E₃ := E₂.bkb (by decide) f₃
  have kp : ∀ r, 140260 ≤ r → r < 140310 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    f₃.1 r (by sio [Bkb, Bk])
  have r₃ := r₂.keep fun r h1 h2 => kp r (by omega) (by omega)
  have hc := seg_at E.hσ hUV hq hqy
  have w₃ := e₃.wb_right
  unfold xTree
  by_cases t : c₃.nreg 140314 < c₃.nreg K1
  · have hA : ¬ 0 < σ * (((chainModel C).pos (Qof P) ⟨p, i + 1⟩).1 - z.1) := fun h => by
      have := a₃.2.2 h; rwo [E₃.k1] at t
    rw [ite_eq_right hA] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) (z := z) (σ := σ) c₃ w₃
      (hc.2 (by norm_num))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_true t ex))), by omega, ca,
      ((fe₁.trans fe₂).trans fe₃).trans f⟩
  · have hA : 0 < σ * (((chainModel C).pos (Qof P) ⟨p, i + 1⟩).1 - z.1) :=
      a₃.2.1 (by have := a₃.1; rwo [E₃.k1] at t)
    rw [ite_eq_left hA] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₃ w₃
      (by omega) (A := 140292) (e := 140262) (h := 140304) (by norm_num) (by norm_num)
      (by norm_num) r₃.1 (hc.1 rfl)
      (by rw [kp _ (by norm_num) (by norm_num), kp _ (by norm_num) (by norm_num),
        k₂' _ (Or.inl rfl), k₂' _ (Or.inr rfl), q62, q04]; exact hpp)
      (by rwx [kp _ (by norm_num) (by norm_num), k₂' _ (Or.inl rfl), q62])
      (by rw [kp _ (by norm_num) (by norm_num), kp _ (by norm_num) (by norm_num),
        k₂' _ (Or.inl rfl), k₂' _ (Or.inr rfl), q62, q04, ← hqy])
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false t ex))), by omega, ca,
      ((fe₁.trans fe₂).trans fe₃).trans f⟩

/-! ## The origin strictly inside the heights -/

/-- The geometry of the segment on the walk edge `p`. -/
def SegGeo (C : Chain) (p : ℕ) (pU pV : Point) : Prop :=
  p < (chainModel C).W.n ∧ ∃ α β : ℝ, 0 ≤ α ∧ α ≤ β ∧ β ≤ 1 ∧
    pU = Chazelle.Geometry.lerp ((chainModel C).wa p) ((chainModel C).wb p) α ∧
    pV = Chazelle.Geometry.lerp ((chainModel C).wa p) ((chainModel C).wb p) β

theorem midTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (rU : PtRecB P c 140270 pU C.radius)
    (rV : PtRecB P c 140281 pV C.radius) (h62 : c.nreg 140262 = p)
    (geo : SegGeo C p pU pV) (hUV : pU.2 ≠ pV.2) (hzU : z.2 ≠ pU.2) (hzV : z.2 ≠ pV.2)
    (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W midTree c c' k ∧ k ≤ 17300 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; ufo hostWords at this
  have hR := C.radius_pos
  -- the four height bits
  have step : ∀ (c₀ : Config) (dst : ℕ), WordsBounded W c₀ → ShEnv P W H C z σ c₀ →
      PtRecB P c₀ 140270 pU C.radius → PtRecB P c₀ 140281 pV C.radius →
      c₀.nreg 140262 = p → c₀.nreg ALLOC = c.nreg ALLOC → 140317 ≤ dst → dst < 140321 →
      ∀ a b ya yb, (a = 140274 ∨ a = 140234 ∨ a = 140285) → (b = 140274 ∨ b = 140234 ∨ b = 140285) →
      HRecS P c₀ a ya C.radius → HRecS P c₀ b yb C.radius →
      ∃ c₁ k, Exec P W (hLess a b dst) c₀ c₁ k ∧ k ≤ 250 ∧ BitIs c₁ dst (ya < yb) ∧
        FrameB (Bkb dst) c₀ c₁ ∧ ShEnv P W H C z σ c₁ ∧ PtRecB P c₁ 140270 pU C.radius ∧
        PtRecB P c₁ 140281 pV C.radius ∧ c₁.nreg 140262 = p ∧ c₁.nreg ALLOC = c.nreg ALLOC ∧
        ∀ r, r ≠ dst → 140262 ≤ r → r < 140330 → c₁.nreg r = c₀.nreg r :=
    fun c₀ dst hw₀ E₀ rU₀ rV₀ h62₀ hA₀ hd1 hd2 a b ya yb ha hb hA hB => by
      obtain ⟨c₁, k, ex, hk, bt, f⟩ := hLess_exec E₀.hG hW c₀ hw₀ (a := a) (b := b) (dst := dst)
        (by omega) (by omega) (by omega) E₀.k1 hR hA hB
      have kp : ∀ r, r ≠ dst → 140262 ≤ r → r < 140330 → c₁.nreg r = c₀.nreg r :=
        fun r h1 h2 h3 => f.1 r (by sio [Bkb, Bk])
      exact ⟨c₁, k, ex, hk, bt, f, E₀.bkb (by sio [Bedge]) f,
        rU₀.keep fun r h1 h2 => kp r (by omega) (by omega) (by omega),
        rV₀.keep fun r h1 h2 => kp r (by omega) (by omega) (by omega),
        by rw [kp _ (by omega) (by norm_num) (by norm_num), h62₀],
        by rw [f.1 ALLOC (by sio [Bkb, Bk, ALLOC]), hA₀], kp⟩
  obtain ⟨c₁, k₁, e₁, hk₁, b17, f₁, E₁, rU₁, rV₁, q₁, a₁, kp₁⟩ := step c 140317 hw E rU rV h62 rfl
    le_rfl (by norm_num) 140274 140234 _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) rU.2.1 E.oy
  obtain ⟨c₂, k₂, e₂, hk₂, b18, f₂, E₂, rU₂, rV₂, q₂, a₂, kp₂⟩ := step c₁ 140318 e₁.wb_right E₁ rU₁
    rV₁ q₁ a₁ (by norm_num) (by norm_num) 140234 140285 _ _ (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl)) E₁.oy rV₁.2.1
  obtain ⟨c₃, k₃, e₃, hk₃, b19, f₃, E₃, rU₃, rV₃, q₃, a₃, kp₃⟩ := step c₂ 140319 e₂.wb_right E₂ rU₂
    rV₂ q₂ a₂ (by norm_num) (by norm_num) 140285 140234 _ _ (Or.inr (Or.inr rfl))
    (Or.inr (Or.inl rfl)) rV₂.2.1 E₂.oy
  obtain ⟨c₄, k₄, e₄, hk₄, b20, f₄, E₄, rU₄, rV₄, q₄, a₄, kp₄⟩ := step c₃ 140320 e₃.wb_right E₃ rU₃
    rV₃ q₃ a₃ (by norm_num) (by norm_num) 140234 140274 _ _ (Or.inr (Or.inl rfl))
    (Or.inl rfl) E₃.oy rU₃.2.1
  -- the bits survive
  have b17' : BitIs c₄ 140317 (pU.2 < z.2) :=
    ((b17.of_eq (kp₂ _ (by norm_num) (by norm_num) (by norm_num))).of_eq
      (kp₃ _ (by norm_num) (by norm_num) (by norm_num))).of_eq
      (kp₄ _ (by norm_num) (by norm_num) (by norm_num))
  have b18' : BitIs c₄ 140318 (z.2 < pV.2) :=
    (b18.of_eq (kp₃ _ (by norm_num) (by norm_num) (by norm_num))).of_eq
      (kp₄ _ (by norm_num) (by norm_num) (by norm_num))
  have b19' : BitIs c₄ 140319 (pV.2 < z.2) :=
    b19.of_eq (kp₄ _ (by norm_num) (by norm_num) (by norm_num))
  have fe : FrameB Bedge c c₄ :=
    (((FrameB.wk f₁ (Bkb_bedge (by decide))).trans (FrameB.wk f₂ (Bkb_bedge (by decide)))).trans
      (FrameB.wk f₃ (Bkb_bedge (by decide)))).trans (FrameB.wk f₄ (Bkb_bedge (by decide)))
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₄ c' k →
      Exec P W (.seq (hLess 140274 140234 140317) (.seq (hLess 140234 140285 140318)
        (.seq (hLess 140285 140234 140319) (.seq (hLess 140234 140274 140320) s)))) c c'
        (k₁ + (k₂ + (k₃ + (k₄ + k)))) := fun ex => .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ ex)))
  have w₄ := e₄.wb_right
  -- the answer when the origin is strictly between
  obtain ⟨hpn, α, β, hα, hαβ, hβ, hpU, hpV⟩ := geo
  have xcase : (pU.2 < z.2 ∧ z.2 < pV.2) ∨ (pV.2 < z.2 ∧ z.2 < pU.2) →
      ∃ c' k, Exec P W xTree c₄ c' k ∧ k ≤ 16200 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
        FrameB Bedge c₄ c' := fun hmid => by
    have bU := rU.2.1.bounds hR
    have bV := rV.2.1.bounds hR
    -- the origin is at the height of a vertex of `Q`
    obtain ⟨-, hzR, -, hi, hzi⟩ : c₄.nreg 140234 = 1 ∧ |z.2| < C.radius ∧
        c₄.nreg (140234 + 1) = 0 ∧ c₄.nreg (140234 + 2) < P.n ∧
        z.2 = ((Qof P).vtx (c₄.nreg (140234 + 2))).2 := by
      rcases E₄.oy with ⟨_, h⟩ | ⟨_, h⟩ | h
      · exfalso; rw [h] at hmid; rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      · exfalso; rw [h] at hmid; rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      · exact h
    set i := c₄.nreg (140234 + 2) with hi_def
    have hm := mid_pos (chainModel C) (Qof P) (p := p) (h := i) hα hαβ hβ (by
      rwx [← hpU, ← hpV, ← hzi])
    rw [← hpU, ← hpV] at hm
    obtain ⟨hmem, hy, hp0, hp1⟩ := hm
    exact xTree_exec c₄ w₄ E₄ (p := p) (i := i) q₄ rfl hmem (by rw [hy, ← hzi])
      ⟨hp0.le, hp1, show i + 1 ≤ P.n by omega⟩ hpn (by rwx [hy, ← hzi]) hUV hz
      (by rwx [a₄])
  have ocase : ¬ ((pU.2 < z.2 ∧ z.2 < pV.2) ∨ (pV.2 < z.2 ∧ z.2 < pU.2)) →
      ∃ c' k, Exec P W cand0 c₄ c' k ∧ k = 1 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
        FrameB Bedge c₄ c' := fun hmid => by
    refine cand0_exec c₄ w₄ ((seg_out (x := 0) ?_).2 (by norm_num))
    rintro ⟨h1, h2⟩
    apply hmid
    rcases le_total pU.2 pV.2 with h | h
    · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
      exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm hzU), lt_of_le_of_ne h2 hzV⟩
    · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
      exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm hzV), lt_of_le_of_ne h2 hzU⟩
  have k1 := E₄.k1
  unfold midTree
  -- the tree
  have T2 : (¬ (pU.2 < z.2 ∧ z.2 < pV.2)) → ∃ c' k, Exec P W (.ifLtN 140319 K1 cand0
      (.ifLtN 140320 K1 cand0 xTree)) c₄ c' k ∧ k ≤ 16210 ∧
      CandAt P C c' 140220 (seg pU pV) z σ ∧ FrameB Bedge c₄ c' := fun hn => by
    by_cases t19 : c₄.nreg 140319 < c₄.nreg K1
    · have h19 : ¬ pV.2 < z.2 := fun h => by have := b19'.2.2 h; rwo [k1] at t19
      obtain ⟨c', k, ex, hk, ca, f⟩ := ocase (by tauto)
      exact ⟨c', _, .ifLtN_true t19 ex, by omega, ca, f⟩
    have h19 : pV.2 < z.2 := b19'.2.1 (by have := b19'.1; rwo [k1] at t19)
    by_cases t20 : c₄.nreg 140320 < c₄.nreg K1
    · have h20 : ¬ z.2 < pU.2 := fun h => by have := b20.2.2 h; rwo [k1] at t20
      obtain ⟨c', k, ex, hk, ca, f⟩ := ocase (by tauto)
      exact ⟨c', _, .ifLtN_false t19 (.ifLtN_true t20 ex), by omega, ca, f⟩
    have h20 : z.2 < pU.2 := b20.2.1 (by have := b20.1; rwo [k1] at t20)
    obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inr ⟨h19, h20⟩)
    exact ⟨c', _, .ifLtN_false t19 (.ifLtN_false t20 ex), by omega, ca, f⟩
  by_cases t17 : c₄.nreg 140317 < c₄.nreg K1
  · have h17 : ¬ pU.2 < z.2 := fun h => by have := b17'.2.2 h; rwo [k1] at t17
    obtain ⟨c', k, ex, hk, ca, f⟩ := T2 (fun h => h17 h.1)
    exact ⟨c', _, hpre (.ifLtN_true t17 ex), by omega, ca, fe.trans f⟩
  have h17 : pU.2 < z.2 := b17'.2.1 (by have := b17'.1; rwo [k1] at t17)
  by_cases t18 : c₄.nreg 140318 < c₄.nreg K1
  · have h18 : ¬ z.2 < pV.2 := fun h => by have := b18'.2.2 h; rwo [k1] at t18
    obtain ⟨c', k, ex, hk, ca, f⟩ := T2 (fun h => h18 h.2)
    exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_true t18 ex)), by omega, ca, fe.trans f⟩
  have h18 : z.2 < pV.2 := b18'.2.1 (by have := b18'.1; rwo [k1] at t18)
  obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inl ⟨h17, h18⟩)
  exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_false t18 ex)), by omega, ca, fe.trans f⟩

/-! ## The ends at different heights -/

/-- The answer at an end of the segment at the height of the origin. -/
theorem endCase_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV q : Point} {A e h : ℕ} (hq : q ∈ seg pU pV) (hqz : q.2 = z.2) (hUV : pU.2 ≠ pV.2)
    (hz : z ∉ seg pU pV) (hA : 140262 ≤ A ∧ A + 11 ≤ 140310) (he : 140262 ≤ e ∧ e < 140270)
    (hh : 140262 ≤ h ∧ h < 140270) (rq : PtRecB P c A q C.radius) (pq : PosAt P C c e h q) :
    ∃ c' k, Exec P W (.seq (aheadT A 140314) (.ifLtN 140314 K1 cand0 (candFrom A e h))) c c' k ∧
      k ≤ 270 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧ FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; ufo hostWords at this
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec (P := P) c hw E (A := A) (dst := 140314)
    (by omega) (by norm_num) rq.1 (ne_of_seg hz hq hqz.symm)
  have E₁ := E.bkb (by decide) f₁
  have kp : ∀ r, 140262 ≤ r → r < 140310 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by sio [Bkb, Bk])
  have rq₁ := rq.keep fun r h1 h2 => kp r (by omega) (by omega)
  have pq₁ := pq.keep (kp e (by omega) (by omega)) (kp h (by omega) (by omega))
  have fe₁ : FrameB Bedge c c₁ := FrameB.wk f₁ (Bkb_bedge (by decide))
  have hc := seg_at E.hσ hUV hq hqz
  have w₁ := e₁.wb_right
  by_cases t : c₁.nreg 140314 < c₁.nreg K1
  · have hA' : ¬ 0 < σ * (q.1 - z.1) := fun h => by
      have := a₁.2.2 h; rwo [E₁.k1] at t
    rw [ite_eq_right hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) (z := z) (σ := σ) c₁ w₁
      (hc.2 (by norm_num))
    exact ⟨c', _, .seq e₁ (.ifLtN_true t ex), by omega, ca, fe₁.trans f⟩
  · have hA' : 0 < σ * (q.1 - z.1) := a₁.2.1 (by have := a₁.1; rwo [E₁.k1] at t)
    rw [ite_eq_left hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₁ w₁
      (by omega) (A := A) (e := e) (h := h) (by omega) (by omega) (by omega) rq₁.1 (hc.1 rfl)
      pq₁.2.1 pq₁.2.2 (by rw [pq₁.1, ← hqz])
    exact ⟨c', _, .seq e₁ (.ifLtN_false t ex), by omega, ca, fe₁.trans f⟩

theorem neTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (rU : PtRecB P c 140270 pU C.radius)
    (rV : PtRecB P c 140281 pV C.radius) (pU' : PosAt P C c 140263 140264 pU)
    (pV' : PosAt P C c 140265 140266 pV) (h62 : c.nreg 140262 = p) (geo : SegGeo C p pU pV)
    (hUV : pU.2 ≠ pV.2) (b12 : BitIs c 140312 (z.2 = pU.2)) (b13 : BitIs c 140313 (z.2 = pV.2))
    (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W neTree c c' k ∧ k ≤ 17400 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have k1 := E.k1
  unfold neTree
  by_cases t12 : c.nreg 140312 < c.nreg K1
  · have hzU : z.2 ≠ pU.2 := fun h => by have := b12.2.2 h; rwo [k1] at t12
    by_cases t13 : c.nreg 140313 < c.nreg K1
    · have hzV : z.2 ≠ pV.2 := fun h => by have := b13.2.2 h; rwo [k1] at t13
      obtain ⟨c', k, ex, hk, ca, f⟩ := midTree_exec c hw E rU rV h62 geo hUV hzU hzV hz hroom
      exact ⟨c', _, .ifLtN_true t12 (.ifLtN_true t13 ex), by omega, ca, f⟩
    have hzV : z.2 = pV.2 := b13.2.1 (by have := b13.1; rwo [k1] at t13)
    obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E (V_mem_seg pU pV) hzV.symm hUV hz
      (A := 140281) (e := 140265) (h := 140266) (by norm_num) (by norm_num) (by norm_num) rV pV'
    exact ⟨c', _, .ifLtN_true t12 (.ifLtN_false t13 ex), by omega, ca, f⟩
  have hzU : z.2 = pU.2 := b12.2.1 (by have := b12.1; rwo [k1] at t12)
  obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E (U_mem_seg pU pV) hzU.symm hUV hz
    (A := 140270) (e := 140263) (h := 140264) (by norm_num) (by norm_num) (by norm_num) rU pU'
  exact ⟨c', _, .ifLtN_false t12 ex, by omega, ca, f⟩

/-! ## The segment machine -/

/-- The input of the segment machine: an end position, proper, and a box vertex or strictly
inside the height range of the box. -/
def EndIn (P : Polygon) (C : Chain) (c : Config) (e h : ℕ) (q : Point) : Prop :=
  PosAt P C c e h q ∧ (c.nreg h = 0 ∨ |q.2| < C.radius)

theorem edgeH_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p : ℕ} (iU : EndIn P C c 140263 140264 pU) (iV : EndIn P C c 140265 140266 pV)
    (h62 : c.nreg 140262 = p) (geo : SegGeo C p pU pV) (hz : z ∉ seg pU pV)
    (hroom : c.nreg ALLOC + 50000 ≤ W) :
    ∃ c' k, Exec P W edgeH c c' k ∧ k ≤ 50000 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; ufo hostWords at this
  have hR := C.radius_pos
  -- `U`
  obtain ⟨⟨pUe, pUp, pUn⟩, pUy⟩ := iU
  obtain ⟨c₁, k₁, e₁, hk₁, rU₁, f₁⟩ := ptLoad_exec (P := P) c hw E (e := 140263) (h := 140264)
    (B := 140270) (by norm_num) (by norm_num) (by norm_num) pUn pUp (by rw [pUe]; exact pUy)
    (by omega)
  rw [pUe] at rU₁
  have fe₁ : FrameB Bedge c c₁ := FrameB.wk f₁ (Bld_bedge (by norm_num))
  have E₁ := E.frame fe₁ Bedge_env
  have kp₁ : ∀ r, 140262 ≤ r → r < 140270 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by sio [Bld, Bprim])
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 ALLOC (by simp [Bld, Bprim, ALLOC])
  -- `V`
  obtain ⟨⟨pVe, pVp, pVn⟩, pVy⟩ := iV
  obtain ⟨c₂, k₂, e₂, hk₂, rV₂, f₂⟩ := ptLoad_exec (P := P) c₁ e₁.wb_right E₁ (e := 140265)
    (h := 140266) (B := 140281) (by norm_num) (by norm_num) (by norm_num)
    (by rw [kp₁ _ (by norm_num) (by norm_num)]; exact pVn)
    (by rw [kp₁ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num)]; exact pVp)
    (by rw [kp₁ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num), pVe]; exact pVy)
    (by rwo [hA₁])
  rw [kp₁ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num), pVe] at rV₂
  have fe₂ : FrameB Bedge c₁ c₂ := FrameB.wk f₂ (Bld_bedge (by norm_num))
  have E₂ := E₁.frame fe₂ Bedge_env
  have kp₂ : ∀ r, 140262 ≤ r → r < 140281 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r (by sio [Bld, Bprim])
  have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [f₂.1 ALLOC (by simp [Bld, Bprim, ALLOC]), hA₁]
  have rU₂ := rU₁.keep fun r h1 h2 => kp₂ r (by omega) (by omega)
  have pU₂ : PosAt P C c₂ 140263 140264 pU := by
    refine PosAt.keep ⟨pUe, pUp, pUn⟩ ?_ ?_
    · rw [kp₂ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num)]
    · rw [kp₂ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num)]
  have pV₂ : PosAt P C c₂ 140265 140266 pV := by
    refine PosAt.keep ⟨pVe, pVp, pVn⟩ ?_ ?_
    · rw [kp₂ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num)]
    · rw [kp₂ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num)]
  have q62 : c₂.nreg 140262 = p := by
    rw [kp₂ _ (by norm_num) (by norm_num), kp₁ _ (by norm_num) (by norm_num), h62]
  -- the three height bits
  have hEqStep : ∀ (c₀ : Config) (a b dst : ℕ) (ya yb : ℝ), WordsBounded W c₀ →
      ShEnv P W H C z σ c₀ → 140311 ≤ dst → dst < 140314 → HRecS P c₀ a ya C.radius →
      HRecS P c₀ b yb C.radius →
      ∃ c₁ k, Exec P W (hEq a b dst) c₀ c₁ k ∧ k ≤ 20 ∧ BitIs c₁ dst (ya = yb) ∧
        (∀ r, r ≠ dst → c₁.nreg r = c₀.nreg r) ∧ FrameB Bedge c₀ c₁ ∧ ShEnv P W H C z σ c₁ :=
    fun c₀ a b dst ya yb hw₀ E₀ hd1 hd2 hA hB => by
      obtain ⟨c₁, k, ex, hk, bt, hc⟩ := hEq_exec E₀.hG (by omega) c₀ hw₀ (dst := dst) E₀.k1 hR hA hB
      have kp : ∀ r, r ≠ dst → c₁.nreg r = c₀.nreg r := fun r hr => by rw [hc]; simp [hr]
      have fr : FrameB Bedge c₀ c₁ := by
        rw [hc]; exact frameB_upd c₀ _ (by sio [Bedge])
      exact ⟨c₁, k, ex, hk, bt, kp, fr, E₀.frame fr Bedge_env⟩
  obtain ⟨c₃, k₃, e₃, hk₃, b11, kp₃, fe₃, E₃⟩ := hEqStep c₂ 140274 140285 140311 _ _ e₂.wb_right
    E₂ le_rfl (by norm_num) rU₂.2.1 rV₂.2.1
  have rU₃ := rU₂.keep fun r h1 h2 => kp₃ r (by omega)
  have rV₃ := rV₂.keep fun r h1 h2 => kp₃ r (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, b12, kp₄, fe₄, E₄⟩ := hEqStep c₃ 140234 140274 140312 _ _ e₃.wb_right
    E₃ (by norm_num) (by norm_num) E₃.oy rU₃.2.1
  have rU₄ := rU₃.keep fun r h1 h2 => kp₄ r (by omega)
  have rV₄ := rV₃.keep fun r h1 h2 => kp₄ r (by omega)
  obtain ⟨c₅, k₅, e₅, hk₅, b13, kp₅, fe₅, E₅⟩ := hEqStep c₄ 140234 140285 140313 _ _ e₄.wb_right
    E₄ (by norm_num) (by norm_num) E₄.oy rV₄.2.1
  have rU₅ := rU₄.keep fun r h1 h2 => kp₅ r (by omega)
  have rV₅ := rV₄.keep fun r h1 h2 => kp₅ r (by omega)
  have kk : ∀ r, 140262 ≤ r → r < 140270 → c₅.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [kp₅ r (by omega), kp₄ r (by omega), kp₃ r (by omega)]
  have pU₅ := pU₂.keep (kk _ (by norm_num) (by norm_num)) (kk _ (by norm_num) (by norm_num))
  have pV₅ := pV₂.keep (kk _ (by norm_num) (by norm_num)) (kk _ (by norm_num) (by norm_num))
  have q62' : c₅.nreg 140262 = p := by rw [kk _ (by norm_num) (by norm_num), q62]
  have b11' : BitIs c₅ 140311 (pU.2 = pV.2) :=
    (b11.of_eq (kp₄ _ (by norm_num))).of_eq (kp₅ _ (by norm_num))
  have b12' : BitIs c₅ 140312 (z.2 = pU.2) := b12.of_eq (kp₅ _ (by norm_num))
  have hA₅ : c₅.nreg ALLOC = c.nreg ALLOC := by
    rw [kp₅ _ (by decide), kp₄ _ (by decide), kp₃ _ (by decide), hA₂]
  have fe  := (((fe₁.trans fe₂).trans fe₃).trans fe₄).trans fe₅
  have w₅ := e₅.wb_right
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₅ c' k →
      Exec P W (.seq (ptLoad 140263 140264 140270) (.seq (ptLoad 140265 140266 140281)
        (.seq (hEq 140274 140285 140311) (.seq (hEq 140234 140274 140312)
          (.seq (hEq 140234 140285 140313) s))))) c c' (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k))))) :=
    fun ex => .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ ex))))
  unfold edgeH
  by_cases t11 : c₅.nreg 140311 < c₅.nreg K1
  · have hUV : pU.2 ≠ pV.2 := fun h => by have := b11'.2.2 h; rwo [E₅.k1] at t11
    obtain ⟨c', k, ex, hk, ca, f⟩ := neTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ q62' geo hUV b12' b13
      hz (by rwo [hA₅])
    exact ⟨c', _, hpre (.ifLtN_true t11 ex), by omega, ca, fe.trans f⟩
  · have hUV : pU.2 = pV.2 := b11'.2.1 (by have := b11'.1; rwo [E₅.k1] at t11)
    obtain ⟨c', k, ex, hk, ca, f⟩ := eqTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ hUV b12' hz
    exact ⟨c', _, hpre (.ifLtN_false t11 ex), by omega, ca, fe.trans f⟩

end

end ShootCut

end Chazelle.Core
