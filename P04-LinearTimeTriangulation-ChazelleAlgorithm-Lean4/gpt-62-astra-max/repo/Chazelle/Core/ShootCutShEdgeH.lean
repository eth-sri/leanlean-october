module
public import Chazelle.Core.ModelAccess
public import Chazelle.Machine.Contract
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence
public import Chazelle.Programs.ReadWords
public import Chazelle.Programs.RunProof
public import Chazelle.Programs.Verification

public import Chazelle.Core.ShootCutShEdgeR

/-!
# WP-G, part 45: the segment machine `edgeH`

The decision tree of `edgeSel` on the RAM (see `ShootCutShEdgeR`).  `eqTree`: the ends at one
height; `neTree`: the ends at different heights, with `midTree` for the origin strictly between.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

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
  refine ⟨absRec_copy' ax (guarded (hk _ le_rfl)) (at_index hk _)
    (at_index hk _) (at_index hk _),
    hy.copy (hk _ (by omega) (by omega)) (by read_words)
      (by read_words), fun h7 => ?_⟩
  obtain ⟨s, hs, hl, hv⟩ := fr (by simp_all)
  exact ⟨s, NFLoc.symPtIn_copy hs (hk _ (by omega) (by omega)) (by read_words)
    (by read_words), hl, hv⟩

theorem Bkb_bedge {dst : ℕ} (hd : Bedge dst = true) (r : ℕ) (h : Bkb dst r = true) :
    Bedge r = true := by
  simp [Bkb, Bk] at h
  rcases h with h | rfl
  · address_omega
  · exact hd

theorem Bld_bedge {B : ℕ} (hB : 140262 ≤ B ∧ B + 11 ≤ 140330) (r : ℕ) (h : Bld B r = true) :
    Bedge r = true := by
  address_omega

/-! ## The ends at one height -/

/-- The walk position in `e`, `h` has the point `q`, is proper, on a walk edge. -/
def PosAt (P : Polygon) (C : Chain) (c : Config) (e h : ℕ) (q : Point) : Prop :=
  (chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ = q ∧
    ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩ ∧ c.nreg e < (chainModel C).W.n

theorem PosAt.keep {c c' : Config} {e h : ℕ} {q : Point} (hp : PosAt P C c e h q)
    (he : c'.nreg e = c.nreg e) (hh : c'.nreg h = c.nreg h) : PosAt P C c' e h q := by
  simp_all [PosAt]

theorem ne_of_seg {U V z X : Point} (hz : z ∉ seg U V) (hX : X ∈ seg U V) (hy : z.2 = X.2) :
    X.1 ≠ z.1 := fun h => hz (by
  have : z = X := Prod.ext h.symm hy
  rw [this]; exact hX)

theorem eqTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} (rU : PtRecB P c 140270 pU C.radius) (rV : PtRecB P c 140281 pV C.radius)
    (pU' : PosAt P C c 140263 140264 pU) (pV' : PosAt P C c 140265 140266 pV)
    (hUV : pU.2 = pV.2) (b12 : BitIs c 140312 (z.2 = pU.2)) (hz : z ∉ seg pU pV) :
    ∃ c' k, Exec P W eqTree c c' k ∧ k ≤ 600 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  have hc := edge_cand (U := pU) (V := pV) (X := pU) E.hσ hz (fun h => by
    grind)
  simp at hc
  unfold eqTree
  by_cases t0 : c.nreg 140312 < c.nreg K1
  · have hzU : ¬ z.2 = pU.2 := fun h => by have := b12.2.2 h; grind [E.k1]
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by grind [edgeSel]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) c hw
      (guarded hc.2)
    finish_run (.ifLtN_true t0 ex)
  have hzU := b12.2.1 (by have := b12.1; rw [E.k1] at t0; omega)
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec c hw E (dst := 140314)
    (by norm_num) (by norm_num) rU.1 (ne_of_seg hz (U_mem_seg pU pV) hzU)
  have E₁ := E.frame f₁ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140314 r
    · rfl
    · exact at_index absurd (Bkb_bedge (by decide) r h)
  have kp : ∀ r ≥ 140260, r < 140300 → r ≠ 140314 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    f₁.1 r (by simp [Bkb, Bk]; omega)
  have rU₁ := rU.keep fun r h1 h2 => at_index kp r
  have rV₁ := rV.keep fun r h1 h2 => at_index kp r
  have pU₁ := pU'.keep (at_index kp _)
    (at_index kp _)
  have pV₁ := pV'.keep (at_index kp _)
    (at_index kp _)
  have fe₁ := FrameB.wk f₁ (Bkb_bedge (by decide))
  have w₁ := e₁.wb_right
  have t0' := t0
  by_cases t1 : c₁.nreg 140314 < c₁.nreg K1
  · have hA : ¬ 0 < σ * (pU.1 - z.1) := fun h => by
      have := a₁.2.2 h; grind [E₁.k1]
    rw [show edgeSel _ _ _ _ _ _ _ _ = 0 by grind [edgeSel]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := cand0_exec (P := P) (C := C) c₁ w₁
      (guarded hc.2)
    exact ⟨c', _, .ifLtN_false t0' (e₁ ;; .ifLtN_true t1 ex), by omega, ca, fe₁.trans f⟩
  have hA := a₁.2.1 (by have := a₁.1; rw [E₁.k1] at t1; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, a₂, f₂⟩ := nearT_exec (P := P) c₁ w₁ E₁ (dst := 140316) (by norm_num)
    rU₁.1 rV₁.1
  have E₂ := E₁.frame f₂ fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb 140316 r
    · rfl
    · exact at_index absurd (Bkb_bedge (by decide) r h)
  have kp₂ : ∀ r, 140260 ≤ r → r < 140300 → r ≠ 140316 → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => f₂.1 r (by simp [Bkb, Bk]; omega)
  have rU₂ := rU₁.keep fun r h1 h2 => at_index kp₂ r
  have rV₂ := rV₁.keep fun r h1 h2 => at_index kp₂ r
  have pU₂ := pU₁.keep (at_index kp₂ _)
    (at_index kp₂ _)
  have pV₂ := pV₁.keep (at_index kp₂ _)
    (at_index kp₂ _)
  have fe₂ : FrameB Bedge c₁ c₂ := FrameB.wk f₂ (Bkb_bedge (by decide))
  have w₂ := e₂.wb_right
  have t1' : ¬ c₁.nreg 140314 < c₁.nreg K1 := t1
  by_cases t2 : c₂.nreg 140316 < c₂.nreg K1
  · have hn : σ * pU.1 ≤ σ * pV.1 := by
      by_contra h; have := a₂.2.2 h; rw [E₂.k1] at t2; omega
    rw [show edgeSel _ _ _ _ _ _ _ _ = 1 by grind [edgeSel]] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₂ w₂
      (by omega) (A := 140270) (e := 140263) (h := 140264) (by norm_num) (by norm_num)
      (by norm_num) rU₂.1 (hc.1 rfl) pU₂.2.1 pU₂.2.2 (by rw [pU₂.1, hzU])
    exact ⟨c', _, .ifLtN_false t0' (e₁ ;; .ifLtN_false t1' (.seq e₂ (.ifLtN_true t2 ex))),
      by omega, ca, (fe₁.trans fe₂).trans f⟩
  have hn : ¬ σ * pU.1 ≤ σ * pV.1 := a₂.2.1 (by have := a₂.1; rw [E₂.k1] at t2; omega)
  rw [show edgeSel _ _ _ _ _ _ _ _ = 2 by grind [edgeSel]] at hc
  obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₂ w₂
    (by omega) (A := 140281) (e := 140265) (h := 140266) (by norm_num) (by norm_num)
    (by norm_num) rV₂.1 (hc.1 rfl) pV₂.2.1 pV₂.2.2 (by rw [pV₂.1, hzU, hUV])
  exact ⟨c', _, .ifLtN_false t0' (e₁ ;; .ifLtN_false t1' (.seq e₂ (.ifLtN_false t2 ex))),
    by omega, ca, (fe₁.trans fe₂).trans f⟩

/-! ## The point at the height of the origin -/

/-- A step framed by `Bkb dst` keeps the environment. -/
theorem ShEnv.bkb {c c' : Config} (E : ShEnv P W H C z σ c) {dst : ℕ} (hd : Bedge dst = true)
    (f : FrameB (Bkb dst) c c') : ShEnv P W H C z σ c' :=
  E.frame f fun r hr => by
    have := Bedge_env r hr
    cases h : Bkb dst r
    · rfl
    · exact absurd (Bkb_bedge hd r h) (by rw [this]; decide)

theorem xTree_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV : Point} {p i : ℕ} (h62 : c.nreg 140262 = p) (h36 : c.nreg 140236 = i)
    (hq : (chainModel C).pos (Qof P) ⟨p, i + 1⟩ ∈ seg pU pV)
    (hqy : ((chainModel C).pos (Qof P) ⟨p, i + 1⟩).2 = z.2)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨p, i + 1⟩) (hpn : p < (chainModel C).W.n)
    (hqR : |((chainModel C).pos (Qof P) ⟨p, i + 1⟩).2| < C.radius)
    (hUV : pU.2 ≠ pV.2) (hz : z ∉ seg pU pV) (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W xTree c c' k ∧ k ≤ 16200 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧
      FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  have hin : i + 1 ≤ P.n := hpp.2.2
  have e₁ := Exec.addN (P := P) hw 140304 140236 K1 (by rw [h36, E.k1]; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 140304 (c.nreg 140236 + c.nreg K1) } with hc₁
  have fe₁ : FrameB Bedge c c₁ := frameB_upd c _ (by decide)
  have E₁ := E.frame fe₁ Bedge_env
  have q04 : c₁.nreg 140304 = i + 1 := by rw [hc₁]; simp [h36, E.k1]
  have q62 : c₁.nreg 140262 = p := by simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, f₂⟩ := guarded (ptLoad_exec (P := P) c₁ e₁.wb_right E₁ (e := 140262)
    (h := 140304) (B := 140292) (by norm_num) (by norm_num) (by norm_num) (by simp_all)
    (by simp_all) (Or.inr (by simp_all)))
  rw [q62, q04] at r₂
  have fe₂ : FrameB Bedge c₁ c₂ := FrameB.wk f₂ (guarded Bld_bedge)
  have E₂ := E₁.frame fe₂ Bedge_env
  have k₂' : ∀ r, (r = 140262 ∨ r = 140304) → c₂.nreg r = c₁.nreg r := fun r hr =>
    at_index f₂.1 r
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, f₃⟩ := aheadT_exec (P := P) c₂ e₂.wb_right E₂ (A := 140292)
    (dst := 140314) (by norm_num) (by norm_num) r₂.1 (ne_of_seg hz hq hqy.symm)
  have fe₃ : FrameB Bedge c₂ c₃ := FrameB.wk f₃ (Bkb_bedge (by decide))
  have E₃ := E₂.bkb (by decide) f₃
  have kp : AgreeOnBand 140260 140310 c₃.nreg c₂.nreg := fun r h1 h2 =>
    f₃.1 r (by simp [Bkb, Bk]; omega)
  have hc := from_facts seg_at
  have w₃ := e₃.wb_right
  unfold xTree
  by_cases t : c₃.nreg 140314 < c₃.nreg K1
  · have hA : ¬ 0 < σ * ((C.chainModel.pos P.Qof ⟨p, i + 1⟩).1 - z.1) := fun h => by
      have := a₃.2.2 h; grind [E₃.k1]
    rw_facts [ite_eq_right] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := from_facts (cand0_exec (P := P) (C := C) (z := z) (σ := σ) c₃)
    exact ⟨c', _, e₁ ;; e₂ ;; e₃ ;; .ifLtN_true t ex, by omega, ca,
      ((fe₁.trans fe₂).trans fe₃).trans f⟩
  · 
    rw [ite_eq_left (a₃.2.1 (by have := a₃.1; rw [E₃.k1] at t; omega))] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₃ w₃
      (by omega) (A := 140292) (e := 140262) (h := 140304) (by norm_num) (by norm_num)
      (by norm_num) (r₂.keep fun r h1 h2 => at_index kp r).1 (hc.1 rfl)
      (by grind)
      (by grind)
      (by grind)
    exact ⟨c', _, e₁ ;; e₂ ;; e₃ ;; .ifLtN_false t ex, by omega, ca,
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
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
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
        fun r h1 h2 h3 => f.1 r (by simp [Bkb, Bk]; omega)
      exact ⟨c₁, k, ex, hk, bt, f, E₀.bkb (by simp [Bedge]; omega) f,
        rU₀.keep fun r h1 h2 => at_index kp r,
        rV₀.keep fun r h1 h2 => at_index kp r,
        by read_words,
        by rw [f.1 ALLOC (by simp [Bkb, Bk, ALLOC]; omega), hA₀], kp⟩
  obtain ⟨c₁, k₁, e₁, hk₁, b17, f₁, E₁, rU₁, rV₁, q₁, a₁, kp₁⟩ := from_facts (step c 140317 140274 140234 _ _)
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
    ((b17.of_eq (at_index kp₂ _)).of_eq
      (at_index kp₃ _)).of_eq
      (at_index kp₄ _)
  have b18' : BitIs c₄ 140318 (z.2 < pV.2) :=
    (b18.of_eq (at_index kp₃ _)).of_eq
      (at_index kp₄ _)
  have b19' : BitIs c₄ 140319 (pV.2 < z.2) :=
    b19.of_eq (at_index kp₄ _)
  have fe : FrameB Bedge c c₄ :=
    (((FrameB.wk f₁ (Bkb_bedge (by decide))).trans (FrameB.wk f₂ (Bkb_bedge (by decide)))).trans
      (FrameB.wk f₃ (Bkb_bedge (by decide)))).trans (FrameB.wk f₄ (Bkb_bedge (by decide)))
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₄ c' k →
      Exec P W (hLess 140274 140234 140317 ;; hLess 140234 140285 140318 ;; hLess 140285 140234 140319 ;; hLess 140234 140274 140320 ;; s) c c'
        (k₁ + (k₂ + (k₃ + (k₄ + k)))) := fun ex => e₁ ;; e₂ ;; e₃ ;; e₄ ;; ex
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
        z.2 = (P.Qof.vtx (c₄.nreg (140234 + 2))).2 := by
      rcases E₄.oy with ⟨_, h⟩ | ⟨_, h⟩ | h
      · exfalso; rw [h] at hmid; grind
      · grind
      · exact h
    set i := c₄.nreg (140234 + 2) with hi_def
    have hm := mid_pos C.chainModel P.Qof (p := p) (h := i) hα hαβ hβ (by
      rw [← hpU, ← hpV, ← hzi]; exact hmid)
    rw [← hpU, ← hpV] at hm
    obtain ⟨hmem, hy, hp0, hp1⟩ := hm
    exact xTree_exec c₄ w₄ E₄ (p := p) (i := i) q₄ rfl hmem (by simp [hy, hzi])
      ⟨hp0.le, hp1, show i + 1 ≤ P.n by omega⟩ hpn (by grind) hUV hz
      (by rw [a₄]; exact hroom)
  have ocase : ¬ ((pU.2 < z.2 ∧ z.2 < pV.2) ∨ (pV.2 < z.2 ∧ z.2 < pU.2)) →
      RunsFor P W cand0 c₄ 1 fun c' => CandAt P C c' 140220 (seg pU pV) z σ ∧
        FrameB Bedge c₄ c' := fun hmid => by
    refine cand0_exec c₄ w₄ (guarded (seg_out (x := 0) ?_).2)
    rintro ⟨h1, h2⟩
    apply hmid
    rcases le_total pU.2 pV.2 with h | h
    · rw_facts [min_eq_left] at h1; rw_facts [max_eq_right] at h2
      exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm hzU), lt_of_le_of_ne h2 hzV⟩
    · rw_facts [min_eq_right] at h1; rw_facts [max_eq_left] at h2
      exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm hzV), lt_of_le_of_ne h2 hzU⟩
  have k1 := E₄.k1
  unfold midTree
  -- the tree
  have T2 : (¬ (pU.2 < z.2 ∧ z.2 < pV.2)) → ∃ c' k, Exec P W (.ifLtN 140319 K1 cand0
      (.ifLtN 140320 K1 cand0 xTree)) c₄ c' k ∧ k ≤ 16210 ∧
      CandAt P C c' 140220 (seg pU pV) z σ ∧ FrameB Bedge c₄ c' := fun hn => by
    by_cases t19 : c₄.nreg 140319 < c₄.nreg K1
    · have h19 : ¬ pV.2 < z.2 := fun h => by have := b19'.2.2 h; grind
      obtain ⟨c', k, ex, hk, ca, f⟩ := ocase (by tauto)
      exact ⟨c', _, .ifLtN_true t19 ex, by omega, ca, f⟩
    by_cases t20 : c₄.nreg 140320 < c₄.nreg K1
    · have h20 : ¬ z.2 < pU.2 := fun h => by have := b20.2.2 h; grind
      obtain ⟨c', k, ex, hk, ca, f⟩ := ocase (by tauto)
      exact ⟨c', _, .ifLtN_false t19 (.ifLtN_true t20 ex), by omega, ca, f⟩
    obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inr ⟨(b19'.2.1 (by have := b19'.1; rw [k1] at t19; omega)), (b20.2.1 (by have := b20.1; rw [k1] at t20; omega))⟩)
    exact ⟨c', _, .ifLtN_false t19 (.ifLtN_false t20 ex), by omega, ca, f⟩
  by_cases t17 : c₄.nreg 140317 < c₄.nreg K1
  · 
    obtain ⟨c', k, ex, hk, ca, f⟩ := T2 (fun h => (fun h => by have := b17'.2.2 h; grind) h.1)
    exact ⟨c', _, hpre (.ifLtN_true t17 ex), by omega, ca, fe.trans f⟩
  by_cases t18 : c₄.nreg 140318 < c₄.nreg K1
  · 
    obtain ⟨c', k, ex, hk, ca, f⟩ := T2 (fun h => (fun h => by have := b18'.2.2 h; grind) h.2)
    exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_true t18 ex)), by omega, ca, fe.trans f⟩
  obtain ⟨c', k, ex, hk, ca, f⟩ := xcase (Or.inl ⟨(b17'.2.1 (by have := b17'.1; rw [k1] at t17; omega)), (b18'.2.1 (by have := b18'.1; rw [k1] at t18; omega))⟩)
  exact ⟨c', _, hpre (.ifLtN_false t17 (.ifLtN_false t18 ex)), by omega, ca, fe.trans f⟩

/-! ## The ends at different heights -/

/-- The answer at an end of the segment at the height of the origin. -/
theorem endCase_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {pU pV q : Point} {A e h : ℕ} (hq : q ∈ seg pU pV) (hqz : q.2 = z.2) (hUV : pU.2 ≠ pV.2)
    (hz : z ∉ seg pU pV) (hA : 140262 ≤ A ∧ A + 11 ≤ 140310) (he : 140262 ≤ e ∧ e < 140270)
    (hh : 140262 ≤ h ∧ h < 140270) (rq : PtRecB P c A q C.radius) (pq : PosAt P C c e h q) :
    ∃ c' k, Exec P W (.seq (aheadT A 140314) (.ifLtN 140314 K1 cand0 (candFrom A e h))) c c' k ∧
      k ≤ 270 ∧ CandAt P C c' 140220 (seg pU pV) z σ ∧ FrameB Bedge c c' := by
  have hW : P.n + 3 ≤ W := by have := E.hW; unfold hostWords at this; omega
  obtain ⟨c₁, k₁, e₁, hk₁, a₁, f₁⟩ := aheadT_exec (P := P) c hw E (A := A) (dst := 140314)
    (by omega) (by norm_num) rq.1 (ne_of_seg hz hq hqz.symm)
  have E₁ := E.bkb (by decide) f₁
  have kp : AgreeOnBand 140262 140310 c₁.nreg c.nreg := fun r h1 h2 =>
    f₁.1 r (by simp [Bkb, Bk]; omega)
  have rq₁ := rq.keep fun r h1 h2 => at_index kp r
  have pq₁ := pq.keep (at_index kp e) (at_index kp h)
  have fe₁ : FrameB Bedge c c₁ := FrameB.wk f₁ (Bkb_bedge (by decide))
  have hc := from_facts seg_at
  have w₁ := e₁.wb_right
  by_cases t : c₁.nreg 140314 < c₁.nreg K1
  · have hA' : ¬ 0 < σ * (q.1 - z.1) := fun h => by
      have := a₁.2.2 h; grind [E₁.k1]
    rw [ite_eq_right hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := from_facts (cand0_exec (P := P) (C := C) (z := z) (σ := σ) c₁)
    exact ⟨c', _, e₁ ;; .ifLtN_true t ex, by omega, ca, fe₁.trans f⟩
  · have hA' : 0 < σ * (q.1 - z.1) := a₁.2.1 (by have := a₁.1; rw [E₁.k1] at t; omega)
    rw [ite_eq_left hA'] at hc
    obtain ⟨c', k, ex, hk, ca, f⟩ := candFrom_exec (P := P) (C := C) (S := seg pU pV) c₁ w₁
      (by omega) (A := A) (e := e) (h := h) (by omega) (by omega) (by omega) rq₁.1 (hc.1 rfl)
      pq₁.2.1 pq₁.2.2 (by rw [pq₁.1, ← hqz])
    exact ⟨c', _, e₁ ;; .ifLtN_false t ex, by omega, ca, fe₁.trans f⟩

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
  · have hzU : z.2 ≠ pU.2 := fun h => by have := b12.2.2 h; simp_all
    by_cases t13 : c.nreg 140313 < c.nreg K1
    · have hzV : z.2 ≠ pV.2 := fun h => by have := b13.2.2 h; simp_all
      obtain ⟨c', k, ex, hk, ca, f⟩ := from_facts midTree_exec
      finish_run (.ifLtN_true t12 (.ifLtN_true t13 ex))
    obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E (V_mem_seg pU pV) (b13.2.1 (by have := b13.1; rw [k1] at t13; omega)).symm hUV hz
      (A := 140281) (e := 140265) (h := 140266) (by norm_num) (by norm_num) (by norm_num) rV pV'
    finish_run (.ifLtN_true t12 (.ifLtN_false t13 ex))
  obtain ⟨c', k, ex, hk, ca, f⟩ := endCase_exec c hw E (U_mem_seg pU pV) (b12.2.1 (by have := b12.1; rw [k1] at t12; omega)).symm hUV hz
    (A := 140270) (e := 140263) (by norm_num) (by norm_num) (by norm_num) rU pU'
  finish_run (.ifLtN_false t12 ex)

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
  -- `U`
  obtain ⟨⟨pUe, pUp, pUn⟩, pUy⟩ := iU
  obtain ⟨c₁, k₁, e₁, hk₁, rU₁, f₁⟩ := ptLoad_exec c hw E
    (B := 140270) (by norm_num) (by norm_num) (by norm_num) pUn pUp (by simp_all)
    (by omega)
  rw [pUe] at rU₁
  have fe₁ := FrameB.wk f₁ (guarded Bld_bedge)
  have E₁ := E.frame fe₁ Bedge_env
  have kp₁ : AgreeOnBand 140262 140270 c₁.nreg c.nreg := fun r h1 h2 =>
    at_index f₁.1 r
  have hA₁ := f₁.1 ALLOC (rfl)
  -- `V`
  obtain ⟨⟨pVe, pVp, pVn⟩, pVy⟩ := iV
  obtain ⟨c₂, k₂, e₂, hk₂, rV₂, f₂⟩ := ptLoad_exec c₁ e₁.wb_right E₁ (e := 140265)
    (h := 140266) (B := 140281) (by norm_num) (by norm_num) (by norm_num)
    (by simp_all)
    (by simp_all)
    (by simp_all)
    (by rw [hA₁]; omega)
  rw [at_index kp₁ _, at_index kp₁ _, pVe] at rV₂
  have fe₂ := FrameB.wk f₂ (guarded Bld_bedge)
  have kp₂ : AgreeOnBand 140262 140281 c₂.nreg c₁.nreg := fun r h1 h2 =>
    at_index f₂.1 r
  have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw_facts [f₂.1, hA₁]
  have rU₂ := rU₁.keep fun r h1 h2 => at_index kp₂ r
  have pU₂ : PosAt P C c₂ 140263 140264 pU := by
    refine PosAt.keep ⟨pUe, pUp, pUn⟩ ?_ ?_ <;> simp [*]
  have pV₂ : PosAt P C c₂ 140265 140266 pV := by
    refine PosAt.keep ⟨pVe, pVp, pVn⟩ ?_ ?_ <;> simp [*]
  have q62 : c₂.nreg 140262 = p := by
    simp_all
  -- the three height bits
  have hEqStep : ∀ (c₀ : Config) (a b dst : ℕ) (ya yb : ℝ), WordsBounded W c₀ →
      ShEnv P W H C z σ c₀ → 140311 ≤ dst → dst < 140314 → HRecS P c₀ a ya C.radius →
      HRecS P c₀ b yb C.radius →
      ∃ c₁ k, Exec P W (hEq a b dst) c₀ c₁ k ∧ k ≤ 20 ∧ BitIs c₁ dst (ya = yb) ∧
        (∀ r, r ≠ dst → c₁.nreg r = c₀.nreg r) ∧ FrameB Bedge c₀ c₁ ∧ ShEnv P W H C z σ c₁ :=
    fun c₀ a b dst ya yb hw₀ E₀ hd1 hd2 hA hB => by
      obtain ⟨c₁, k, ex, hk, bt, hc⟩ := hEq_exec E₀.hG (by omega) c₀ hw₀ (dst := dst) E₀.k1 C.radius_pos hA hB
      have fr : FrameB Bedge c₀ c₁ := by
        rw [hc]; exact frameB_upd c₀ _ (by simp [Bedge]; omega)
      exact ⟨c₁, k, ex, hk, bt, (fun r hr => by rw [hc]; simp [hr]), fr, E₀.frame fr Bedge_env⟩
  obtain ⟨c₃, k₃, e₃, hk₃, b11, kp₃, fe₃, E₃⟩ := hEqStep c₂ 140274 140285 140311 _ _ e₂.wb_right
    (E₁.frame fe₂ Bedge_env) le_rfl (by norm_num) rU₂.2.1 rV₂.2.1
  have rU₃ := rU₂.keep fun r h1 h2 => at_index kp₃ r
  obtain ⟨c₄, k₄, e₄, hk₄, b12, kp₄, fe₄, E₄⟩ := hEqStep c₃ 140234 140274 140312 _ _ e₃.wb_right
    E₃ (by norm_num) (by norm_num) E₃.oy rU₃.2.1
  have rV₄ := (rV₂.keep fun r h1 h2 => at_index kp₃ r).keep fun r h1 h2 => at_index kp₄ r
  obtain ⟨c₅, k₅, e₅, hk₅, b13, kp₅, fe₅, E₅⟩ := hEqStep c₄ 140234 140285 140313 _ _ e₄.wb_right
    E₄ (by norm_num) (by norm_num) E₄.oy rV₄.2.1
  have rU₅ := (rU₃.keep fun r h1 h2 => at_index kp₄ r).keep fun r h1 h2 => at_index kp₅ r
  have rV₅ := rV₄.keep fun r h1 h2 => at_index kp₅ r
  have kk : AgreeOnBand 140262 140270 c₅.nreg c₂.nreg := fun r h1 h2 => by
    frame_simp [kp₅, kp₄, kp₃]
  have pU₅ := pU₂.keep (at_index kk _) (at_index kk _)
  have pV₅ := pV₂.keep (at_index kk _) (at_index kk _)
  have b11' :=
    (b11.of_eq (at_index kp₄ _)).of_eq (at_index kp₅ _)
  have b12' := b12.of_eq (at_index kp₅ _)
  have hA₅ : c₅.nreg ALLOC = c.nreg ALLOC := by
    frame_simp [kp₅, kp₄, kp₃, hA₂]
  have fe := (((fe₁.trans fe₂).trans fe₃).trans fe₄).trans fe₅
  have w₅ := e₅.wb_right
  have hpre : ∀ {s : Stmt} {c' : Config} {k : ℕ}, Exec P W s c₅ c' k →
      Exec P W (ptLoad 140263 140264 140270 ;; ptLoad 140265 140266 140281 ;; hEq 140274 140285 140311 ;; hEq 140234 140274 140312 ;; hEq 140234 140285 140313 ;; s) c c' (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k))))) :=
    fun ex => e₁ ;; e₂ ;; e₃ ;; e₄ ;; e₅ ;; ex
  unfold edgeH
  by_cases t11 : c₅.nreg 140311 < c₅.nreg K1
  · 
    obtain ⟨c', k, ex, hk, ca, f⟩ := neTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ (by frame_simp [kk, q62]) geo (fun h => by have := b11'.2.2 h; grind [E₅.k1]) b12' b13
      hz (by rw [hA₅]; omega)
    exact ⟨c', _, hpre (.ifLtN_true t11 ex), by omega, ca, fe.trans f⟩
  · 
    obtain ⟨c', k, ex, hk, ca, f⟩ := eqTree_exec c₅ w₅ E₅ rU₅ rV₅ pU₅ pV₅ (b11'.2.1 (by have := b11'.1; rw [E₅.k1] at t11; omega)) b12' hz
    exact ⟨c', _, hpre (.ifLtN_false t11 ex), by omega, ca, fe.trans f⟩

end

end ShootCut

end Chazelle.Core
