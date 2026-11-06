module

public import Chazelle.Core.GranPz
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-F, init part 2: the bit `pz` on the RAM

`pzStmt` decides, for the walk position `⟨e, h⟩` (`r110 = e`, `r111 = h`), whether its edge is
counted and its parameter is nonzero, into `r112` (`pz_exec`).  It reuses the host and index
routines of double identification (`NFLoc`): `chHead`, `chIdx`, `cntStmt`, `hostPt` (chain
model, via `chPts`, the two walk vertices of a tour edge) and `intIdx` (interior model), and
compares height-vertex indices (distinct heights, `GranPz`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

/-- The two host points of tour edge `r56` into `lr 40` and `lr 43` (`chGeneral` without the
comparison). -/
def chPts : Stmt :=
  .seq chIdx (.seq cntStmt (.seq (block [.copyN 50087 50063, .copyN 50091 50078])
    (.seq hostPt (.seq (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048,
        .copyN 50091 50079])
      (.seq hostPt (block [.copyN 50043 50046, .copyN 50044 50047, .copyN 50045 50048]))))))

theorem wr_chPts : wr Bdir chPts = true := by decide

/-- **The two walk vertices of a tour edge.** -/
theorem chPts_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {H : Host} {Hh s m T b i : ℕ} (hH : HostAt c.nmem Hh H)
    (hwf : HostWF P.n H) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hNW : 2 * (H.pts P.n).length ≤ W) (hs : s < (H.pts P.n).length)
    (hmN : m < (H.pts P.n).length) (hT : T ≤ m) (hi : i < 2 * m)
    (h32 : c.nreg 50032 = 1) (h60 : c.nreg 50060 = Hh) (h52 : c.nreg 50052 = s)
    (h53 : c.nreg 50053 = m) (h54 : c.nreg 50054 = T) (h55 : c.nreg 50055 = b)
    (h56 : c.nreg 50056 = i) :
    ∃ c' k, Exec P W chPts c c' k ∧ k ≤ 70 * H.length + 500 ∧ FrameB Bdir c c' ∧
      ∃ sp₁ sp₂ : SymPt,
        (H.pts P.n)[(s + sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m))) %
          (H.pts P.n).length]? = some sp₁ ∧
        (H.pts P.n)[(s + sideE m (((if b = 1 then T else 2 * m - T) + i) % (2 * m) + 1)) %
          (H.pts P.n).length]? = some sp₂ ∧
        SymPtIn c' 50040 sp₁ ∧ SymPtIn c' 50043 sp₂ ∧ sp₁.Lt P.n ∧ sp₂.Lt P.n := by
  set N := (H.pts P.n).length with hNdef
  have hn0 : 0 < P.n := by have := hG.1.1; omega
  have hLt := hostWF_pts hwf hn0
  obtain ⟨c₁, k₁, e₁, hk₁, k78, k79, f₁⟩ := chIdx_exec (P := P) c hw h32 h53 h54 h55 h56 hi hT
    (by omega)
  have w₁ := e₁.wb_right
  set j := ((if b = 1 then T else 2 * m - T) + i) % (2 * m) with hj
  have hjm : j < 2 * m := Nat.mod_lt _ (by omega)
  have hk1 : sideE m j ≤ m := Chain.sideE_le (by omega)
  have hk2 : sideE m (j + 1) ≤ m := Chain.sideE_le (by omega)
  have g₁ := fun r (hr : Bl [50058, 50059, 50089, 50077, 50078, 50090, 50079] r = false) =>
    f₁.1 r hr
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    (by rwx [f₁.2.2.1]) ((g₁ _ (by decide)).trans h60) haW (by omega)
  have g₂ := fun r (hr : Bhost r = false) => f₂.1 r hr
  obtain ⟨c₃, k₃, e₃, hk₃, q87, q91, r₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 50087 50063, .copyN 50091 50078]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 50087 = N ∧ c₃.nreg 50091 = sideE m j ∧
      ∀ r, r ≠ 50087 → r ≠ 50091 → c₃.nreg r = c₂.nreg r := by
    have hw₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, by config_simp; exact n63, ?_, fun r h1 h2 => by simp [h1, h2]⟩
    config_simp; rw [g₂ _ (by decide), k78]
  have E₃ : HostEnv W Hh H.length c.nmem c₃ :=
    ⟨e₃.wb_right, by rw [r₃ _ (by omega) (by omega), E₂.h60],
      by rw [r₃ _ (by omega) (by omega), E₂.h61], by rw [r₃ _ (by omega) (by omega), E₂.h67],
      by rw [r₃ _ (by omega) (by omega), E₂.h68], by rw [r₃ _ (by omega) (by omega), E₂.h69],
      by rw [(exec_frameB e₃ (B := Bl [50087, 50091]) (by decide)).2.2.1, E₂.mem,
        f₁.2.2.1]⟩
  have s₃ : c₃.nreg 50052 = s := by
    rw [r₃ _ (by omega) (by omega), g₂ _ (by decide), g₁ _ (by decide), h52]
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₁, hsp₁, in₁⟩ := hostPt_exec (P := P) c₃ E₃ hH hwf
    (by omega) haW hNW s₃ q87 q91 hs (by omega)
  have g₄ := fun r (hr : Bhost r = false) => f₄.1 r hr
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, q91', r₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 50040 50046, .copyN 50041 50047, .copyN 50042 50048, .copyN 50091 50079])
      c₄ c₅ k₅ ∧ k₅ = 4 ∧ SymPtIn c₅ 50040 sp₁ ∧ c₅.nreg 50091 = sideE m (j + 1) ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50042 → r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    have hw₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp), ?_,
      fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩
    config_simp
    rw [g₄ _ (by decide), r₃ _ (by omega) (by omega), g₂ _ (by decide), k79]
  have E₅ : HostEnv W Hh H.length c.nmem c₅ :=
    ⟨e₅.wb_right, by rw [r₅ _ (by omega) (by omega) (by omega) (by omega), E₄.h60],
      by rw [r₅ _ (by omega) (by omega) (by omega) (by omega), E₄.h61],
      by rw [r₅ _ (by omega) (by omega) (by omega) (by omega), E₄.h67],
      by rw [r₅ _ (by omega) (by omega) (by omega) (by omega), E₄.h68],
      by rw [r₅ _ (by omega) (by omega) (by omega) (by omega), E₄.h69],
      by rw [(exec_frameB e₅ (B := Bl [50040, 50041, 50042, 50091]) (by decide)).2.2.1,
        E₄.mem]⟩
  have s₅ : c₅.nreg 50052 = s := by
    rw [r₅ _ (by omega) (by omega) (by omega) (by omega), g₄ _ (by decide), s₃]
  have n₅ : c₅.nreg 50087 = N := by
    rw [r₅ _ (by omega) (by omega) (by omega) (by omega), g₄ _ (by decide), q87]
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, sp₂, hsp₂, in₂⟩ := hostPt_exec (P := P) c₅ E₅ hH hwf
    (by omega) haW hNW s₅ n₅ q91' hs (by omega)
  have a₆ : SymPtIn c₆ 50040 sp₁ := symPtIn_copy a₅ (f₆.1 _ (by decide)) (f₆.1 _ (by decide))
    (f₆.1 _ (by decide))
  obtain ⟨c₇, k₇, e₇, hk₇, a₇, b₇⟩ : ∃ c₇ k₇, Exec P W
      (block [.copyN 50043 50046, .copyN 50044 50047, .copyN 50045 50048]) c₆ c₇ k₇ ∧ k₇ = 3 ∧
      SymPtIn c₇ 50040 sp₁ ∧ SymPtIn c₇ 50043 sp₂ := by
    have hw₆ := e₆.wb_right
    exec_block
    exact ⟨rfl, symPtIn_copy a₆ (by config_simp) (by config_simp) (by config_simp),
      symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp)⟩
  have l₁ : sp₁.Lt P.n := hLt _ (List.mem_of_getElem? hsp₁)
  have l₂ : sp₂.Lt P.n := hLt _ (List.mem_of_getElem? hsp₂)
  have ex : Exec P W chPts c c₇ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  exact ⟨c₇, _, ex, by omega, exec_frameB ex wr_chPts, sp₁, sp₂, hsp₁, hsp₂, a₇, b₇, l₁, l₂⟩

/-! ## Height-vertex indices and bit tests -/

/-- `dst := hv` of the symbolic point at `r` (`r50032 = 1`). -/
def hvS (dst r : ℕ) : Stmt :=
  .ifLtN r 50032 (.instr (.copyN dst (r + 1))) (.instr (.copyN dst (r + 2)))

theorem hvS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {dst r : ℕ}
    {sp : SymPt} (h32 : c.nreg 50032 = 1) (hsp : SymPtIn c r sp) :
    ∃ c' k, Exec P W (hvS dst r) c c' k ∧ k ≤ 3 ∧ c'.nreg dst = hv sp ∧
      (∀ q, q ≠ dst → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
  unfold hvS
  cases sp with
  | vtx i =>
    obtain ⟨h0, h1⟩ := hsp
    exact ⟨_, _, .ifLtN_true (by rwo [h0, h32]) (Exec.copyN hw _ _), by omega,
      by simp [upd, h1, hv], fun q hq => by simp [upd, hq], rfl⟩
  | onEdge e k =>
    obtain ⟨h0, -, h2⟩ := hsp
    exact ⟨_, _, .ifLtN_false (by rwo [h0, h32]) (Exec.copyN hw _ _), by omega,
      by simp [upd, h2, hv], fun q hq => by simp [upd, hq], rfl⟩

/-- `s` if `r a ≠ r b`, else `t`. -/
def ifNe (a b : ℕ) (s t : Stmt) : Stmt := .ifLtN a b s (.ifLtN b a s t)

theorem ifNe_ne {P : Polygon} {W : ℕ} {a b : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : c.nreg a ≠ c.nreg b) (e : Exec P W s c c' k) :
    ∃ k', Exec P W (ifNe a b s t) c c' k' ∧ k' ≤ k + 3 := by
  by_cases hlt : c.nreg a < c.nreg b
  · exact ⟨_, .ifLtN_true hlt e, by omega⟩
  · exact ⟨_, .ifLtN_false hlt (.ifLtN_true (by omega) e), by omega⟩

theorem ifNe_eq {P : Polygon} {W : ℕ} {a b : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : c.nreg a = c.nreg b) (e : Exec P W t c c' k) :
    Exec P W (ifNe a b s t) c c' (k + 2 + 2) :=
  .ifLtN_false (by omega) (.ifLtN_false (by omega) e)

/-- `r112 := 1` if `r111 ≠ 0`, `r ra ≠ r rb` and `r rc ≠ r rd` (else unchanged). -/
def tail3 (ra rb rc rd : ℕ) : Stmt :=
  .ifLtN 90111 90019 .skip (ifNe ra rb (ifNe rc rd (.instr (.constN 90112 1)) .skip) .skip)

theorem tail3_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (ra rb rc rd : ℕ) (h19 : c.nreg 90019 = 1) (h112 : c.nreg 90112 = 0) :
    ∃ c' k, Exec P W (tail3 ra rb rc rd) c c' k ∧ k ≤ 10 ∧
      c'.nreg 90112 ≤ 1 ∧
      (c'.nreg 90112 = 1 ↔ (c.nreg 90111 ≠ 0 ∧ c.nreg ra ≠ c.nreg rb ∧ c.nreg rc ≠ c.nreg rd)) ∧
      (∀ q, q ≠ 90112 → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
  unfold tail3
  by_cases h0 : c.nreg 90111 = 0
  · exact ⟨c, _, .ifLtN_true (by rwo [h19]) (.skip hw), by omega, by omega,
      by simp [h0, h112], fun _ _ => rfl, rfl⟩
  have e0 : ¬ c.nreg 90111 < c.nreg 90019 := by rwo [h19]
  by_cases h1 : c.nreg ra = c.nreg rb
  · exact ⟨c, _, .ifLtN_false e0 (ifNe_eq h1 (.skip hw)), by omega, by omega,
      by simp [h1, h112], fun _ _ => rfl, rfl⟩
  by_cases h2 : c.nreg rc = c.nreg rd
  · obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd (.instr (.constN 90112 1)) .skip)
      (t := .skip) h1 (ifNe_eq (P := P) (W := W) (s := .instr (.constN 90112 1)) h2 (.skip hw))
    exact ⟨c, _, .ifLtN_false e0 e', by omega, by omega, by simp [h2, h112],
      fun _ _ => rfl, rfl⟩
  · obtain ⟨k₁, e₁, hk₁⟩ := ifNe_ne (s := .instr (.constN 90112 1)) (t := .skip) h2
      (Exec.constN (P := P) hw 90112 1 hW)
    obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd (.instr (.constN 90112 1)) .skip)
      (t := .skip) h1 e₁
    exact ⟨_, _, .ifLtN_false e0 e', by omega, by simp [upd], by simp [upd, h0, h1, h2],
      fun q hq => by simp [upd, hq], rfl⟩

/-! ## The procedure -/

/-- The chain model (after `chHead`). -/
def pzChain : Stmt :=
  .ifLtN 50002 50081 (.instr (.constN 90112 0))
    (.seq (block [.subN 50056 50002 50081, .subN 50057 50056 50053])
      (.ifLtN 50057 50053
        (.seq chPts (.seq (hvS 90113 50040) (.seq (hvS 90114 50043)
          (.seq (block [.constN 90112 0, .subN 90115 90111 90019])
            (tail3 90113 90114 90115 90113)))))
        (.instr (.constN 90112 0))))

/-- The interior model. -/
def pzInt : Stmt :=
  .seq intIdx (.seq (block [.constN 90112 0, .subN 90115 90111 90019])
    (tail3 90115 50041 90115 50041))

/-- **The bit `pz`** of the position `⟨r110, r111⟩` into `r112`. -/
def pzStmt : Stmt :=
  .seq (.instr (.copyN 50002 90110)) (.ifLtN 90023 90019 (.seq chHead pzChain) pzInt)

/-- The registers `pzStmt` writes. -/
def Bpz (r : ℕ) : Bool := Bdir r || decide (r = 50002) || decide (90110 ≤ r ∧ r < 90120)

theorem wr_pzStmt : wr Bpz pzStmt = true := by decide

/-- The registers `chPts` writes. -/
def Bpts (r : ℕ) : Bool := decide (50040 ≤ r ∧ r < 50049) || decide (50056 ≤ r ∧ r < 50100)

theorem wr_chPts_fine : wr Bpts chPts = true := by decide

end

end Gran

end Chazelle.Core
