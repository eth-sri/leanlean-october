module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShotListCut
public import Chazelle.Core.ShotListFrame

/-!
# Shooting at a list of arcs with holes, part 4: the cutting block

`cutB R ℓ`: the eight key comparisons (`kltSeq`), the correction of `a < b` by `offCmp` for two
interior positions of one edge (`offB`), the six tests of `cutK` (compiled formulas, `formB`)
and the selection (`selB`).  `cutB_exec`: the pieces of the arc of level `ℓ` outside its hole
(`cut1`), or the arc itself when the hole is absent, in the registers of the next level.
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## The math of the bits -/

/-- A vertex position is normalised. -/
theorem normPos_vtx (M : Model) (Q : Polygon) (n x : ℕ) : NormPos M Q n ⟨x, 0⟩ := by
  refine ⟨⟨?_, ?_, by simp⟩, Or.inl rfl⟩ <;> simp [Model.param]

theorem key_vtx (M : Model) (Q : Polygon) (x : ℕ) : M.key Q ⟨x, 0⟩ = x := by
  simp [Model.key, Model.param]

/-- **Lexicographic comparison of normalised positions** (not both inside one edge). -/
theorem lexLt_iff_key {M : Model} {Q : Polygon} {n : ℕ} {u v : WPos} (hu : NormPos M Q n u)
    (hv : NormPos M Q n v) (hne : ¬ (u.edge = v.edge ∧ 0 < u.hgt ∧ 0 < v.hgt)) :
    LexLt u.edge (ibv u.hgt) v.edge (ibv v.hgt) ↔ M.key Q u < M.key Q v := by
  rw [key_lt_iff hu hv hne]; rfl

/-- The test `sideInArc` as a formula of three comparison bits. -/
def siaF (uw uk kw : ℕ) : BF :=
  .or (.and (.and (.var uw) (.var uk)) (.var kw)) (.and (.not (.var uw)) (.or (.var uk) (.var kw)))

theorem siaF_size (uw uk kw : ℕ) : (siaF uw uk kw).size = 12 := rfl

/-- The test `x = a` from the two comparison bits. -/
def eqF (xa ax : ℕ) : BF := .and (.not (.var xa)) (.not (.var ax))

theorem eqF_size (xa ax : ℕ) : (eqF xa ax).size = 5 := rfl

theorem siaF_eval {c : Config} {uw uk kw : ℕ} {u w k : ℝ} (h1 : BitIs c uw (u < w))
    (h2 : BitIs c uk (u < k)) (h3 : BitIs c kw (k < w)) :
    (siaF uw uk kw).eval (fun r => decide (c.nreg r = 1)) = true ↔ sideInArc u w k := by
  obtain ⟨-, i1⟩ := h1
  obtain ⟨-, i2⟩ := h2
  obtain ⟨-, i3⟩ := h3
  unfold siaF sideInArc
  simp only [BF.eval, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, i1, i2, i3]
  grind

theorem eqF_eval {c : Config} {xa ax : ℕ} {x a : ℝ} (h1 : BitIs c xa (x < a))
    (h2 : BitIs c ax (a < x)) :
    (eqF xa ax).eval (fun r => decide (c.nreg r = 1)) = true ↔ x = a := by
  obtain ⟨-, i1⟩ := h1
  obtain ⟨-, i2⟩ := h2
  unfold eqF
  simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, i1, i2]
  grind

/-! ## The blocks -/

section
variable (R ℓ : ℕ)
include R ℓ
/-- The arc registers of level `ℓ`: `rL R ℓ … rL R ℓ + 3`. -/
def rL : ℕ := R + 40 + 10 * ℓ

/-- The eight comparisons of level `ℓ`: `a < b`, `a < x`, `x < a`, `a < y`, `y < b`, `x < b`,
`x < y`, `y < x` into `R + 100 … R + 107`. -/
def cmpList : List Cmp :=
  let L := rL R ℓ
  let hx := R + 10 + 2 * ℓ
  let hy := R + 11 + 2 * ℓ
  let z := R + 30
  [(L, L + 1, L + 2, L + 3, R + 100), (L, L + 1, hx, z, R + 101), (hx, z, L, L + 1, R + 102),
    (L, L + 1, hy, z, R + 103), (hy, z, L + 2, L + 3, R + 104), (hx, z, L + 2, L + 3, R + 105),
    (hx, z, hy, z, R + 106), (hy, z, hx, z, R + 107)]

/-- `a < b` by `offCmp` when `a`, `b` are interior positions of one edge. -/
def offCall : Stmt :=
  let L := rL R ℓ
  .seq (block [.copyN 50200 (R + 34), .copyN 50201 L, .copyN 50202 (L + 1), .copyN 50203 (L + 2),
      .copyN 50204 (L + 3), .copyN 50205 (R + 30)])
    (.seq offCmp (block [.copyN (R + 100) 50210]))

/-- The correction of the bit `a < b`. -/
def offB : Stmt :=
  let L := rL R ℓ
  .ifLtN L (L + 2) .skip (.ifLtN (L + 2) L .skip
    (.ifLtN (R + 30) (L + 1) (.ifLtN (R + 30) (L + 3) (offCall R ℓ) .skip) .skip))


end

/-- The six tests of `cutK` into `R + 120`, `R + 140`, …, `R + 220`. -/
def formB (R : ℕ) : Stmt :=
  .seq ((siaF (R + 106) (R + 102) (R + 103)).compile (R + 120))
    (.seq ((siaF (R + 100) (R + 103) (R + 104)).compile (R + 140))
      (.seq ((siaF (R + 104) (R + 107) (R + 105)).compile (R + 160))
        (.seq ((siaF (R + 100) (R + 101) (R + 105)).compile (R + 180))
          (.seq ((siaF (R + 105) (R + 106) (R + 104)).compile (R + 200))
            ((eqF (R + 102) (R + 101)).compile (R + 220))))))

/-- **The cutting block of level `ℓ`.** -/
def cutB (R ℓ : ℕ) : Stmt :=
  let L := rL R ℓ
  .seq (kltSeq (R + 30) (cmpList R ℓ)) (.seq (offB R ℓ) (.seq (formB R)
    (selB L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) (L + 10) (L + 4) (L + 8) (R + 30 + ℓ)
      (R + 9) (R + 120) (R + 140) (R + 160) (R + 180) (R + 200) (R + 220))))


/-! ## Execution: the correction of `a < b` -/

/-- **The caller's register block** `R … R + 299` lies in one band, which is neither band `0`
(the allocator) nor a band of the kernels or the oracles (`oracleBands`). -/
def RegsOK (R : ℕ) : Prop :=
  R % 10000 + 300 ≤ 10000 ∧ R / 10000 ≠ 0 ∧ R / 10000 ≠ 1 ∧ R / 10000 ≠ 3 ∧ R / 10000 ≠ 4 ∧
    R / 10000 ≠ 5 ∧ R / 10000 ≠ 6 ∧ R / 10000 ≠ 12 ∧ R / 10000 ≠ 13 ∧ R / 10000 ≠ 14 ∧
    R / 10000 ≠ 15

theorem bprim_R {R : ℕ} (hR : RegsOK R) {i : ℕ} (hi : i < 300) : Bprim (R + i) = false := by
  core_grind

/-- The registers written by `offB`. -/
def Boff (R r : ℕ) : Bool := r == R + 100 || Bprim r || decide (50200 ≤ r ∧ r < 50210)

theorem wr_offCmp' (R : ℕ) : wr (Boff R) offCmp = true :=
  wr_mono wr_offCmp (fun r hr => by core_grind)

theorem wr_offCall (R ℓ : ℕ) : wr (Boff R) (offCall R ℓ) = true := by
  have h := wr_offCmp' R
  simp_all [offCall, wr, block, wrOK, Boff]

theorem wr_offB (R ℓ : ℕ) : wr (Boff R) (offB R ℓ) = true := by
  have h := wr_offCall R ℓ
  simp_all [offB, wr]

section
variable {P : Polygon} {W : ℕ}
/-- Loading the inputs of `offCmp`. -/
theorem offLoad_exec (c : Config) (hw : WordsBounded W c) (cd L z : ℕ)
    (hLr : L + 4 ≤ 50200 ∨ 50206 ≤ L)
    (hz : z < 50200 ∨ 50206 ≤ z) :
    ∃ c₁ k₁, Exec P W
      (block [.copyN 50200 cd, .copyN 50201 L, .copyN 50202 (L + 1), .copyN 50203 (L + 2),
        .copyN 50204 (L + 3), .copyN 50205 z]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 50200 = c.nreg cd ∧ c₁.nreg 50201 = c.nreg L ∧
      c₁.nreg 50202 = c.nreg (L + 1) ∧ c₁.nreg 50203 = c.nreg (L + 2) ∧
      c₁.nreg 50204 = c.nreg (L + 3) ∧ c₁.nreg 50205 = c.nreg z ∧
      (∀ r, ¬ (50200 ≤ r ∧ r < 50206) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.nreg ALLOC = c.nreg ALLOC := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, ?_⟩ <;> (try unfold ALLOC) <;> rsimp

/-- **The correction of `a < b`**: afterwards the bit `R + 100` is the key order of `a`, `b`. -/
theorem offB_exec {R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (R + 34)))
    (hC : ChainDescAt c.nmem (c.nreg (R + 34)) (Qof P) H C) (hm : 2 * C.m + 7 ≤ W)
    (hroom : c.nreg ALLOC + 11000 ≤ W) (hz : c.nreg (R + 30) = 0)
    (ha : NormPos (chainModel C) (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos (chainModel C) (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hae : c.nreg (rL R ℓ) < (chainModel C).W.n) (hbe : c.nreg (rL R ℓ + 2) < (chainModel C).W.n)
    (hbit : BitIs c (R + 100) (LexLt (c.nreg (rL R ℓ)) (ibv (c.nreg (rL R ℓ + 1)))
      (c.nreg (rL R ℓ + 2)) (ibv (c.nreg (rL R ℓ + 3))))) :
    ∃ c' k, Exec P W (offB R ℓ) c c' k ∧ k ≤ 11100 ∧
      BitIs c' (R + 100) ((chainModel C).key (Qof P) (posR c (rL R ℓ, rL R ℓ + 1)) <
        (chainModel C).key (Qof P) (posR c (rL R ℓ + 2, rL R ℓ + 3))) ∧
      FrameB (Boff R) c c' := by
  set L := rL R ℓ with hL
  set M := chainModel C with hM
  have hLd : L = R + 40 + 10 * ℓ := rfl
  have hne_of : ¬ (c.nreg L = c.nreg (L + 2) ∧ 0 < c.nreg (L + 1) ∧ 0 < c.nreg (L + 3)) →
      BitIs c (R + 100) (M.key (Qof P) (posR c (L, L + 1)) <
        M.key (Qof P) (posR c (L + 2, L + 3))) := fun hne => by
    have := lexLt_iff_key ha hb hne
    grind [posR]
  have wk := wr_offB R ℓ
  unfold offB
  simp only
  by_cases h1 : c.nreg L < c.nreg (L + 2)
  · have ex : Exec P W (offB R ℓ) c c _ := .ifLtN_true h1 (.skip hw)
    exact ⟨c, _, ex, by omega, hne_of (by omega), exec_frameB ex wk⟩
  by_cases h2 : c.nreg (L + 2) < c.nreg L
  · have ex : Exec P W (offB R ℓ) c c _ := .ifLtN_false h1 (.ifLtN_true h2 (.skip hw))
    exact ⟨c, _, ex, by omega, hne_of (by omega), exec_frameB ex wk⟩
  by_cases h3 : c.nreg (R + 30) < c.nreg (L + 1)
  swap
  · have ex : Exec P W (offB R ℓ) c c _ :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_false h3 (.skip hw)))
    exact ⟨c, _, ex, by omega, hne_of (by omega), exec_frameB ex wk⟩
  by_cases h4 : c.nreg (R + 30) < c.nreg (L + 3)
  swap
  · have ex : Exec P W (offB R ℓ) c c _ :=
      .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_false h4 (.skip hw))))
    exact ⟨c, _, ex, by omega, hne_of (by omega), exec_frameB ex wk⟩
  -- two interior positions of one edge: `offCmp`
  have hR' := hR; unfold RegsOK at hR'
  obtain ⟨c₁, k₁, e₁, hk₁, p1, p2, p3, p4, p5, p6, pr, pm, pal⟩ :=
    offLoad_exec (P := P) c hw (R + 34) L (R + 30) (by omega) (by omega)
  rw [hz] at p6
  have w₁ := e₁.wb_right
  have hn0 : 0 < M.W.n := by
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := offCmp_meets P W c₁ w₁
    ⟨hG, hHW, by grind, H, C, by grind,
      by grind, by grind, by grind,
      by rw [p2, p3]; exact ha.1, by rw [p4, p5]; exact hb.1,
      fun h => by omega, fun h => by omega, hm⟩
    (by grind)
  replace hk₂ : k₂ ≤ 11000 := hk₂
  obtain ⟨o1, -⟩ := post₂ H C (by grind)
  
  have e₃ := Exec.copyN (P := P) e₂.wb_right (R + 100) 50210
  have ex : Exec P W (offB R ℓ) c _ _ :=
    .ifLtN_false h1 (.ifLtN_false h2 (.ifLtN_true h3 (.ifLtN_true h4
      (.seq e₁ (.seq e₂ (Exec.block_cons e₃ (Exec.block_nil e₃.wb_right)))))))
  refine ⟨_, _, ex, by omega, ⟨?_, ?_⟩, exec_frameB ex wk⟩
  · simp only [upd_same]; exact o1.1
  · simp only [upd_same]
    rw [o1.2, p2, p3, p4, p5, p6]
    have kx := ha.1.1
    have ky := hb.1.1
    simp only [posR] at kx ky ⊢
    rw [Nat.cast_zero]
    exact (key_lt_iff_off kx ky).symm


/-! ## Execution: the six tests -/


end

theorem bitIs_toNat {c : Config} {d : ℕ} {b : Bool} {p : Prop} (hv : c.nreg d = b.toNat)
    (hb : b = true ↔ p) : BitIs c d p := by
  grind [Chazelle.Core.SweepPrim.BitIs]

section
variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
include hw hW
/-- A compiled `sideInArc` test. -/
theorem siaF_exec
    {uw uk kw d : ℕ} (h1 : uw < d) (h2 : uk < d) (h3 : kw < d) {u w k : ℝ}
    (b1 : BitIs c uw (u < w)) (b2 : BitIs c uk (u < k)) (b3 : BitIs c kw (k < w)) :
    ∃ c' k', Exec P W ((siaF uw uk kw).compile d) c c' k' ∧ k' ≤ 48 ∧
      BitIs c' d (sideInArc u w k) ∧ FrameB ((siaF uw uk kw).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (siaF uw uk kw) d c hw
    ⟨⟨⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩, ⟨h3, b3.1⟩⟩, ⟨⟨h1, b1.1⟩, ⟨⟨h2, b2.1⟩, ⟨h3, b3.1⟩⟩⟩⟩
  exact ⟨c', k', ex, by grind [siaF_size], bitIs_toNat hv (siaF_eval b1 b2 b3), hf⟩

/-- The compiled test `x = a`. -/
theorem eqF_exec
    {xa ax d : ℕ} (h1 : xa < d) (h2 : ax < d) {x a : ℝ} (b1 : BitIs c xa (x < a))
    (b2 : BitIs c ax (a < x)) :
    ∃ c' k', Exec P W ((eqF xa ax).compile d) c c' k' ∧ k' ≤ 20 ∧ BitIs c' d (x = a) ∧
      FrameB ((eqF xa ax).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (eqF xa ax) d c hw
    ⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩
  exact ⟨c', k', ex, by grind [eqF_size], bitIs_toNat hv (eqF_eval b1 b2), hf⟩


end

/-- The registers written by `formB`. -/
def Bform (R r : ℕ) : Bool := decide (R + 120 ≤ r ∧ r < R + 240)

theorem bitIs_keep {c c' : Config} {B : ℕ → Bool} {r : ℕ} {p : Prop} (h : BitIs c r p)
    (hf : FrameB B c c') (hr : B r = false) : BitIs c' r p := h.of_eq (hf.1 r hr)

theorem wset_lt {f : BF} {d r : ℕ} (h : r < d) : f.wset d r = false := by
  core_grind

/-- **The six tests of `cutK`** from the eight comparison bits. -/
theorem formB_exec {P : Polygon} {W : ℕ} (R : ℕ) (c : Config) (hw : WordsBounded W c)
    (hW : 2 ≤ W) {ka kb kx ky : ℝ}
    (bab : BitIs c (R + 100) (ka < kb)) (bax : BitIs c (R + 101) (ka < kx))
    (bxa : BitIs c (R + 102) (kx < ka)) (bay : BitIs c (R + 103) (ka < ky))
    (byb : BitIs c (R + 104) (ky < kb)) (bxb : BitIs c (R + 105) (kx < kb))
    (bxy : BitIs c (R + 106) (kx < ky)) (byx : BitIs c (R + 107) (ky < kx)) :
    ∃ c' k, Exec P W (formB R) c c' k ∧ k ≤ 300 ∧
      BitIs c' (R + 120) (sideInArc kx ky ka) ∧ BitIs c' (R + 140) (sideInArc ka kb ky) ∧
      BitIs c' (R + 160) (sideInArc ky kb kx) ∧ BitIs c' (R + 180) (sideInArc ka kb kx) ∧
      BitIs c' (R + 200) (sideInArc kx kb ky) ∧ BitIs c' (R + 220) (kx = ka) ∧
      FrameB (Bform R) c c' := by
  have fr : ∀ {B : ℕ → Bool} {cc cc' : Config}, FrameB B cc cc' →
      (∀ r, B r = true → R + 120 ≤ r ∧ r < R + 240) → FrameB (Bform R) cc cc' := fun h h1 =>
    frameB_mono h (fun r hr => by
      simp_all [Bform, decide_eq_true_eq])
  have kp : ∀ {B : ℕ → Bool} {cc cc' : Config} {r : ℕ} {p : Prop}, BitIs cc r p →
      FrameB B cc cc' → B r = false → BitIs cc' r p := fun h hf hr => bitIs_keep h hf hr
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := siaF_exec (P := P) c hw hW (d := R + 120)
    (by omega) (by omega) (by omega) bxy bxa bay
  have k1 := fun {r : ℕ} {p : Prop} (h : BitIs c r p) (hr : r < R + 120) =>
    kp h f₁ (wset_lt hr)
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := siaF_exec (P := P) c₁ e₁.wb_right hW (d := R + 140)
    (by omega) (by omega) (by omega) (k1 bab (by omega)) (k1 bay (by omega)) (k1 byb (by omega))
  have k2 := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : r < R + 140) =>
    kp h f₂ (wset_lt hr)
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := siaF_exec (P := P) c₂ e₂.wb_right hW (d := R + 160)
    (by omega) (by omega) (by omega) (k2 (k1 byb (by omega)) (by omega))
    (k2 (k1 byx (by omega)) (by omega)) (k2 (k1 bxb (by omega)) (by omega))
  have k3 := fun {r : ℕ} {p : Prop} (h : BitIs c₂ r p) (hr : r < R + 160) =>
    kp h f₃ (wset_lt hr)
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := siaF_exec (P := P) c₃ e₃.wb_right hW (d := R + 180)
    (by omega) (by omega) (by omega) (k3 (k2 (k1 bab (by omega)) (by omega)) (by omega))
    (k3 (k2 (k1 bax (by omega)) (by omega)) (by omega))
    (k3 (k2 (k1 bxb (by omega)) (by omega)) (by omega))
  have k4 := fun {r : ℕ} {p : Prop} (h : BitIs c₃ r p) (hr : r < R + 180) =>
    kp h f₄ (wset_lt hr)
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅⟩ := siaF_exec (P := P) c₄ e₄.wb_right hW (d := R + 200)
    (by omega) (by omega) (by omega)
    (k4 (k3 (k2 (k1 bxb (by omega)) (by omega)) (by omega)) (by omega))
    (k4 (k3 (k2 (k1 bxy (by omega)) (by omega)) (by omega)) (by omega))
    (k4 (k3 (k2 (k1 byb (by omega)) (by omega)) (by omega)) (by omega))
  have k5 := fun {r : ℕ} {p : Prop} (h : BitIs c₄ r p) (hr : r < R + 200) =>
    kp h f₅ (wset_lt hr)
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, f₆⟩ := eqF_exec (P := P) c₅ e₅.wb_right hW (d := R + 220)
    (by omega) (by omega)
    (k5 (k4 (k3 (k2 (k1 bxa (by omega)) (by omega)) (by omega)) (by omega)) (by omega))
    (k5 (k4 (k3 (k2 (k1 bax (by omega)) (by omega)) (by omega)) (by omega)) (by omega))
  have k6 := fun {r : ℕ} {p : Prop} (h : BitIs c₅ r p) (hr : r < R + 220) =>
    kp h f₆ (wset_lt hr)
  have fz : ∀ {f : BF} {d : ℕ} {cc cc' : Config}, FrameB (f.wset d) cc cc' → R + 120 ≤ d →
      d + f.size < R + 240 → FrameB (Bform R) cc cc' := fun h h1 h2 => fr h (fun r hr => by
    simp only [SweepPrim.BF.wset, decide_eq_true_eq] at hr; omega)
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega,
    k6 (k5 (k4 (k3 (k2 v₁ (by omega)) (by omega)) (by omega)) (by omega)) (by omega),
    k6 (k5 (k4 (k3 v₂ (by omega)) (by omega)) (by omega)) (by omega),
    k6 (k5 (k4 v₃ (by omega)) (by omega)) (by omega), k6 (k5 v₄ (by omega)) (by omega),
    k6 v₅ (by omega), v₆, ?_⟩
  exact (fz f₁ (by omega) (by grind [siaF_size])).trans
    ((fz f₂ (by omega) (by grind [siaF_size])).trans
    ((fz f₃ (by omega) (by grind [siaF_size])).trans
    ((fz f₄ (by omega) (by grind [siaF_size])).trans
    ((fz f₅ (by omega) (by grind [siaF_size])).trans
    (fz f₆ (by omega) (by grind [eqF_size]))))))


/-! ## The cutting block -/

/-- The registers written by `cutB`. -/
def Bcut (R ℓ r : ℕ) : Bool :=
  Bouts (cmpList R ℓ) r || Boff R r || Bform R r || decide (rL R ℓ + 4 ≤ r ∧ r < rL R ℓ + 14)

/-- The pieces of the arc of level `ℓ`: `cut1` if the hole is present, else the arc. -/
noncomputable def levPieces (M : Model) (Q : Polygon) (hp : Prop) [Decidable hp] (a b : WPos)
    (x y : ℕ) : List (WPos × WPos) :=
  if hp then cut1 (M.key Q) a b ⟨x, 0⟩ ⟨y, 0⟩ else [(a, b)]

theorem cmpList_ok {R ℓ : ℕ} (hℓ : ℓ ≤ 2) : CmpOK (R + 30) (cmpList R ℓ) := by
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · simp_all [cmpOuts, cmpList, rL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  · simp [cmpOuts, cmpList]
  · simp only [cmpList, rL, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [cmpOuts, cmpList, rL, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      omega

/-- **The cutting block of level `ℓ`**: the pieces `levPieces` in the registers of the next
level (`rL R ℓ + 10 …`, `rL R ℓ + 4 …`, their number in `rL R ℓ + 8`). -/
theorem cutB_exec {P : Polygon} {W R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
    (hw : WordsBounded W c) (hW : 2 ≤ W) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W)
    {H : Host} {C : Chain} (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (R + 34)))
    (hC : ChainDescAt c.nmem (c.nreg (R + 34)) (Qof P) H C) (hm : 2 * C.m + 7 ≤ W)
    (hroom : c.nreg ALLOC + 11000 ≤ W) (hz : c.nreg (R + 30) = 0)
    (ha : NormPos (chainModel C) (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos (chainModel C) (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hae : c.nreg (rL R ℓ) < (chainModel C).W.n)
    (hbe : c.nreg (rL R ℓ + 2) < (chainModel C).W.n) :
    ∃ c' k, Exec P W (cutB R ℓ) c c' k ∧ k ≤ 11500 ∧
      PiecesAt c' (rL R ℓ + 10) (rL R ℓ + 4) (rL R ℓ + 8)
        (levPieces (chainModel C) (Qof P) (c.nreg (R + 30 + ℓ) < c.nreg (R + 9))
          (posR c (rL R ℓ, rL R ℓ + 1)) (posR c (rL R ℓ + 2, rL R ℓ + 3))
          (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ))) ∧
      FrameB (Bcut R ℓ) c c' := by
  set L := rL R ℓ with hL
  have hLd : L = R + 40 + 10 * ℓ := rfl
  set M := chainModel C with hM
  set Q := Qof P
  set a := posR c (L, L + 1) with ha_def
  set b := posR c (L + 2, L + 3) with hb_def
  set x := c.nreg (R + 10 + 2 * ℓ)
  set y := c.nreg (R + 11 + 2 * ℓ)
  have hX : NormPos M Q P.n ⟨x, 0⟩ := normPos_vtx M Q P.n x
  have hY : NormPos M Q P.n ⟨y, 0⟩ := normPos_vtx M Q P.n y
  -- the comparisons
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltSeq_exec (P := P) (by omega) (R + 30) (cmpList R ℓ) c hw
    hz (cmpList_ok hℓ)
  have in₁ : ∀ r, (r < R + 100 ∨ R + 108 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by
      simp only [Bouts, cmpOuts, cmpList, List.map_cons, List.map_nil, List.contains_eq_mem,
        List.mem_cons, List.not_mem_nil, or_false, decide_eq_false_iff_not, not_or]
      omega)
  have mem : ∀ t ∈ cmpList R ℓ, BitIs c₁ t.2.2.2.2 (LexLt (c.nreg t.1) (ibv (c.nreg t.2.1))
      (c.nreg t.2.2.1) (ibv (c.nreg t.2.2.2.1))) := b₁
  simp only [cmpList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mem
  obtain ⟨bab, bax, bxa, bay, byb, bxb, bxy, byx⟩ := mem
  rw [hz] at bax bxa bay byb bxb bxy byx
  -- the key order
  have vtx : ∀ (u v : WPos), NormPos M Q P.n u → NormPos M Q P.n v → (u.hgt = 0 ∨ v.hgt = 0) →
      (LexLt u.edge (ibv u.hgt) v.edge (ibv v.hgt) ↔ M.key Q u < M.key Q v) :=
    fun u v hu hv h0 => lexLt_iff_key hu hv (by omega)
  have kax : BitIs c₁ (R + 101) (M.key Q a < M.key Q ⟨x, 0⟩) :=
    ⟨bax.1, bax.2.trans (vtx _ _ ha hX (Or.inr rfl))⟩
  have kxa : BitIs c₁ (R + 102) (M.key Q ⟨x, 0⟩ < M.key Q a) :=
    ⟨bxa.1, bxa.2.trans (vtx _ _ hX ha (Or.inl rfl))⟩
  have kay : BitIs c₁ (R + 103) (M.key Q a < M.key Q ⟨y, 0⟩) :=
    ⟨bay.1, bay.2.trans (vtx _ _ ha hY (Or.inr rfl))⟩
  have kyb : BitIs c₁ (R + 104) (M.key Q ⟨y, 0⟩ < M.key Q b) :=
    ⟨byb.1, byb.2.trans (vtx _ _ hY hb (Or.inl rfl))⟩
  have kxb : BitIs c₁ (R + 105) (M.key Q ⟨x, 0⟩ < M.key Q b) :=
    ⟨bxb.1, bxb.2.trans (vtx _ _ hX hb (Or.inl rfl))⟩
  have kxy : BitIs c₁ (R + 106) (M.key Q ⟨x, 0⟩ < M.key Q ⟨y, 0⟩) :=
    ⟨bxy.1, bxy.2.trans (vtx _ _ hX hY (Or.inl rfl))⟩
  have kyx : BitIs c₁ (R + 107) (M.key Q ⟨y, 0⟩ < M.key Q ⟨x, 0⟩) :=
    ⟨byx.1, byx.2.trans (vtx _ _ hY hX (Or.inl rfl))⟩
  -- the correction of `a < b`
  have g34 := in₁ (R + 34) (by omega)
  have g30 := in₁ (R + 30) (by omega)
  have gL0 : c₁.nreg L = c.nreg L := in₁ _ (by omega)
  have gL1 : c₁.nreg (L + 1) = c.nreg (L + 1) := in₁ _ (by omega)
  have gL2 : c₁.nreg (L + 2) = c.nreg (L + 2) := in₁ _ (by omega)
  have gL3 : c₁.nreg (L + 3) = c.nreg (L + 3) := in₁ _ (by omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := in₁ _ (by grind [ALLOC, RegsOK])
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
  have pa : posR c₁ (L, L + 1) = a := by
    grind [posR, WPos.mk.injEq]
  have pb : posR c₁ (L + 2, L + 3) = b := by
    grind [posR, WPos.mk.injEq]
  obtain ⟨c₂, k₂, e₂, hk₂, kab, f₂⟩ := offB_exec (P := P) hR hℓ c₁ e₁.wb_right hG hHW
    (H := H) (C := C) (by grind) (by grind) hm
    (by omega) (by rw [g30, hz]) (by grind) (by grind)
    (by grind) (by grind)
    (by grind)
  rw [pa, pb] at kab
  
  have o₂ : ∀ r, (R + 100 < r ∧ r < R + 300) → Boff R r = false := fun r hr => by
    have := bprim_R hR (i := r - R) (by omega)
    rw [show R + (r - R) = r by omega] at this
    unfold RegsOK at hR
    simp only [Boff, this, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not]
    omega
  have ks := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : R + 100 < r ∧ r < R + 300) =>
    bitIs_keep h f₂ (o₂ r hr)
  -- the six tests
  obtain ⟨c₃, k₃, e₃, hk₃, t1, t2, t3, t4, t5, t6, f₃⟩ := formB_exec (P := P) R c₂ e₂.wb_right
    hW kab (ks kax (by omega)) (ks kxa (by omega)) (ks kay (by omega)) (ks kyb (by omega))
    (ks kxb (by omega)) (ks kxy (by omega)) (ks kyx (by omega))
  -- registers of `c` read by the selection
  have gsel : ∀ r, (r < R + 100 ∧ bandOf r = bandOf r) → ¬ (50200 ≤ r ∧ r < 50210) →
      Bprim r = false → c₃.nreg r = c.nreg r := fun r hr h5 hp => by
    rw [f₃.1 r (by grind [Bform, decide_eq_false_iff_not]),
      f₂.1 r (by simp only [Boff, hp, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
        decide_eq_false_iff_not]; omega), in₁ r (Or.inl hr.1)]
  have gR : ∀ i, i < 100 → c₃.nreg (R + i) = c.nreg (R + i) := fun i hi => by
    have hp := bprim_R hR (i := i) (by omega)
    unfold RegsOK at hR
    exact gsel _ ⟨by omega, rfl⟩ (by omega) hp
  have gR' : ∀ r, R ≤ r → r < R + 100 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    have := gR (r - R) (by omega)
    rwa [show R + (r - R) = r by omega] at this
  have z3 : c₃.nreg (R + 30) = 0 := by grind
  obtain ⟨c₄, k₄, e₄, hk₄, pc₄, r₄, m₄, rr₄, rm₄, o₄⟩ := selB_exec (P := P) c₃ e₃.wb_right hW
    (L := L) (hx := R + 10 + 2 * ℓ) (hy := R + 11 + 2 * ℓ) (z := R + 30) (N := L + 10)
    (S := L + 4) (Cn := L + 8) (hpA := R + 30 + ℓ) (hpB := R + 9) (c1 := R + 120)
    (c2 := R + 140) (c3 := R + 160) (c4 := R + 180) (c5 := R + 200) (c6 := R + 220)
    (by intro e o ho; cases e <;> simp only [End.regs] <;> omega) (by omega) (by omega)
    (by omega) z3 t1.1 t2.1 t3.1 t4.1 t5.1 t6.1
  have ex : Exec P W (cutB R ℓ) c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, _, ex, by simp only [cmpList, List.length_cons, List.length_nil] at hk₁; omega,
    ?_, ?_⟩
  · -- the pieces
    have hsel : selPos c₃ L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) =
        fun tl => tl.map fun e => (End.val a b ⟨x, 0⟩ ⟨y, 0⟩ e.1, End.val a b ⟨x, 0⟩ ⟨y, 0⟩ e.2) := by
      funext tl
      unfold selPos
      congr 1
      funext e
      have ev : ∀ u : End, posR c₃ (End.regs L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) u) =
          End.val a b ⟨x, 0⟩ ⟨y, 0⟩ u := by
        intro u
        cases u <;> simp only [End.regs, End.val, posR, ha_def, hb_def, WPos.mk.injEq]
        · exact ⟨gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)⟩
        · exact ⟨gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)⟩
        · exact ⟨gR' _ (by omega) (by omega), z3⟩
        · exact ⟨gR' _ (by omega) (by omega), z3⟩
      rw [ev, ev]
    rw [hsel] at pc₄
    have hp3 : (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) ↔ (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) := by
      rw [gR' _ (by omega) (by omega), gR' _ (by omega) (by omega)]
    unfold levPieces
    by_cases hp : c.nreg (R + 30 + ℓ) < c.nreg (R + 9)
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = true := by
        grind
      rw [hd] at pc₄
      rw [ite_yes _ _ hp]
      unfold cut1
      rw [cutK_eq_selT (M.key Q a) (M.key Q b) (M.key Q ⟨x, 0⟩) (M.key Q ⟨y, 0⟩) a b ⟨x, 0⟩
        ⟨y, 0⟩ (c1 := decide (c₃.nreg (R + 120) = 1)) (c2 := decide (c₃.nreg (R + 140) = 1))
        (c3 := decide (c₃.nreg (R + 160) = 1)) (c4 := decide (c₃.nreg (R + 180) = 1))
        (c5 := decide (c₃.nreg (R + 200) = 1)) (c6 := decide (c₃.nreg (R + 220) = 1))
        (by rw [decide_eq_true_iff]; exact t1.2) (by rw [decide_eq_true_iff]; exact t2.2)
        (by rw [decide_eq_true_iff]; exact t3.2) (by rw [decide_eq_true_iff]; exact t4.2)
        (by rw [decide_eq_true_iff]; exact t5.2) (by rw [decide_eq_true_iff]; exact t6.2)]
      exact pc₄
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = false := by
        grind
      rw [hd] at pc₄
      rw [ite_no _ _ hp]
      exact pc₄
  · -- the frame
    have f₄ : FrameB (fun r => decide (L + 4 ≤ r ∧ r < L + 14)) c₃ c₄ :=
      ⟨fun r hr => r₄ r (by grind)
        (by grind)
        (by grind),
       fun r _ => by rw [rr₄], m₄, rm₄, o₄⟩
    have c1 : FrameB (Bcut R ℓ) c c₁ := frameB_mono f₁ (fun r hr => by simp [Bcut, hr])
    have c2 : FrameB (Bcut R ℓ) c₁ c₂ := frameB_mono f₂ (fun r hr => by simp [Bcut, hr])
    have c3 : FrameB (Bcut R ℓ) c₂ c₃ := frameB_mono f₃ (fun r hr => by simp [Bcut, hr])
    have c4 : FrameB (Bcut R ℓ) c₃ c₄ := frameB_mono f₄ (fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [Bcut, ← hL, hr])
    exact c1.trans (c2.trans (c3.trans c4))

end

end ShotList

end Chazelle.Core
