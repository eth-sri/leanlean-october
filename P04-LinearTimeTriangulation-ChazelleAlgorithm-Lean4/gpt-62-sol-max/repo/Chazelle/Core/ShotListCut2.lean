module

meta import Chazelle.Programs.RamEval

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
  split_ifs with h <;> tauto

theorem eqF_eval {c : Config} {xa ax : ℕ} {x a : ℝ} (h1 : BitIs c xa (x < a))
    (h2 : BitIs c ax (a < x)) :
    (eqF xa ax).eval (fun r => decide (c.nreg r = 1)) = true ↔ x = a := by
  obtain ⟨-, i1⟩ := h1
  obtain ⟨-, i2⟩ := h2
  unfold eqF
  simp only [BF.eval, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, i1, i2]
  constructor
  · rintro ⟨h, h'⟩; exact le_antisymm (not_lt.1 h') (not_lt.1 h)
  · rintro rfl; exact ⟨lt_irrefl _, lt_irrefl _⟩

/-! ## The blocks -/

/-- The arc registers of level `ℓ`: `rL R ℓ … rL R ℓ + 3`. -/
def rL (R ℓ : ℕ) : ℕ := R + 40 + 10 * ℓ

/-- The eight comparisons of level `ℓ`: `a < b`, `a < x`, `x < a`, `a < y`, `y < b`, `x < b`,
`x < y`, `y < x` into `R + 100 … R + 107`. -/
def cmpList (R ℓ : ℕ) : List Cmp :=
  let L := rL R ℓ
  let hx := R + 10 + 2 * ℓ
  let hy := R + 11 + 2 * ℓ
  let z := R + 30
  [(L, L + 1, L + 2, L + 3, R + 100), (L, L + 1, hx, z, R + 101), (hx, z, L, L + 1, R + 102),
    (L, L + 1, hy, z, R + 103), (hy, z, L + 2, L + 3, R + 104), (hx, z, L + 2, L + 3, R + 105),
    (hx, z, hy, z, R + 106), (hy, z, hx, z, R + 107)]

/-- `a < b` by `offCmp` when `a`, `b` are interior positions of one edge. -/
def offCall (R ℓ : ℕ) : Stmt :=
  let L := rL R ℓ
  .seq (block [.copyN 50200 (R + 34), .copyN 50201 L, .copyN 50202 (L + 1), .copyN 50203 (L + 2),
      .copyN 50204 (L + 3), .copyN 50205 (R + 30)])
    (.seq offCmp (block [.copyN (R + 100) 50210]))

/-- The correction of the bit `a < b`. -/
def offWith (R ℓ : ℕ) (sameEdge : Stmt) : Stmt :=
  let L := rL R ℓ
  .ifLtN L (L + 2) .skip (.ifLtN (L + 2) L .skip
    (.ifLtN (R + 30) (L + 1) (.ifLtN (R + 30) (L + 3) sameEdge .skip) .skip))

def offB (R ℓ : ℕ) : Stmt := offWith R ℓ (offCall R ℓ)

/-- The six tests of `cutK` into `R + 120`, `R + 140`, …, `R + 220`. -/
def formB (R : ℕ) : Stmt :=
  .seq ((siaF (R + 106) (R + 102) (R + 103)).compile (R + 120))
    (.seq ((siaF (R + 100) (R + 103) (R + 104)).compile (R + 140))
      (.seq ((siaF (R + 104) (R + 107) (R + 105)).compile (R + 160))
        (.seq ((siaF (R + 100) (R + 101) (R + 105)).compile (R + 180))
          (.seq ((siaF (R + 105) (R + 106) (R + 104)).compile (R + 200))
            ((eqF (R + 102) (R + 101)).compile (R + 220))))))

/-- **The cutting block of level `ℓ`.** -/
def cutWith (R ℓ : ℕ) (s : Stmt) : Stmt :=
  let L := rL R ℓ
  .seq (kltSeq (R + 30) (cmpList R ℓ)) (.seq s (.seq (formB R)
    (selB L (R + 10 + 2 * ℓ) (R + 11 + 2 * ℓ) (R + 30) (L + 10) (L + 4) (L + 8) (R + 30 + ℓ)
      (R + 9) (R + 120) (R + 140) (R + 160) (R + 180) (R + 200) (R + 220))))

def cutB (R ℓ : ℕ) : Stmt := cutWith R ℓ (offB R ℓ)


/-! ## Execution: the correction of `a < b` -/

/-- **The caller's register block** `R … R + 299` lies in one band, which is neither band `0`
(the allocator) nor a band of the kernels or the oracles (`oracleBands`). -/
def RegsOK (R : ℕ) : Prop :=
  R % 10000 + 300 ≤ 10000 ∧ R / 10000 ≠ 0 ∧ R / 10000 ≠ 1 ∧ R / 10000 ≠ 3 ∧ R / 10000 ≠ 4 ∧
    R / 10000 ≠ 5 ∧ R / 10000 ≠ 6 ∧ R / 10000 ≠ 12 ∧ R / 10000 ≠ 13 ∧ R / 10000 ≠ 14 ∧
    R / 10000 ≠ 15

theorem bprim_R {R : ℕ} (hR : RegsOK R) {i : ℕ} (hi : i < 300) : Bprim (R + i) = false := by
  unfold RegsOK at hR
  simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- The registers written by `offB`. -/
def Boff (R : ℕ) (r : ℕ) : Bool := r == R + 100 || Bprim r || decide (50200 ≤ r ∧ r < 50210)

theorem wr_offCmp' (R : ℕ) : wr (Boff R) offCmp = true :=
  wr_mono wr_offCmp (fun r hr => by simp [Boff, hr])

theorem wr_offCall (R ℓ : ℕ) : wr (Boff R) (offCall R ℓ) = true := by
  have h := wr_offCmp' R
  simp [offCall, write_check, block, Boff, h]

section

variable {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)

include P hw in
/-- Loading the inputs of `offCmp`. -/
theorem offLoad_exec (cd L z : ℕ)
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

/-- The same-edge comparison is needed only when both heights are positive on the same edge. -/
theorem offWith_exec {P : Polygon} {W : ℕ} {M : Model} {R ℓ : ℕ} {B : ℕ → Bool} {K : ℕ}
    (c : Config) (hw : WordsBounded W c) (s : Stmt) (hz : c.nreg (R + 30) = 0)
    (ha : NormPos M (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos M (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hbit : BitIs c (R + 100) (LexLt (c.nreg (rL R ℓ)) (ibv (c.nreg (rL R ℓ + 1)))
      (c.nreg (rL R ℓ + 2)) (ibv (c.nreg (rL R ℓ + 3)))))
    (same : c.nreg (rL R ℓ) = c.nreg (rL R ℓ + 2) →
      0 < c.nreg (rL R ℓ + 1) → 0 < c.nreg (rL R ℓ + 3) →
      ∃ d k, Exec P W s c d k ∧ k ≤ K ∧
        BitIs d (R + 100) (M.key (Qof P) (posR c (rL R ℓ, rL R ℓ + 1)) <
          M.key (Qof P) (posR c (rL R ℓ + 2, rL R ℓ + 3))) ∧ FrameB B c d) :
    ∃ d k, Exec P W (offWith R ℓ s) c d k ∧ k ≤ K + 8 ∧
      BitIs d (R + 100) (M.key (Qof P) (posR c (rL R ℓ, rL R ℓ + 1)) <
        M.key (Qof P) (posR c (rL R ℓ + 2, rL R ℓ + 3))) ∧ FrameB B c d := by
  set L := rL R ℓ
  have nk : ¬ (c.nreg L = c.nreg (L + 2) ∧ 0 < c.nreg (L + 1) ∧ 0 < c.nreg (L + 3)) →
      BitIs c (R + 100) (M.key (Qof P) (posR c (L, L + 1)) <
        M.key (Qof P) (posR c (L + 2, L + 3))) :=
    fun h => ⟨hbit.1, hbit.2.trans (lexLt_iff_key ha hb h)⟩
  have f := FrameB.refl B c
  by_cases h₁ : c.nreg L < c.nreg (L + 2)
  · exact ⟨c, _, .ifLtN_true h₁ (.skip hw), by omega, nk (by omega), f⟩
  by_cases h₂ : c.nreg (L + 2) < c.nreg L
  · exact ⟨c, _, .ifLtN_false h₁ (.ifLtN_true h₂ (.skip hw)), by omega, nk (by omega), f⟩
  by_cases h₃ : c.nreg (R + 30) < c.nreg (L + 1)
  swap
  · exact ⟨c, _, .ifLtN_false h₁ (.ifLtN_false h₂ (.ifLtN_false h₃ (.skip hw))),
      by omega, nk (by omega), f⟩
  by_cases h₄ : c.nreg (R + 30) < c.nreg (L + 3)
  swap
  · exact ⟨c, _, .ifLtN_false h₁ (.ifLtN_false h₂ (.ifLtN_true h₃ (.ifLtN_false h₄ (.skip hw)))),
      by omega, nk (by omega), f⟩
  obtain ⟨d, k, e, hk, b, f⟩ := (ram_app% (same ?_ ?_ ?_))
  exact ⟨d, _, .ifLtN_false h₁ (.ifLtN_false h₂ (by ram_path)), by omega, b, f⟩

/-- **The correction of `a < b`**: afterwards the bit `R + 100` is the key order of `a`, `b`. -/
theorem offB_exec {P : Polygon} {W : ℕ} {R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
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
  refine offWith_exec (K := 11092) c hw (offCall R ℓ) hz ha hb hbit ?_
  set L := rL R ℓ
  intro _ h₃ h₄
  let M := chainModel C
  have hLd : L = R + 40 + 10 * ℓ := rfl
  -- two interior positions of one edge: `offCmp`
  have hR' := hR; unfold RegsOK at hR'
  obtain ⟨c₁, k₁, e₁, hk₁, p1, p2, p3, p4, p5, p6, pr, pm, pal⟩ :=
    ram_app% (offLoad_exec (P := P) c hw (R + 34) L (R + 30) ?_ ?_)
  rw [hz] at p6
  have w₁ := e₁.wb_right
  have hn0 : 0 < M.W.n := by
    have : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
    change 0 < (chainModel C).W.n
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := offCmp_meets P W c₁ w₁
    ⟨hG, hHW, by rwa [pal, pm, p1], H, C, by rwa [pm, p1],
      by rwa [p2], by rwa [p4], by rwa [p6],
      by rw [p2, p3]; exact ha.1, by rw [p4, p5]; exact hb.1,
      fun h => by rw [p3] at h; omega, fun h => by rw [p5] at h; omega, hm⟩
    (by rw [pal]; omega)
  replace hk₂ : k₂ ≤ 11000 := hk₂
  obtain ⟨o1, -⟩ := post₂ H C (by rwa [pm, p1])
  have e₃ := Exec.copyN (P := P) e₂.wb_right (R + 100) 50210
  have ex : Exec P W (offCall R ℓ) c _ _ :=
    .seq e₁ (.seq e₂ (Exec.block_cons e₃ (Exec.block_nil e₃.wb_right)))
  refine ⟨_, _, ex, by omega, ⟨?_, ?_⟩, exec_frameB ex (wr_offCall R ℓ)⟩
  · simp only [upd_same]; exact o1.1
  · simp only [upd_same]
    rw [o1.2, p2, p3, p4, p5, p6]
    have kx := ha.1.1
    have ky := hb.1.1
    simp only [posR] at kx ky ⊢
    rw [Nat.cast_zero]
    exact (key_lt_iff_off kx ky).symm


/-! ## Execution: the six tests -/

theorem bitIs_toNat {c : Config} {d : ℕ} {b : Bool} {p : Prop} (hv : c.nreg d = b.toNat)
    (hb : b = true ↔ p) : BitIs c d p := by
  refine ⟨by rw [hv]; cases b <;> simp, ?_⟩
  simp_all

include P hw in
/-- A compiled `sideInArc` test. -/
theorem siaF_exec (hW : 2 ≤ W)
    {uw uk kw d : ℕ} (h1 : uw < d) (h2 : uk < d) (h3 : kw < d) {u w k : ℝ}
    (b1 : BitIs c uw (u < w)) (b2 : BitIs c uk (u < k)) (b3 : BitIs c kw (k < w)) :
    ∃ c' k', Exec P W ((siaF uw uk kw).compile d) c c' k' ∧ k' ≤ 48 ∧
      BitIs c' d (sideInArc u w k) ∧ FrameB ((siaF uw uk kw).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (siaF uw uk kw) d c hw
    ⟨⟨⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩, ⟨h3, b3.1⟩⟩, ⟨⟨h1, b1.1⟩, ⟨⟨h2, b2.1⟩, ⟨h3, b3.1⟩⟩⟩⟩
  exact ⟨c', k', ex, by reg_omega, bitIs_toNat hv (siaF_eval b1 b2 b3), hf⟩

include P hw in
/-- The compiled test `x = a`. -/
theorem eqF_exec (hW : 2 ≤ W)
    {xa ax d : ℕ} (h1 : xa < d) (h2 : ax < d) {x a : ℝ} (b1 : BitIs c xa (x < a))
    (b2 : BitIs c ax (a < x)) :
    ∃ c' k', Exec P W ((eqF xa ax).compile d) c c' k' ∧ k' ≤ 20 ∧ BitIs c' d (x = a) ∧
      FrameB ((eqF xa ax).wset d) c c' := by
  obtain ⟨c', k', ex, hk, hv, hf⟩ := BF.compile_exec (P := P) hW (eqF xa ax) d c hw
    ⟨⟨h1, b1.1⟩, ⟨h2, b2.1⟩⟩
  exact ⟨c', k', ex, by reg_omega, bitIs_toNat hv (eqF_eval b1 b2), hf⟩

end

/-- The registers written by `formB`. -/
def Bform (R : ℕ) (r : ℕ) : Bool := decide (R + 120 ≤ r ∧ r < R + 240)

theorem bitIs_keep {c c' : Config} {B : ℕ → Bool} {r : ℕ} {p : Prop} (h : BitIs c r p)
    (hf : FrameB B c c') (hr : B r = false) : BitIs c' r p := h.of_eq (hf.1 r hr)

theorem wset_lt {f : BF} {d r : ℕ} (h : r < d) : f.wset d r = false := by
  simp only [BF.wset, decide_eq_false_iff_not]; omega

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
    (by ram_frame)
  have kp : ∀ {B : ℕ → Bool} {cc cc' : Config} {r : ℕ} {p : Prop}, BitIs cc r p →
      FrameB B cc cc' → B r = false → BitIs cc' r p := fun h hf hr => bitIs_keep h hf hr
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := (ram_app% (siaF_exec (P := P) c hw hW (d := R + 120)
    ?_ ?_ ?_ bxy bxa bay))
  have k1 := fun {r : ℕ} {p : Prop} (h : BitIs c r p) (hr : r < R + 120) =>
    kp h f₁ (wset_lt hr)
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := ram_app% (siaF_exec (P := P) c₁ e₁.wb_right hW (d := R + 140)
    ?_ ?_ ?_ (k1 bab ?_) (k1 bay ?_) (k1 byb ?_))
  have k2 := fun {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : r < R + 140) =>
    kp h f₂ (wset_lt hr)
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := ram_app% (siaF_exec (P := P) c₂ e₂.wb_right hW (d := R + 160)
    ?_ ?_ ?_ (k2 (k1 byb ?_) ?_)
    (k2 (k1 byx ?_) ?_) (k2 (k1 bxb ?_) ?_))
  have k3 := fun {r : ℕ} {p : Prop} (h : BitIs c₂ r p) (hr : r < R + 160) =>
    kp h f₃ (wset_lt hr)
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := ram_app% (siaF_exec (P := P) c₃ e₃.wb_right hW (d := R + 180)
    ?_ ?_ ?_ (k3 (k2 (k1 bab ?_) ?_) ?_)
    (k3 (k2 (k1 bax ?_) ?_) ?_)
    (k3 (k2 (k1 bxb ?_) ?_) ?_))
  have k4 := fun {r : ℕ} {p : Prop} (h : BitIs c₃ r p) (hr : r < R + 180) =>
    kp h f₄ (wset_lt hr)
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅⟩ := ram_app% (siaF_exec (P := P) c₄ e₄.wb_right hW (d := R + 200)
    ?_ ?_ ?_
    (k4 (k3 (k2 (k1 bxb ?_) ?_) ?_) ?_)
    (k4 (k3 (k2 (k1 bxy ?_) ?_) ?_) ?_)
    (k4 (k3 (k2 (k1 byb ?_) ?_) ?_) ?_))
  have k5 := fun {r : ℕ} {p : Prop} (h : BitIs c₄ r p) (hr : r < R + 200) =>
    kp h f₅ (wset_lt hr)
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, f₆⟩ := ram_app% (eqF_exec (P := P) c₅ e₅.wb_right hW (d := R + 220)
    ?_ ?_
    (k5 (k4 (k3 (k2 (k1 bxa ?_) ?_) ?_) ?_) ?_)
    (k5 (k4 (k3 (k2 (k1 bax ?_) ?_) ?_) ?_) ?_))
  have k6 := fun {r : ℕ} {p : Prop} (h : BitIs c₅ r p) (hr : r < R + 220) =>
    kp h f₆ (wset_lt hr)
  have fz : ∀ {f : BF} {d : ℕ} {cc cc' : Config}, FrameB (f.wset d) cc cc' → R + 120 ≤ d →
      d + f.size < R + 240 → FrameB (Bform R) cc cc' := fun h h1 h2 => fr h (fun r hr => by
    simp only [SweepPrim.BF.wset, decide_eq_true_eq] at hr; omega)
  refine ⟨c₆, _, (by ram_path), by omega,
    k6 (k5 (k4 (k3 (k2 v₁ (by omega)) (by omega)) (by omega)) (by omega)) (by omega),
    k6 (k5 (k4 (k3 v₂ (by omega)) (by omega)) (by omega)) (by omega),
    k6 (k5 (k4 v₃ (by omega)) (by omega)) (by omega), k6 (k5 v₄ (by omega)) (by omega),
    k6 v₅ (by omega), v₆, ?_⟩
  refine (fz f₁ ?_ (by rw [siaF_size]; omega)).trans
    ((fz f₂ ?_ (by rw [siaF_size]; omega)).trans
    ((fz f₃ ?_ (by rw [siaF_size]; omega)).trans
    ((fz f₄ ?_ (by rw [siaF_size]; omega)).trans
    ((fz f₅ ?_ (by rw [siaF_size]; omega)).trans
    (fz f₆ ?_ (by rw [eqF_size]; omega)))))) <;> omega


/-! ## The cutting block -/

/-- The registers written by `cutB`. -/
def Bcut (R ℓ : ℕ) (r : ℕ) : Bool :=
  Bouts (cmpList R ℓ) r || Boff R r || Bform R r || decide (rL R ℓ + 4 ≤ r ∧ r < rL R ℓ + 14)

/-- The pieces of the arc of level `ℓ`: `cut1` if the hole is present, else the arc. -/
noncomputable def levPieces (M : Model) (Q : Polygon) (hp : Prop) [Decidable hp] (a b : WPos)
    (x y : ℕ) : List (WPos × WPos) :=
  if hp then cut1 (M.key Q) a b ⟨x, 0⟩ ⟨y, 0⟩ else [(a, b)]

theorem bouts_range {R ℓ r : ℕ} (h : Bouts (cmpList R ℓ) r = true) : R + 100 ≤ r ∧ r < R + 108 := by
  simp only [Bouts, cmpOuts, cmpList, List.map_cons, List.map_nil, List.contains_eq_mem,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at h
  omega

theorem cmpList_ok {R ℓ : ℕ} (hℓ : ℓ ≤ 2) : CmpOK (R + 30) (cmpList R ℓ) := by
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · simp [cmpOuts, cmpList, rL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil]
  · simp [cmpOuts, cmpList]
  · simp only [cmpList, rL, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [cmpOuts, cmpList, rL, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      omega

/-- The write set of a cutting block with a supplied correction mask. -/
def BcutWith (R ℓ : ℕ) (B : ℕ → Bool) (r : ℕ) : Bool :=
  Bouts (cmpList R ℓ) r || B r || Bform R r || decide (rL R ℓ + 4 ≤ r ∧ r < rL R ℓ + 14)

/-- Verification of the entire cutting block from the contract for its same-edge correction. -/
theorem cutWith_exec {P : Polygon} {W : ℕ} {M : Model} {R ℓ : ℕ} (hℓ : ℓ ≤ 2) (c : Config)
    (hw : WordsBounded W c) (hW : 2 ≤ W) (hz : c.nreg (R + 30) = 0)
    (ha : NormPos M (Qof P) P.n (posR c (rL R ℓ, rL R ℓ + 1)))
    (hb : NormPos M (Qof P) P.n (posR c (rL R ℓ + 2, rL R ℓ + 3)))
    (hae : c.nreg (rL R ℓ) < M.W.n) (hbe : c.nreg (rL R ℓ + 2) < M.W.n)
    {s : Stmt} {B : ℕ → Bool} {K : ℕ}
    (hkeep : ∀ r, R ≤ r → r < R + 300 → r ≠ R + 100 → B r = false)
    (hfix : ∀ d, WordsBounded W d → FrameB (Bouts (cmpList R ℓ)) c d →
      (∀ r, r < R + 100 → d.nreg r = c.nreg r) →
      NormPos M (Qof P) P.n (posR d (rL R ℓ, rL R ℓ + 1)) →
      NormPos M (Qof P) P.n (posR d (rL R ℓ + 2, rL R ℓ + 3)) →
      d.nreg (rL R ℓ) < M.W.n → d.nreg (rL R ℓ + 2) < M.W.n →
      BitIs d (R + 100) (LexLt (d.nreg (rL R ℓ)) (ibv (d.nreg (rL R ℓ + 1)))
        (d.nreg (rL R ℓ + 2)) (ibv (d.nreg (rL R ℓ + 3)))) →
      ∃ c' k, Exec P W s d c' k ∧ k ≤ K ∧
        BitIs c' (R + 100) (M.key (Qof P) (posR d (rL R ℓ, rL R ℓ + 1)) <
          M.key (Qof P) (posR d (rL R ℓ + 2, rL R ℓ + 3))) ∧ FrameB B d c') :
    ∃ c' k, Exec P W (cutWith R ℓ s) c c' k ∧ k ≤ K + 400 ∧
      PiecesAt c' (rL R ℓ + 10) (rL R ℓ + 4) (rL R ℓ + 8)
        (levPieces M (Qof P) (c.nreg (R + 30 + ℓ) < c.nreg (R + 9))
          (posR c (rL R ℓ, rL R ℓ + 1)) (posR c (rL R ℓ + 2, rL R ℓ + 3))
          (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ))) ∧
      FrameB (BcutWith R ℓ B) c c' := by
  set L := rL R ℓ with hL
  have hLd : L = R + 40 + 10 * ℓ := rfl
  set Q := Qof P
  set a := posR c (L, L + 1) with ha_def
  set b := posR c (L + 2, L + 3) with hb_def
  set x := c.nreg (R + 10 + 2 * ℓ)
  set y := c.nreg (R + 11 + 2 * ℓ)
  have hX := normPos_vtx M Q P.n x
  have hY := normPos_vtx M Q P.n y
  -- the comparisons
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := kltSeq_exec (P := P) (by omega) (R + 30) (cmpList R ℓ) c hw
    hz (cmpList_ok hℓ)
  have keep₁ : ∀ r, r < R + 100 → c₁.nreg r = c.nreg r := fun r hr => by
    apply f₁.1
    cases h : Bouts (cmpList R ℓ) r
    · rfl
    · have := bouts_range h; omega
  have mem := b₁
  simp only [cmpList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mem
  obtain ⟨bab, bax, bxa, bay, byb, bxb, bxy, byx⟩ := mem
  rw [hz] at bax bxa bay byb bxb bxy byx
  have order {u v : WPos} {r : ℕ} (hu : NormPos M Q P.n u) (hv : NormPos M Q P.n v)
      (h0 : u.hgt = 0 ∨ v.hgt = 0)
      (b : BitIs c₁ r (LexLt u.edge (ibv u.hgt) v.edge (ibv v.hgt))) :
      BitIs c₁ r (M.key Q u < M.key Q v) :=
    ⟨b.1, b.2.trans (lexLt_iff_key hu hv (by omega))⟩
  -- The caller handles comparisons of two interior positions of one edge.
  have p₀ := keep₁ L (by omega)
  have p (i : ℕ) (hi : i < 4) := keep₁ (L + i) (by omega)
  have pa : posR c₁ (L, L + 1) = a := by
    simp only [posR, ha_def, WPos.mk.injEq]; exact ⟨p₀, p 1 (by omega)⟩
  have pb : posR c₁ (L + 2, L + 3) = b := by
    simp only [posR, hb_def, WPos.mk.injEq]; exact ⟨p 2 (by omega), p 3 (by omega)⟩
  obtain ⟨c₂, k₂, e₂, hk₂, kab, f₂⟩ := hfix c₁ e₁.wb_right f₁ keep₁
    (by rwa [pa]) (by rwa [pb]) (by rwa [p₀]) (by ram_rw assumption [p 2])
    (by ram_rw assumption [p₀, p 1, p 2, p 3])
  rw [pa, pb] at kab
  have ks {r : ℕ} {p : Prop} (h : BitIs c₁ r p) (hr : R + 100 < r ∧ r < R + 300) :=
    bitIs_keep h f₂ (hkeep r (by omega) hr.2 (by omega))
  -- the six tests
  obtain ⟨c₃, k₃, e₃, hk₃, t1, t2, t3, t4, t5, t6, f₃⟩ := formB_exec (P := P) R c₂ e₂.wb_right
    hW kab (ks (order ha hX (Or.inr rfl) bax) (by omega))
    (ks (order hX ha (Or.inl rfl) bxa) (by omega)) (ks (order ha hY (Or.inr rfl) bay) (by omega))
    (ks (order hY hb (Or.inl rfl) byb) (by omega)) (ks (order hX hb (Or.inl rfl) bxb) (by omega))
    (ks (order hX hY (Or.inl rfl) bxy) (by omega)) (ks (order hY hX (Or.inl rfl) byx) (by omega))
  have gR' : ∀ r, R ≤ r → r < R + 100 → c₃.nreg r = c.nreg r := fun r lo hi => by
    rw [f₃.1 r (by simp only [Bform, decide_eq_false_iff_not]; omega),
      f₂.1 r (hkeep r lo (by omega) (by omega)), keep₁ r hi]
  have z3 : c₃.nreg (R + 30) = 0 := (gR' _ (by omega) (by omega)).trans hz
  obtain ⟨c₄, k₄, e₄, hk₄, pc₄, r₄, m₄, rr₄, rm₄, o₄⟩ := selB_exec (P := P) c₃ e₃.wb_right hW
    (L := L) (hx := R + 10 + 2 * ℓ) (hy := R + 11 + 2 * ℓ) (z := R + 30) (N := L + 10)
    (S := L + 4) (Cn := L + 8) (hpA := R + 30 + ℓ) (hpB := R + 9) (c1 := R + 120)
    (c2 := R + 140) (c3 := R + 160) (c4 := R + 180) (c5 := R + 200) (c6 := R + 220)
    (by intro e o ho; cases e <;> simp only [End.regs] <;> omega) (by omega) (by omega)
    (by omega) z3 t1.1 t2.1 t3.1 t4.1 t5.1 t6.1
  refine ⟨c₄, _, (by ram_path), by simp only [cmpList, List.length_cons, List.length_nil] at hk₁; omega,
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
        cases u <;> simp (disch := omega) only [End.regs, End.val, posR, ha_def, hb_def, z3, gR', x, y]
      rw [ev, ev]
    rw [hsel] at pc₄
    have hp3 : (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) ↔ (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) := by
      frame_finish [gR']
    unfold levPieces
    by_cases hp : c.nreg (R + 30 + ℓ) < c.nreg (R + 9)
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = true := by
        simp [hp3.2 hp]
      rw [hd] at pc₄
      rw [ite_yes _ _ hp]
      unfold cut1
      rwa [cutK_eq_selT (M.key Q a) (M.key Q b) (M.key Q ⟨x, 0⟩) (M.key Q ⟨y, 0⟩) a b ⟨x, 0⟩
        ⟨y, 0⟩ (c1 := decide (c₃.nreg (R + 120) = 1)) (c2 := decide (c₃.nreg (R + 140) = 1))
        (c3 := decide (c₃.nreg (R + 160) = 1)) (c4 := decide (c₃.nreg (R + 180) = 1))
        (c5 := decide (c₃.nreg (R + 200) = 1)) (c6 := decide (c₃.nreg (R + 220) = 1))
        (by rw [decide_eq_true_iff]; exact t1.2) (by rw [decide_eq_true_iff]; exact t2.2)
        (by rw [decide_eq_true_iff]; exact t3.2) (by rw [decide_eq_true_iff]; exact t4.2)
        (by rw [decide_eq_true_iff]; exact t5.2) (by rw [decide_eq_true_iff]; exact t6.2)]
    · have hd : decide (c₃.nreg (R + 30 + ℓ) < c₃.nreg (R + 9)) = false := by
        simp only [decide_eq_false_iff_not]; exact fun h => hp (hp3.1 h)
      rw [hd] at pc₄
      rwa [ite_no _ _ hp]
  · -- the frame
    have f₄ : FrameB (fun r => decide (L + 4 ≤ r ∧ r < L + 14)) c₃ c₄ :=
      ⟨fun r hr => r₄ r (by simp only [decide_eq_false_iff_not] at hr; omega)
        (by simp only [decide_eq_false_iff_not] at hr; omega)
        (by simp only [decide_eq_false_iff_not] at hr; omega),
       fun r _ => by rw [rr₄], m₄, rm₄, o₄⟩
    have c1 : FrameB (BcutWith R ℓ B) c c₁ := frameB_mono f₁ (fun r hr => by simp [BcutWith, hr])
    have c2 : FrameB (BcutWith R ℓ B) c₁ c₂ := frameB_mono f₂ (fun r hr => by simp [BcutWith, hr])
    have c3 : FrameB (BcutWith R ℓ B) c₂ c₃ := frameB_mono f₃ (fun r hr => by simp [BcutWith, hr])
    have c4 : FrameB (BcutWith R ℓ B) c₃ c₄ := frameB_mono f₄ (fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [BcutWith, ← hL, hr])
    exact c1.trans (c2.trans (c3.trans c4))

/-- **The cutting block of level `ℓ`**: the pieces `levPieces` in the registers of the next
level (`rL R ℓ + 10 …`, `rL R ℓ + 4 …`, their number in `rL R ℓ + 8`). -/
theorem cutB_exec {P : Polygon} {W : ℕ} {R ℓ : ℕ} (hR : RegsOK R) (hℓ : ℓ ≤ 2) (c : Config)
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
  refine cutWith_exec hℓ c hw hW hz ha hb hae hbe (s := offB R ℓ)
    (B := Boff R) (K := 11100) ?_ ?_
  · intro r hlo hhi hne
    have h := bprim_R hR (i := r - R) (by omega)
    rw [show R + (r - R) = r by omega] at h
    unfold RegsOK at hR
    simp only [Boff, h, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not]
    omega
  · intro d hd hf keep ha' hb' he₁ he₂ bit
    have hm' := hf.2.2.1
    have hA : d.nreg ALLOC = c.nreg ALLOC := keep _ (by unfold ALLOC; unfold RegsOK at hR; omega)
    have h34 := keep (R + 34) (by omega)
    exact offB_exec hR hℓ d hd hG hHW (H := H) (C := C)
      (by rwa [hA, hm', h34]) (by rwa [hm', h34]) hm (by rwa [hA])
      ((keep _ (by omega)).trans hz) ha' hb' he₁ he₂ bit

end

end ShotList

end Chazelle.Core
