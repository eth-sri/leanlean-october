module

public import Chazelle.Core.SweepIoPipe

/-!
# The sweep RAM (WP-D), answers: register steps of the per-query pipeline

* `loadQ`: read the query `j` at `pA` (and its index into `qJ`);
* `bitT`, `bitsQ`: the bits `bL`, `bR` (symbolic top of a chain, one sign test);
* `store4`: four result words at `pR`;
* `convQ`: the query position converted to the walk of `C` (by the side);
* `qryP`: the per-query program.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A pipeline scratch register. -/
def tAq : ℕ := sw 3228

/-- **Read the query** `j` (at `pA`) and its index. -/
def loadQ : Stmt :=
  block [.copyN qJ pJ, .loadN qE pA, .addN tAq pA K1, .loadN qH tAq, .addN tAq pA K2, .loadN qD tAq]

theorem loadQ_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hW : c.nreg pA + 2 ≤ W) :
    IRS P W c₀ loadQ c 6 (fun c' => c'.nreg qJ = c.nreg pJ ∧ c'.nreg qE = c.nmem (c.nreg pA) ∧
      c'.nreg qH = c.nmem (c.nreg pA + 1) ∧ c'.nreg qD = c.nmem (c.nreg pA + 2) ∧
      (∀ r, r ≠ qJ → r ≠ qE → r ≠ qH → r ≠ qD → r ≠ tAq → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have k2 : c.nreg K2 = 2 := hKc.2.2.2.2.2.1
  have s : ∀ r, 240700 ≤ r → r < 250000 → IScr r := fun r h1 h2 => iscr_sw h1 h2
  have ok : okB W c.nmem [.copyN qJ pJ, .loadN qE pA, .addN tAq pA K1, .loadN qH tAq,
      .addN tAq pA K2, .loadN qD tAq] c.nreg := by
    simp only [qJ, pJ, qE, pA, tAq, K1, K2, qH, qD, sw, Nat.reduceAdd] at k1 k2 hW ⊢
    simp only [okB, okI, regI, upd, Nat.reduceEqDiff, ite_false, k1, k2]
    refine ⟨s _ (by norm_num) (by norm_num), s _ (by norm_num) (by norm_num),
      ⟨s _ (by norm_num) (by norm_num), by omega⟩, s _ (by norm_num) (by norm_num),
      ⟨s _ (by norm_num) (by norm_num), by omega⟩, s _ (by norm_num) (by norm_num), trivial⟩
  refine (IRS.block _ hI ok).mono le_rfl ?_
  rintro c' rfl
  simp only [qJ, pJ, qE, pA, tAq, K1, K2, qH, qD, sw, Nat.reduceAdd] at k1 k2 ⊢
  simp only [regB, regI, upd, Nat.reduceEqDiff, ite_false, ite_true, k1, k2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | trivial
    | (intro r h1 h2 h3 h4 h5; simp only [h1, h2, h3, h4, h5, ite_false])

/-! ## The bits -/

/-- The position `(6, 0)` of a chain model is the top. -/
theorem top_pos (C : Chain) (Q : Polygon) : (chainModel C).pos Q ⟨6, 0⟩ = C.top := by
  show Geometry.lerp ((chainModel C).wa 6) ((chainModel C).wb 6) 0 = C.top
  rw [Geometry.lerp_zero]; exact C.sideWalk_vtx_six _

/-- Registers of the bit test. -/
def sZ : ℕ := sw 3240
def sTq : ℕ := sw 3244
def kO : ℕ := sw 3249

/-- **The bit `bt`**: `1` iff the height of the query code is not above the top of the chain of
the descriptor `dsc`. -/
def bitT (dsc bt : ℕ) : Stmt :=
  .seq (block [.copyN sZ K0, .subN (sZ + 1) qH K1])
    (.seq (callSym dsc K6 K0 sTq) (.seq (callKb (sTq + 1) sZ 1 kO) (block [.subN bt K1 kO])))

set_option maxHeartbeats 4000000 in
theorem bitT_irs {dsc bt : ℕ} {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hctx : ChainCtx P W c dsc C) (hdsc : IFix dsc) (hbt : bt = bL ∨ bt = bR)
    (hqH : 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n) (hroom : c.nreg ALLOC + 16962 ≤ W) :
    IRS P W c₀ (bitT dsc bt) c 16962 (fun c' => c'.nreg bt ≤ 1 ∧
      (c'.nreg bt = 1 ↔ ((Qof P).vtx (c.nreg qH - 1)).2 ≤ C.top.2) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ bt → ¬ (sw 3230 ≤ r ∧ r < sw 3300) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hKc := hK.fix hI
  have k0 : c.nreg K0 = 0 := hKc.1
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have hG := hctx.1
  have hWh := hctx.2.1
  have hWn : P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  have s : ∀ r, 240700 ≤ r → r < 250000 → IScr r := fun r h1 h2 => iscr_sw h1 h2
  have hbt' : 243225 ≤ bt ∧ bt ≤ 243226 := by rcases hbt with rfl | rfl <;> simp [bL, bR, sw]
  have hdl : 240000 ≤ dsc ∧ dsc < 240700 := hdsc
  -- 1. the vertex point of the height code
  have ok1 : okB W c.nmem [.copyN sZ K0, .subN (sZ + 1) qH K1] c.nreg :=
    ⟨s _ (by unfold sZ sw; norm_num) (by unfold sZ sw; norm_num),
      s _ (by unfold sZ sw; norm_num) (by unfold sZ sw; norm_num), trivial⟩
  refine (IRS.seq (K₂ := 16960) (IRS.block _ hI ok1) ?_).mono (by simp) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have v1 : c₁.nreg sZ = 0 ∧ c₁.nreg (sZ + 1) = c.nreg qH - 1 ∧
      (∀ r, r ≠ sZ → r ≠ sZ + 1 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    subst hc1
    simp only [sZ, K0, K1, qH, sw, Nat.reduceAdd] at k0 k1 ⊢
    simp only [regB, regI, upd, Nat.reduceEqDiff, ite_false, ite_true, k0, k1]
    refine ⟨trivial, trivial, fun r h1 h2 => ?_, trivial⟩
    simp only [h1, h2, ite_false]
  obtain ⟨z1, z2, r1, m1⟩ := v1
  have hsz : SymPtIn c₁ sZ (.vtx (c.nreg qH - 1)) := ⟨z1, z2⟩
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := r1 _ (by unfold sZ ALLOC sw; omega)
    (by unfold sZ ALLOC sw; omega)
  have hctx₁ : ChainCtx P W c₁ dsc C := hctx.transport (r1 _ (by unfold sZ sw; omega)
    (by unfold sZ sw; omega)) (fun a _ => by rw [m1]) (by rw [hA1])
  have rK6 : c₁.nreg K6 = 6 := by rw [r1 _ (by unfold sZ K6 sw; omega) (by unfold sZ K6 sw; omega)]; exact hKc.2.2.1
  have rK0 : c₁.nreg K0 = 0 := by rwa [r1 _ (by unfold sZ K0 sw; omega) (by unfold sZ K0 sw; omega)]
  have hm1 := C.one_le
  have hn := cm_n C
  -- 2. the top
  have hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c₁.nreg K6, c₁.nreg K0⟩ := by
    rw [rK6, rK0]; exact ⟨le_refl _, by show (0 : ℝ) < 1; norm_num, Nat.zero_le _⟩
  refine IRS.seq (K₂ := 251 + 2) (callSym_irs hI₁ hctx₁ ⟨by omega, by omega,
      by unfold K6 sw; norm_num, by unfold K6 sw; norm_num, by unfold K0 sw; norm_num,
      by unfold K0 sw; norm_num⟩ ⟨by unfold sTq sw; norm_num, by unfold sTq sw; norm_num⟩
      (by rw [rK6]; omega) hpp
      (by rw [rK6, rK0, top_pos]; exact absy_lt C C.top_mem_set)
      (Or.inl ⟨by rw [rK6], by rw [rK6]; omega⟩) (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨sp, hsp, hlt, hev, f2, hA2, m2⟩
  rw [rK6, rK0, top_pos] at hev
  have hsz₂ : SymPtIn c₂ sZ (.vtx (c.nreg qH - 1)) := symPtIn_copy hsz
    (f2 _ (not_oracle_sw (by unfold sZ sw; norm_num) (by unfold sZ sw; norm_num))
      (Or.inl (by unfold sZ sTq sw; norm_num)) (by unfold sZ ALLOC sw; omega))
    (f2 _ (not_oracle_sw (by unfold sZ sw; norm_num) (by unfold sZ sw; norm_num))
      (Or.inl (by unfold sZ sTq sw; norm_num)) (by unfold sZ ALLOC sw; omega))
    (f2 _ (not_oracle_sw (by unfold sZ sw; norm_num) (by unfold sZ sw; norm_num))
      (Or.inl (by unfold sZ sTq sw; norm_num)) (by unfold sZ ALLOC sw; omega))
  -- 3. the sign test
  refine IRS.seq (K₂ := 2) (callKb_irs (by norm_num) hI₂ hG hWn
      ⟨by unfold sTq sw; norm_num, by unfold sTq sw; norm_num⟩
      ⟨by unfold sZ sw; norm_num, by unfold sZ sw; norm_num⟩
      ⟨by unfold kO sw; norm_num, by unfold kO sw; norm_num⟩ hsp hsz₂ hlt
      (show c.nreg qH - 1 < P.n by omega) (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨o1, o2, f3, hA3, m3⟩
  have k1₃ : c₃.nreg K1 = 1 := (hK.fix hI₃).2.1
  refine (IRS.block [.subN bt K1 kO] hI₃ ⟨s _ (by omega) (by omega), trivial⟩).mono (by norm_num) ?_
  rintro c' rfl
  have vb : regB c₃.nmem [.subN bt K1 kO] c₃.nreg bt = 1 - c₃.nreg kO := by
    simp only [regB, regI, upd_same, k1₃]
  have kb : ∀ r, r ≠ bt → regB c₃.nmem [.subN bt K1 kO] c₃.nreg r = c₃.nreg r := by
    intro r hr; simp only [regB, regI]; exact upd_other _ _ _ hr
  refine ⟨by simp only; rw [vb]; omega, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
  · simp only; rw [vb]
    have : SignTest 1 (sp.eval (Qof P)) ((SymPt.vtx (c.nreg qH - 1)).eval (Qof P))
        (sp.eval (Qof P)) ↔ C.top.2 < ((Qof P).vtx (c.nreg qH - 1)).2 := by
      rw [hev]; exact Iff.rfl
    rw [this] at o2
    constructor
    · intro h; exact not_lt.1 (fun h' => by have := o2.2 h'; omega)
    · intro h; have : c₃.nreg kO ≠ 1 := fun h' => absurd (o2.1 h') (not_lt.2 h); omega
  · simp only; rw [kb r h2]
    rw [f3 r h1 (fun h => h3 (by rw [h]; unfold kO sw; norm_num)) h4,
      f2 r h1 (by
        by_contra hh; push Not at hh
        simp only [sTq, sw] at hh
        exact h3 ⟨by unfold sw; omega, by unfold sw; omega⟩) h4,
      r1 r (fun h => h3 (by rw [h]; unfold sZ sw; norm_num)) (fun h => h3 (by rw [h]; unfold sZ sw; norm_num))]
  · simp only
    rw [kb ALLOC (by rcases hbt with rfl | rfl <;> simp [bL, bR, ALLOC, sw])]; omega
  · intro a ha; simp only
    rw [m3 a (by omega), m2 a (by omega), m1]

/-- **The two bits**: the bit of the query chain is `1`, the other one is tested. -/
def bitsQ : Stmt :=
  .ifLtN sSide K1 (.seq (block [.copyN bL K1]) (bitT (sw 21) bR))
    (.seq (block [.copyN bR K1]) (bitT (sw 20) bL))

set_option maxHeartbeats 4000000 in
theorem bitsQ_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c₀) {i : ℕ}
    (hi : i ≤ 1) (hs : c.nreg sSide = i)
    (hL : ChainCtx P W c (sw 20) J.left) (hR : ChainCtx P W c (sw 21) J.right)
    (hqH : 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n)
    (h0 : i = 0 → ((Qof P).vtx (c.nreg qH - 1)).2 ≤ J.left.top.2)
    (h1 : i = 1 → ((Qof P).vtx (c.nreg qH - 1)).2 ≤ J.right.top.2)
    (hroom : c.nreg ALLOC + 16966 ≤ W) :
    IRS P W c₀ bitsQ c 16966 (fun c' => (c'.nreg bL ≤ 1 ∧
      (c'.nreg bL = 1 ↔ ((Qof P).vtx (c.nreg qH - 1)).2 ≤ J.left.top.2)) ∧
      (c'.nreg bR ≤ 1 ∧ (c'.nreg bR = 1 ↔ ((Qof P).vtx (c.nreg qH - 1)).2 ≤ J.right.top.2)) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ bL → r ≠ bR → ¬ (sw 3230 ≤ r ∧ r < sw 3300) →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have s : ∀ r, 240700 ≤ r → r < 250000 → IScr r := fun r h1 h2 => iscr_sw h1 h2
  -- one branch: set `b₁ := 1`, test `b₂`
  have br : ∀ (b₁ b₂ d : ℕ) (C₁ C₂ : Chain), (b₁ = bL ∧ b₂ = bR ∨ b₁ = bR ∧ b₂ = bL) →
      IFix d → ChainCtx P W c d C₂ →
      IRS P W c₀ (.seq (block [.copyN b₁ K1]) (bitT d b₂)) c 16963 (fun c' =>
        c'.nreg b₁ = 1 ∧ c'.nreg b₂ ≤ 1 ∧
        (c'.nreg b₂ = 1 ↔ ((Qof P).vtx (c.nreg qH - 1)).2 ≤ C₂.top.2) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ b₁ → r ≠ b₂ → ¬ (sw 3230 ≤ r ∧ r < sw 3300) →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
    intro b₁ b₂ d C₁ C₂ hb hd hctx
    have hb1 : 243225 ≤ b₁ ∧ b₁ ≤ 243226 ∧ 243225 ≤ b₂ ∧ b₂ ≤ 243226 ∧ b₁ ≠ b₂ := by
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [bL, bR, sw]
    refine IRS.seq (K₂ := 16962) (IRS.block [.copyN b₁ K1] hI ⟨s _ (by omega) (by omega), trivial⟩) ?_
    rintro c₁ hI₁ - - rfl
    have v1 : ∀ r, r ≠ b₁ → regB c.nmem [.copyN b₁ K1] c.nreg r = c.nreg r := by
      intro r hr; simp only [regB, regI]; exact upd_other _ _ _ hr
    have e1 : regB c.nmem [.copyN b₁ K1] c.nreg b₁ = 1 := by
      simp only [regB, regI, upd_same, k1]
    have hctx₁ : ChainCtx P W { c with nreg := regB c.nmem [.copyN b₁ K1] c.nreg } d C₂ :=
      hctx.transport (v1 d (by unfold IFix at hd; omega)) (fun _ _ => rfl)
        (by simp only; rw [v1 ALLOC (by unfold ALLOC; omega)])
    have hA1 : regB c.nmem [.copyN b₁ K1] c.nreg ALLOC = c.nreg ALLOC := v1 _ (by unfold ALLOC; omega)
    have hq1 : regB c.nmem [.copyN b₁ K1] c.nreg qH = c.nreg qH := v1 _ (by unfold qH sw; omega)
    refine (bitT_irs hI₁ hK hctx₁ hd (by rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp)
      (by simp only; rwa [hq1])
      (by simp only; rw [hA1]; omega)).mono le_rfl ?_
    rintro c' ⟨q1, q2, q3, q4, q5⟩
    simp only [hq1, hA1] at q1 q2 q3 q4 q5
    refine ⟨?_, q1, q2, fun r r0 r1 r2 r3 r4 => ?_, q4, q5⟩
    · rw [q3 b₁ (not_oracle_sw (by omega) (by omega)) hb1.2.2.2.2
        (fun h => by unfold sw at h; omega) (by unfold ALLOC; omega), e1]
    · rw [q3 r r0 r2 r3 r4, v1 r r1]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · have ht : c.nreg sSide < c.nreg K1 := by rw [hs, k1]; norm_num
    refine (IRS.ifT ht (br bL bR (sw 21) J.left J.right (Or.inl ⟨rfl, rfl⟩)
      (by unfold IFix sw; omega) hR)).mono (by norm_num) ?_
    rintro c' ⟨q1, q2, q3, q4, q5⟩
    exact ⟨⟨by omega, ⟨fun _ => h0 rfl, fun _ => q1⟩⟩, ⟨q2, q3⟩,
      fun r r0 r1 r2 r3 r4 => q4 r r0 r1 r2 r3 r4, q5⟩
  · have ht : ¬ c.nreg sSide < c.nreg K1 := by rw [hs, k1]; norm_num
    refine (IRS.ifF ht (br bR bL (sw 20) J.right J.left (Or.inr ⟨rfl, rfl⟩)
      (by unfold IFix sw; omega) hL)).mono (by norm_num) ?_
    rintro c' ⟨q1, q2, q3, q4, q5⟩
    exact ⟨⟨q2, q3⟩, ⟨by omega, ⟨fun _ => h1 rfl, fun _ => q1⟩⟩,
      fun r r0 r1 r2 r3 r4 => q4 r r0 r2 r1 r3 r4, q5⟩

/-! ## The result store -/

/-- **Store four words** at `pR`. -/
def store4 (v0 v1 v2 v3 : ℕ) : Stmt :=
  .seq (.instr (.storeN pR v0)) (.seq (.instr (.addN tAq pR K1)) (.seq (.instr (.storeN tAq v1))
    (.seq (.instr (.addN tAq pR K2)) (.seq (.instr (.storeN tAq v2))
    (.seq (.instr (.addN tAq pR K3)) (.instr (.storeN tAq v3)))))))

/-- The memory after four stores. -/
def mem4' (m : ℕ → ℕ) (A v0 v1 v2 v3 : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd m A v0) (A + 1) v1) (A + 2) v2) (A + 3) v3

set_option maxHeartbeats 4000000 in
theorem store4_irs {v0 v1 v2 v3 : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (h1 : v1 ≠ tAq) (h2 : v2 ≠ tAq) (h3 : v3 ≠ tAq)
    (hA : c₀.nreg ALLOC ≤ c.nreg pR) (hW : c.nreg pR + 3 ≤ W) :
    IRS P W c₀ (store4 v0 v1 v2 v3) c 7 (fun c' =>
      c'.nmem = mem4' c.nmem (c.nreg pR) (c.nreg v0) (c.nreg v1) (c.nreg v2) (c.nreg v3) ∧
      (∀ r, r ≠ tAq → c'.nreg r = c.nreg r)) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have k2 : c.nreg K2 = 2 := hKc.2.2.2.2.2.1
  have k3 : c.nreg K3 = 3 := hKc.2.2.2.2.2.2
  have stA : IScr tAq := iscr_sw (by unfold tAq sw; norm_num) (by unfold tAq sw; norm_num)
  have pRA : pR ≠ tAq := by unfold pR tAq sw; norm_num
  have K2A : K2 ≠ tAq := by unfold K2 tAq sw; norm_num
  have K3A : K3 ≠ tAq := by unfold K3 tAq sw; norm_num
  unfold store4
  refine (IRS.seq (K₂ := 6) (IRS.store (v := v0) hI hA) ?_).mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - rfl
  refine IRS.seq (K₂ := 5) (IRS.instr1 (i := .addN tAq pR K1) hI₁ ⟨stA, by
    simp only; rw [k1]; omega⟩) ?_
  rintro c₂ hI₂ - - rfl
  simp only [regI] at hI₂ ⊢
  refine IRS.seq (K₂ := 4) (IRS.store (v := v1) hI₂ (by dsimp only; rw [upd_same, k1]; omega)) ?_
  rintro c₃ hI₃ - - rfl
  refine IRS.seq (K₂ := 3) (IRS.instr1 (i := .addN tAq pR K2) hI₃ ⟨stA, by
    dsimp only; rw [upd_other _ _ _ pRA, upd_other _ _ _ K2A, k2]; omega⟩) ?_
  rintro c₄ hI₄ - - rfl
  simp only [regI] at hI₄ ⊢
  refine IRS.seq (K₂ := 2) (IRS.store (v := v2) hI₄ (by
    dsimp only; rw [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ K2A, k2]; omega)) ?_
  rintro c₅ hI₅ - - rfl
  refine IRS.seq (K₂ := 1) (IRS.instr1 (i := .addN tAq pR K3) hI₅ ⟨stA, by
    dsimp only
    rw [upd_other _ _ _ pRA, upd_other _ _ _ pRA, upd_other _ _ _ K3A, upd_other _ _ _ K3A, k3]
    omega⟩) ?_
  rintro c₆ hI₆ - - rfl
  simp only [regI] at hI₆ ⊢
  refine (IRS.store (v := v3) hI₆ (by
    dsimp only; rw [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ pRA, upd_other _ _ _ K3A,
      upd_other _ _ _ K3A, k3]; omega)).mono le_rfl ?_
  rintro c' rfl
  dsimp only
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ K2A,
      upd_other _ _ _ K3A, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, k1, k2, k3]
    rfl
  · rw [upd_other _ _ _ hr, upd_other _ _ _ hr, upd_other _ _ _ hr]


/-! ## The per-query program -/

/-- The query position converted to the walk of `C`. -/
def convQ : Stmt := .ifLtN sSide K1 (convS (sw 45) (sw 33) qE zE) (convS (sw 40) (sw 34) qE zE)

/-- A pipeline register: the height code minus one. -/
def tH : ℕ := sw 3229

/-- **The per-query program** with the candidate steps `c0` (side `0`) and `c1` (side `1`). -/
def qryP (c0 c1 : Stmt) : Stmt :=
  .seq loadQ (.seq convQ (.seq flagS
    (.ifLtN zF K1 (store4 K0 K0 K0 K0)
      (.seq bitsQ (.seq (block [.constN accA 0]) (.seq (.ifLtN sSide K1 c0 c1)
        (.seq winQ (.seq recS (.seq (block [.subN tH qH K1]) (store4 K1 tH rL rR))))))))))

end

end SweepIo

end Chazelle.Core
