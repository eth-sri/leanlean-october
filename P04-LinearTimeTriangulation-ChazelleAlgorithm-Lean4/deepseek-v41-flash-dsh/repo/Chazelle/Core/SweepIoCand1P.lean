module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoCand1ShrSpec
public import Chazelle.Core.SweepIoCand1TabSpec

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the program and its frame

* the scratch registers `sw 4800 … 4813`, `ifEq`, the blocks `prepL`, `midB`, the program
  `cand1P tabB shrB bruteS sh`;
* `Mid`: the state after the local hit in the model of `C₂` (accumulator, good candidates, the
  first hit of `C₂` a candidate, frame); `fin1`, `fin2`: from `Mid` to the output;
* `midB_irs`: the edge `6 + midT C₂` of the top of `C₂` (third tour position).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

/-! ## Registers and programs -/

def tE : ℕ := sw 4800
def tH : ℕ := sw 4801
def nO : ℕ := sw 4802
def y34 : ℕ := sw 4804
def k2 : ℕ := sw 4805
def jx : ℕ := sw 4806
def tgt : ℕ := sw 4807
def m2 : ℕ := sw 4808
def ti : ℕ := sw 4809
def bt : ℕ := sw 4810
def tmp : ℕ := sw 4811
def dd : ℕ := sw 4812
def m2x : ℕ := sw 4813

/-- `t` if the registers `a`, `b` are equal, else `e`. -/
def ifEq (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e (.ifLtN b a e t)

/-- Copies of the position, `2 m₂ + 6`, `K₂`, `qJ - K₂`. -/
def prepL : List Instr :=
  [.copyN tE qE, .copyN tH qH, .subN y34 (sw 34) K1, .loadN k2 (sw 4), .subN jx qJ k2]

/-- The fields of the chain descriptor of `C₂`. -/
def midL : List Instr :=
  [.addN tmp (sw 21) K2, .loadN m2 tmp, .addN tmp (sw 21) K3, .loadN ti tmp,
    .addN tmp (sw 21) K4, .loadN bt tmp, .addN dd ti ti, .addN m2x m2 m2]

/-- `tgt := 6 + midT C₂`. -/
def midB : Stmt :=
  .seq (block midL)
    (ifEq bt K1 (block [.subN tgt m2x dd, .addN tgt tgt K6])
      (.ifLtN ti m2 (block [.addN tgt dd K6]) (block [.copyN tgt K6])))

/-- The box class: the local hit at the box twin in the model of `C₁` if `bL = 1`. -/
def boxB (sh : Stmt) : Stmt := .ifLtN K0 bL (lhs (sw 30) (sw 3) (sw 33) qE 0 sh) .skip

/-- The brute-force class: if `bL = 1`, the symbolic point and the brute-force shot. -/
def bruteB (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN K0 bL (.seq (callSym (sw 21) qE qH (sw 3230)) (bruteS sh)) .skip

/-- A vertex position other than the shared vertex: top test for an endpoint query. -/
def topT (tabB : Stmt) (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN jx k2
    (ifEq qE K6 (bruteB bruteS sh) (ifEq qE y34 (bruteB bruteS sh)
      (ifEq qE tgt (bruteB bruteS sh) tabB)))
    (bruteB bruteS sh)

/-- A position inside an edge. -/
def genT (tabB : Stmt) (bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .ifLtN jx k2 tabB (bruteB bruteS sh)

/-- A vertex position: shared test. -/
def zeroT (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  ifEq qE (sw 41) (shrB sh)
    (ifEq qE y34 (ifEq (sw 41) K6 (shrB sh) (topT tabB bruteS sh)) (topT tabB bruteS sh))

/-- A tour position. -/
def tourB (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (block prepL) (.seq (normS (sw 21) tE tH nO) (.seq midB
    (.ifLtN K0 tH (genT tabB bruteS sh) (zeroT tabB shrB bruteS sh))))

/-- **The candidate step of side `1`.** -/
def cand1P (tabB : Stmt) (shrB bruteS : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (lhs (sw 31) (sw 4) (sw 34) qE 1 sh)
    (ifEq qE K1 (boxB sh) (ifEq qE K3 (boxB sh) (tourB tabB shrB bruteS sh)))

/-! ## Run-step helpers -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem irs_ifEq {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (ifEq a b t e) c (K + 4) Q := by
  unfold ifEq
  by_cases h1 : c.nreg a < c.nreg b
  · exact (IRS.ifT h1 (he (⋄))).mono (⋄) (fun _ h => h)
  · refine (IRS.ifF h1 ?_).mono (K := K + 2 + 2) (⋄) (fun _ h => h)
    by_cases h2 : c.nreg b < c.nreg a
    · exact IRS.ifT h2 (he (⋄))
    · exact IRS.ifF h2 (ht (⋄))

/-! ## Frames -/

/-- The registers a candidate step may write (besides the oracle bands and the allocator). -/
def Alw (r : ℕ) : Prop :=
  (sw 1000 ≤ r ∧ r < sw 3200) ∨ (sw 3230 ≤ r ∧ r < sw 3400) ∨ (sw 4000 ≤ r ∧ r < sw 5000)

theorem candFr_of {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ Alw r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 h2 h3 h4 h5 => h r h1 (by rintro (x | x | x) <;> tauto) h5, ha, hm⟩

theorem candFr_alw {c c' : Config} (h : CandFr c c') :
    ∀ r, bandOf r ∉ oracleBands → ¬ Alw r → r ≠ ALLOC → c'.nreg r = c.nreg r :=
  fun r h1 h2 h3 => h.1 r h1 (fun x => h2 (Or.inl x)) (fun x => h2 (Or.inr (Or.inl x)))
    (fun x => h2 (Or.inr (Or.inr x))) h3

theorem candFr_trans {c c₁ c₂ : Config} (h₁ : CandFr c c₁) (h₂ : CandFr c₁ c₂) : CandFr c c₂ :=
  candFr_of (fun r a b d => (candFr_alw h₂ r a b d).trans (candFr_alw h₁ r a b d))
    (h₁.2.1.trans h₂.2.1) (fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans (h₁.2.2 a ha))

/-- The frame of a local hit. -/
theorem candFr_lhw {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  candFr_of (fun r a b d => h r a (by unfold LHW; unfold Alw sw at b; unfold sw; omega) d) ha hm

/-- The frame of a part. -/
theorem candFr_part {c c' : Config} (h : PartFr c c') : CandFr c c' :=
  candFr_of (fun r a b d => h.1 r a (by unfold Alw sw at b; unfold sw; omega)
    (by unfold Alw sw at b; unfold sw; omega) (by unfold Alw sw at b; unfold sw; omega) d)
    h.2.1 h.2.2

/-- A frame that writes only allowed registers. -/
theorem candFr_regs {c c' : Config} {S : ℕ → Prop} (hS : ∀ r, S r → Alw r)
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  candFr_of (fun r a b d => h r a (fun x => b (hS r x)) d) ha hm

/-- The pipeline registers are kept. -/
theorem candFr_pipe {c c' : Config} (h : CandFr c c') {r : ℕ} (hr : sw 3200 ≤ r ∧ r < sw 3230) :
    c'.nreg r = c.nreg r :=
  candFr_alw h r (not_oracle_sw (by unfold sw at hr; omega) (by unfold sw at hr; omega))
    (by unfold Alw; unfold sw at hr ⊢; omega) (by unfold ALLOC; unfold sw at hr; omega)

theorem candFr_qE {c c' : Config} (h : CandFr c c') : c'.nreg qE = c.nreg qE :=
  candFr_pipe h (by unfold qE sw; omega)
theorem candFr_qH {c c' : Config} (h : CandFr c c') : c'.nreg qH = c.nreg qH :=
  candFr_pipe h (by unfold qH sw; omega)
theorem candFr_qD {c c' : Config} (h : CandFr c c') : c'.nreg qD = c.nreg qD :=
  candFr_pipe h (by unfold qD sw; omega)
theorem candFr_bL {c c' : Config} (h : CandFr c c') : c'.nreg bL = c.nreg bL :=
  candFr_pipe h (by unfold bL sw; omega)
theorem candFr_bR {c c' : Config} (h : CandFr c c') : c'.nreg bR = c.nreg bR :=
  candFr_pipe h (by unfold bR sw; omega)
theorem candFr_qJ {c c' : Config} (h : CandFr c c') : c'.nreg qJ = c.nreg qJ :=
  candFr_pipe h (by unfold qJ sw; omega)

/-! ## The state after the local hit in the model of `C₂` -/

variable {J : Merge.Junction}

/-- **The state after the local hit in the model of `C₂`.** -/
def Mid (P : Polygon) (J : Merge.Junction) (z : Point) (c c' : Config) (L : Set ℝ) : Prop :=
  AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c' ∧
    (∀ τ ∈ L, 0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ)) ∧
    J.right.hitParam z (dirOf (c.nreg qD)) ∈ L ∧ CandFr c c'

/-- **A step that adds good candidates** keeps `Mid`. -/
theorem mid_step {z : Point} {c₂ c₃ : Config} {L L' : Set ℝ} (hM : Mid P J z c c₂ L)
    (hacc : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD))
      L' c₃) (hsub : L ⊆ L')
    (hg : ∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ)))
    (hF : CandFr c₂ c₃) : Mid P J z c c₃ L' :=
  ⟨hacc, fun τ hτ => (hg τ hτ).elim (fun h => hM.2.1 τ h) id, hsub hM.2.2.1,
    candFr_trans hM.2.2.2 hF⟩

/-- **The output**, from the first hit of `C₁` below its top. -/
theorem fin1 {z : Point} {c' : Config} {L : Set ℝ} (hq : QState P J 1 z c)
    (hM : Mid P J z c c' L)
    (h1 : z.2 ≤ J.left.top.2 → J.left.hitParam z (dirOf (c.nreg qD)) ∈ L) :
    CandOut P J z c c' ∧ CandFr c c' := by
  obtain ⟨-, -, -, -, hz₂, -, -, hσ, -⟩ := q1_facts hq
  exact ⟨⟨L, hM.1, hM.2.1, whole_mem hσ hz₂ hq.hfree hM.2.2.1 h1⟩, hM.2.2.2⟩

/-- **The output**, from the table step. -/
theorem fin2 {z : Point} {c' : Config} {L : Set ℝ} (hM : Mid P J z c c' L)
    (h : J.whole.hitParam z (dirOf (c.nreg qD)) ∈ L ∨
      J.whole.hitParam z (dirOf (c.nreg qD)) = J.right.hitParam z (dirOf (c.nreg qD))) :
    CandOut P J z c c' ∧ CandFr c c' := by
  refine ⟨⟨L, hM.1, hM.2.1, ?_⟩, hM.2.2.2⟩
  rcases h with h | h
  · exact h
  · rw [h]; exact hM.2.2.1

/-! ## The top edge of `C₂` -/

/-- A register outside `sw 4807 … 4813`. -/
def OutM (r : ℕ) : Prop := r < sw 4807 ∨ sw 4813 < r


theorem midB_irs (hI : IInv W c₀ c) (hK : Consts c) (hctx : ChainCtx P W c (sw 21) J.right) :
    IRS P W c₀ midB c 20 (fun c' => c'.nreg tgt = 6 + midT J.right ∧
      (∀ r, OutM r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  obtain ⟨-, -, hwf, ⟨H, hC, -⟩, -, hWm⟩ := hctx
  obtain ⟨-, -, -, hm2, hti, hbt⟩ := hC
  have hB : c.nreg 240021 + 5 ≤ c.nreg ALLOC := hwf.1
  have hAW := hI.hw.1 ALLOC
  have hT := J.right.topIdx_le
  obtain ⟨k0, k1, k6, k4, k5, k2', k3⟩ := hK
  have a2 : c.nmem (c.nreg 240021 + 2) = J.right.m := hm2
  have a3 : c.nmem (c.nreg 240021 + 3) = J.right.topIdx := hti
  have a4 : c.nmem (c.nreg 240021 + 4) = 1 ↔ J.right.sideBeta = true := hbt
  have kk2 : c.nreg 240615 = 2 := k2'
  have kk3 : c.nreg 240616 = 3 := k3
  have kk4 : c.nreg 240613 = 4 := k4
  have s : ∀ j, 4807 ≤ j → j ≤ 4813 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by unfold sw; omega) (by unfold sw; omega)
  -- the block
  have v : regB c.nmem midL c.nreg m2 = J.right.m ∧
      regB c.nmem midL c.nreg ti = J.right.topIdx ∧
      (regB c.nmem midL c.nreg bt = 1 ↔ J.right.sideBeta = true) ∧
      regB c.nmem midL c.nreg dd = 2 * J.right.topIdx ∧
      regB c.nmem midL c.nreg m2x = 2 * J.right.m ∧
      (∀ r, OutM r → regB c.nmem midL c.nreg r = c.nreg r) := by
    ϴ midL, regB, regI, upd, tmp, m2, ti, bt, dd, m2x, sw, K2, K3, K4
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · Θ kk2, a2
    · Θ kk3, a3
    · Θ kk4, a4
    · simp [kk3, a3]; ring
    · simp [kk2, a2]; ring
    · unfold OutM sw at hr
      simp only [show r ≠ 244811 by omega, show r ≠ 244808 by omega, show r ≠ 244809 by omega,
        show r ≠ 244810 by omega, show r ≠ 244812 by omega, show r ≠ 244813 by omega,
        ite_false]
  obtain ⟨vm, vi, vb, vd, vx, vo⟩ := v
  have ok : okB W c.nmem midL c.nreg := by
    ϴ midL, okB, okI, regI
    refine ⟨⟨s 4811 (⊛) (⊛), ?_⟩, s 4808 (⊛) (⊛),
      ⟨s 4811 (⊛) (⊛), ?_⟩, s 4809 (⊛) (⊛),
      ⟨s 4811 (⊛) (⊛), ?_⟩, s 4810 (⊛) (⊛),
      ⟨s 4812 (⊛) (⊛), ?_⟩, ⟨s 4813 (⊛) (⊛), ?_⟩, trivial⟩
    all_goals simp [upd, tmp, m2, ti, bt, dd, sw, K2, K3, K4, kk2, kk3, kk4, a2, a3]
    all_goals (have := J.right.topIdx_le; ϴ' Merge.Junction.right_m at hWm this; omega)
  refine IRS.seq (K₁ := 8) (K₂ := 12) ((IRS.block midL hI ok).mono (⊚ midL)
    (fun _ h => h)) ?_
  rintro c₁ hI₁ - - rfl
  have hb6 := k6
  have e6 : regB c.nmem midL c.nreg K6 = 6 := by
    rw [vo _ (by unfold OutM K6 sw; omega)]; exact k6
  have e1 : regB c.nmem midL c.nreg K1 = 1 := by
    rw [vo _ (by unfold OutM K1 sw; omega)]; exact k1
  have fin : ∀ (l : List Instr) (c₂ : Config), c₂ = { c with nreg := regB c.nmem midL c.nreg } →
      IInv W c₀ c₂ → l.length ≤ 2 → okB W c₂.nmem l c₂.nreg →
      (∀ i ∈ l, dstI i = tgt) →
      regB c₂.nmem l c₂.nreg tgt = 6 + midT J.right →
      IRS P W c₀ (block l) c₂ 2 (fun c' => c'.nreg tgt = 6 + midT J.right ∧
        (∀ r, OutM r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
    intro l c₂ hc₂ hI₂ hlen hok hd hv
    refine (IRS.block l hI₂ hok).mono hlen ?_
    rintro c' rfl
    refine ⟨hv, fun r hr => ?_, Ρ hc₂⟩
    simp only
    rw [regB_other _ l _ (fun i hi h => by
      Ξ' hd i hi at h; subst h; unfold OutM tgt sw at hr; omega)]
    rw [hc₂]; exact vo r hr
  have st : IScr tgt := s 4807 le_rfl (⊛)
  refine irs_ifEq (K := 8) (fun hb => ?_) (fun hb => ?_)
  · simp only at hb
    have hβ : J.right.sideBeta = true := vb.1 (by rw [hb]; exact e1)
    have hmid : midT J.right = 2 * J.right.m - 2 * J.right.topIdx := by unfold midT; Ξ ite_eq_left hβ
    refine (fin [.subN tgt m2x dd, .addN tgt tgt K6] _ rfl hI₁ (✓) ?_ ?_ ?_).mono
      (⊛) (fun _ h => h)
    · ϴ okB, okI, regI
      refine ⟨st, ⟨st, ?_⟩, trivial⟩
      ϴ' upd, tgt, m2x, dd, K6, sw at *
      simp
      rw [vx, vd, e6]; omega
    · Θ dstI
    · ϴ regB, regI
      ϴ' upd, tgt, m2x, dd, K6, sw at *
      simp
      rw [vx, vd, e6, hmid]; omega
  · simp only at hb
    have hβ : J.right.sideBeta ≠ true := fun h => hb ((vb.2 h).trans e1.symm)
    refine IRS.ite (K := 6) (fun hl => ?_) (fun hl => ?_)
    · simp only at hl
      Ξ' vi, vm at hl
      have hmid : midT J.right = 2 * J.right.topIdx := by
        unfold midT; Ξ ite_eq_right hβ, ite_eq_left hl
      refine (fin [.addN tgt dd K6] _ rfl hI₁ (✓) ?_ ?_ ?_).mono
        (⊛) (fun _ h => h)
      · ϴ okB, okI
        refine ⟨⟨st, ?_⟩, trivial⟩
        rw [vd, e6]; omega
      · Θ dstI
      · ϴ regB, regI
        ϴ' upd, tgt, dd, K6, sw at *
        simp
        rw [vd, e6, hmid]; omega
    · simp only at hl
      Ξ' vi, vm at hl
      have hmid : midT J.right = 0 := by
        unfold midT; Ξ ite_eq_right hβ, ite_eq_right hl
      refine (fin [.copyN tgt K6] _ rfl hI₁ (✓) ?_ ?_ ?_).mono
        (⊛) (fun _ h => h)
      · ϴ okB, okI
        exact ⟨st, trivial⟩
      · Θ dstI
      · ϴ regB, regI
        ϴ' upd, tgt, K6, sw at *
        simp
        Ξ e6, hmid

end Cand1

end

end SweepIo

end Chazelle.Core
