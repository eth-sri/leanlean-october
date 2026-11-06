module

public import Chazelle.Core.SweepIoCand0U

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0` (`Cand0Spec`)

**`cand0Spec (hM : Side0MathSpec) (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec`.**

The initialisation and its fact `Aux` are those of `S0CandSpec`.  The per-query procedure
`cand0 lab0 candC sh`:

1. the local hit in the model of `C₁` at the query position (`start_irs`);
2. `bR = 0` (above the top of `C₂`): done (`above_out`);
3. a query on a vertical side of the box (`qE < 4`): the local hit in the model of `C₂` at the
   same position (`box_irs`);
4. otherwise the class test (`cls0`): normalise `(qE, qH)` in the model of `C₁` (`normS`); the
   shared vertex is the position with parameter `0` on the edge `cstL 1` (or on the last walk
   edge when `cstL 1 = 6`) (`shared_iff₁`): then `sharedS` (`shared_irs`), else `mainS`
   (`main_irs`).

Cost `κ0 κL κS D · (F γ + TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The program -/

/-- Scratch registers of the class test. -/
def nE : ℕ := sw 4810
def nH : ℕ := sw 4811
def nO : ℕ := sw 4812
def tq : ℕ := sw 4814

/-- The test of the last walk edge (`qE + 1 = 2 m₁ + 7` and `cstL 1 = 6`). -/
def t3S (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (block [.addN tq qE K1])
    (.ifLtN tq (sw 33) (mainS lab0 candC sh) (.ifLtN K6 (sw 46) (mainS lab0 candC sh) (sharedS sh)))

/-- **The class test** of a query off the box, not above the top of `C₂`. -/
def cls0 (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (block [.copyN nE qE, .copyN nH qH])
    (.seq (normS (sw 20) nE nH nO)
      (.ifLtN K0 nH (mainS lab0 candC sh)
        (.ifLtN qE (sw 46) (t3S lab0 candC sh)
          (.ifLtN (sw 46) qE (t3S lab0 candC sh) (sharedS sh)))))

/-- **The candidate step of side `0`.** -/
def cand0 (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (lhs (sw 30) (sw 3) (sw 33) qE 0 sh)
    (.ifLtN bR K1 .skip
      (.ifLtN qE K4 (lhs (sw 31) (sw 4) (sw 34) qE 1 sh) (cls0 lab0 candC sh)))

/-- The cost of a branch (main class or shared vertex). -/
def Kbr (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  Kmain κL κS c₀ F + (35007 + (Klh c₀ F + 2))

/-- The cost of the class test. -/
def Kcls (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ := 11030 + Kbr κL κS c₀ F

/-- The cost of the candidate step. -/
def Kc0 (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  Klh c₀ F + (2 + (2 + (Klh c₀ F + Kcls κL κS c₀ F)))

/-! ## Frames of the scratch blocks -/

/-- The accumulator state survives a step keeping the accumulator registers. -/
theorem AccSt.keep {J : Merge.Junction} {z : Point} {L : Set ℝ} {c₁ c₂ : Config}
    (h : AccSt P J z c L c₁) (hr : ∀ j, j ≤ 12 → c₂.nreg (accA + j) = c₁.nreg (accA + j)) :
    AccSt P J z c L c₂ :=
  ⟨h.1.transport hr, h.2⟩

/-- The scratch set of the class test. -/
def NS (r : ℕ) : Prop := sw 4810 ≤ r ∧ r ≤ sw 4814

theorem candFr_ns {c₁ c₂ : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r)
    (hA : c₁.nreg ALLOC ≤ c₂.nreg ALLOC) (hm : ∀ a, a < c₁.nreg ALLOC → c₂.nmem a = c₁.nmem a) :
    CandFr c₁ c₂ :=
  candFr_of_set (fun r hr => Or.inr (by unfold NS sw at hr; unfold sw; omega)) h hA hm

theorem acc_ns {c₁ c₂ : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) :
    ∀ j, j ≤ 12 → c₂.nreg (accA + j) = c₁.nreg (accA + j) := fun j hj =>
  h _ (not_oracle_sw (by unfold accA sw; omega) (by unfold accA sw; omega))
    (by unfold NS accA sw; omega) (by unfold accA ALLOC sw; omega)

/-! ## The class test -/

section Steps

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}
  {lab0 : Stmt → Stmt} {candC : Stmt} {Aux : Polygon → Merge.Junction → NF → Config → Prop}
  {κL κS : ℕ → ℕ}

theorem kmain_le : Kmain κL κS c₀ F ≤ Kbr κL κS c₀ F := by unfold Kbr; omega
theorem kshared_le : 35007 + (Klh c₀ F + 2) ≤ Kbr κL κS c₀ F := by unfold Kbr; omega

set_option maxHeartbeats 8000000 in
/-- **The test of the last walk edge.** -/
theorem t3_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L)
    (hzL : z ∈ J.left.set) (hbR : c.nreg bR = 1)
    (hpar : (chainModel J.left).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = 0)
    (hne : c.nreg qE ≠ cstL J 1)
    (hroom : c'.nreg ALLOC + (1 + (2 + (2 + Kbr κL κS c₀ F))) ≤ W) :
    IRS P W c₀ (t3S lab0 candC sh) c' (1 + (2 + (2 + Kbr κL κS c₀ F))) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  have q := q0_of hQ
  obtain ⟨eE, -, -, -, -, -, -, -⟩ := pipe8 hfr
  have hK := hA.hK.fix hI
  have hWq : c'.nreg qE + c'.nreg K1 ≤ W := by
    rw [hK.2.1]; have := hI.hw.1 qE; have := hI.hw.1 ALLOC
    rw [eE]; have := q.he; rw [cm_n] at this
    have := hA.hWm; have : J.left.m ≤ J.whole.m := by show J.m₁ ≤ J.m₁ + J.m₂; omega
    omega
  unfold t3S
  refine IRS.seq (K₁ := 1) ((IRS.block [.addN tq qE K1] hI (by
    simp only [okB, okI]; exact ⟨⟨iscr_sw (by unfold tq sw; omega) (by unfold tq sw; omega),
      hWq⟩, trivial⟩)).mono (by simp) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' hc₂
  have hm₂ : c₂.nmem = c'.nmem := by rw [hc₂]
  have hr₂ : ∀ r, r ≠ tq → c₂.nreg r = c'.nreg r := fun r hr => by
    rw [hc₂]; simp only [regB, regI, ]; exact upd_other _ _ _ hr
  have htq : c₂.nreg tq = c'.nreg qE + c'.nreg K1 := by
    rw [hc₂]; simp only [regB, regI, ]; exact upd_same _ _ _
  have fr2 : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c'.nreg r :=
    fun r _ h2 _ => hr₂ r (fun h => h2 (by subst h; unfold NS tq sw; omega))
  have hfr₂ : CandFr c c₂ := hfr.trans (candFr_ns fr2 hA₂ (fun a _ => by rw [hm₂]))
  have hst₂ : AccSt P J z c L c₂ := hst.keep (acc_ns fr2)
  have hA2e : c₂.nreg ALLOC = c'.nreg ALLOC := hr₂ ALLOC (by unfold tq ALLOC sw; omega)
  obtain ⟨eE2, -, -, -, -, -, -, -⟩ := pipe8 hfr₂
  have e33 : c₂.nreg (sw 33) = 2 * J.m₁ + 7 := by
    rw [hI₂.hin _ (by unfold IFix sw; omega)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -⟩ := hA.hst
    exact h33
  have e46 : c₂.nreg (sw 46) = cstL J 1 := by
    rw [hI₂.hin _ (by unfold IFix sw; omega)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, -⟩ := hA.hst
    exact h45 1 (by norm_num)
  have hK₂ := hA.hK.fix hI₂
  have htq' : c₂.nreg tq = c.nreg qE + 1 := by rw [htq, eE, hK.2.1]
  have hmain : z ≠ J.shared → IRS P W c₀ (mainS lab0 candC sh) c₂ (Kbr κL κS c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := fun hzs =>
    (main_irs hM hLab hSC hsh hBs hXl hA hAux hI₂ hQ hfr₂ hst₂ hl hzL hzs hbR
      (by have := kmain_le (κL := κL) (κS := κS) (c₀ := c₀) (F := F); omega)).mono kmain_le
      (fun _ h => h)
  have hn₁ : c.nreg qE < 2 * J.m₁ + 7 := by have := q.he; rwa [cm_n] at this
  refine (IRS.ite (K := 2 + Kbr κL κS c₀ F) (fun h1 => ?_) (fun h1 => ?_)).mono (by omega)
    (fun _ h => h)
  · refine (hmain fun hzs => ?_).mono (by omega) (fun _ h => h)
    rw [htq', e33] at h1
    rcases ((shared_iff₁ hA.hP (Qof P) q.he q.hP0 q.hP1).1 (q.hpos.trans hzs)).2 with h | h
    · exact hne h
    · have h' : c.nreg qE + 1 = 2 * J.m₁ + 7 := h.1
      omega
  · rw [htq', e33] at h1
    refine (IRS.ite (K := Kbr κL κS c₀ F) (fun h2 => ?_) (fun h2 => ?_)).mono (by omega)
      (fun _ h => h)
    · refine hmain fun hzs => ?_
      rw [hK₂.2.2.1, e46] at h2
      rcases ((shared_iff₁ hA.hP (Qof P) q.he q.hP0 q.hP1).1 (q.hpos.trans hzs)).2 with h | h
      · exact hne h
      · have h' : cstL J 1 = 6 := h.2
        omega
    · rw [hK₂.2.2.1, e46] at h2
      have h6 : cstL J 1 = 6 := by rw [cstL_one] at h2 ⊢; omega
      have hzs : z = J.shared := q.hpos.symm.trans
        ((shared_iff₁ hA.hP (Qof P) q.he q.hP0 q.hP1).2 ⟨hpar, Or.inr ⟨by show c.nreg qE + 1 = _; omega, h6⟩⟩)
      exact (shared_irs hsh hBs hXl hA hI₂ hQ hfr₂ hst₂ hl hzs
        (by have := kshared_le (κL := κL) (κS := κS) (c₀ := c₀) (F := F); omega)).mono
        kshared_le (fun _ h => h)

/-- The cost of `t3S`. -/
abbrev Kt3 (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ := 1 + (2 + (2 + Kbr κL κS c₀ F))

set_option maxHeartbeats 8000000 in
/-- **The class test.** -/
theorem cls0_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L)
    (hbR : c.nreg bR = 1) (h4 : 4 ≤ c.nreg qE)
    (hroom : c'.nreg ALLOC + Kcls κL κS c₀ F ≤ W) :
    IRS P W c₀ (cls0 lab0 candC sh) c' (Kcls κL κS c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  have q := q0_of hQ
  obtain ⟨eE, eH, -, -, -, -, -, -⟩ := pipe8 hfr
  have h6 : 6 ≤ c.nreg qE := by
    rcases q.hcls with h | ⟨h, -⟩ | ⟨h, -⟩
    · have h' : c.nreg qE = 1 ∨ c.nreg qE = 3 := h; omega
    · exact h
    · have h' : c.nreg qE = 2 * J.left.m + 6 := h; omega
  have hzL : z ∈ J.left.set := q.hpos ▸ posClass_mem q.hcls h6 q.hP0 q.hP1
  unfold cls0
  refine (IRS.seq (K₁ := 2) (K₂ := 11015 + (2 + (2 + (2 + Kt3 κL κS c₀ F))))
    ((IRS.block [.copyN nE qE, .copyN nH qH] hI (by
      simp only [okB, okI]
      exact ⟨iscr_sw (by unfold nE sw; omega) (by unfold nE sw; omega),
        iscr_sw (by unfold nH sw; omega) (by unfold nH sw; omega), trivial⟩)).mono
      (by simp) (fun _ h => h)) ?_).mono (by unfold Kcls Kt3; omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' hc₂
  have hm₂ : c₂.nmem = c'.nmem := by rw [hc₂]
  have v2 : c₂.nreg nE = c'.nreg qE ∧ c₂.nreg nH = c'.nreg qH ∧
      ∀ r, r ≠ nE → r ≠ nH → c₂.nreg r = c'.nreg r := by
    rw [hc₂]
    refine ⟨?_, ?_, fun r h1 h2 => ?_⟩ <;>
      simp (disch := (unfold nE nH qE qH sw at *; omega)) only [regB, regI, upd_same, upd_other]
  obtain ⟨vE, vH, vo⟩ := v2
  have fr2 : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c'.nreg r :=
    fun r _ h2 _ => vo r (fun h => h2 (by subst h; unfold NS nE sw; omega))
      (fun h => h2 (by subst h; unfold NS nH sw; omega))
  have hfr₂ : CandFr c c₂ := hfr.trans (candFr_ns fr2 hA₂ (fun a _ => by rw [hm₂]))
  have hst₂ : AccSt P J z c L c₂ := hst.keep (acc_ns fr2)
  have hA2e : c₂.nreg ALLOC = c'.nreg ALLOC := vo ALLOC (by unfold nE ALLOC sw; omega)
    (by unfold nH ALLOC sw; omega)
  have hK₂ := hA.hK.fix hI₂
  have hctx₂ : ChainCtx P W c₂ (sw 20) J.left :=
    (sideD₁ hA).hctx.transport (hI₂.hin _ (by unfold IFix sw; omega)) (fun a ha => hI₂.hm a ha)
      hI₂.hA
  rw [eE] at vE
  rw [eH] at vH
  -- normalise
  refine IRS.seq (K₁ := 11015) (normS_irs (dsc := sw 20) (pe := nE) (ph := nH) (o := nO) hI₂ hK₂
    hctx₂ (by unfold nE nH sw; omega) (by unfold nO nE nH sw; omega) (by rw [vE]; exact q.he)
    (by rw [vE, vH]; exact q.hpp) (fun h _ _ _ => by rw [vE] at h; omega)
    (by unfold Kcls at hroom; omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨n3E, n3H, fr3, hA3, hm3⟩
  rw [vE, vH] at n3H
  have fr3' : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => fr3 r h1 (fun h => h2 (by subst h; unfold NS nH sw; omega))
      (fun h => h2 (by subst h; unfold NS nO sw; omega))
      (fun h => h2 (by subst h; unfold NS nO sw; omega)) h3
  have hfr₃ : CandFr c c₃ := hfr₂.trans (candFr_ns fr3' hA3 hm3)
  have hst₃ : AccSt P J z c L c₃ := hst₂.keep (acc_ns fr3')
  obtain ⟨eE3, -, -, -, -, -, -, -⟩ := pipe8 hfr₃
  have hK₃ := hA.hK.fix hI₃
  have e46 : c₃.nreg (sw 46) = cstL J 1 := by
    rw [hI₃.hin _ (by unfold IFix sw; omega)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, -⟩ := hA.hst
    exact h45 1 (by norm_num)
  refine (IRS.ite (K := 2 + (2 + Kt3 κL κS c₀ F)) (fun h1 => ?_) (fun h1 => ?_)).mono (by omega)
    (fun _ h => h)
  · -- a positive parameter: not the shared vertex
    rw [hK₃.1, n3H] at h1
    have hpar : (chainModel J.left).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ≠ 0 := fun h0 =>
      by rw [(nhgt_eq_zero_iff _ _ _).2 h0] at h1; exact lt_irrefl _ h1
    refine (main_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL (fun hzs => hpar
      ((shared_iff₁ hA.hP (Qof P) q.he q.hP0 q.hP1).1 (q.hpos.trans hzs)).1) hbR
      (by have h := hroom; unfold Kcls Kbr at h; omega)).mono
      (by show _ ≤ 2 + (2 + (1 + (2 + (2 + Kbr κL κS c₀ F)))); unfold Kbr; omega) (fun _ h => h)
  · rw [hK₃.1, n3H] at h1
    have hpar : (chainModel J.left).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = 0 :=
      (nhgt_eq_zero_iff _ _ _).1 (by omega)
    refine (IRS.ite (K := 2 + Kt3 κL κS c₀ F) (fun h2 => ?_) (fun h2 => ?_)).mono (by omega)
      (fun _ h => h)
    · rw [eE3, e46] at h2
      exact (t3_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL hbR hpar (by omega)
        (by have h := hroom; unfold Kcls at h; show _ + (1 + (2 + (2 + Kbr κL κS c₀ F))) ≤ W; omega)).mono
        (by show _ ≤ 2 + (1 + (2 + (2 + Kbr κL κS c₀ F))); omega) (fun _ h => h)
    · rw [eE3, e46] at h2
      refine (IRS.ite (K := Kt3 κL κS c₀ F) (fun h3 => ?_) (fun h3 => ?_)).mono (by omega)
        (fun _ h => h)
      · rw [eE3, e46] at h3
        exact t3_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL hbR hpar (by omega)
          (by have h := hroom; unfold Kcls at h; show _ + (1 + (2 + (2 + Kbr κL κS c₀ F))) ≤ W; omega)
      · rw [eE3, e46] at h3
        have hzs : z = J.shared := q.hpos.symm.trans
          ((shared_iff₁ hA.hP (Qof P) q.he q.hP0 q.hP1).2 ⟨hpar, Or.inl (by
            show c.nreg qE = cstL J 1; omega)⟩)
        exact (shared_irs hsh hBs hXl hA hI₃ hQ hfr₃ hst₃ hl hzs
          (by have h := hroom; unfold Kcls Kbr at h; omega)).mono
          (by show _ ≤ 1 + (2 + (2 + Kbr κL κS c₀ F)); unfold Kbr; omega) (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- **The candidate step of side `0`.** -/
theorem cand0_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) (hI : IInv W c₀ c)
    (hQ : QState P J 0 z c) (h0 : c.nreg accA = 0) (hroom : c.nreg ALLOC + Kc0 κL κS c₀ F ≤ W) :
    IRS P W c₀ (cand0 lab0 candC sh) c (Kc0 κL κS c₀ F) (fun c' =>
      CandOut P J z c c' ∧ CandFr c c') := by
  unfold cand0 Kc0
  unfold Kc0 at hroom
  refine IRS.seq (start_irs hsh hBs hXl hA hI hQ h0 (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨L, hst, hl, hfr⟩
  obtain ⟨eE, -, -, -, -, -, -, eR⟩ := pipe8 hfr
  have hK₁ := hA.hK.fix hI₁
  have hbR1 := hQ.hbR.1
  refine (IRS.ite (K := 2 + (Klh c₀ F + Kcls κL κS c₀ F)) (fun h1 => ?_) (fun h1 => ?_)).mono
    (by omega) (fun _ h => h)
  · rw [hK₁.2.1, eR] at h1
    exact IRS.skip hI₁ (above_out hQ hfr hst hl (by omega))
  · rw [hK₁.2.1, eR] at h1
    have hbR : c.nreg bR = 1 := by omega
    refine (IRS.ite (K := Klh c₀ F + Kcls κL κS c₀ F) (fun h2 => ?_) (fun h2 => ?_)).mono
      (by omega) (fun _ h => h)
    · rw [hK₁.2.2.2.1, eE] at h2
      exact (box_irs hsh hBs hXl hA hI₁ hQ hfr hst hl hbR h2 (by omega)).mono (by omega)
        (fun _ h => h)
    · rw [hK₁.2.2.2.1, eE] at h2
      exact (cls0_irs hM hLab hSC hsh hBs hXl hA hAux hI₁ hQ hfr hst hl hbR (by omega)
        (by omega)).mono (by omega) (fun _ h => h)

end Steps

end

end SweepIo

end Chazelle.Core
