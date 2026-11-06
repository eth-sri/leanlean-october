module

public import Chazelle.Golf

public import Chazelle.Core.SweepPrimSecRam
public import Chazelle.Core.NFLocateSpec

/-!
# Sweep RAM primitives (WP-D2), part 5: the calling convention, walk directions, turn tests

## Calling convention of the primitives

A primitive is `.seq pHead core`: `pHead` reads the chain descriptor whose address is in register
`50200`; the other inputs are in `50201 … 50209`, the outputs in `50210 …`.  A primitive writes
only the bands `bSign` and `bLocate` (registers `10000 … 10599`, `50000 … 50199` and
`50210 … 50999`: `Bprim`), no memory, and does not move the allocator.  Its contract
(`prim_meets`) has the precondition `PrimPre Inp` (good environment, the word bound
`hostWords n ≤ W`, a well-formed chain descriptor below the allocator, the input condition
`Inp`) and the postcondition `PrimPost Out` (the output condition `Out` for **every** chain the
descriptor describes, i.e. for the chain, `NFLoc.chain_eq_of_desc`).

## Primitives of this file (design-merge-v2 §9.6 item 2)

* `dirAt`: the direction code `WalkKey.dirCode (chainModel C) e` of a walk edge (the procedure
  of `NFLoc.chainDir` on the chain environment, which it restores).
* `turnNext`: the sign code (`sgnCode`) of `sideCross (W.vtx (p + 1) - W.vtx p) (σ, 0)`;
  `turnPrev`: that of `sideCross (σ, 0) (W.vtx (p - 1) - W.vtx p)` (indices modulo `n`,
  `σ = dirOf (register 50203)`), the turning conditions of `Sweep.genuine_of_after` and
  `Sweep.genuine_of_before`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)

@[expose] public section

/-! ## The calling convention -/

/-- The registers a primitive may write. -/
def Bprim (r : ℕ) : Bool :=
  decide (10000 ≤ r ∧ r < 10600) || decide (50000 ≤ r ∧ r < 50200) ||
    decide (50210 ≤ r ∧ r < 51000)

/-- The bands of the primitives. -/
def primBands : Finset ℕ := {bSign, bLocate}

theorem Bprim_band (r : ℕ) (h : Bprim r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  ϴ' Bprim, Bool.or_eq_true, decide_eq_true_eq at h
  refine ⟨?_, by unfold ALLOC; omega⟩
  ϴ primBands, bandOf, bSign, bLocate, Finset.mem_insert, Finset.mem_singleton
  omega

/-- **The precondition of a primitive**: good environment, word bound, a well-formed chain
descriptor below the allocator at the address in `50200`, and the input condition. -/
def PrimPre (Inp : Polygon → ℕ → Chain → Config → Prop) (P : Polygon) (W : ℕ) (c : Config) :
    Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 50200) ∧
    ∃ H C, ChainDescAt c.nmem (c.nreg 50200) (Qof P) H C ∧ Inp P W C c

/-- **The postcondition of a primitive**: the output condition for the chain of the
descriptor. -/
def PrimPost (Out : Polygon → Chain → Config → Config → Prop) (P : Polygon) (c c' : Config) :
    Prop :=
  ∀ H C, ChainDescAt c.nmem (c.nreg 50200) (Qof P) H C → Out P C c c'

/-- The input registers survive `pHead`. -/
theorem pHead_inputs {c c' : Config} (h : FrameB Bhead c c') :
    ∀ r, 50200 ≤ r → r < 50210 → c'.nreg r = c.nreg r := fun r h1 h2 =>
  h.1 r (by simp only [Bhead, Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)

/-- **From an execution lemma of the core to the contract of the primitive.** -/
theorem prim_meets {core : Stmt} {B : ℕ → Bool} {K : ℕ}
    {Inp : Polygon → ℕ → Chain → Config → Prop} {Out : Polygon → Chain → Config → Config → Prop}
    (hB : ∀ r, B r = true → Bprim r = true) (hwr : wr B (.seq pHead core) = true)
    (hcore : ∀ (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c₀ c : Config),
      ChainDescAt c₀.nmem (c₀.nreg 50200) (Qof P) H C →
      CEnv P W H C c → Inp P W C c₀ → (∀ r, 50200 ≤ r → r < 50210 → c.nreg r = c₀.nreg r) →
      ∃ c' k, Exec P W core c c' k ∧ k ≤ K ∧ Out P C c₀ c') :
    Meets (.seq pHead core) primBands (PrimPre Inp) (PrimPost Out) (fun _ _ => K + 800) := by
  intro P W c hw ⟨hG, hW, hwf, H, C, hC, hin⟩ hroom
  obtain ⟨hX5, hwf'⟩ := hwf
  obtain ⟨hlen, hHwf, haW, hs⟩ := hwf' H C hC
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hE₁⟩ := pHead_exec hG hW c hw rfl hC (⋄) hlen hHwf
    (⋄) hs
  obtain ⟨c₂, k₂, e₂, hk₂, hout⟩ := hcore P W H C c c₁ hC hE₁ hin (pHead_inputs f₁)
  have ex : Exec P W (.seq pHead core) c c₂ (k₁ + k₂) := .seq e₁ e₂
  refine ⟨c₂, _, ex, by simp only; omega, fun H' C' hC' => ?_, frame_of_frameB (exec_frameB ex hwr)
    (fun r hr => Bprim_band r (hB r hr)) _⟩
  Ξ ← chain_eq_of_desc hC hC'
  exact hout

/-! ## The direction of a walk edge -/

/-- The direction procedure of `NFLoc.chainDir` without its header (edge in `50002`). -/
def dirCore : Stmt :=
  .ifLtN 50002 50081 smallDir
    (.seq (block [.subN 50056 50002 50081, .subN 50057 50056 50053])
      (.ifLtN 50057 50053 chGeneral (setDir 1)))

/-- Restore the chain environment (the constant `1` and the host count). -/
def envRestore : Stmt := .seq (.instr (.constN 50032 1)) (.seq cntStmt (.instr (.copyN 50087 50063)))

/-- **The direction code of the walk edge in `50002`** into `10502`. -/
def dirAt : Stmt := .seq dirCore envRestore

/-- The registers `dirCore` may write: those of `NFLoc`'s direction procedure except the
descriptor registers of the chain environment. -/
def Bdc (r : ℕ) : Bool :=
  Bdir r && !([50052, 50053, 50054, 50055, 50060, 50081, 50082, 50083, 50084, 50085].contains r)

theorem wr_dirCore : wr Bdc dirCore = true := ⌖

theorem wr_dirAt : wr Bdir dirAt = true := ⌖

/-- **The direction code of a walk edge** (at most `82 |H| + 640` steps). -/
theorem dirAt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e : ℕ} (h02 : c.nreg 50002 = e) (he : e < 2 * C.m + 7) :
    ∃ c' k, Exec P W dirAt c c' k ∧ k ≤ 82 * H.length + 640 ∧ FrameB Bdir c c' ∧
      CEnv P W H C c' ∧ c'.nreg 10502 = dirCode (chainModel C) e := by
  have hw := hE.wb
  have hG := hE.hG
  have hW := hE.hW
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hNlen := hE.n_eq
  have hmN := C.m_lt
  have hT := C.topIdx_le
  have hm1 := C.one_le
  -- the core
  obtain ⟨c₁, k₁, e₁, hk₁, d₁⟩ : ∃ c₁ k₁, Exec P W dirCore c c₁ k₁ ∧ k₁ ≤ 70 * H.length + 600 ∧
      c₁.nreg 10502 = dirCode (chainModel C) e := by
    by_cases hsm : e < 6
    · obtain ⟨c₂, k₂, e₂, hk₂, d₂⟩ := smallDir_exec (P := P) c hw (⋄) hE.r32 hE.r82
        hE.r83 hE.r84 hE.r85 (by rw [h02]; exact hsm)
      refine ⟨c₂, _, .ifLtN_true (by rw [h02, hE.r81]; exact hsm) e₂, ⋄, ?_⟩
      Ξ d₂, h02, chain_dirCode_small C hsm
    obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
        (block [.subN 50056 50002 50081, .subN 50057 50056 50053]) c c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
        ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c.nreg r := by
      exec_block
      refine ⟨rfl, by config_simp; rw [h02, hE.r81], by config_simp; rw [h02, hE.r81, hE.r53],
        fun r h1 h2 => ⊚ h1, h2⟩
    have w₂ := e₂.wb_right
    have p53 : c₂.nreg 50053 = C.m := Ρ r₂ _ (⋄) (⋄), hE.r53
    by_cases hg : e - 6 - C.m < C.m
    · have hi : e - 6 < 2 * C.m := ⋄
      have hH₂ : HostAt c₂.nmem (c.nreg 50060) H := by
        have f₂ := exec_frameB e₂ (B := Bl [50056, 50057]) (⌖)
        rw [f₂.2.2.1]; exact hE.hH
      obtain ⟨c₃, k₃, e₃, hk₃, sp₁, sp₂, hsp₁, hsp₂, d₃⟩ := chGeneral_exec (P := P) hG hW c₂ w₂
        hH₂ hE.wf hE.aW hE.NW hE.hs (by rw [← hNlen]; exact hmN) hT hi
        (Ρ r₂ _ (⋄) (⋄), hE.r32) (Ρ r₂ _ (⋄) (⋄))
        (Ρ r₂ _ (⋄) (⋄), hE.r52) p53
        (Ρ r₂ _ (⋄) (⋄), hE.r54) rfl q56
      refine ⟨c₃, _, .ifLtN_false (by rw [h02, hE.r81]; exact hsm)
        (.seq e₂ (.ifLtN_true (by rw [q57, p53]; exact hg) e₃)), ⋄, ?_⟩
      Ξ d₃, show e = (e - 6) + 6 by omega, chain_dirCode_tour C hi
      obtain ⟨i1, i2⟩ := sideIdx_pair C (e - 6)
      have hS : (if c₂.nreg 50055 = 1 then C.topIdx else 2 * C.m - C.topIdx) =
          C.sideS C.sideBeta := by
        Ξ r₂ _ (⋄) (⋄)
        unfold Chain.sideS
        by_cases hb : C.sideBeta = true
        · Ξ ite_eq_left (hE.r55.2 hb), ite_eq_left hb
        · Ξ ite_eq_right (mt hE.r55.1 hb), ite_eq_right hb
      Ξ' hS, ← hNlen, ← i1 at hsp₁
      Ξ' hS, ← hNlen, ← i2 at hsp₂
      rw [chain_vertex_host C hE.hP _ (by rw [hQn]; exact hsp₁),
        chain_vertex_host C hE.hP _ (by rw [hQn]; exact hsp₂)]
    · have hlast : e = 2 * C.m + 6 := ⋄
      have hsm' : ¬ c.nreg 50002 < c.nreg 50081 := by rw [h02, hE.r81]; exact hsm
      have hg' : ¬ c₂.nreg 50057 < c₂.nreg 50053 := by rw [q57, p53]; exact hg
      refine ⟨{ c₂ with nreg := upd c₂.nreg 10502 1 }, _, .ifLtN_false hsm'
        (.seq e₂ (.ifLtN_false hg' (Exec.constN w₂ _ _ (⋄)))), ⋄, ?_⟩
      ϴ upd_same
      Ξ hlast, chain_dirCode_last
  have f₁ := exec_frameB e₁ wr_dirCore
  have w₁ := e₁.wb_right
  -- restoring the environment
  have e₂ := Exec.constN (P := P) w₁ 50032 1 (⋄)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50032 1 } with hc₂
  have w₂ : WordsBounded W c₂ := e₂.wb_right
  have m₂ : c₂.nmem = c.nmem := by rw [hc₂]; exact f₁.2.2.1
  have k₂ : ∀ r, Bdc r = false → r ≠ 50032 → c₂.nreg r = c.nreg r := fun r hr h => by
    rw [hc₂]; simp only [upd]; rw [ite_eq_right h]; exact f₁.1 r hr
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, n63, E₃⟩ := cnt_exec (P := P) (n := P.n) c₂ w₂
    (by rw [m₂]; exact hE.hH) (k₂ _ (⌖) (⌖))
    hE.aW (by have := hE.NW; omega)
  have w₃ := e₃.wb_right
  have e₄ := Exec.copyN (P := P) w₃ 50087 50063
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 50087 (c₃.nreg 50063) } with hc₄
  have ex : Exec P W dirAt c c₄ (k₁ + (1 + (k₃ + 1))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have r₄ : ∀ r, r ≠ 50087 → c₄.nreg r = c₃.nreg r := fun r hr => by rw [hc₄]; Θ hr
  have hlen := hE.hlen
  refine ⟨c₄, _, ex, ⋄, exec_frameB ex wr_dirAt, ?_, ?_⟩
  · refine hE.keep e₄.wb_right (by rw [hc₄]; show c₃.nmem = c.nmem; rw [f₃.2.2.1, m₂])
      fun r hr => ?_
    ϴ' envRegs, List.mem_cons, List.not_mem_nil, or_false at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · rw [r₄ _ (⌖), f₃.1 _ (⌖), hc₂]; Θ hE.r32
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), E₃.h61, hE.host.h61
    · Ξ r₄ _ (⌖), E₃.h67, hE.host.h67
    · Ξ r₄ _ (⌖), E₃.h68, hE.host.h68
    · Ξ r₄ _ (⌖), E₃.h69, hE.host.h69
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · Ξ r₄ _ (⌖), f₃.1 _ (⌖), k₂ _ (⌖) (⌖)
    · rw [hc₄]; Θ n63, hE.r87
  · rw [r₄ _ (⌖), f₃.1 _ (⌖), hc₂]; Θ d₁

/-! ## Turning tests -/

/-- The sign code of a real number: `1` positive, `2` negative, `0` zero. -/
noncomputable def sgnCode (x : ℝ) : ℕ := if 0 < x then 1 else if x < 0 then 2 else 0

/-- The sign code the machine computes from a direction code `d` and a direction register `σ`. -/
def turnCode (d σ : ℕ) : ℕ :=
  if d = 0 then 0 else if σ = 1 then (if d = 2 then 1 else 2) else (if d = 2 then 2 else 1)

/-- The output of the turning tests: `50210 := turnCode (10502) (50203)`. -/
def turnOut : Stmt :=
  .ifLtN 10502 50032 (.instr (.constN 50210 0))
    (.ifLtN 50203 50032
      (.ifLtN 50032 10502 (.instr (.constN 50210 2)) (.instr (.constN 50210 1)))
      (.ifLtN 50032 50203
        (.ifLtN 50032 10502 (.instr (.constN 50210 2)) (.instr (.constN 50210 1)))
        (.ifLtN 50032 10502 (.instr (.constN 50210 1)) (.instr (.constN 50210 2)))))

theorem turnOut_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (hd : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W turnOut c c' k ∧ k ≤ 9 ∧ c'.nreg 50210 = turnCode (c.nreg 10502)
      (c.nreg 50203) ∧ ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  unfold turnOut
  have fin : ∀ v, v ≤ 2 → v = turnCode (c.nreg 10502) (c.nreg 50203) →
      ∃ c' k, Exec P W (.instr (.constN 50210 v)) c c' k ∧ k = 1 ∧
      c'.nreg 50210 = turnCode (c.nreg 10502) (c.nreg 50203) ∧
        ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := fun v hv hvt =>
    ⟨_, 1, Exec.constN hw _ _ (⋄), rfl, by simp [hvt], fun r hr => by simp [hr]⟩
  unfold turnCode at fin
  by_cases h0 : c.nreg 10502 < c.nreg 50032
  · obtain ⟨c', k, e, hk, h1, h2⟩ := fin 0 (⋄) (by rw [h32] at h0; simp [show c.nreg 10502 = 0 by omega])
    exact ⟨c', _, .ifLtN_true h0 e, ⋄, h1, h2⟩
  rw [h32] at h0
  have g0 : ¬ c.nreg 10502 < c.nreg 50032 := by rw [h32]; exact h0
  by_cases hs : c.nreg 50203 < c.nreg 50032
  · rw [h32] at hs
    have gs : c.nreg 50203 < c.nreg 50032 := by rw [h32]; exact hs
    by_cases h2 : c.nreg 50032 < c.nreg 10502
    · rw [h32] at h2
      obtain ⟨c', k, e, hk, h1, h3⟩ := fin 2 le_rfl (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_true gs (.ifLtN_true (by rw [h32]; exact h2) e)),
        ⋄, h1, h3⟩
    · rw [h32] at h2
      obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 (⋄) (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_true gs (.ifLtN_false (by rw [h32]; exact h2) e)),
        ⋄, h1, h3⟩
  rw [h32] at hs
  have gs : ¬ c.nreg 50203 < c.nreg 50032 := by rw [h32]; exact hs
  by_cases hs2 : 1 < c.nreg 50203
  · have gs2 : c.nreg 50032 < c.nreg 50203 := by rw [h32]; exact hs2
    by_cases h2 : 1 < c.nreg 10502
    · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 2 le_rfl (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_true gs2
        (.ifLtN_true (by rw [h32]; exact h2) e))), ⋄, h1, h3⟩
    · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 (⋄) (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_true gs2
        (.ifLtN_false (by rw [h32]; exact h2) e))), ⋄, h1, h3⟩
  · have gs2 : ¬ c.nreg 50032 < c.nreg 50203 := by rw [h32]; exact hs2
    by_cases h2 : 1 < c.nreg 10502
    · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 (⋄) (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_false gs2
        (.ifLtN_true (by rw [h32]; exact h2) e))), ⋄, h1, h3⟩
    · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 2 le_rfl (by split_ifs <;> omega)
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_false gs2
        (.ifLtN_false (by rw [h32]; exact h2) e))), ⋄, h1, h3⟩

theorem dirCode_le_two (M : Model) (e : ℕ) : dirCode M e ≤ 2 := by
  unfold dirCode; split_ifs <;> omega

/-- **The turning sign after a vertex**: `sideCross (b - v) (s, 0)` for the walk edge `v → b`. -/
theorem sgnCode_turnNext (M : Model) (p σ : ℕ) :
    sgnCode (sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((dirOf σ, 0) : Point)) =
      turnCode (dirCode M p) σ := by
  have e : sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((dirOf σ, 0) : Point) =
      -(dirOf σ * ((M.W.vtx ((p + 1) % M.W.n)).2 - (M.W.vtx p).2)) := by
    unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  Ξ e
  unfold sgnCode turnCode dirCode Model.wa Model.wb dirOf
  split_ifs <;> first | rfl | omega | (exfalso; linarith)

/-- **The turning sign before a vertex**: `sideCross (s, 0) (a - v)` for the walk edge
`a → v`. -/
theorem sgnCode_turnPrev (M : Model) {p : ℕ} (hp : p < M.W.n) (σ : ℕ) :
    sgnCode (sideCross ((dirOf σ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p)) =
      turnCode (dirCode M ((p + M.W.n - 1) % M.W.n)) σ := by
  have hq : ((p + M.W.n - 1) % M.W.n + 1) % M.W.n = p := by
    have hn : 0 < M.W.n := ⋄
    rcases Nat.eq_zero_or_pos p with rfl | h0
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (show M.W.n - 1 < M.W.n by omega),
        Nat.sub_add_cancel hn, Nat.mod_self]
    · rw [show p + M.W.n - 1 = (p - 1) + M.W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show p - 1 < M.W.n by omega), Nat.sub_add_cancel h0,
        Nat.mod_eq_of_lt hp]
  Ξ ← sgnCode_turnNext M _ σ, hq
  congr 1
  unfold sideCross; simp only [Prod.fst_sub, Prod.snd_sub]; ring

end

end SweepPrim

end Chazelle.Core
