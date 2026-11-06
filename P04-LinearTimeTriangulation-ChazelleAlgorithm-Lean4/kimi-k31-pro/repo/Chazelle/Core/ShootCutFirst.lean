module

public import Chazelle.Core.ShootCutGen
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-G, part 29: the first piece

* `uFlag_exec`: the flag of the uncounted block and the position in it;
* the pieces `pSE`, `pSV`, `pVE` (kind `0`) and their weights (`wt_last_edge`: from the last
  edge `2m + 5` of the double boundary into the uncounted block, at most `1`);
* `first_exec`: the first piece, from the start `s` to the first walk vertex `c₀` of the main
  loop, or, when the subarc is short (`Done`), to its end `e`.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- **The flag of the uncounted block** of the walk edge in `src`, and its position there. -/
theorem uFlag_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) (src dst idx : ℕ)
    (h1 : src ≠ dst) (h2 : dst ≠ idx) (h3 : dst ≠ 150091) {p m : ℕ} (hs : d.nreg src = p)
    (hp : p < 2 * m + 7) (h96 : d.nreg 150096 = 6) (h91 : d.nreg 150091 = 1)
    (h32 : d.nreg 150032 = 2 * m + 6) (hW : 7 ≤ W) :
    ∃ d' k, Exec P W (uFlag src dst idx) d d' k ∧ k ≤ 8 ∧
      d'.nreg dst = (if p ≤ 5 ∨ p = 2 * m + 6 then 1 else 0) ∧ d'.nreg idx = uIx p ∧
      (∀ x, x ≠ dst → x ≠ idx → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold uFlag uIx
  by_cases hp6 : p < 6
  · refine spec_ifLtN_true (by rwx [hs, h96]) ?_
    refine spec_step (Exec.constN hw _ _ (by omega)) fun w₁ => ?_
    refine spec_step (Exec.addN w₁ _ _ _ (by
      simp only [upd, h1, Ne.symm h3, ite_false]; rwo [hs, h91]))
      fun w₂ => spec_nil w₂ ⟨by omega, ?_, ?_, fun x hx1 hx2 => ?_, rfl⟩
    · simp only [upd, h2, ite_false, ite_true]; rw [ite_eq_left (by omega)]
    · simp only [upd, ite_true, h1, Ne.symm h3, ite_false]
      rw [hs, h91, ite_eq_left (by omega)]
    · simp only [upd, hx1, hx2, ite_false]
  · by_cases hpm : p < 2 * m + 6
    · refine spec_ifLtN_false (by rwx [hs, h96])
        (spec_ifLtN_true (by rwx [hs, h32]) ?_)
      refine spec_step (Exec.constN hw _ _ (by omega)) fun w₁ => ?_
      refine spec_step (Exec.constN w₁ _ _ (by omega))
        fun w₂ => spec_nil w₂ ⟨by omega, ?_, ?_, fun x hx1 hx2 => ?_, rfl⟩
      · simp only [upd, h2, ite_false, ite_true]; rw [ite_eq_right (by omega)]
      · simp only [upd, ite_true]; rw [ite_eq_right (by omega)]
      · simp only [upd, hx1, hx2, ite_false]
    · refine spec_ifLtN_false (by rwx [hs, h96])
        (spec_ifLtN_false (by rwx [hs, h32])
          (spec_ifLtN_false (by rwo [hs, h32]) ?_))
      refine spec_step (Exec.constN hw _ _ (by omega)) fun w₁ => ?_
      refine spec_step (Exec.constN w₁ _ _ (by omega))
        fun w₂ => spec_nil w₂ ⟨by omega, ?_, ?_, fun x hx1 hx2 => ?_, rfl⟩
      · simp only [upd, h2, ite_false, ite_true]; rw [ite_eq_left (by omega)]
      · simp only [upd, ite_true]; rw [ite_eq_right (by omega)]
      · simp only [upd, hx1, hx2, ite_false]

/-! ## The pieces of kind `0` -/

/-- The piece `[s, e]`. -/
def pSE (s e : WPos) : Pc := ⟨s, e, 0, 0, 0, 0, 0⟩

/-- The piece from `s` to the walk vertex `v`. -/
def pSV (s : WPos) (v : ℕ) : Pc := ⟨s, ⟨v, 0⟩, 0, 0, 0, 0, 0⟩

/-- The piece from the walk vertex `v` to `e`. -/
def pVE (v : ℕ) (e : WPos) : Pc := ⟨⟨v, 0⟩, e, 0, 0, 0, 0, 0⟩

/-- **From the last edge of the double boundary into the uncounted block**: weight at most
`1`. -/
theorem wt_last_edge (C : Chain) (Q : Polygon) {n : ℕ} {x y : WPos}
    (hx : ProperPos (chainModel C) Q n x) (hy : ProperPos (chainModel C) Q n y)
    (hxe : x.edge = 2 * C.m + 5) (hU : InU C y.edge) :
    (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1 := by
  rw [arcWt_chain C Q hx hy]
  have hc := le_keyCeil y.edge ((chainModel C).param Q y)
  have hc' := keyCeil_le y.edge ((chainModel C).param Q y)
  have hm := C.one_le
  unfold arcWtNat

  rw [hxe]
  split_ifs with h
  · omega
  · rcases hU with hU | hU
    · omega
    · exfalso
      apply h
      rw [hU]
      push_cast
      linarith [hx.2.1, hy.1]

variable {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ : ℕ}

theorem pSE_ok {s e : WPos} (hs : ProperPos (chainModel C) (Qof P) P.n s)
    (he : ProperPos (chainModel C) (Qof P) P.n e) (hs1 : s.edge < 2 * C.m + 7)
    (he1 : e.edge < 2 * C.m + 7)
    (hw : (chainModel C).arcWt ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e) ≤ 1) :
    PcOK P C m₀ h γ (pSE s e) :=
  ⟨hs, he, hs1, he1, Or.inl rfl, fun _ => hw, fun h1 => by simp [pSE] at h1⟩

theorem pSV_ok {s : WPos} {v : ℕ} (hs : ProperPos (chainModel C) (Qof P) P.n s)
    (hs1 : s.edge < 2 * C.m + 7) (hv : v < 2 * C.m + 7)
    (hw : (chainModel C).arcWt ((chainModel C).key (Qof P) s) (v : ℝ) ≤ 1) :
    PcOK P C m₀ h γ (pSV s v) :=
  ⟨hs, proper_vtx' P C v, hs1, hv, Or.inl rfl, fun _ => by simp only [pSV, key_hgt0]; exact hw,
    fun h1 => by simp [pSV] at h1⟩

theorem pVE_ok {e : WPos} {v : ℕ} (he : ProperPos (chainModel C) (Qof P) P.n e)
    (he1 : e.edge < 2 * C.m + 7) (hv : v < 2 * C.m + 7)
    (hw : (chainModel C).arcWt (v : ℝ) ((chainModel C).key (Qof P) e) ≤ 1) :
    PcOK P C m₀ h γ (pVE v e) :=
  ⟨proper_vtx' P C v, he, hv, he1, Or.inl rfl, fun _ => by simp only [pVE, key_hgt0]; exact hw,
    fun h1 => by simp [pVE] at h1⟩

/-- **A leaf**: a piece written by the block `B`, handed to `emit`, then one instruction `T`
(writing the register `tgt` of the core). -/
theorem leaf_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
    (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {pc : Pc} {B : Stmt} {T : Instr}
    {tgt : ℕ} {post : Config → Prop} (d : Config) (hI : I ps d) (hpv : Pv pc)
    (hB : ∃ d₁ k₁, Exec P W B d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ pc ∧ FrameB Scr d d₁ ∧
      (∀ r, Keep r → d₁.nreg r = d.nreg r))
    (hT : ∀ d₂ : Config, WordsBounded W d₂ → (∀ r, Keep r → d₂.nreg r = d.nreg r) →
      ∃ d₃, Exec P W (.instr T) d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧ post d₃ ∧
        (∀ r, r ≠ tgt → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem) :
    ∃ d' k, Exec P W (.seq B (.seq emit (.instr T))) d d' k ∧ k ≤ K + 6 ∧
      I (ps ++ [pc]) d' ∧ post d' ∧ (∀ r, Keep r → r ≠ tgt → d'.nreg r = d.nreg r) ∧
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  obtain ⟨d₁, k₁, e₁, hk₁, hR, fr₁, kp₁⟩ := hB
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp₂, mem₂⟩ := hE.run _ pc d₁ e₁.wb_right (hE.stable _ _ _ hI fr₁) hR hpv
  obtain ⟨d₃, e₃, fr₃, hp₃, r₃, m₃⟩ := hT d₂ e₂.wb_right fun r hr => (kp₂ r hr).trans (kp₁ r hr)
  refine ⟨d₃, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega, hE.stable _ _ _ hI₂ fr₃, hp₃,
    fun r hr h1 => by rw [r₃ r h1, kp₂ r hr, kp₁ r hr], fun a ha => ?_⟩
  rw [m₃, mem₂ a ha, fr₁.2.2.1]

theorem pcSE_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {s e : WPos}
    (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt) (h03 : d.nreg 150003 = e.edge)
    (h04 : d.nreg 150004 = e.hgt) :
    ∃ d₁ k₁, Exec P W pcSE d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ (pSE s e) ∧ FrameB Scr d d₁ ∧
      (∀ r, Keep r → d₁.nreg r = d.nreg r) := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcSE d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = s.edge ∧ d₁.nreg 150051 = s.hgt ∧ d₁.nreg 150052 = e.edge ∧
      d₁.nreg 150053 = e.hgt ∧ d₁.nreg 150054 = 0 ∧
      (∀ r, (r < 150050 ∨ 150055 ≤ r) → d₁.nreg r = d.nreg r) := by
    unfold pcSE
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    all_goals first | (config_simp; first | exact h01 | exact h02 | exact h03 | exact h04; done) |
      (config_simp; done) | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  exact ⟨d₁, k₁, e₁, by omega, ⟨v50, v51, v52, v53, v54, fun h => by simp [pSE] at h⟩,
    exec_frameB e₁ (by decide), fun r hr => r₁ r (by ufo Keep at hr)⟩

theorem pcSV_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {s : WPos} {v : ℕ}
    (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt) (h75 : d.nreg 150075 = v) :
    ∃ d₁ k₁, Exec P W pcSV d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ (pSV s v) ∧ FrameB Scr d d₁ ∧
      (∀ r, Keep r → d₁.nreg r = d.nreg r) := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcSV d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = s.edge ∧ d₁.nreg 150051 = s.hgt ∧ d₁.nreg 150052 = v ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      (∀ r, (r < 150050 ∨ 150055 ≤ r) → d₁.nreg r = d.nreg r) := by
    unfold pcSV
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    all_goals first | (config_simp; first | exact h01 | exact h02 | exact h75; done) |
      (config_simp; done) | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  exact ⟨d₁, k₁, e₁, by omega, ⟨v50, v51, v52, v53, v54, fun h => by simp [pSV] at h⟩,
    exec_frameB e₁ (by decide), fun r hr => r₁ r (by ufo Keep at hr)⟩

theorem pcVE_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {e : WPos} {v : ℕ}
    (h75 : d.nreg 150075 = v) (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) :
    ∃ d₁ k₁, Exec P W pcVE d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ (pVE v e) ∧ FrameB Scr d d₁ ∧
      (∀ r, Keep r → d₁.nreg r = d.nreg r) := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcVE d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = v ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = e.edge ∧
      d₁.nreg 150053 = e.hgt ∧ d₁.nreg 150054 = 0 ∧
      (∀ r, (r < 150050 ∨ 150055 ≤ r) → d₁.nreg r = d.nreg r) := by
    unfold pcVE
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    all_goals first | (config_simp; first | exact h03 | exact h04 | exact h75; done) |
      (config_simp; done) | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  exact ⟨d₁, k₁, e₁, by omega, ⟨v50, v51, v52, v53, v54, fun h => by simp [pVE] at h⟩,
    exec_frameB e₁ (by decide), fun r hr => r₁ r (by ufo Keep at hr)⟩

end

end ShootCut

end Chazelle.Core
