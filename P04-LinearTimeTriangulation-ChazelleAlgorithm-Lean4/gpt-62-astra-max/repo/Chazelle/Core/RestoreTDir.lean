module

public import Chazelle.Core.RestoreTOps

/-!
# WP-E, the candidate test on the RAM, part 14: the turning tests (both models)

The turn from the next walk edge to the direction `σ` (and from `σ` to the previous edge) at the
candidate vertex only depends on the direction codes of the walk edges (`sgnCode_turnNext`,
`sgnCode_turnPrev`), which WP-C's `locDir` computes for both kinds of model descriptors.

* `tTurnN`, `tTurnP`: the tests, meeting `TurnOK` (`turn_ok`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The registers the turning tests write: those of `locDir`, `50000`, `50002`, `50203`,
`50210`. -/
def Bturn (r : ℕ) : Bool := Bdir r || r == 50000 || r == 50002 || r == 50203 || r == 50210

theorem Bturn_band (r : ℕ) (h : Bturn r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  unfold Bturn at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · have := Bdir_band r h
    refine ⟨?_, this.2⟩
    have h1 := this.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    simp only [primBands, Finset.mem_insert, Finset.mem_singleton]
    tauto
  all_goals
    subst h
    exact ⟨by simp [primBands, bandOf, bLocate], by unfold ALLOC; omega⟩

/-- The tail of a turning test: `50210 := turnCode (10502) σ`. -/
def turnTail : Stmt := .seq (block [.copyN 50203 83008, .constN 50032 1]) turnOut

/-- **The turn after the candidate vertex.** -/
def tTurnN : Stmt :=
  .seq (block [.copyN 50000 83000, .copyN 50002 83005]) (.seq locDir turnTail)

/-- **The turn before the candidate vertex** (the previous edge is `p - 1`, or `n - 1` for
`p = 0`, which only happens in the interior model, where `n` is the input size). -/
def tTurnP : Stmt :=
  .seq (.seq (block [.copyN 50000 83000, .constN 50032 1])
    (.ifLtN 83005 83023 (block [.inputSize 50002, .subN 50002 50002 50032])
      (.instr (.subN 50002 83005 50032)))) (.seq locDir turnTail)

theorem wr_tTurnN : wr Bturn tTurnN = true := by decide
theorem wr_tTurnP : wr Bturn tTurnP = true := by decide

/-- The direction procedure's precondition in a run. -/
theorem locDPre_of (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {c₁ : Config}
    (h00 : c₁.nreg 50000 = c.nreg 83000) (hm : c₁.nmem = c.nmem)
    (_hA : c₁.nreg ALLOC = c.nreg ALLOC) (he : c₁.nreg 50002 < M.W.n) :
    LocDPre P W c₁ := by
  obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
  have hAW := hI.hw.1 ALLOC
  obtain ⟨h6, hloc⟩ := locChainWF_of hwf hAW hE.hW
  refine ⟨hE.hG, by have := hE.hW; unfold hostWords at this; omega, by rw [h00]; exact h6,
    by rw [h00, hm]; exact hloc, M, by rw [h00, hm]; exact hMD, he⟩

/-- The turn code is `1` iff the turn is positive. -/
theorem sgnCode_eq_one {x : ℝ} : sgnCode x = 1 ↔ 0 < x := by
  unfold sgnCode; split_ifs <;> simp_all

/-- **The turning tests meet their contract.** -/
theorem turn_ok : TurnOK tTurnN tTurnP 5200 := by
  refine ⟨fun P W M N c₀ c hE hI hroom => ?_, fun P W M N c₀ c hE hI hv hroom => ?_⟩
  · have hw := hI.hw
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W
        (block [.copyN 50000 83000, .copyN 50002 83005]) c c₁ k₁ ∧ k₁ = 2 ∧
        (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = c.nreg 83005 ∧ c₁.nmem = c.nmem ∧
          c₁.nreg ALLOC = c.nreg ALLOC ∧ c₁.nreg 83008 = c.nreg 83008) := by
      exec_block
      exact ⟨rfl, by config_simp, by config_simp, rfl, by config_simp; rfl, by config_simp⟩
    obtain ⟨q00, q02, qm, qA, q08⟩ := q
    have i5 := hI.hin 83005 (by norm_num) (by norm_num)
    have i8 := hI.hin 83008 (by norm_num) (by norm_num)
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, d₂⟩ := locDir_ok P W c₁ e₁.wb_right
      (locDPre_of hE hI q00 qm qA (by rw [q02, i5]; exact hE.hxe))
    have hMD : ModelDescAt c₁.nmem (c₁.nreg 50000) (Qof P) M := by
      rw [q00, qm]; exact (hI.modelDesc hE).1
    have hd := d₂ M hMD
    rw [q02, i5] at hd
    have w₂ := e₂.wb_right
    obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50203 83008,
        .constN 50032 1]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 50203 = c₂.nreg 83008 ∧
        c₃.nreg 50032 = 1 ∧ c₃.nreg 10502 = c₂.nreg 10502) := by
      exec_block
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, by config_simp⟩
    obtain ⟨q3a, q3b, q3c⟩ := q3
    obtain ⟨c₄, k₄, e₄, hk₄, o₄, -⟩ := turnOut_exec (P := P) c₃ e₃.wb_right (by omega) q3b
      (by rw [q3c, hd]; exact dirCode_le_two _ _)
    have ex : Exec P W tTurnN c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
    have hfr : FrameB Bturn c c₄ := exec_frameB ex wr_tTurnN
    refine ⟨c₄, _, ex, by omega, ?_, hI.prim ex.wb_right (frame_of_frameB hfr Bturn_band _)⟩
    have e08 : c₂.nreg 83008 = c₀.nreg 83008 := by
      rw [f₂.1 83008 (by decide), q08, i8]
    rw [o₄, q3c, q3a, hd, e08, ← sgnCode_turnNext, sgnCode_eq_one]
    rfl
  · have hw := hI.hw
    have i5 := hI.hin 83005 (by norm_num) (by norm_num)
    have i8 := hI.hin 83008 (by norm_num) (by norm_num)
    have h23 := hI.h23
    have hxe := hE.hxe
    have hn : ∀ C : Chain, M = chainModel C → 6 ≤ c₀.nreg 83005 := fun C hM =>
      hE.xPosG.2.2 C hM hv
    -- the previous edge
    set n := M.W.n
    have hpe : ∃ pe, pe = (c₀.nreg 83005 + n - 1) % n ∧ pe < n ∧
        (c₀.nreg 83005 = 0 → pe = P.n - 1) ∧ (0 < c₀.nreg 83005 → pe = c₀.nreg 83005 - 1) := by
      refine ⟨_, rfl, Nat.mod_lt _ (by omega), fun h0 => ?_, fun h0 => ?_⟩
      · rcases hE.hkind with ⟨H, C, -, -, -, -, hM⟩ | hI'
        · exact absurd h0 (by have := hn C hM; omega)
        · have : n = P.n := by
            simp only [n, hI', interiorModel, NFLoc.interiorWalk_n]; exact shear_n _ _
          rw [h0, this, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      · rw [show c₀.nreg 83005 + n - 1 = (c₀.nreg 83005 - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
    obtain ⟨pe, hpe, hpen, hp0, hp1⟩ := hpe
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W
        (.seq (block [.copyN 50000 83000, .constN 50032 1])
          (.ifLtN 83005 83023 (block [.inputSize 50002, .subN 50002 50002 50032])
            (.instr (.subN 50002 83005 50032)))) c c₁ k₁ ∧ k₁ ≤ 6 ∧
        (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = pe ∧ c₁.nmem = c.nmem ∧
          c₁.nreg ALLOC = c.nreg ALLOC ∧ c₁.nreg 83008 = c.nreg 83008) := by
      refine spec_seq ?_
      obtain ⟨c', k', e', hk', q'⟩ : ∃ c' k', Exec P W (block [.copyN 50000 83000,
          .constN 50032 1]) c c' k' ∧ k' = 2 ∧ (c'.nreg 50000 = c.nreg 83000 ∧
          c'.nreg 50032 = 1 ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
          c'.nreg 83008 = c.nreg 83008 ∧ c'.nreg 83005 = c.nreg 83005 ∧
          c'.nreg 83023 = c.nreg 83023) := by
        exec_block
        · omega
        · exact ⟨rfl, by config_simp, by config_simp, rfl, by config_simp; rfl, by config_simp,
            by config_simp, by config_simp⟩
      obtain ⟨p00, p32, pm, pA, p08, p05, p23⟩ := q'
      refine ⟨c', k', e', ?_⟩
      have w' := e'.wb_right
      by_cases h0 : c'.nreg 83005 < c'.nreg 83023
      · refine spec_ifLtN_true h0 ?_
        exec_block
        · have := hE.hW; unfold hostWords at this; omega
        · refine ⟨by omega, by config_simp; exact p00, ?_, pm, by config_simp; exact pA,
            by config_simp; exact p08⟩
          config_simp
          rw [p32, hp0 (by rw [p05, i5, p23, h23] at h0; omega)]
      · refine spec_ifLtN_false h0 (spec_instr (Exec.subN w' _ _ _) fun _ => ?_)
        refine ⟨by omega, by config_simp; exact p00, ?_, pm, by config_simp; exact pA,
          by config_simp; exact p08⟩
        config_simp
        rw [p32, p05, i5, hp1 (by rw [p05, i5, p23, h23] at h0; omega)]
    obtain ⟨q00, q02, qm, qA, q08⟩ := q
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, d₂⟩ := locDir_ok P W c₁ e₁.wb_right
      (locDPre_of hE hI q00 qm qA (by rw [q02]; exact hpen))
    have hMD : ModelDescAt c₁.nmem (c₁.nreg 50000) (Qof P) M := by
      rw [q00, qm]; exact (hI.modelDesc hE).1
    have hd := d₂ M hMD
    rw [q02] at hd
    have w₂ := e₂.wb_right
    clear hw
    obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50203 83008,
        .constN 50032 1]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 50203 = c₂.nreg 83008 ∧
        c₃.nreg 50032 = 1 ∧ c₃.nreg 10502 = c₂.nreg 10502) := by
      exec_block
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, by config_simp⟩
    obtain ⟨q3a, q3b, q3c⟩ := q3
    obtain ⟨c₄, k₄, e₄, hk₄, o₄, -⟩ := turnOut_exec (P := P) c₃ e₃.wb_right (by omega) q3b
      (by rw [q3c, hd]; exact dirCode_le_two _ _)
    have ex : Exec P W tTurnP c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
    have hfr : FrameB Bturn c c₄ := exec_frameB ex wr_tTurnP
    refine ⟨c₄, _, ex, by omega, ?_, hI.prim ex.wb_right (frame_of_frameB hfr Bturn_band _)⟩
    have e08 : c₂.nreg 83008 = c₀.nreg 83008 := by
      rw [f₂.1 83008 (by decide), q08, i8]
    rw [o₄, q3c, q3a, hd, e08, hpe, ← sgnCode_turnPrev M hxe, sgnCode_eq_one]
    rfl

end

end Restore

end Chazelle.Core
