module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleCuR5
public import Chazelle.Core.DownPhaseOracleShH

/-!
# WP-M (E7-B, RAM part 20): the set-up and the query of the interior cutter

* `frontC = saveS ; initI ; bitI ; clrC`: the inputs of band `bCut` saved in band `17`, the
  constants, the host record `Host.whole n`, the orientation bit, a dummy origin and the four slots
  free (`frontC_exec`: the static environment `SEnv` for `statC`).
* `queryC cu = normI ; branchC cu ; asmC`: the normalized query, one sub-query (`L ≤ n - 1`) or
  two (`L ≥ n`) of the chain cutter `cu` (`sqC`), recorded as slots, and the assembly of the
  answer (`queryC_exec`: the answer is a list of valid pieces of the interior walk forming a path of
  unwrapped keys from the start of the query to its end).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open ShootCut (Pc KPath)

@[expose] public section

/-! ## The programs -/

/-- A dummy origin and the four slots free. -/
def clrC : Stmt :=
  block [.constN 170020 0, .constN 170021 0, .constN 170200 0, .constN 170205 0,
    .constN 170210 0, .constN 170215 0]

/-- **The set-up of the interior cutter.** -/
def frontC : Stmt := .seq (saveS 150000) (.seq (.seq initI bitI) clrC)

/-- The static data of a query of the interior cutter. -/
noncomputable def statC (c : Config) : Stat :=
  ⟨c.nreg ALLOC, c.nmem, c.nreg 150013, c.nreg 150009, c.nreg 150001, c.nreg 150002,
    c.nreg 150003, c.nreg 150004, c.nreg 150008, .vtx 0⟩

/-- One or two sub-queries of the cutter. -/
def branchC (cu : Stmt) : Stmt :=
  .ifLtN 170032 170010 (.seq setOne (sqC cu 0))
    (.seq setTwoA (.seq (sqC cu 0) (.seq setTwoB (sqC cu 2))))

/-- **The query of the interior cutter.** -/
def queryC (cu : Stmt) : Stmt := .seq normI (.seq (branchC cu) asmC)

/-! ## Lemmas -/

theorem flat_len_le {m : ℕ → ℕ} {n Gγ : ℕ} :
    ∀ {sls : List Slot}, (∀ sl ∈ sls, sl.q ≤ Gγ) →
      (sls.flatMap (slotPcs m n)).length ≤ sls.length * Gγ
  | [], _ => ✓
  | sl :: sls, h => by
    have ih := flat_len_le (m := m) (n := n) (sls := sls) (fun s hs => h s (⊚ hs))
    have h1 := h sl (✓)
    Ξ List.flatMap_cons, List.length_append, slotPcs_length, List.length_cons
    nlinarith

theorem slotPcs_fields {m : ℕ → ℕ} {n : ℕ} {sls : List Slot} {pc : Pc}
    (h : pc ∈ sls.flatMap (slotPcs m n)) : pc.dir = 0 ∧ pc.pw = 0 := by
  obtain ⟨sl, -, hpc⟩ := List.mem_flatMap.1 h
  unfold slotPcs at hpc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hpc
  exact ⟨rfl, rfl⟩

/-- A piece record read back. -/
theorem rdPc_of_words {m : ℕ → ℕ} {A j : ℕ} {pc : Pc}
    (h : ∀ f, f < 7 → m (A + 1 + 7 * j + f) = pcW pc f) (hd : pc.dir = 0) (hp : pc.pw = 0) :
    rdPc m A j = pc := by
  obtain ⟨⟨a, b⟩, ⟨d, e⟩, k, en, x, dir, pw⟩ := pc
  simp only at hd hp
  subst hd hp
  have h0 := h 0 (⊛)
  have h1 := h 1 (⊛)
  have h2 := h 2 (⊛)
  have h3 := h 3 (⊛)
  have h4 := h 4 (⊛)
  have h5 := h 5 (⊛)
  have h6 := h 6 (⊛)
  simp only [Nat.add_zero, pcW] at h0 h1 h2 h3 h4 h5 h6
  unfold rdPc
  Ξ h0, h1, h2, h3, h4, h5, h6

theorem slotsOf_nil {c : Config} (h : ∀ j, j < 4 → c.nreg (170200 + 5 * j) = 0) :
    slotsOf c 4 = [] := by
  rw [slotsOf_free (k := 0) (⊛) (fun j _ hj => h j hj)]; rfl

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface}

/-- **The set-up of the interior cutter.** -/
theorem frontC_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hX : (gradeCtx O).holds P c.nmem (c.nreg 150013) (c.nreg ALLOC))
    (hcap : c.nreg 150009 ≤ (gradeCtx O).cap P c.nmem (c.nreg 150013))
    (hwf : c.nreg 150000 + 6 ≤ c.nreg ALLOC)
    (hbit : c.nmem (c.nreg 150000 + 1) = 1 ↔ Mountain.LeftInside (Qof P))
    (hroom : c.nreg ALLOC + 8 ≤ W) :
    ∃ c' k, Exec P W frontC c c' k ∧ k ≤ 50 ∧ SEnv P W O (statC c) c' ∧
      (∀ j, j < 4 → c'.nreg (170200 + 5 * j) = 0) ∧ c'.nreg ALLOC = c.nreg ALLOC + 8 ∧
      Frame ioBands c c' k := by
  have hn3 : 3 ≤ P.n := Chazelle.Jordan.simple_three_le hG.1
  have hW := hHW
  unfold hostWords at hW
  -- save
  obtain ⟨c₁, e₁, a10, a13, ar, arr, am, arm, ao⟩ := saveS_exec (P := P) 150000 (by norm_num) c hw
  have w₁ := e₁.wb_right
  have aA : c₁.nreg ALLOC = c.nreg ALLOC := ar _ (by unfold ALLOC; omega)
  have F₁ : Frame ioBands c c₁ 11 := frameIO_of_frameB
    (B := fun r => decide (170000 ≤ r ∧ r < 170014))
    (fun r hr => io_of_band (Or.inl (by simp at hr; omega)))
    ⟨fun r hr => ar r (by simpa using hr), fun r _ => by rw [arr], am, arm, ao⟩ 11
  have hlow := ShootCut.grade_low hX
  have a0 : c₁.nreg 170000 = c.nreg 150000 := a10 0 (by norm_num)
  have a13' : c₁.nreg 170013 = c.nreg 150013 := a13
  -- the constants and the host record
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b10, b11, b12, b18, b19, b16, b17, b14, b14', b15, bA, b70, bm0,
      bm1, bm2, bm3, bmlo, br, brr, brm, bo⟩ := initI_exec (P := P) c₁ w₁
    (by rw [a0]; have := hw.1 ALLOC; omega) (by rw [a13']; have := hlow.1; have := hw.1 ALLOC; omega)
    (by rw [aA]; exact hroom) (by omega) (by omega)
  have w₂ := e₂.wb_right
  have F₂ : Frame ioBands c₁ c₂ k₂ := by
    refine ⟨fun r hr ha => br r ?_, fun r _ => by rw [brr], fun a ha => bmlo a ha,
      fun a _ => by rw [brm], bo, by rw [bA]; omega, by rw [bA]; omega⟩
    intro hb
    unfold BinitR at hb
    apply hr
    rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (try (subst h; decide))
    exact absurd h ha
  -- the dummy origin and the free slots
  obtain ⟨c₃, k₃, e₃, hk₃, d20, d21, d200, d205, d210, d215, dr, drr, dm, drm, dout⟩ :
      ∃ c₃ k₃, Exec P W clrC c₂ c₃ k₃ ∧ k₃ = 6 ∧ c₃.nreg 170020 = 0 ∧ c₃.nreg 170021 = 0 ∧
      c₃.nreg 170200 = 0 ∧ c₃.nreg 170205 = 0 ∧ c₃.nreg 170210 = 0 ∧ c₃.nreg 170215 = 0 ∧
      (∀ r, r ≠ 170020 → r ≠ 170021 → r ≠ 170200 → r ≠ 170205 → r ≠ 170210 → r ≠ 170215 →
        c₃.nreg r = c₂.nreg r) ∧ c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧ c₃.rmem = c₂.rmem ∧
      c₃.output = c₂.output := by
    unfold clrC
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp
    simp [upd, h1, h2, h3, h4, h5, h6]
  have F₃ : Frame ioBands c₂ c₃ k₃ := frameIO_of_frameB
    (B := fun r => decide (r = 170020 ∨ r = 170021 ∨ r = 170200 ∨ r = 170205 ∨ r = 170210 ∨
      r = 170215))
    (fun r hr => io_of_band (Or.inl (by simp at hr; omega)))
    ⟨fun r hr => dr r (by simp at hr; omega) (by simp at hr; omega) (by simp at hr; omega)
      (by simp at hr; omega) (by simp at hr; omega) (by simp at hr; omega),
      fun r _ => by rw [drr], dm, drm, dout⟩ k₃
  have q : ∀ r, r < 170020 ∨ (170021 < r ∧ r < 170200) → c₃.nreg r = c₂.nreg r := fun r hr =>
    dr r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have g : ∀ r, r < 170020 ∨ (170021 < r ∧ r < 170200) → ¬ BinitR r → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 => by rw [q r h1, br r h2]
  have gs : ∀ i, i < 10 → c₃.nreg (170000 + i) = c.nreg (150000 + i) := fun i hi => by
    rw [g _ (by omega) (by unfold BinitR; omega)]; exact a10 i hi
  have ex : Exec P W frontC c c₃ (11 + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have cA : c₃.nreg ALLOC = c.nreg ALLOC + 8 := by
    rw [q _ (by unfold ALLOC; omega), bA, aA]
  refine ⟨c₃, _, ex, by omega, ⟨hG, hHW, gs 1 (by norm_num), gs 2 (by norm_num),
    gs 3 (by norm_num), gs 4 (by norm_num), gs 8 (by norm_num), gs 9 (by norm_num),
    by rw [g _ (by omega) (by unfold BinitR; omega)]; exact a13',
    by rw [q _ (by omega)]; exact b10, by rw [q _ (by omega)]; exact b11,
    by rw [q _ (by omega)]; exact b12, by rw [q _ (by omega)]; exact b18,
    by rw [q _ (by omega)]; exact b19,
    by rw [q _ (by omega), b14, a0, am]; exact hbit,
    by rw [q _ (by omega)]; exact b14',
    by rw [q _ (by omega), b15, aA]; rfl,
    by rw [q _ (by omega), b16, a13', am]; rfl,
    by rw [q _ (by omega), b17, a13', am]; rfl, ⟨d20, d21⟩,
    fun a ha => by rw [dm, bmlo a (by rw [aA]; exact ha), am]; rfl,
    by rw [dm]; show c₂.nmem (c.nreg ALLOC) = 1; rw [← aA]; exact bm0,
    by rw [dm]; show c₂.nmem (c.nreg ALLOC + 1) = 0; rw [← aA]; exact bm1,
    by rw [dm]; show c₂.nmem (c.nreg ALLOC + 2) = 0; rw [← aA]; exact bm2,
    by rw [dm]; show c₂.nmem (c.nreg ALLOC + 3) = P.n - 1; rw [← aA]; exact bm3,
    by rw [cA]; show c.nreg ALLOC + 8 ≤ c.nreg ALLOC + 8; exact le_rfl, hX, hcap⟩,
    fun j hj => ?_, cA, ((F₁.trans F₂).trans F₃).mono (by simp) (by omega)⟩
  interval_cases j
  · exact d200
  · exact d205
  · exact d210
  · exact d215

end exec

end

end IOrc

end Chazelle.Core
