module

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
  | [], _ => by simp
  | sl :: sls, h => by
    have ih := flat_len_le (m := m) (n := n) (sls := sls) (fun s hs => h s (by simp [hs]))
    have h1 := h sl (by simp)
    rw [List.flatMap_cons, List.length_append, slotPcs_length, List.length_cons]
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
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  simp only [Nat.add_zero, pcW] at h0 h1 h2 h3 h4 h5 h6
  unfold rdPc
  rw [h0, h1, h2, h3, h4, h5, h6]

theorem slotsOf_nil {c : Config} (h : ∀ j, j < 4 → c.nreg (170200 + 5 * j) = 0) :
    slotsOf c 4 = [] := by
  rw [slotsOf_free (k := 0) (by norm_num) (fun j _ hj => h j hj)]; rfl

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
  obtain ⟨c₁, c₂, k₂, e₁, e₂, hk₂, hE, -, bA, -, F₂⟩ := front_init_exec
    (P := P) 150000 (by decide) c hw hG hHW hX hcap hwf hbit hroom (.vtx 0)
  have w₂ := e₂.wb_right
  have hW := hHW
  unfold hostWords at hW
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
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    ⟨hE.keep (fun r h1 h2 => q r (by omega)) (fun a _ => congrFun dm a) F₃.2.2.2.2.2.1, ⟨d20, d21⟩⟩,
    fun j hj => ?_, (q _ (Or.inl (by decide))).trans bA, ?_⟩
  · interval_cases j <;> assumption
  · simpa only [Finset.union_self, Nat.add_assoc] using F₂.trans F₃

end exec

end

end IOrc

end Chazelle.Core
