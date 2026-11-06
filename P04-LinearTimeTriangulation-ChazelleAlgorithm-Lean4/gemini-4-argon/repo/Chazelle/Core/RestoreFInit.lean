module

public import Chazelle.Core.RestoreFPairs
public import Chazelle.Core.DownPhaseOracleHit

/-!
# WP-E, the search on the RAM (`FindOK`), part 28: the initialisation

`fInit` sets the constants of the search (`81011 …`), the input size `81020`, `n / 2` (from the
halving table of the context), and the walk data of the model: its length `81017`, the range
`81021 … 81019` of the walk vertices on the chain and the end `81025` of the counted edges (chain
model: `6`, `2m + 6`, `2m + 6`, `2m + 7`; interior model: `0`, `n`, `n`, `n`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-! ## Blocks outside the search -/

/-- The side condition of an instruction of a block run outside the search. -/
def okX (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN _ k => k ≤ W
  | .copyN _ _ => True
  | .addN _ a b => f a + f b ≤ W
  | .subN _ _ _ => True
  | .loadN _ _ => True
  | _ => False

/-- The side conditions of a block run outside the search. -/
def okXB (W : ℕ) (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → Prop
  | [], _ => True
  | i :: l, f => okX W f i ∧ okXB W m l (regI m i f)

theorem execB {P : Polygon} {W : ℕ} : ∀ (l : List Instr) {c : Config}, WordsBounded W c →
    okXB W c.nmem l c.nreg →
    Exec P W (Stmt.block l) c { c with nreg := regB c.nmem l c.nreg } l.length
  | [], c, hw, _ => Exec.skip hw
  | i :: l, c, hw, h => by
    obtain ⟨hi, hl⟩ := h
    have h1 : Exec P W (.instr i) c { c with nreg := regI c.nmem i c.nreg } 1 := by
      cases i with
      | constN r k => exact Exec.constN hw r k hi
      | copyN r a => exact Exec.copyN hw r a
      | addN r a b => exact Exec.addN hw r a b hi
      | subN r a b => exact Exec.subN hw r a b
      | loadN r a => exact Exec.loadN hw r a
      | _ => exact absurd hi (by simp [okX])
    have h2 := execB l (P := P) (c := { c with nreg := regI c.nmem i c.nreg }) h1.wb_right hl
    exact (Exec.seq h1 h2).cast (by simp [Nat.add_comm])

/-! ## The program -/

/-- The constants, the input size and `n / 2`, the kind of the model (`81029`). -/
def fIniL : List Instr := [.constN 81007 0, .constN 81011 0, .constN 81012 1, .constN 81013 2,
  .constN 81014 3, .constN 81015 5, .constN 81016 7, .constN 81024 10,
  .addN 81028 81004 81014, .loadN 81028 81028, .addN 81028 81028 81020, .loadN 81023 81028,
  .addN 81022 81023 81023, .loadN 81029 81000]

/-- The walk data of a chain model (`m` from the chain descriptor). -/
def fChL : List Instr := [.addN 81028 81000 81014, .loadN 81028 81028, .constN 81021 6,
  .addN 81019 81028 81028, .addN 81019 81019 81021, .copyN 81025 81019, .addN 81017 81019 81012]

/-- The walk data of the interior model. -/
def fIntL : List Instr := [.constN 81021 0, .copyN 81017 81020, .copyN 81019 81020,
  .copyN 81025 81020]

/-- **The initialisation.** -/
def fInit : Stmt := .seq (.instr (.inputSize 81020)) (.seq (Stmt.block fIniL)
  (.ifLtN 81011 81029 (Stmt.block fIntL) (Stmt.block fChL)))

/-- The registers the initialisation writes. -/
def IniW (q : ℕ) : Prop := 81007 ≤ q ∧ q < 81030

theorem fInit_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (h10 : 10 ≤ W)
    (hnW : P.n ≤ W) {X : MemCtx} (hX : X.holds P c.nmem (c.nreg 81004) (c.nreg ALLOC))
    (hhalf : X.Halves) (hMD : c.nreg 81000 + 6 ≤ c.nreg ALLOC)
    (hk : c.nmem (c.nreg 81000) = 0 → 2 * c.nmem (c.nreg 81000 + 3) + 7 ≤ W) :
    ∃ c₀ k, Exec P W fInit c c₀ k ∧ k ≤ 30 ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output ∧ (∀ q, ¬ IniW q → c₀.nreg q = c.nreg q) ∧
      c₀.nreg 81007 = 0 ∧ c₀.nreg 81011 = 0 ∧ c₀.nreg 81012 = 1 ∧ c₀.nreg 81013 = 2 ∧
      c₀.nreg 81014 = 3 ∧ c₀.nreg 81015 = 5 ∧ c₀.nreg 81016 = 7 ∧ c₀.nreg 81024 = 10 ∧
      c₀.nreg 81020 = P.n ∧ c₀.nreg 81023 = P.n / 2 ∧ c₀.nreg 81022 = 2 * (P.n / 2) ∧
      (c.nmem (c.nreg 81000) = 0 → c₀.nreg 81021 = 6 ∧
        c₀.nreg 81019 = 2 * c.nmem (c.nreg 81000 + 3) + 6 ∧
        c₀.nreg 81025 = 2 * c.nmem (c.nreg 81000 + 3) + 6 ∧
        c₀.nreg 81017 = 2 * c.nmem (c.nreg 81000 + 3) + 7) ∧
      (c.nmem (c.nreg 81000) ≠ 0 → c₀.nreg 81021 = 0 ∧ c₀.nreg 81019 = P.n ∧
        c₀.nreg 81025 = P.n ∧ c₀.nreg 81017 = P.n) := by
  obtain ⟨hg3, hT⟩ := hhalf P c.nmem (c.nreg 81004) (c.nreg ALLOC) hX
  obtain ⟨hTn, hTv⟩ := hT P.n le_rfl
  have hAW := hw.1 ALLOC
  -- the input size
  have e1 := Exec.inputSize (P := P) hw 81020 hnW
  set c₁ : Config := { c with nreg := upd c.nreg 81020 P.n } with hc₁
  have hw₁ : WordsBounded W c₁ := e1.wb_right
  have r₁ : ∀ q, q ≠ 81020 → c₁.nreg q = c.nreg q := fun q h => by simp [hc₁, upd, h]
  have n₁ : c₁.nreg 81020 = P.n := by simp [hc₁, upd]
  -- the constants
  have ok2 : okXB W c₁.nmem fIniL c₁.nreg := by
    simp only [fIniL, okXB, okX, regI]
    simp only [upd, n₁, r₁ 81004 (by norm_num), show c₁.nmem = c.nmem from rfl]
    norm_num [hTv]
    (repeat' apply And.intro) <;> omega
  have e2 := execB (P := P) fIniL hw₁ ok2
  set c₂ : Config := { c₁ with nreg := regB c₁.nmem fIniL c₁.nreg }
  have hw₂ : WordsBounded W c₂ := e2.wb_right
  have v₂ : ∀ q, c₂.nreg q = regB c.nmem fIniL c₁.nreg q := fun q => rfl
  have f₂ : ∀ q, ¬ IniW q → c₂.nreg q = c.nreg q := fun q hq => by
    rw [v₂, regB_other _ _ _ (fun i hi => ?_), r₁ q (fun h => hq (by unfold IniW; omega))]
    simp only [fIniL, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold IniW at hq
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp only [dstI] <;> omega
  have z : c₂.nreg 81011 = 0 := by rw [v₂]; simp [fIniL, regB, regI, upd]
  have kd : c₂.nreg 81029 = c.nmem (c.nreg 81000) := by
    rw [v₂]; simp [fIniL, regB, regI, upd, r₁ 81000 (by norm_num)]
  have c20 : c₂.nreg 81020 = P.n := by rw [v₂]; simp [fIniL, regB, regI, upd, n₁]
  have c00 : c₂.nreg 81000 = c.nreg 81000 := f₂ _ (by unfold IniW; omega)
  have c12 : c₂.nreg 81012 = 1 := by rw [v₂]; simp [fIniL, regB, regI, upd]
  have c14 : c₂.nreg 81014 = 3 := by rw [v₂]; simp [fIniL, regB, regI, upd]
  have vals : c₂.nreg 81007 = 0 ∧ c₂.nreg 81011 = 0 ∧ c₂.nreg 81012 = 1 ∧ c₂.nreg 81013 = 2 ∧
      c₂.nreg 81014 = 3 ∧ c₂.nreg 81015 = 5 ∧ c₂.nreg 81016 = 7 ∧ c₂.nreg 81024 = 10 ∧
      c₂.nreg 81020 = P.n ∧ c₂.nreg 81023 = P.n / 2 ∧ c₂.nreg 81022 = 2 * (P.n / 2) := by
    refine ⟨?_, z, c12, ?_, c14, ?_, ?_, ?_, c20, ?_, ?_⟩ <;>
      (rw [v₂]; simp [fIniL, regB, regI, upd, n₁, r₁ 81004 (by norm_num)])
    · exact hTv
    · rw [hTv]; ring
  -- the walk data
  by_cases a : c₂.nreg 81011 < c₂.nreg 81029
  · have hk1 : c.nmem (c.nreg 81000) ≠ 0 := by rw [← kd]; omega
    have ok3 : okXB W c₂.nmem fIntL c₂.nreg := by
      simp only [fIntL, okXB, okX]; norm_num
    have e3 := execB (P := P) fIntL hw₂ ok3
    refine ⟨_, _, .seq e1 (.seq e2 (.ifLtN_true a e3)), by simp [fIniL, fIntL], rfl, rfl, rfl, rfl,
      fun q hq => ?_,
      ?_⟩
    · show regB c₂.nmem fIntL c₂.nreg q = _
      rw [regB_other _ _ _ (fun i hi => ?_), f₂ q hq]
      simp only [fIntL, List.mem_cons, List.not_mem_nil, or_false] at hi
      unfold IniW at hq
      rcases hi with rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
    · have g : ∀ q, q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 →
          regB c₂.nmem fIntL c₂.nreg q = c₂.nreg q := fun q a b d e => by
        simp [fIntL, regB, regI, upd, a, b, d, e]
      obtain ⟨v07, v11, v12, v13, v14, v15, v16, v24, v20, v23, v22⟩ := vals
      have G : ∀ q, q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 → ∀ v, c₂.nreg q = v →
          regB c₂.nmem fIntL c₂.nreg q = v := fun q a b d e v h => by rw [g q a b d e, h]
      have w : ∀ q, q = 81021 ∨ q = 81017 ∨ q = 81019 ∨ q = 81025 →
          regB c₂.nmem fIntL c₂.nreg q = if q = 81021 then 0 else P.n := fun q hq => by
        rcases hq with rfl | rfl | rfl | rfl <;> simp [fIntL, regB, regI, upd, c20]
      exact ⟨G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v07,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v11,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v12,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v13,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v14,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v15,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v16,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v24,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v20,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v23,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v22,
        fun h => absurd h hk1, fun _ => ⟨(w 81021 (by norm_num)).trans (by norm_num),
          (w 81019 (by norm_num)).trans (by norm_num), (w 81025 (by norm_num)).trans (by norm_num),
          (w 81017 (by norm_num)).trans (by norm_num)⟩⟩
  · have hk0 : c.nmem (c.nreg 81000) = 0 := by rw [← kd]; omega
    have hm := hk hk0
    have ok3 : okXB W c₂.nmem fChL c₂.nreg := by
      simp only [fChL, okXB, okX, regI]
      simp only [upd, c00, c14, c12, show c₂.nmem = c.nmem from rfl]
      norm_num
      refine ⟨by omega, by omega, by omega, by omega⟩
    have e3 := execB (P := P) fChL hw₂ ok3
    refine ⟨_, _, .seq e1 (.seq e2 (.ifLtN_false a e3)), by simp [fIniL, fChL], rfl, rfl, rfl, rfl,
      fun q hq => ?_,
      ?_⟩
    · show regB c₂.nmem fChL c₂.nreg q = _
      rw [regB_other _ _ _ (fun i hi => ?_), f₂ q hq]
      simp only [fChL, List.mem_cons, List.not_mem_nil, or_false] at hi
      unfold IniW at hq
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
    · have g : ∀ q, q ≠ 81028 → q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 →
          regB c₂.nmem fChL c₂.nreg q = c₂.nreg q := fun q a b d e f => by
        simp [fChL, regB, regI, upd, a, b, d, e, f]
      obtain ⟨v07, v11, v12, v13, v14, v15, v16, v24, v20, v23, v22⟩ := vals
      have G : ∀ q, q ≠ 81028 → q ≠ 81021 → q ≠ 81017 → q ≠ 81019 → q ≠ 81025 → ∀ v,
          c₂.nreg q = v → regB c₂.nmem fChL c₂.nreg q = v := fun q a b d e f v h => by
        rw [g q a b d e f, h]
      have w21 : regB c₂.nmem fChL c₂.nreg 81021 = 6 := by simp [fChL, regB, regI, upd]
      have w19 : regB c₂.nmem fChL c₂.nreg 81019 = 2 * c.nmem (c.nreg 81000 + 3) + 6 := by
        simp [fChL, regB, regI, upd, c00, c14, show c₂.nmem = c.nmem from rfl]; ring
      have w25 : regB c₂.nmem fChL c₂.nreg 81025 = 2 * c.nmem (c.nreg 81000 + 3) + 6 := by
        simp [fChL, regB, regI, upd, c00, c14, show c₂.nmem = c.nmem from rfl]; ring
      have w17 : regB c₂.nmem fChL c₂.nreg 81017 = 2 * c.nmem (c.nreg 81000 + 3) + 7 := by
        simp [fChL, regB, regI, upd, c00, c14, c12, show c₂.nmem = c.nmem from rfl]; ring
      exact ⟨G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v07,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v11,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v12,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v13,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v14,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v15,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v16,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v24,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v20,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v23,
        G _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ v22,
        fun _ => ⟨w21, w19, w25, w17⟩, fun h => absurd hk0 h⟩

end

end Restore

end Chazelle.Core
