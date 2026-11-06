module

public import Chazelle.Core.DownPhaseDrvRPc
public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Core.NFBuildMain

/-!
# Down-phase driver (RAM side): the leaf planner, part 1 (the chunk loop)

`plCh` writes the pieces `chunks C s a L` (`DownPhaseDrvRPc`) as triples at the pointer
`r219016` and counts them in `r219004` (`plCh_exec`, `15` steps per piece).

Registers (band `bDownDrv`): `219002` the chunk size `C ≥ 1`, `219012` `s`, `219013` `a`,
`219014` `L`, `219015` the piece length, `219016` the write pointer, `219004` the count,
constants `219017 = 0`, `219018 = 1`, `219020 = 3`, scratch `219021`.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-- One piece: `len := min C L`, emit `(s, len, a)`, advance. -/
def plChBody : Stmt :=
  .seq (.ifLtN 219002 219014 (.instr (.copyN 219015 219002)) (.instr (.copyN 219015 219014)))
    (block [.storeN 219016 219012, .addN 219021 219016 219018, .storeN 219021 219015,
      .addN 219021 219021 219018, .storeN 219021 219013, .addN 219016 219016 219020,
      .addN 219004 219004 219018, .addN 219012 219012 219015, .addN 219013 219013 219015,
      .subN 219014 219014 219015])

/-- **The chunk loop.** -/
def plCh : Stmt := .whileLtN 219017 219014 plChBody

/-- The registers the chunk loop writes. -/
def Bch (r : ℕ) : Bool :=
  decide (r = 219004) || decide (219012 ≤ r ∧ r ≤ 219016) || decide (r = 219021)

theorem wrM_plChBody : wrM Bch plChBody = true := by decide

/-- One piece off the front. -/
theorem chunks_cons {C s a L : ℕ} (hC : 1 ≤ C) (hL : 1 ≤ L) :
    chunks C s a L = (s, min C L, a) :: chunks C (s + min C L) (a + min C L) (L - min C L) := by
  by_cases h : L ≤ C
  · rw [chunks_le (by omega) (Or.inl h), min_eq_right h, Nat.sub_self, chunks_zero]
  · rw [chunks_gt (by omega) (by omega) (by omega), min_eq_left (by omega)]

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem plChBody_exec (d : Config) (hw : WordsBounded W d) {C L s a k ptr : ℕ}
    (h02 : d.nreg 219002 = C) (h14 : d.nreg 219014 = L) (h12 : d.nreg 219012 = s)
    (h13 : d.nreg 219013 = a) (h16 : d.nreg 219016 = ptr) (h04 : d.nreg 219004 = k)
    (h18 : d.nreg 219018 = 1) (h20 : d.nreg 219020 = 3)
    (hW1 : ptr + 3 ≤ W) (hW2 : s + L ≤ W) (hW3 : a + L ≤ W) (hW4 : k + 1 ≤ W) :
    ∃ d' j, Exec P W plChBody d d' j ∧ j ≤ 13 ∧
      d'.nreg 219012 = s + min C L ∧ d'.nreg 219013 = a + min C L ∧
      d'.nreg 219014 = L - min C L ∧ d'.nreg 219016 = ptr + 3 ∧ d'.nreg 219004 = k + 1 ∧
      d'.nmem = upd (upd (upd d.nmem ptr s) (ptr + 1) (min C L)) (ptr + 2) a ∧
      FrameM Bch d d' := by
  obtain ⟨d₁, j₁, e₁, hj₁, v15, g₁, m₁⟩ : ∃ d₁ j₁, Exec P W
      (.ifLtN 219002 219014 (.instr (.copyN 219015 219002)) (.instr (.copyN 219015 219014)))
      d d₁ j₁ ∧ j₁ ≤ 3 ∧ d₁.nreg 219015 = min C L ∧ (∀ r, r ≠ 219015 → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem := by
    by_cases h : C < L
    · refine ⟨_, _, .ifLtN_true (by rwa [h02, h14]) (Exec.copyN (P := P) hw 219015 219002),
        by omega, ?_, fun r hr => by simp [hr], rfl⟩
      simp only [Machine.upd_same, h02]; rw [min_eq_left h.le]
    · refine ⟨_, _, .ifLtN_false (by rwa [h02, h14]) (Exec.copyN (P := P) hw 219015 219014),
        by omega, ?_, fun r hr => by simp [hr], rfl⟩
      simp only [Machine.upd_same, h14]; rw [min_eq_right (by omega)]
  have w₁ := e₁.wb_right
  have a12 : d₁.nreg 219012 = s := by rw [g₁ _ (by decide), h12]
  have a13 : d₁.nreg 219013 = a := by rw [g₁ _ (by decide), h13]
  have a14 : d₁.nreg 219014 = L := by rw [g₁ _ (by decide), h14]
  have a16 : d₁.nreg 219016 = ptr := by rw [g₁ _ (by decide), h16]
  have a04 : d₁.nreg 219004 = k := by rw [g₁ _ (by decide), h04]
  have a18 : d₁.nreg 219018 = 1 := by rw [g₁ _ (by decide), h18]
  have a20 : d₁.nreg 219020 = 3 := by rw [g₁ _ (by decide), h20]
  have hmin : min C L ≤ L := min_le_right _ _
  obtain ⟨d₂, j₂, e₂, hj₂, b12, b13, b14, b16, b04, bm⟩ : ∃ d₂ j₂, Exec P W
      (block [.storeN 219016 219012, .addN 219021 219016 219018, .storeN 219021 219015,
        .addN 219021 219021 219018, .storeN 219021 219013, .addN 219016 219016 219020,
        .addN 219004 219004 219018, .addN 219012 219012 219015, .addN 219013 219013 219015,
        .subN 219014 219014 219015]) d₁ d₂ j₂ ∧ j₂ = 10 ∧
      d₂.nreg 219012 = s + min C L ∧ d₂.nreg 219013 = a + min C L ∧
      d₂.nreg 219014 = L - min C L ∧ d₂.nreg 219016 = ptr + 3 ∧ d₂.nreg 219004 = k + 1 ∧
      d₂.nmem = upd (upd (upd d₁.nmem ptr s) (ptr + 1) (min C L)) (ptr + 2) a := by
    exec_block
    all_goals try (config_simp; (try simp only [a12, a13, a14, a16, a04, a18, a20, v15]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [a12, a13, a14, a16, a04, a18, a20, v15])
  refine ⟨d₂, j₁ + j₂, .seq e₁ e₂, by omega, b12, b13, b14, b16, b04, by rw [bm, m₁], ?_⟩
  exact exec_frameM (.seq e₁ e₂) wrM_plChBody

/-- **The chunk loop** writes the pieces of the segment as triples at the pointer. -/
theorem plCh_exec {C : ℕ} (hC : 1 ≤ C) : ∀ (L : ℕ) (d : Config) (s a k ptr : ℕ),
    WordsBounded W d → d.nreg 219002 = C → d.nreg 219014 = L → d.nreg 219012 = s →
    d.nreg 219013 = a → d.nreg 219016 = ptr → d.nreg 219004 = k → d.nreg 219017 = 0 →
    d.nreg 219018 = 1 → d.nreg 219020 = 3 → s + L ≤ W → a + L ≤ W →
    ptr + 3 * (chunks C s a L).length ≤ W → k + (chunks C s a L).length ≤ W →
    ∃ d' j, Exec P W plCh d d' j ∧ j ≤ 15 * (chunks C s a L).length + 2 ∧
      d'.nreg 219016 = ptr + 3 * (chunks C s a L).length ∧
      d'.nreg 219004 = k + (chunks C s a L).length ∧
      ChordListAt d'.nmem ptr (chunks C s a L) ∧
      (∀ x, (x < ptr ∨ ptr + 3 * (chunks C s a L).length ≤ x) → d'.nmem x = d.nmem x) ∧
      FrameM Bch d d' := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro d s a k ptr hw h02 h14 h12 h13 h16 h04 h17 h18 h20 hWs hWa hWp hWk
    by_cases hL : L = 0
    · subst hL
      rw [chunks_zero]
      refine ⟨d, 2, .whileLtN_false (by rw [h17, h14]; omega) hw, by simp, by simp [h16],
        by simp [h04], fun i hi => by simp at hi, fun _ _ => rfl, FrameM.refl _ _⟩
    · have hcons := chunks_cons (s := s) (a := a) hC (by omega : 1 ≤ L)
      set len := min C L
      have hlen1 : 1 ≤ len := le_min hC (by omega)
      have hlenL : len ≤ L := min_le_right _ _
      rw [hcons] at hWp hWk
      simp only [List.length_cons] at hWp hWk
      obtain ⟨d₁, j₁, e₁, hj₁, b12, b13, b14, b16, b04, bm, f₁⟩ :=
        plChBody_exec (P := P) d hw h02 h14 h12 h13 h16 h04 h18 h20 (by omega) hWs hWa (by omega)
      have g₁ : ∀ r, Bch r = false → d₁.nreg r = d.nreg r := f₁.1
      obtain ⟨d', j₂, e₂, hj₂, c16, c04, cL, cm, cf⟩ := ih (L - len) (by omega) d₁ (s + len)
        (a + len) (k + 1) (ptr + 3) e₁.wb_right (by rw [g₁ _ (by decide), h02]) b14 b12 b13 b16
        b04 (by rw [g₁ _ (by decide), h17]) (by rw [g₁ _ (by decide), h18])
        (by rw [g₁ _ (by decide), h20]) (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', j₁ + 2 + j₂, .whileLtN_true (by rw [h17, h14]; omega) e₁ e₂, ?_, ?_, ?_, ?_,
        ?_, f₁.trans cf⟩
      · rw [hcons, List.length_cons]; omega
      · rw [c16, hcons, List.length_cons]; ring
      · rw [c04, hcons, List.length_cons]; ring
      · rw [hcons]
        intro i hi
        rcases i with _ | i
        · rw [cm _ (Or.inl (by omega)), cm _ (Or.inl (by omega)), cm _ (Or.inl (by omega)), bm]
          simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]
          refine ⟨?_, ?_, ?_⟩
          · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
              Machine.upd_same]
          · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_same]
          · rw [Machine.upd_same]
        · simp only [List.length_cons] at hi
          obtain ⟨x1, x2, x3⟩ := cL i (by omega)
          simp only [List.getD_cons_succ]
          refine ⟨?_, ?_, ?_⟩
          · rwa [show ptr + 3 * (i + 1) = ptr + 3 + 3 * i by ring]
          · rwa [show ptr + 3 * (i + 1) + 1 = ptr + 3 + 3 * i + 1 by ring]
          · rwa [show ptr + 3 * (i + 1) + 2 = ptr + 3 + 3 * i + 2 by ring]
      · intro x hx
        rw [hcons, List.length_cons] at hx
        rw [cm x (by omega), bm, Machine.upd_other _ _ _ (by omega),
          Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]

end exec

end

end DrvR

end Chazelle.Core
