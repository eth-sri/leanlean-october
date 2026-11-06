module

public import Chazelle.Core.DownPhaseDrvTOrient
public import Chazelle.Core.BruteRam3
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 2000000

/-!
# Down-phase transition (D2), RAM part 2: the inner-side shift `c₀`

`c0S` runs the set-up of the brute-force procedure (`Brute.setupS`) on the top chain
(`s = 0`, `m = n - 1`), which computes its top index and the tour start `S = sideS sideBeta`
(register `180015`), then `c0Calc` computes, from `S`, `2m` and the `LeftInside` bit (register
`190001`), the shift `c₀ = c0 C li` (register `190014`, `i0F`, `i0F_eq`), `c₀ + m` (`190015`),
the index of interior walk vertex `0` (`190016`) and `m` (`190010`) (`c0S_exec`).
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

/-! ## The arithmetic -/

/-- The tour index `i0` from the tour start `S`: `sA = S mod 2m`, then
`(2m - sA) mod 2m` (if `LeftInside`) or `(3m - sA) mod 2m`. -/
def i0F (li : Bool) (m tS : ℕ) : ℕ :=
  if li then (if 0 < (if tS < 2 * m then tS else 0) then 2 * m - (if tS < 2 * m then tS else 0)
    else 0)
  else (if m < (if tS < 2 * m then tS else 0) then 2 * m + m - (if tS < 2 * m then tS else 0)
    else m - (if tS < 2 * m then tS else 0))

theorem sideS_le_two_m (C : Chain) (β : Bool) : C.sideS β ≤ 2 * C.m := by
  have := C.topIdx_le
  unfold Chain.sideS; splao

/-- **The formula is `i0`.** -/
theorem i0F_eq (C : Chain) (li : Bool) : i0F li C.m (C.sideS C.sideBeta) = i0 C li := by
  have hm := C.one_le
  have hS := sideS_le_two_m C C.sideBeta
  have hsA : TourA.sA C C.sideBeta = if C.sideS C.sideBeta < 2 * C.m then C.sideS C.sideBeta
      else 0 := by
    rw [sA_eq]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show C.sideS C.sideBeta = 2 * C.m by omega, Nat.mod_self]
  rw [i0_eq]
  have hs := sA_lt' (C := C)
  unfold i0F
  rw [← hsA]
  cases li
  · simp [Bool.false_eq_true, ite_false]
    split_ifs with h
    · rwo [Nat.mod_eq_of_lt (by omega)]
    · rw [show 3 * C.m - TourA.sA C C.sideBeta = (C.m - TourA.sA C C.sideBeta) + 2 * C.m by
        omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · simp [ite_true]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]
    · rw [show TourA.sA C C.sideBeta = 0 by omega, Nat.sub_zero, Nat.mod_self]

/-! ## The program -/

/-- `s := 0`, `m := n - 1`. -/
def c0Pre : Stmt :=
  block [.constN 180000 0, .inputSize 190002, .constN 190017 1, .subN 180001 190002 190017]

/-- The shift from the tour start. -/
def c0Calc : Stmt :=
  .seq (block [.constN 190005 0, .constN 190006 6, .constN 190012 0, .copyN 190010 180001])
  (.seq (.ifLtN 180015 180012 (.instr (.copyN 190012 180015)) .skip)
  (.seq (.ifLtN 190005 190001
      (.seq (.instr (.constN 190013 0))
        (.ifLtN 190005 190012 (.instr (.subN 190013 180012 190012)) .skip))
      (.ifLtN 180001 190012 (block [.addN 190007 180012 180001, .subN 190013 190007 190012])
        (.instr (.subN 190013 180001 190012))))
  (.seq (block [.addN 190014 190013 190006, .addN 190015 190014 180001])
    (.ifLtN 190005 190001 (.instr (.constN 190016 0)) (.instr (.copyN 190016 180001))))))

/-- **The shift of the top chain.** -/
def c0S : Stmt := .seq c0Pre (.seq Brute.setupS c0Calc)

/-- The registers of `c0Calc`. -/
def Bcalc (r : ℕ) : Bool := decide (190005 ≤ r ∧ r ≤ 190016)

theorem wrM_c0Calc : wrM Bcalc c0Calc = true := by decide

/-- The registers of `c0S`. -/
def Bc0 (r : ℕ) : Bool := Brute.Bm r || B19 r

/-- The registers of `c0Pre`. -/
def Bpre (r : ℕ) : Bool := decide (r = 180000 ∨ r = 180001 ∨ r = 190002 ∨ r = 190017)

theorem wrM_c0Pre' : wrM Bpre c0Pre = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

theorem c0Calc_exec (c : Config) (hw : WordsBounded W c) {m tS : ℕ} {li : Bool}
    (h01 : c.nreg 180001 = m) (h12 : c.nreg 180012 = 2 * m) (h15 : c.nreg 180015 = tS)
    (hb : c.nreg 190001 = if li then 1 else 0) (_htS : tS ≤ 2 * m) (hW : 3 * m + 6 ≤ W) :
    ∃ c' k, Exec P W c0Calc c c' k ∧ k ≤ 20 ∧ c'.nreg 190010 = m ∧
      c'.nreg 190014 = i0F li m tS + 6 ∧ c'.nreg 190015 = i0F li m tS + 6 + m ∧
      c'.nreg 190016 = (if li then 0 else m) ∧ FrameM Bcalc c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, h4, hm⟩ : ∃ c' k, Exec P W c0Calc c c' k ∧ k ≤ 20 ∧
      c'.nreg 190010 = m ∧ c'.nreg 190014 = i0F li m tS + 6 ∧
      c'.nreg 190015 = i0F li m tS + 6 + m ∧ c'.nreg 190016 = (if li then 0 else m) ∧
      c'.nmem = c.nmem := by
    unfold c0Calc
    refine spec_seq ?_
    exec_block
    · omega
    · omega
    · omega
    -- `sA`
    refine spec_seq ?_
    set sA := if tS < 2 * m then tS else 0 with hsA
    have hsA2 : sA < 2 * m ∨ (sA = 0) := by rw [hsA]; splao
    obtain ⟨c₁, k₁, e₁, hk₁, v12, g₁, m₁⟩ : ∃ c₁ k₁, Exec P W
        (.ifLtN 180015 180012 (.instr (.copyN 190012 180015)) .skip)
        { pc := c.pc, nreg := upd (upd (upd (upd c.nreg 190005 0) 190006 6) 190012 0) 190010
            (c.nreg 180001), rreg := c.rreg, nmem := c.nmem, rmem := c.rmem,
            output := c.output } c₁ k₁ ∧ k₁ ≤ 2 ∧ c₁.nreg 190012 = sA ∧
        (∀ r, r ≠ 190012 → c₁.nreg r = (upd (upd (upd (upd c.nreg 190005 0) 190006 6) 190012 0)
          190010 (c.nreg 180001)) r) ∧ c₁.nmem = c.nmem := by
      by_cases h : tS < 2 * m
      · refine spec_ifLtN_true (by config_simp; rwx [h15, h12]) ?_
        refine spec_instr (Exec.copyN ‹WordsBounded _ _› _ _) fun _ => ?_
        refine ⟨by omega, by config_simp; rw [h15, hsA, ite_eq_left h], fun r hr => ?_, rfl⟩
        simp; rw [Machine.upd_other _ _ _ hr]
      · refine spec_ifLtN_false (by config_simp; rwx [h15, h12]) ?_
        refine spec_skip ‹WordsBounded _ _› ?_
        refine ⟨by omega, by config_simp; rw [hsA, ite_eq_right h], fun r _ => rfl, rfl⟩
    refine ⟨c₁, k₁, e₁, ?_⟩
    have w₁ := e₁.wb_right
    have g : ∀ r, r ≠ 190012 → r ≠ 190005 → r ≠ 190006 → r ≠ 190010 →
        c₁.nreg r = c.nreg r := fun r a1 a2 a3 a4 => by
      rw [g₁ r a1]; simp [a1, a2, a3, a4]
    have v05 : c₁.nreg 190005 = 0 := by rws [g₁ _ (by norm_num)]
    have v06 : c₁.nreg 190006 = 6 := by rws [g₁ _ (by norm_num)]
    have v10 : c₁.nreg 190010 = m := by rw [g₁ _ (by norm_num)]; simp [h01]
    have v01 : c₁.nreg 180001 = m := by rw [g _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h01]
    have v12' : c₁.nreg 180012 = 2 * m := by rw [g _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h12]
    have vb : c₁.nreg 190001 = if li then 1 else 0 := by
      rw [g _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hb]
    -- `i0`
    refine spec_seq ?_
    obtain ⟨c₂, k₂, e₂, hk₂, v13, g₂, m₂⟩ : ∃ c₂ k₂, Exec P W
        (.ifLtN 190005 190001
          (.seq (.instr (.constN 190013 0))
            (.ifLtN 190005 190012 (.instr (.subN 190013 180012 190012)) .skip))
          (.ifLtN 180001 190012 (block [.addN 190007 180012 180001, .subN 190013 190007 190012])
            (.instr (.subN 190013 180001 190012)))) c₁ c₂ k₂ ∧ k₂ ≤ 8 ∧
        c₂.nreg 190013 = i0F li m tS ∧
        (∀ r, r ≠ 190013 → r ≠ 190007 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
      cases li
      · -- not `LeftInside`
        refine spec_ifLtN_false (by rws [v05, vb]) ?_
        by_cases h : m < sA
        · refine spec_ifLtN_true (by rwx [v01, v12]) ?_
          exec_block
          · rwo [v12', v01]
          refine ⟨by omega, ?_, fun r a1 a2 => by config_simp; simp [a1, a2], rfl⟩
          config_simp
          rw [v12', v01, v12]
          unfold i0F; rw [← hsA]; simp [h]
        · refine spec_ifLtN_false (by rwx [v01, v12]) ?_
          refine spec_instr (Exec.subN ‹WordsBounded _ _› _ _ _) fun _ => ?_
          refine ⟨by omega, ?_, fun r a1 a2 => by config_simp; simp [a1], rfl⟩
          config_simp
          rw [v01, v12]
          unfold i0F; rw [← hsA]; simp [h]
      · -- `LeftInside`
        refine spec_ifLtN_true (by rws [v05, vb]) ?_
        refine spec_seq ?_
        refine spec_instr (Exec.constN ‹WordsBounded _ _› _ _ (by omega)) fun _ => ?_
        by_cases h : 0 < sA
        · refine spec_ifLtN_true (by config_simp; rwx [v05, v12]) ?_
          refine spec_instr (Exec.subN ‹WordsBounded _ _› _ _ _) fun _ => ?_
          refine ⟨by omega, ?_, fun r a1 a2 => by config_simp; simp [a1], rfl⟩
          config_simp
          rw [v12', v12]
          unfold i0F; rw [← hsA]; simp [h]
        · refine spec_ifLtN_false (by config_simp; rwx [v05, v12]) ?_
          refine spec_skip ‹WordsBounded _ _› ?_
          refine ⟨by omega, ?_, fun r a1 a2 => by config_simp; simp [a1], rfl⟩
          config_simp
          unfold i0F; rw [← hsA]; simp [h]
    refine ⟨c₂, k₂, e₂, ?_⟩
    have w₂ := e₂.wb_right
    have hi0 : i0F li m tS ≤ 2 * m := by
      unfold i0F; splao
    refine spec_seq ?_
    exec_block
    · rwo [v13, g₂ _ (by norm_num) (by norm_num), v06]
    · config_simp; rw [v13, g₂ _ (by norm_num) (by norm_num), v06,
        g₂ _ (by norm_num) (by norm_num), v01]; omega
    have w₃ := ‹WordsBounded W _›
    cases li
    · refine spec_ifLtN_false (by config_simp; rw [g₂ _ (by norm_num) (by norm_num), v05,
        g₂ _ (by norm_num) (by norm_num), vb]; simp) ?_
      refine spec_instr (Exec.copyN ‹WordsBounded _ _› _ _) fun _ => ?_
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · config_simp; rw [g₂ _ (by norm_num) (by norm_num), v10]
      · config_simp; rw [v13, g₂ _ (by norm_num) (by norm_num), v06]
      · config_simp; rw [v13, g₂ _ (by norm_num) (by norm_num), v06,
          g₂ _ (by norm_num) (by norm_num), v01]
      · config_simp; rwr [g₂ _ (by norm_num) (by norm_num), v01]
      · config_simp; rw [m₂, m₁]
    · refine spec_ifLtN_true (by config_simp; rw [g₂ _ (by norm_num) (by norm_num), v05,
        g₂ _ (by norm_num) (by norm_num), vb]; simp) ?_
      refine spec_instr (Exec.constN ‹WordsBounded _ _› _ _ (by omega)) fun _ => ?_
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · config_simp; rw [g₂ _ (by norm_num) (by norm_num), v10]
      · config_simp; rw [v13, g₂ _ (by norm_num) (by norm_num), v06]
      · config_simp; rw [v13, g₂ _ (by norm_num) (by norm_num), v06,
          g₂ _ (by norm_num) (by norm_num), v01]
      · csr
      · config_simp; rw [m₂, m₁]
  exact ⟨c', k, e, hk, h1, h2, h3, h4, exec_frameM e wrM_c0Calc, hm⟩

theorem c0Pre_exec (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W c0Pre c c' k ∧ k = 4 ∧ c'.nreg 180000 = 0 ∧ c'.nreg 180001 = P.n - 1 ∧
      FrameM Bpre c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W c0Pre c c' k ∧ k = 4 ∧
      c'.nreg 180000 = 0 ∧ c'.nreg 180001 = P.n - 1 ∧ c'.nmem = c.nmem := by
    unfold c0Pre
    exec_block
    · omega
    · omega
    · omega
    exact ⟨rfl, by config_simp, by config_simp, rfl⟩
  exact ⟨c', k, e, hk, h1, h2, exec_frameM e wrM_c0Pre', hm⟩

/-- **The inner-side shift of the top chain.** -/
theorem c0S_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {C : Chain} (hC : TopChain P C)
    {li : Bool} (c : Config) (hw : WordsBounded W c) (hb : c.nreg 190001 = if li then 1 else 0)
    (hroom : c.nreg ALLOC + 2 * P.n + 10 ≤ W) :
    ∃ c' k, Exec P W c0S c c' k ∧ k ≤ 260 * P.n + 1950 ∧
      c'.nreg 190010 = C.m ∧ c'.nreg 190014 = c0 C li ∧ c'.nreg 190015 = c0 C li + C.m ∧
      c'.nreg 190016 = idxI li P.n 0 ∧ c'.nreg 190001 = (if li then 1 else 0) ∧
      FrameM Bc0 c c' ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) := by
  obtain ⟨hCP, hCs, hCm⟩ := hC
  have hWn : P.n + 3 ≤ W := by ufo hostWords at hWh
  obtain ⟨c₁, k₁, e₁, hk₁, p0, p1, F₁, m₁⟩ := c0Pre_exec (P := P) hWn c hw
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := F₁.1 _ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hCtx, -, hlow, -, -, R₂, RR₂, rm₂, o₂⟩ :=
    Brute.setup_exec (P := P) hG (by ufo hostWords at hWh)
      (by ufo hostWords at hWh) hCP (by omega) c₁ e₁.wb_right
      (by rw [p0, hCs]) (by rwo [p1]) (by rwo [hA₁])
  obtain ⟨-, x01, -, -, -, x12, -, x15, -⟩ := hCtx
  have hb₂ : c₂.nreg 190001 = if li then 1 else 0 := by
    rw [R₂ _ (by decide), F₁.1 _ (by decide), hb]
  obtain ⟨c₃, k₃, e₃, hk₃, v10, v14, v15, v16, F₃, m₃⟩ := c0Calc_exec (P := P) c₂ e₂.wb_right
    (m := C.m) (tS := C.sideS C.sideBeta) (li := li) x01 x12 x15 hb₂
    (sideS_le_two_m C C.sideBeta) (by ufo hostWords at hWh)
  have hi0 := i0F_eq C li
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, v10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwr [v14, hi0]
  · rwr [v15, hi0]
  · rw [v16]; unfold idxI; cases li <;> simp; omega
  · rw [F₃.1 _ (by decide), hb₂]
  · refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · unfold Bc0 at hr; simp [Bool.or_eq_false_iff] at hr
      rw [F₃.1 r (by unfold Bcalc; unfold B19 at hr; sio at hr ⊢), R₂ r hr.1, F₁.1 r
        (by unfold Bpre; unfold B19 at hr; unfold Brute.Bm at hr; sio at hr ⊢)]
    · unfold Bc0 at hr; simp [Bool.or_eq_false_iff] at hr
      rw [F₃.2.1 r (by unfold Bcalc; unfold B19 at hr; sio at hr ⊢), RR₂ r hr.1, F₁.2.1 r
        (by unfold Bpre; unfold B19 at hr; unfold Brute.Bm at hr; sio at hr ⊢)]
    · rw [F₃.2.2.1, rm₂, F₁.2.2.1]
    · rw [F₃.2.2.2, o₂, F₁.2.2.2]
  · intro a ha
    rw [m₃, hlow a (by rwx [hA₁]), m₁]

end exec

end

end DrvT

end Chazelle.Core
