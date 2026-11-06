module

public import Chazelle.Core.SweepEvInit2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stages 2–3: the initialisation, part 3 (the table of powers)

`tabS`: the table of powers `2 ^ j` for `j < L`, `L = ⌈log₂ (a₁ + a₂ + 1)⌉` (`aᵢ` the numbers of
arcs of the normal forms at `sw 3`, `sw 4`, read from their headers), at the allocator: base
`TBR = sw 600`, length `TLR = sw 601`; the allocator moves by `L`.  (The table of `OracleR.tbS`
uses registers outside the sweep and oracle bands.)
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

def iX : ℕ := sw 712
def iN : ℕ := sw 713
def iP : ℕ := sw 714

set_option hygiene false in
/-- Register arithmetic on the named registers of the table. -/
macro "swoInit3" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only [iX, iN,
  iP, iA, iV, K1, ALLOC, TBR, TLR, sw] at *; omega))

/-- The head of the table: `TBR := ALLOC`, `TLR := 0`, `x := 1`, `N := a₁ + a₂ + 1`. -/
def tabHead : List Instr :=
  [.copyN TBR ALLOC, .constN TLR 0, .constN iX 1, .addN iA (sw 3) K1, .loadN iN iA,
    .addN iA (sw 4) K1, .loadN iV iA, .addN iN iN iV, .addN iN iN K1]

/-- The body: `T[TLR] := x`, `x := 2 x`, `TLR := TLR + 1`. -/
def tabBodyI : List Instr :=
  [.addN iP TBR TLR, .storeN iP iX, .addN iX iX iX, .addN TLR TLR K1]

/-- **The table of powers.** -/
def tabS : Stmt :=
  .seq (block tabHead) (.seq (.whileLtN iX iN (block tabBodyI)) (.instr (.addN ALLOC ALLOC TLR)))

/-- **A loop with an exact count**: an invariant indexed by the number `j` of iterations done,
the test true exactly while `j < L`, a body of cost exactly `B`. -/
theorem while_exact {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} (I : ℕ → Config → Prop)
    (L B : ℕ) (htest : ∀ j d, I j d → (d.nreg a < d.nreg b ↔ j < L))
    (hwb : ∀ j d, I j d → WordsBounded W d)
    (hbody : ∀ j d, I j d → j < L → ∃ d', Exec P W body d d' B ∧ I (j + 1) d') :
    ∀ j d, I j d → j ≤ L →
      ∃ d', Exec P W (.whileLtN a b body) d d' ((B + 2) * (L - j) + 2) ∧ I L d' := by
  intro j d hI hj
  induction hn : L - j generalizing j d with
  | zero =>
    have hjL : j = L := by omega
    subst hjL
    exact ⟨d, .whileLtN_false (fun h => absurd ((htest j d hI).1 h) (lt_irrefl _)) (hwb j d hI),
      hI⟩
  | succ n ih =>
    have hlt : j < L := by omega
    obtain ⟨d₁, e₁, hI₁⟩ := hbody j d hI hlt
    obtain ⟨d', e', hI'⟩ := ih (j + 1) d₁ hI₁ (by omega) (by omega)
    refine ⟨d', (Exec.whileLtN_true ((htest j d hI).2 hlt) e₁ e').cast (by ring), hI'⟩

theorem tabHead_val (m f : ℕ → ℕ) :
    regB m tabHead f TBR = f ALLOC ∧ regB m tabHead f TLR = 0 ∧ regB m tabHead f iX = 1 ∧
      (f K1 = 1 → regB m tabHead f iN = m (f (sw 3) + 1) + m (f (sw 4) + 1) + 1) ∧
      ∀ r, r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → regB m tabHead f r = f r := by
  refine ⟨?_, ?_, ?_, fun h1 => ?_, fun r a b d e g i => ?_⟩
  all_goals simp [tabHead, regB, regI, TBR, TLR, iX, iA, iN, iV, K1, ALLOC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  · simp [K1, sw, Nat.reduceAdd] at h1; rw [h1]
  · simp [TBR, TLR, iX, iA, iN, iV, sw, Nat.reduceAdd] at a b d e g i
    simp [upd_apply, ite_eq_right a, ite_eq_right b, ite_eq_right d, ite_eq_right e, ite_eq_right g, ite_eq_right i]

/-- **The table of powers**: base `A₀` (the allocator), length `L = ⌈log₂ (a₁ + a₂ + 1)⌉`. -/
theorem tabS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hK1 : c.nreg K1 = 1) (h3 : c.nreg (sw 3) + 1 ≤ W) (h4 : c.nreg (sw 4) + 1 ≤ W)
    (hroom : c.nreg ALLOC + 2 * (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1) + 4
      ≤ W) :
    ∃ c' k, Exec P W tabS c c' k ∧
      k = 6 * Nat.clog 2 (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1) + 12 ∧
      c'.nreg TBR = c.nreg ALLOC ∧
      c'.nreg TLR = Nat.clog 2 (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1) ∧
      c'.nreg ALLOC = c.nreg ALLOC + c'.nreg TLR ∧
      (∀ j, j < c'.nreg TLR → c'.nmem (c.nreg ALLOC + j) = 2 ^ j) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ ALLOC → r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → r ≠ iP →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set a₁ := c.nmem (c.nreg (sw 3) + 1) with ha₁
  set a₂ := c.nmem (c.nreg (sw 4) + 1) with ha₂
  set A₀ := c.nreg ALLOC with hA₀
  set Lf := Nat.clog 2 (a₁ + a₂ + 1) with hLf
  have hLpow : a₁ + a₂ + 1 ≤ 2 ^ Lf := Nat.le_pow_clog (by norm_num) _
  have hLle : Lf ≤ a₁ + a₂ + 1 := by
    rw [hLf, Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_two_pow_self).le
  -- the head
  obtain ⟨vB, vL, vX, vN, vo⟩ := tabHead_val c.nmem c.nreg
  have e₁ := exec_regB (P := P) tabHead hw (by
    simp [tabHead, okW, okWI, regI, TBR, TLR, iX, iA, iN, iV, K1, ALLOC, sw, Nat.reduceAdd,
      upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, true_and, and_true]
    simp [K1, sw, Nat.reduceAdd] at hK1 h3 h4 ha₁ ha₂
    rw [hK1]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩)
  set c₁ : Config := { c with nreg := regB c.nmem tabHead c.nreg } with hc₁
  have n₁ : ∀ r, r ≠ TBR → r ≠ TLR → r ≠ iX → r ≠ iA → r ≠ iN → r ≠ iV → c₁.nreg r = c.nreg r :=
    vo
  have g11 : c₁.nreg K1 = 1 := by rw [n₁ _ (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3), hK1]
  have gA : c₁.nreg ALLOC = A₀ :=
    n₁ _ (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3) (by swoInit3)
  have gB : c₁.nreg TBR = A₀ := vB
  have gN : c₁.nreg iN = a₁ + a₂ + 1 := vN hK1
  -- the loop
  let I : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg TLR = j ∧
    d.nreg iX = 2 ^ j ∧ (∀ t, t < j → d.nmem (A₀ + t) = 2 ^ t) ∧
    (∀ r, r ≠ iX → r ≠ iP → r ≠ TLR → d.nreg r = c₁.nreg r) ∧
    (∀ a, a < A₀ → d.nmem a = c₁.nmem a) ∧ d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧
    d.output = c₁.output
  have I₁ : I 0 c₁ := ⟨e₁.wb_right, vL, vX.trans (pow_zero 2).symm,
    fun t ht => absurd ht (Nat.not_lt_zero _), fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  have hN : ∀ j d, I j d → d.nreg iN = a₁ + a₂ + 1 := fun j d h => by
    rw [h.2.2.2.2.1 _ (by swoInit3) (by swoInit3) (by swoInit3), gN]
  obtain ⟨c₂, e₂, w₂, hj, hx, htab, hr₂, hm₂, rr₂, rm₂, o₂⟩ :=
    while_exact (P := P) (W := W) (a := iX) (b := iN) (body := block tabBodyI) I Lf 4
      (fun j d h => by
        rw [h.2.2.1, hN j d h, hLf, Nat.lt_clog_iff_pow_lt (by norm_num)])
      (fun j d h => h.1)
      (fun j d ⟨hwd, hj, hx, htab, hr, hm, rr, rm, o⟩ hjl => by
        have dB : d.nreg TBR = A₀ := by rw [hr _ (by swoInit3) (by swoInit3) (by swoInit3), gB]
        have d11 : d.nreg K1 = 1 := by rw [hr _ (by swoInit3) (by swoInit3) (by swoInit3), g11]
        have ht : 2 ^ j < a₁ + a₂ + 1 := by
          rwx [← Nat.lt_clog_iff_pow_lt (by norm_num)]
        have hjL : j ≤ Lf := hjl.le
        have e₁ := Exec.addN (P := P) hwd iP TBR TLR (by rwo [dB, hj])
        have e₂ := Exec.storeN (P := P) e₁.wb_right iP iX
        have e₃ := Exec.addN (P := P) e₂.wb_right iX iX iX (by
          simp
          rwo [upd_other _ _ _ (by swoInit3), hx])
        have e₄ := Exec.addN (P := P) e₃.wb_right TLR TLR K1 (by
          simp
          rw [upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3),
            upd_other _ _ _ (by swoInit3), hj, d11]; omega)
        refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃
          (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right)))), e₄.wb_right, ?_, ?_,
          fun t ht' => ?_, fun r a b c' => ?_, fun a ha => ?_, rr, rm, o⟩
        · simp [upd_same]
          rw [upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3), upd_other _ _ _ (by swoInit3),
            upd_other _ _ _ (by swoInit3), hj, d11]
        · simp
          rwring [upd_other _ _ _ (by swoInit3), upd_same, upd_other _ _ _ (by swoInit3), hx, pow_succ]
        · simp [upd_same]
          rw [upd_other _ _ _ (show iX ≠ iP by swoInit3), dB, hj]
          rcases Nat.lt_or_ge t j with h | h
          · rw [upd_other _ _ _ (by omega)]; exact htab t h
          · rw [show t = j by omega, upd_same, hx]
        · simp
          rw [upd_other _ _ _ c', upd_other _ _ _ a, upd_other _ _ _ b]; exact hr r a b c'
        · simp
          rw [upd_other _ _ _ (by simp [upd_same]; rwo [dB, hj])]
          exact hm a ha)
      0 c₁ I₁ (Nat.zero_le _)
  -- the end of the loop
  have g9 : c₂.nreg ALLOC = A₀ := by rw [hr₂ _ (by swoInit3) (by swoInit3) (by swoInit3), gA]
  have e₃ := Exec.addN (P := P) w₂ ALLOC ALLOC TLR (by rwo [hj, g9])
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ?_, ?_, ?_, ?_, fun t ht => ?_, fun a ha => ?_,
    fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, by simp; rw [rr₂], by simp; rw [rm₂],
    by simp; rw [o₂]⟩
  · sio only [tabHead, List.length_cons, List.length_nil]
  · simp; rw [upd_other _ _ _ (by swoInit3), hr₂ _ (by swoInit3) (by swoInit3) (by swoInit3), gB]
  · simp; rw [upd_other _ _ _ (by swoInit3), hj]
  · simp [upd_same]; rw [upd_other _ _ _ (by swoInit3), hj, g9]
  · simp
    simp at ht
    rw [upd_other _ _ _ (by swoInit3), hj] at ht
    exact htab t ht
  · simp; rw [hm₂ a ha]
  · simp
    rw [upd_other _ _ _ h0, hr₂ r h3 h7 h2]
    exact n₁ r h1 h2 h3 h4 h5 h6

end

end SweepEv

end Chazelle.Core
