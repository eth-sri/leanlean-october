module

public import Chazelle.Core.SweepEvStopSort

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 2 (writing one record)

`ssWr`: the raw record whose index is in `srX` (at `gRB + 11 srX`) is written as the stop record
`(e, h, kind, k, b)` (words `0, 1, 3, 4, 5`) at `sB + 5 sC` and as the auxiliary record
(words `6 … 10`) at `aB + 5 sC`; then `sC := sC + 1`.  The memory after the writes is `ssWM`
(`ssWr_exec`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR

@[expose] public section

/-! ## Registers of the task -/

def srIB : ℕ := sw 3001
def srI : ℕ := sw 3002
def srA : ℕ := sw 3003
def srSB : ℕ := sw 3004
def srJ : ℕ := sw 3005
def srX : ℕ := sw 3006
def srP : ℕ := sw 3007
def srT : ℕ := sw 3008
def srS : ℕ := sw 3009
def srD : ℕ := sw 3010
def srE : ℕ := sw 3011
def srV : ℕ := sw 3012
def sr1 : ℕ := sw 3013
def sr2 : ℕ := sw 3014
def sr3 : ℕ := sw 3015
def sr4 : ℕ := sw 3016

set_option hygiene false in
/-- Register arithmetic on the named registers of the sort task. -/
macro "ssoSrt" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [srA0, srIB, srI, srA, srSB, srJ, srX,
                srP, srT, srS, srD, srE, srV, sr1, sr2, sr3, sr4, sB, sC, aB, gRB, gRC, K0, K1, ALLOC,
                sw, Nat.reduceAdd, ne_eq]; omega))

/-! ## The memory after a record write -/

/-- The word of the raw record copied to word `t < 5` of the stop record. -/
def ssOff (t : ℕ) : ℕ := if t < 2 then t else t + 1

/-- The memory after writing `nd` words of the stop record at `D` and `ne` words of the
auxiliary record at `E` from the raw record at `Src`. -/
def ssWM (m : ℕ → ℕ) (Src D E nd ne : ℕ) (a : ℕ) : ℕ :=
  if D ≤ a ∧ a < D + nd then m (Src + ssOff (a - D))
  else if E ≤ a ∧ a < E + ne then m (Src + 6 + (a - E)) else m a

theorem ssWM_zero (m : ℕ → ℕ) (Src D E : ℕ) : ssWM m Src D E 0 0 = m := by
  funext a; unfold ssWM; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem ssWM_src {m : ℕ → ℕ} {Src D E nd ne : ℕ} (hSD : Src + 11 ≤ D) (hDE : D + 5 ≤ E)
    {u : ℕ} (hu : u < 11) : ssWM m Src D E nd ne (Src + u) = m (Src + u) := by
  unfold ssWM; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem ssWM_stepD {m : ℕ → ℕ} {Src D E nd ne : ℕ} (_hDE : D + 5 ≤ E) (hnd : nd < 5) (_hne : ne ≤ 5) :
    upd (ssWM m Src D E nd ne) (D + nd) (m (Src + ssOff nd)) = ssWM m Src D E (nd + 1) ne := by
  funext a
  unfold ssWM
  rw [upd_apply]
  by_cases h : a = D + nd
  · subst h
    rw [ite_eq_left rfl, ite_eq_left (show D ≤ D + nd ∧ D + nd < D + (nd + 1) by omega),
      show D + nd - D = nd by omega]
  · rw [ite_eq_right h]
    by_cases h2 : D ≤ a ∧ a < D + nd
    · rw [ite_eq_left h2, ite_eq_left (show D ≤ a ∧ a < D + (nd + 1) by omega)]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ (D ≤ a ∧ a < D + (nd + 1)) by omega)]

theorem ssWM_stepE {m : ℕ → ℕ} {Src D E nd ne : ℕ} (hDE : D + 5 ≤ E) (hnd : nd ≤ 5) (hne : ne < 5) :
    upd (ssWM m Src D E nd ne) (E + ne) (m (Src + 6 + ne)) = ssWM m Src D E nd (ne + 1) := by
  funext a
  unfold ssWM
  rw [upd_apply]
  by_cases h : a = E + ne
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (show ¬ (D ≤ E + ne ∧ E + ne < D + nd) by omega),
      ite_eq_left (show E ≤ E + ne ∧ E + ne < E + (ne + 1) by omega), show E + ne - E = ne by omega]
  · rw [ite_eq_right h]
    by_cases h2 : D ≤ a ∧ a < D + nd
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : E ≤ a ∧ a < E + ne
      · rw [ite_eq_left h3, ite_eq_left (show E ≤ a ∧ a < E + (ne + 1) by omega)]
      · rw [ite_eq_right h3, ite_eq_right (show ¬ (E ≤ a ∧ a < E + (ne + 1)) by omega)]

/-! ## One copied word -/

/-- Copy the word at `srS` to the address in `R`, advancing both. -/
def ssCw (R : ℕ) : List Instr := [.loadN srV srS, .storeN R srV, .addN srS srS K1, .addN R R K1]

theorem ssCw_exec {P : Polygon} {W : ℕ} {d : Config} (hw : WordsBounded W d) {R : ℕ}
    (hK1 : d.nreg K1 = 1) (hR1 : R ≠ srV) (hR2 : R ≠ srS) (_hR3 : R ≠ K1) (hs : d.nreg srS + 1 ≤ W)
    (ht : d.nreg R + 1 ≤ W) :
    ∃ d', Exec P W (block (ssCw R)) d d' 4 ∧ d'.nreg srS = d.nreg srS + 1 ∧
      d'.nreg R = d.nreg R + 1 ∧ (∀ r, r ≠ srV → r ≠ srS → r ≠ R → d'.nreg r = d.nreg r) ∧
      d'.nmem = upd d.nmem (d.nreg R) (d.nmem (d.nreg srS)) ∧ d'.rreg = d.rreg ∧
      d'.rmem = d.rmem ∧ d'.output = d.output := by
  have nK1 : K1 ≠ srV ∧ K1 ≠ srS := by constructor <;> ssoSrt
  have nVS : srS ≠ srV := by ssoSrt
  have e₁ := Exec.loadN (P := P) hw srV srS
  have e₂ := Exec.storeN (P := P) e₁.wb_right R srV
  have e₃ := Exec.addN (P := P) e₂.wb_right srS srS K1 (by
    simp only; rw [upd_other _ _ _ nVS, upd_other _ _ _ nK1.1, hK1]; exact hs)
  have e₄ := Exec.addN (P := P) e₃.wb_right R R K1 (by
    simp only
    rw [upd_other _ _ _ hR2, upd_other _ _ _ hR1, upd_other _ _ _ nK1.2, upd_other _ _ _ nK1.1,
      hK1]; exact ht)
  refine ⟨_, Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_cons e₃ (Exec.block_cons e₄
    (Exec.block_nil e₄.wb_right)))), ?_, ?_, fun r a b c' => ?_, ?_, rfl, rfl, rfl⟩
  · simp only
    rw [upd_other _ _ _ (Ne.symm hR2), upd_same, upd_other _ _ _ nVS, upd_other _ _ _ nK1.1, hK1]
  · simp only [upd_same]
    rw [upd_other _ _ _ hR2, upd_other _ _ _ hR1, upd_other _ _ _ nK1.2, upd_other _ _ _ nK1.1,
      hK1]
  · simp only
    rw [upd_other _ _ _ c', upd_other _ _ _ b, upd_other _ _ _ a]
  · simp only
    rw [upd_other _ _ _ hR1, upd_same]

/-! ## The record write -/

/-- The source and destination pointers. -/
def ssWrHead : List Instr :=
  [.addN sr1 srX srX, .addN sr2 sr1 sr1, .addN sr3 sr2 sr2, .addN sr4 sr3 sr1, .addN sr4 sr4 srX,
    .addN srS sr4 gRB, .addN sr1 sC sC, .addN sr2 sr1 sr1, .addN sr2 sr2 sC, .addN srD sB sr2,
    .addN srE aB sr2]

/-- **Write the record of `srX`.** -/
def ssWr : Stmt :=
  .seq (block ssWrHead) (.seq (block (ssCw srD)) (.seq (block (ssCw srD))
    (.seq (.instr (.addN srS srS K1)) (.seq (block (ssCw srD)) (.seq (block (ssCw srD))
      (.seq (block (ssCw srD)) (.seq (block (ssCw srE)) (.seq (block (ssCw srE))
        (.seq (block (ssCw srE)) (.seq (block (ssCw srE)) (.seq (block (ssCw srE))
          (.instr (.addN sC sC K1)))))))))))))

set_option maxRecDepth 20000 in
theorem ssWrHead_val (m f : ℕ → ℕ) :
    regB m ssWrHead f srS = f srX + f srX + (f srX + f srX) + (f srX + f srX + (f srX + f srX)) +
      (f srX + f srX) + f srX + f gRB ∧
    regB m ssWrHead f srD = f sB + (f sC + f sC + (f sC + f sC) + f sC) ∧
    regB m ssWrHead f srE = f aB + (f sC + f sC + (f sC + f sC) + f sC) ∧
    ∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE →
      regB m ssWrHead f r = f r := by
  refine ⟨?_, ?_, ?_, fun r a b d e g h i => ?_⟩
  all_goals simp only [ssWrHead, regB, regI, sr1, sr2, sr3, sr4, srS, srD, srE, srX, sC, sB, aB, gRB, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  simp only [sr1, sr2, sr3, sr4, srS, srD, srE, sw, Nat.reduceAdd] at a b d e g h i
  simp only [upd_apply]
  repeat rw [ite_eq_right (by omega)]

set_option maxRecDepth 20000 in
theorem ssWrHead_ok {W : ℕ} (m f : ℕ → ℕ)
    (h1 : f gRB + 11 * f srX + 11 ≤ f sB + 5 * f sC) (h2 : f aB + 5 * f sC + 6 ≤ W)
    (h3 : f sB ≤ f aB) : okW W m ssWrHead f := by
  simp only [srX, sC, sB, aB, gRB, sw, Nat.reduceAdd] at h1 h2 h3
  simp only [ssWrHead, okW, okWI, regI, sr1, sr2, sr3, sr4, srS, srD, srE, srX, sC, sB, aB, gRB, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, and_true]
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Writing one record**: from the raw record `x` at `Src = gRB + 11 x` (below the destination),
the stop record at `D = sB + 5 sC`, the auxiliary record at `E = aB + 5 sC` (`D + 5 ≤ E`),
`sC := sC + 1`. -/
theorem ssWr_exec {P : Polygon} {W : ℕ} {d : Config} (hw : WordsBounded W d)
    (hK1 : d.nreg K1 = 1)
    (hSD : d.nreg gRB + 11 * d.nreg srX + 11 ≤ d.nreg sB + 5 * d.nreg sC)
    (hDE : d.nreg sB + 5 * d.nreg sC + 5 ≤ d.nreg aB + 5 * d.nreg sC)
    (hEW : d.nreg aB + 5 * d.nreg sC + 6 ≤ W) :
    ∃ d' k, Exec P W ssWr d d' k ∧ k = 53 ∧
      d'.nmem = ssWM d.nmem (d.nreg gRB + 11 * d.nreg srX) (d.nreg sB + 5 * d.nreg sC)
        (d.nreg aB + 5 * d.nreg sC) 5 5 ∧
      d'.nreg sC = d.nreg sC + 1 ∧
      (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV → r ≠ sC →
        d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  set Src := d.nreg gRB + 11 * d.nreg srX with hSrc
  set D := d.nreg sB + 5 * d.nreg sC with hD
  set E := d.nreg aB + 5 * d.nreg sC with hE
  set m := d.nmem with hm
  obtain ⟨vS, vD, vE, vo⟩ := ssWrHead_val d.nmem d.nreg
  have e₀ := exec_regB (P := P) ssWrHead hw (ssWrHead_ok d.nmem d.nreg (by omega) (by omega) (by omega))
  set d₀ : Config := { d with nreg := regB d.nmem ssWrHead d.nreg } with hd₀
  have p0S : d₀.nreg srS = Src := by show regB _ _ _ srS = _; rw [vS]; omega
  have p0D : d₀.nreg srD = D := by show regB _ _ _ srD = _; rw [vD]; omega
  have p0E : d₀.nreg srE = E := by show regB _ _ _ srE = _; rw [vE]; omega
  have p0o : ∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE →
      d₀.nreg r = d.nreg r := vo
  have p0K : d₀.nreg K1 = 1 := by
    rw [p0o K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hK1
  have hSDv : Src + 11 ≤ D := by omega
  have hDEv : D + 5 ≤ E := by omega
  have hCW : d.nreg sC + 1 ≤ W := by omega
  -- the state after `nd`, `ne` words, with the source pointer at `u`
  let St : ℕ → ℕ → ℕ → Config → Prop := fun nd ne u d' => WordsBounded W d' ∧
    d'.nreg srS = Src + u ∧ d'.nreg srD = D + nd ∧ d'.nreg srE = E + ne ∧
    d'.nmem = ssWM m Src D E nd ne ∧
    (∀ r, r ≠ sr1 → r ≠ sr2 → r ≠ sr3 → r ≠ sr4 → r ≠ srS → r ≠ srD → r ≠ srE → r ≠ srV →
      d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output
  have S0 : St 0 0 0 d₀ := ⟨e₀.wb_right, p0S.trans (Nat.add_zero _).symm, p0D.trans (Nat.add_zero _).symm,
    p0E.trans (Nat.add_zero _).symm,
    by rw [ssWM_zero], fun r a b c' e f g h _ => p0o r a b c' e f g h, rfl, rfl, rfl⟩
  have stepD : ∀ nd ne u d', St nd ne u d' → nd < 5 → ne ≤ 5 → ssOff nd = u →
      ∃ d'', Exec P W (block (ssCw srD)) d' d'' 4 ∧ St (nd + 1) ne (u + 1) d'' := by
    intro nd ne u d' ⟨w', s1, s2, s3, s4, s5, s6, s7, s8⟩ hnd hne hu
    have hK : d'.nreg K1 = 1 := by
      rw [s5 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hK1
    have hu11 : u < 11 := by rw [← hu]; unfold ssOff; split_ifs <;> omega
    obtain ⟨d'', ex, t1, t2, t3, t4, t5, t6, t7⟩ := ssCw_exec (P := P) (R := srD) w' hK (by ssoSrt)
      (by ssoSrt) (by ssoSrt) (by rw [s1]; omega) (by rw [s2]; omega)
    refine ⟨d'', ex, ex.wb_right, by rw [t1, s1]; omega, by rw [t2, s2]; omega, ?_, ?_,
      fun r a b c' e f g h i => ?_, by rw [t5, s6], by rw [t6, s7], by rw [t7, s8]⟩
    · rw [t3 srE (by ssoSrt) (by ssoSrt) (by ssoSrt), s3]
    · rw [t4, s4, s2, s1, ssWM_src hSDv hDEv hu11, ← hu]
      exact ssWM_stepD hDEv hnd hne
    · rw [t3 r i f g, s5 r a b c' e f g h i]
  have stepE : ∀ ne u d', St 5 ne u d' → ne < 5 → 6 + ne = u →
      ∃ d'', Exec P W (block (ssCw srE)) d' d'' 4 ∧ St 5 (ne + 1) (u + 1) d'' := by
    intro ne u d' ⟨w', s1, s2, s3, s4, s5, s6, s7, s8⟩ hne hu
    have hK : d'.nreg K1 = 1 := by
      rw [s5 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hK1
    obtain ⟨d'', ex, t1, t2, t3, t4, t5, t6, t7⟩ := ssCw_exec (P := P) (R := srE) w' hK (by ssoSrt)
      (by ssoSrt) (by ssoSrt) (by rw [s1]; omega) (by rw [s3]; omega)
    refine ⟨d'', ex, ex.wb_right, by rw [t1, s1]; omega, ?_, by rw [t2, s3]; omega, ?_,
      fun r a b c' e f g h i => ?_, by rw [t5, s6], by rw [t6, s7], by rw [t7, s8]⟩
    · rw [t3 srD (by ssoSrt) (by ssoSrt) (by ssoSrt), s2]
    · rw [t4, s4, s3, s1, ssWM_src hSDv hDEv (by omega), ← hu,
        show Src + (6 + ne) = Src + 6 + ne by omega]
      exact ssWM_stepE hDEv le_rfl hne
    · rw [t3 r i f h, s5 r a b c' e f g h i]
  obtain ⟨d₁, x₁, S1⟩ := stepD 0 0 0 d₀ S0 (by norm_num) (by norm_num) rfl
  obtain ⟨d₂, x₂, S2⟩ := stepD 1 0 1 d₁ S1 (by norm_num) (by norm_num) rfl
  -- skip word `2`
  obtain ⟨w₂, s21, s22, s23, s24, s25, s26, s27, s28⟩ := S2
  have hK₂ : d₂.nreg K1 = 1 := by
    rw [s25 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hK1
  have x₃ := Exec.addN (P := P) w₂ srS srS K1 (by rw [s21, hK₂]; omega)
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg srS (d₂.nreg srS + d₂.nreg K1) } with hd₃
  have S3 : St 2 0 3 d₃ := by
    refine ⟨x₃.wb_right, by simp only [hd₃, upd_same]; rw [s21, hK₂], ?_, ?_, s24,
      fun r a b c' e f g h i => ?_, s26, s27, s28⟩
    · simp only [hd₃]; rw [upd_other _ _ _ (show srD ≠ srS by ssoSrt)]; exact s22
    · simp only [hd₃]; rw [upd_other _ _ _ (show srE ≠ srS by ssoSrt)]; exact s23
    · simp only [hd₃]; rw [upd_other _ _ _ f]; exact s25 r a b c' e f g h i
  obtain ⟨d₄, x₄, S4⟩ := stepD 2 0 3 d₃ S3 (by norm_num) (by norm_num) rfl
  obtain ⟨d₅, x₅, S5⟩ := stepD 3 0 4 d₄ S4 (by norm_num) (by norm_num) rfl
  obtain ⟨d₆, x₆, S6⟩ := stepD 4 0 5 d₅ S5 (by norm_num) (by norm_num) rfl
  obtain ⟨d₇, x₇, S7⟩ := stepE 0 6 d₆ S6 (by norm_num) rfl
  obtain ⟨d₈, x₈, S8⟩ := stepE 1 7 d₇ S7 (by norm_num) rfl
  obtain ⟨d₉, x₉, S9⟩ := stepE 2 8 d₈ S8 (by norm_num) rfl
  obtain ⟨d₁₀, x₁₀, S10⟩ := stepE 3 9 d₉ S9 (by norm_num) rfl
  obtain ⟨d₁₁, x₁₁, S11⟩ := stepE 4 10 d₁₀ S10 (by norm_num) rfl
  obtain ⟨w₁₁, -, -, -, s114, s115, s116, s117, s118⟩ := S11
  have hK₁₁ : d₁₁.nreg K1 = 1 := by
    rw [s115 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hK1
  have hC₁₁ : d₁₁.nreg sC = d.nreg sC :=
    s115 sC (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have x₁₂ := Exec.addN (P := P) w₁₁ sC sC K1 (by rw [hC₁₁, hK₁₁]; exact hCW)
  refine ⟨_, _, .seq e₀ (.seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ (.seq x₇ (.seq x₈
    (.seq x₉ (.seq x₁₀ (.seq x₁₁ x₁₂))))))))))), by simp [ssWrHead], s114, ?_,
    fun r a b c' e f g h i j => ?_, s116, s117, s118⟩
  · simp only [upd_same]; rw [hC₁₁, hK₁₁]
  · simp only; rw [upd_other _ _ _ j]; exact s115 r a b c' e f g h i

end

end SweepEv

end Chazelle.Core
