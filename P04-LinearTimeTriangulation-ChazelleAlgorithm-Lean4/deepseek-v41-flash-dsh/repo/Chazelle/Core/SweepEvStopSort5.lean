module

public import Chazelle.Core.SweepEvStopSort4

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 5 (task S)

The program `ssSrt`:
1. `ssIdx`: the indices `0 … S - 1` in fresh memory (at the entry allocator `A`, saved in `srA0`);
2. `SortR.sortStmt ssCmp` on them (`SortR.sort_meets`): a sorted permutation `L` at `srSB`;
3. `ssAllocL`: the two output arrays `sB` (stop records) and `aB = sB + 5 S` (auxiliary records),
   ten words per raw record;
4. `ssDedup`: the dedupe pass (`ssDedup_exec`).

**`sortTask : SortTask`** (constant `κ = 40000`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR
open SortL

@[expose] public section

/-! ## The program -/

def ssIdxHead : List Instr := [.copyN srA0 ALLOC, .copyN srIB ALLOC, .constN srI 0]

def ssIdxBody : List Instr := [.addN srA srIB srI, .storeN srA srI, .addN srI srI K1]

/-- The indices `0 … S - 1` at the allocator. -/
def ssIdx : Stmt :=
  .seq (block ssIdxHead) (.seq (.whileLtN srI gRC (block ssIdxBody)) (.instr (.addN ALLOC ALLOC gRC)))

/-- The inputs of the sort. -/
def ssSortIn : List Instr := [.copyN 30003 srIB, .copyN 30004 gRC]

/-- The output arrays. -/
def ssAllocL : List Instr :=
  [.copyN srSB 30005, .copyN sB ALLOC, .addN srT gRC gRC, .addN srT srT srT, .addN srT srT gRC,
    .addN aB sB srT, .addN ALLOC ALLOC srT, .addN ALLOC ALLOC srT, .constN sC 0, .constN srJ 0]

/-- **The sort task.** -/
def ssSrt : Stmt :=
  .seq ssIdx (.seq (block ssSortIn) (.seq (sortStmt ssCmp) (.seq (block ssAllocL) ssDedup)))

/-! ## The indices -/

set_option maxRecDepth 20000 in
theorem ssIdx_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hK1 : c.nreg K1 = 1) (hroom : c.nreg ALLOC + c.nreg gRC + 1 ≤ W) :
    ∃ c' k, Exec P W ssIdx c c' k ∧ k = 5 * c.nreg gRC + 6 ∧
      c'.nreg ALLOC = c.nreg ALLOC + c.nreg gRC ∧ c'.nreg srA0 = c.nreg ALLOC ∧
      c'.nreg srIB = c.nreg ALLOC ∧ (∀ i, i < c.nreg gRC → c'.nmem (c.nreg ALLOC + i) = i) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ ALLOC → r ≠ srA0 → r ≠ srIB → r ≠ srI → r ≠ srA → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A := c.nreg ALLOC with hA
  set S := c.nreg gRC with hS
  have e₀ := exec_regB (P := P) ssIdxHead hw (by
    simp only [ssIdxHead, okW, okWI]; exact ⟨trivial, trivial, by omega, trivial⟩)
  set c₁ : Config := { c with nreg := regB c.nmem ssIdxHead c.nreg } with hc₁
  have v1 : ∀ r, r ≠ srA0 → r ≠ srIB → r ≠ srI → c₁.nreg r = c.nreg r := fun r a b d => by
    simp only [hc₁, ssIdxHead, regB, regI]
    rw [upd_other _ _ _ d, upd_other _ _ _ b, upd_other _ _ _ a]
  have vI : c₁.nreg srI = 0 := by simp only [hc₁, ssIdxHead, regB, regI, upd_same]
  have vB : c₁.nreg srIB = A := by
    simp only [hc₁, ssIdxHead, regB, regI]
    rw [upd_other _ _ _ (by ssoSrt), upd_same, upd_other _ _ _ (show ALLOC ≠ srA0 by ssoSrt)]
  have v0 : c₁.nreg srA0 = A := by
    simp only [hc₁, ssIdxHead, regB, regI]
    rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), upd_same]
  have vA : c₁.nreg ALLOC = A := v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have vS : c₁.nreg gRC = S := v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)
  have vK : c₁.nreg K1 = 1 := (v1 _ (by ssoSrt) (by ssoSrt) (by ssoSrt)).trans hK1
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧ d.nreg srI = i ∧
    (∀ t, t < i → d.nmem (A + t) = t) ∧ (∀ a, a < A → d.nmem a = c.nmem a) ∧
    (∀ r, r ≠ srI → r ≠ srA → d.nreg r = c₁.nreg r) ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
    d.output = c.output
  have I₀ : I 0 c₁ := ⟨e₀.wb_right, vI, fun t ht => absurd ht (Nat.not_lt_zero _),
    fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, e₁, w₂, hI2, ht2, hm2, hr2, rr2, rm2, o2⟩ :=
    while_exact (P := P) (W := W) (a := srI) (b := gRC) (body := block ssIdxBody) I S 3
      (fun i d h => by rw [h.2.1, h.2.2.2.2.1 _ (by ssoSrt) (by ssoSrt), vS])
      (fun i d h => h.1)
      (fun i d ⟨hwd, hi, ht, hm, hr, rr, rm, o⟩ hlt => by
        have dB : d.nreg srIB = A := by rw [hr _ (by ssoSrt) (by ssoSrt), vB]
        have dK : d.nreg K1 = 1 := by rw [hr _ (by ssoSrt) (by ssoSrt), vK]
        have x₁ := Exec.addN (P := P) hwd srA srIB srI (by rw [dB, hi]; omega)
        have x₂ := Exec.storeN (P := P) x₁.wb_right srA srI
        have x₃ := Exec.addN (P := P) x₂.wb_right srI srI K1 (by
          simp only
          rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), hi, dK]; omega)
        refine ⟨_, Exec.block_cons x₁ (Exec.block_cons x₂ (Exec.block_cons x₃
          (Exec.block_nil x₃.wb_right))), x₃.wb_right, ?_, fun t ht' => ?_, fun a ha => ?_,
          fun r h1 h2 => ?_, rr, rm, o⟩
        · simp only [upd_same]
          rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), hi, dK]
        · simp only [upd_same]
          rw [upd_other _ _ _ (show srI ≠ srA by ssoSrt), dB, hi]
          rcases Nat.lt_or_ge t i with h | h
          · rw [upd_other _ _ _ (by omega)]; exact ht t h
          · rw [show t = i by omega, upd_same]
        · simp only [upd_same]
          rw [upd_other _ _ _ (by rw [dB, hi]; omega)]; exact hm a ha
        · simp only
          rw [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact hr r h1 h2)
      0 c₁ I₀ (Nat.zero_le _)
  have gA : c₂.nreg ALLOC = A := by rw [hr2 _ (by ssoSrt) (by ssoSrt), vA]
  have gS : c₂.nreg gRC = S := by rw [hr2 _ (by ssoSrt) (by ssoSrt), vS]
  have x₄ := Exec.addN (P := P) w₂ ALLOC ALLOC gRC (by rw [gA, gS]; omega)
  refine ⟨_, _, .seq e₀ (.seq e₁ x₄), by simp [ssIdxHead]; ring, ?_, ?_, ?_, ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, rr2, rm2, o2⟩
  · simp only [upd_same]; rw [gA, gS]
  · simp only
    rw [upd_other _ _ _ (by ssoSrt), hr2 _ (by ssoSrt) (by ssoSrt), v0]
  · simp only
    rw [upd_other _ _ _ (by ssoSrt), hr2 _ (by ssoSrt) (by ssoSrt), vB]
  · intro i hi; exact ht2 i hi
  · intro a ha; exact hm2 a ha
  · simp only
    rw [upd_other _ _ _ h0, hr2 r h3 h4, v1 r h1 h2 h3]

set_option maxRecDepth 20000 in
theorem ssAllocL_val (m f : ℕ → ℕ) :
    regB m ssAllocL f srSB = f 30005 ∧ regB m ssAllocL f sB = f ALLOC ∧
    regB m ssAllocL f aB = f ALLOC + (f gRC + f gRC + (f gRC + f gRC) + f gRC) ∧
    regB m ssAllocL f ALLOC = f ALLOC + (f gRC + f gRC + (f gRC + f gRC) + f gRC) +
      (f gRC + f gRC + (f gRC + f gRC) + f gRC) ∧
    regB m ssAllocL f sC = 0 ∧ regB m ssAllocL f srJ = 0 ∧
    ∀ r, r ≠ srSB → r ≠ sB → r ≠ srT → r ≠ aB → r ≠ ALLOC → r ≠ sC → r ≠ srJ →
      regB m ssAllocL f r = f r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r a b d e g h i => ?_⟩
  all_goals simp only [ssAllocL, regB, regI, srSB, sB, srT, aB, ALLOC, sC, srJ, gRC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true]
  simp only [srSB, sB, srT, aB, ALLOC, sC, srJ, sw, Nat.reduceAdd] at a b d e g h i
  simp only [upd_apply]
  repeat rw [ite_eq_right (by omega)]

set_option maxRecDepth 20000 in
theorem ssAllocL_ok {W : ℕ} (m f : ℕ → ℕ)
    (h : f ALLOC + 10 * f gRC ≤ W) : okW W m ssAllocL f := by
  simp only [ALLOC, gRC, sw, Nat.reduceAdd] at h
  simp only [ssAllocL, okW, okWI, regI, srSB, sB, srT, aB, ALLOC, sC, srJ, gRC, sw,
    Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true, true_and,
    and_true]
  omega

end

end SweepEv

end Chazelle.Core
