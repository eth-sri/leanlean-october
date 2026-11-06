module

public import Chazelle.Core.ClusterSplitExec

/-!
# WP-I, part 41: the split driver on the RAM

`driverStmt`: while the stack is not empty (`0 < tp`), run `splitBody`.  `driver_exec`: from a
memory with the static facts and the driver invariant, the driver ends with an empty stack; its
cost is paid by the potential `120 Σ_{stack} |P| size |P| + splitC L k · (2 μ / s - nsp)`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The split driver. -/
def driverStmt : Stmt := .whileLtN 130009 130701 splitBody

/-- The size potential of a list of segments. -/
def segPot (l : List (ℕ × ℕ)) : ℕ := (l.map (fun p => len p * Nat.size (len p))).sum

section body

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}
  {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin μ → Fin N} {preE slot : ℕ → ℕ}
  {upT : ℕ → ℕ} {k c : ℕ} {P : Polygon} {W : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- The number of splits is at most `2 μ / s`. -/
theorem DInv.nsp_le {S : SS} {m : ℕ → ℕ} {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)}
    {D : Finset ℕ} {nsp : ℕ} (hD : DInv M T k c S m stk fin D nsp) (hs : 0 < S.s) :
    nsp ≤ 2 * μ / S.s := by
  rw [Nat.le_div_iff_mul_le hs]
  have := hD.sinv.pot2
  omega

omit [Fintype F] [DecidableEq F] in
/-- The stack in memory is the list of the invariant. -/
theorem DInv.stk_eq {S : SS} {m : ℕ → ℕ} {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)}
    {D : Finset ℕ} {nsp : ℕ} (hD : DInv M T k c S m stk fin D nsp) :
    stkList m S.bSTK (2 * stk.length / 2) = stk := by
  rw [show 2 * stk.length / 2 = stk.length by omega]
  exact hD.stack.symm

/-- **The split driver.** -/
theorem driver_exec {S : SS} {A0 U : ℕ} {cf : Config} (hw : WordsBounded W cf)
    (hR : S.Regs cf) (hSF : SFacts M T a ha C R first preE slot upT k c S A0 U W cf.nmem)
    {stk : List (ℕ × ℕ)} {fin : Finset (ℕ × ℕ)} {D : Finset ℕ} {nsp : ℕ}
    (hD : DInv M T k c S cf.nmem stk fin D nsp)
    (htp : cf.nreg 130701 = 2 * stk.length) (hnsp : cf.nreg 130704 = nsp)
    (hk : 0 < k) (hs : 0 < S.s) :
    ∃ cf' K, Exec P W driverStmt cf cf' K ∧
      K ≤ 120 * segPot stk + splitC S.L k * (2 * μ / S.s - nsp) + 2 ∧
      WordsBounded W cf' ∧ S.Regs cf' ∧
      (∃ fin' D' nsp', DInv M T k c S cf'.nmem [] fin' D' nsp') ∧
      cf'.nreg 130701 = 0 ∧ StaticEq A0 U cf.nmem cf'.nmem ∧
      (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → cf'.nreg r = cf.nreg r) ∧
      cf'.rreg = cf.rreg ∧ cf'.rmem = cf.rmem ∧ cf'.output = cf.output := by
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ S.Regs c' ∧
    StaticEq A0 U cf.nmem c'.nmem ∧
    (∀ r, ¬ SplitRG r → r ≠ 130701 → r ≠ 130704 → c'.nreg r = cf.nreg r) ∧
    c'.rreg = cf.rreg ∧ c'.rmem = cf.rmem ∧ c'.output = cf.output ∧
    ∃ stk' fin' D' nsp', DInv M T k c S c'.nmem stk' fin' D' nsp' ∧
      c'.nreg 130701 = 2 * stk'.length ∧ c'.nreg 130704 = nsp'
  let Φ : Config → ℕ := fun c' =>
    120 * segPot (stkList c'.nmem S.bSTK (c'.nreg 130701 / 2)) +
      splitC S.L k * (2 * μ / S.s - c'.nreg 130704)
  have hΦ : ∀ c' stk' fin' D' nsp', DInv M T k c S c'.nmem stk' fin' D' nsp' →
      c'.nreg 130701 = 2 * stk'.length → c'.nreg 130704 = nsp' →
      Φ c' = 120 * segPot stk' + splitC S.L k * (2 * μ / S.s - nsp') := by
    intro c' stk' fin' D' nsp' h1 h2 h3
    simp only [Φ]
    rw [h2, h3, h1.stk_eq]
  obtain ⟨cf', K, e, ⟨hw', hR', hst', hfr', hrr', hrm', ho', stk', fin', D', nsp', hD', htp',
      hnsp'⟩, htest, hK⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130701)
    (body := splitBody) I Φ (fun c' h => h.1) (fun c1 hI1 htest => by
      obtain ⟨hw1, hR1, hst1, hfr1, hrr1, hrm1, ho1, stk1, fin1, D1, nsp1, hD1, htp1, hnsp1⟩ := hI1
      have hSF1 := hSF.of_static hst1
      rw [hR1.zero, htp1] at htest
      obtain ⟨⟨lo, hi⟩, rest, rfl⟩ : ∃ p rest, stk1 = p :: rest := by
        cases stk1 with
        | nil => simp at htest
        | cons p rest => exact ⟨p, rest, rfl⟩
      obtain ⟨c2, K2, e2, hK2, hw2, hR2, ⟨news, fin2, D2, hD2, htp2, hpot2⟩, hnsp2, hst2, hfr2,
          hrr2, hrm2, ho2⟩ := splitBody_exec (P := P) hw1 hR1 hSF1 hD1
        (by rw [htp1]; simp; ring) hnsp1 hk hs
      refine ⟨c2, K2, e2, ⟨hw2, hR2, hst1.trans hst2, fun r a b d => (hfr2 r a b d).trans
        (hfr1 r a b d), hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1, news ++ rest, fin2, D2,
        nsp1 + 1, hD2, htp2, hnsp2⟩, ?_⟩
      rw [hΦ c2 _ _ _ _ hD2 htp2 hnsp2, hΦ c1 _ _ _ _ hD1 htp1 hnsp1]
      have hle := hD2.nsp_le hs
      unfold segPot
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      unfold len at hpot2 ⊢
      simp only at hpot2 ⊢
      have hmul : splitC S.L k * (2 * μ / S.s - nsp1) =
          splitC S.L k * (2 * μ / S.s - (nsp1 + 1)) + splitC S.L k := by
        rw [show 2 * μ / S.s - nsp1 = (2 * μ / S.s - (nsp1 + 1)) + 1 by omega, Nat.mul_add,
          Nat.mul_one]
      rw [hmul]
      nlinarith)
    ⟨hw, hR, StaticEq.refl _ _ _, fun _ _ _ _ => rfl, rfl, rfl, rfl, stk, fin, D, nsp, hD, htp,
      hnsp⟩
  rw [hR'.zero, htp'] at htest
  have hnil : stk' = [] := by
    cases stk' with
    | nil => rfl
    | cons p rest => simp at htest
  subst hnil
  refine ⟨cf', K, e, ?_, hw', hR', ⟨fin', D', nsp', hD'⟩, by rw [htp']; rfl, hst', hfr', hrr',
    hrm', ho'⟩
  rwa [hΦ cf _ _ _ _ hD htp hnsp] at hK

end body

end

end Chazelle.Core.Cluster
