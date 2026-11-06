module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvKey2Sel

/-!
# The sweep (WP-D), stage 3: the next key (task K), the labels of a skipped stop

`stopLab`: the labels of the auxiliary record of the stop `sP` (if it is anchored) are appended
to the label list under construction `(kqN, kqL)`, and the flag `kqA` is raised:
`stopLab_irs` (the labels appended are `stopLabs`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## The program -/

/-- Append the labels of an anchored auxiliary record (`kqX` = its address). -/
def anchL : Stmt :=
  .seq (block [.constN kqA 1, .addN kqX kqX K1, .loadN kqY kqX])
    (.ifLtN K0 kqY
      (.seq (block [.addN kqX kqX K1, .loadN kqV kqX]) (.seq (addLab kqN kqL kqV)
        (.ifLtN K1 kqY (.seq (block [.addN kqX kqX K1, .loadN kqV kqX]) (addLab kqN kqL kqV))
          .skip)))
      .skip)

/-- **The labels of the stop `sP`** (if its auxiliary record is anchored). -/
def stopLab : Stmt := .seq (block ldAuxL) (kqIsOne kqV anchL)

/-- The registers of the label step. -/
def KStR (q : ℕ) : Prop := q = kqA ∨ q = kqX ∨ q = kqV ∨ q = kqY ∨ LblR kqN kqL q

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem kqLblOf_eq {c c' : Config} {N L : ℕ} (h : ∀ q, LblR N L q → c'.nreg q = c.nreg q) :
    lblOf c' N L = lblOf c N L := by
  unfold lblOf
  Ξ h N (Or.inl rfl)
  apply List.map_congr_left
  intro i hi
  Ξ' List.mem_range at hi
  exact h _ (Or.inr ⟨⋄, ⋄⟩)

theorem kqAddLs_nil (l : List ℕ) : addLs l [] = l := rfl

theorem kqAddLs_append (l a b : List ℕ) : addLs l (a ++ b) = addLs (addLs l a) b := by
  unfold addLs; Ξ List.foldl_append

theorem addLabK_irs (hI : IInv W c₀ c) (hK : Consts c) (hN : c.nreg kqN ≤ 4) (hW : 4 ≤ W) :
    IRS P W c₀ (addLab kqN kqL kqV) c 30 (fun c' => c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addL (lblOf c kqN kqL) (c.nreg kqV) ∧
      (∀ q, ¬ LblR kqN kqL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) :=
  addLab_irs hI hK (iscr_sw' (⊛) (⊛))
    (fun i hi => iscr_sw (by unfold kqL sw; omega) (by unfold kqL sw; omega))
    (fun i hi => by unfold kqN kqL sw; omega) (by kqr) (fun i hi => by unfold kqV kqL sw; omega)
    (by rintro k (rfl | rfl | rfl | rfl) <;> unfold LblR <;> kqr) hN hW

theorem anchHead_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hW : c.nreg kqX + 1 ≤ W) :
    IRS P W c₀ (block [.constN kqA 1, .addN kqX kqX K1, .loadN kqY kqX]) c 3 (fun c' =>
      c'.nreg kqA = 1 ∧ c'.nreg kqX = c.nreg kqX + 1 ∧ c'.nreg kqY = c.nmem (c.nreg kqX + 1) ∧
      (∀ q, q ≠ kqA → q ≠ kqX → q ≠ kqY → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  ϴ' sw, K1, kqX, Nat.reduceAdd at hK1 hW
  refine (IRS.block _ hI ?_).mono le_rfl ?_
  · Θ okB, okI, regI, upd, kqX, kqA, kqY, K1, sw, IScr, hK1
    omega
  · rintro c' rfl
    Θ regB, regI, upd, kqX, kqA, kqY, K1, sw, hK1
    intro r ha hb hc
    Θ ha, hb, hc

set_option maxHeartbeats 8000000 in
/-- **The labels of an anchored record.** -/
theorem anchL_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hN : c.nreg kqN ≤ 4)
    (hW : c.nreg kqX + 3 ≤ W) (hW4 : 4 ≤ W) :
    IRS P W c₀ anchL c 75 (fun c' =>
      c'.nreg kqA = 1 ∧ c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addLs (lblOf c kqN kqL)
        ((List.range (min (c.nmem (c.nreg kqX + 1)) 2)).map fun t => c.nmem (c.nreg kqX + 2 + t)) ∧
      (∀ q, ¬ KStR q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hK := hK₀.fix hI
  unfold anchL
  refine IRS.seq (K₁ := 3) (K₂ := 72) (anchHead_irs hI hK.2.1 (by omega)) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4, a5⟩
  have hK₁ := hK₀.fix hI₁
  have nA : ∀ q, ¬ KStR q → q ≠ kqA ∧ q ≠ kqX ∧ q ≠ kqY := fun q hq =>
    ⟨fun h => hq (Or.inl h), fun h => hq (Or.inr (Or.inl h)), fun h => hq (Or.inr (Or.inr (Or.inr
      (Or.inl h))))⟩
  have nL : ∀ q, LblR kqN kqL q → q ≠ kqA ∧ q ≠ kqX ∧ q ≠ kqY ∧ q ≠ kqV := fun q hq => by
    simp only [LblR, kqN, kqL, sw] at hq; refine ⟨?_, ?_, ?_, ?_⟩ <;> kqr
  have lb1 : lblOf c₁ kqN kqL = lblOf c kqN kqL := kqLblOf_eq fun q hq =>
    a4 q (nL q hq).1 (nL q hq).2.1 (nL q hq).2.2.1
  have eN1 : c₁.nreg kqN = c.nreg kqN := a4 _ (by kqr) (by kqr) (by kqr)
  set m := c.nmem with hm
  set x := c.nreg kqX with hx
  by_cases h0 : c₁.nreg K0 < c₁.nreg kqY
  · rw [hK₁.1, a3] at h0
    refine IRS.mono (K := 66 + 2) (IRS.ifT (by rw [hK₁.1, a3]; exact h0) ?_) (by norm_num)
      (fun _ h => h)
    refine IRS.seq (K₁ := 2) (K₂ := 64) (ldNext_irs (Or.inl rfl) hI₁ hK₁.2.1 (by omega)) ?_
    rintro c₂ hI₂ - - ⟨b1, b2, b3, b4⟩
    have hK₂ := hK₀.fix hI₂
    have eN2 : c₂.nreg kqN = c.nreg kqN := (b3 _ (by kqr) (by kqr)).trans eN1
    have lb2 : lblOf c₂ kqN kqL = lblOf c kqN kqL := (kqLblOf_eq fun q hq =>
      b3 q (nL q hq).2.1 (nL q hq).2.2.2).trans lb1
    rw [a5, a2] at b2
    refine IRS.seq (K₁ := 30) (K₂ := 34) (addLabK_irs hI₂ hK₂ (by omega) hW4) ?_
    rintro c₃ hI₃ - - ⟨d1, d2, d3, d4⟩
    rw [lb2, b2] at d2
    have hK₃ := hK₀.fix hI₃
    have eY3 : c₃.nreg kqY = m (x + 1) := by
      rw [d3 _ (by unfold LblR; kqr), b3 _ (by kqr) (by kqr), a3]
    have eX3 : c₃.nreg kqX = x + 2 := by rw [d3 _ (by unfold LblR; kqr), b1, a2]
    have eA3 : c₃.nreg kqA = 1 := by
      rw [d3 _ (by unfold LblR; kqr), b3 _ (by kqr) (by kqr), a1]
    have fr3 : ∀ q, ¬ KStR q → c₃.nreg q = c.nreg q := fun q hq => by
      rw [d3 q (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inr h))))),
        b3 q (nA q hq).2.1 (fun h => hq (Or.inr (Or.inr (Or.inl h)))),
        a4 q (nA q hq).1 (nA q hq).2.1 (nA q hq).2.2]
    have mem3 : c₃.nmem = m := by rw [d4, b4, a5]
    by_cases h1 : c₃.nreg K1 < c₃.nreg kqY
    · rw [hK₃.2.1, eY3] at h1
      refine IRS.mono (K := 32 + 2) (IRS.ifT (by rw [hK₃.2.1, eY3]; exact h1) ?_) le_rfl
        (fun _ h => h)
      refine IRS.seq (K₁ := 2) (K₂ := 30) (ldNext_irs (Or.inl rfl) hI₃ hK₃.2.1 (by omega)) ?_
      rintro c₄ hI₄ - - ⟨e1, e2, e3, e4⟩
      have lb4 : lblOf c₄ kqN kqL = lblOf c₃ kqN kqL := kqLblOf_eq fun q hq =>
        e3 q (nL q hq).2.1 (nL q hq).2.2.2
      have eN4 : c₄.nreg kqN = c₃.nreg kqN := e3 _ (by kqr) (by kqr)
      rw [mem3, eX3] at e2
      refine (addLabK_irs hI₄ (hK₀.fix hI₄) (by omega) hW4).mono le_rfl ?_
      rintro c' ⟨f1, f2, f3, f4⟩
      refine ⟨by rw [f3 _ (by unfold LblR; kqr), e3 _ (by kqr) (by kqr), eA3], f1, ?_,
        fun q hq => ?_, by rw [f4, e4, mem3]⟩
      · rw [f2, lb4, d2, e2, show min (m (x + 1)) 2 = 2 by omega]
        simp [addLs, List.range_succ]
      · rw [f3 q (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inr h))))),
          e3 q (nA q hq).2.1 (fun h => hq (Or.inr (Or.inr (Or.inl h)))), fr3 q hq]
    · rw [hK₃.2.1, eY3] at h1
      refine IRS.mono (K := 0 + 2) (IRS.ifF (by rw [hK₃.2.1, eY3]; exact h1) (IRS.skip hI₃ rfl))
        (by norm_num) ?_
      rintro c' rfl
      refine ⟨eA3, d1, ?_, fr3, mem3⟩
      rw [d2, show min (m (x + 1)) 2 = 1 by omega]
      simp [addLs]
  · rw [hK₁.1, a3] at h0
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by rw [hK₁.1, a3]; exact h0) (IRS.skip hI₁ rfl))
      (by norm_num) ?_
    rintro c' rfl
    refine ⟨a1, by rw [eN1]; exact hN, ?_, fun q hq => a4 q (nA q hq).1 (nA q hq).2.1 (nA q hq).2.2,
      a5⟩
    rw [lb1, show min (m (x + 1)) 2 = 0 by omega]
    simp [addLs]

set_option maxHeartbeats 8000000 in
/-- **The labels of the stop `sP`.** -/
theorem stopLab_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hN : c.nreg kqN ≤ 4)
    (hW : c.nreg aB + 5 * c.nreg sP + 3 ≤ W) (hW4 : 4 ≤ W) :
    IRS P W c₀ stopLab c 84 (fun c' =>
      (∀ q, ¬ KStR q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem ∧ c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addLs (lblOf c kqN kqL) (stopLabs c.nmem (c.nreg aB) (c.nreg sP)) ∧
      (c.nmem (c.nreg aB + 5 * c.nreg sP) = 1 → c'.nreg kqA = 1) ∧
      (c.nmem (c.nreg aB + 5 * c.nreg sP) ≠ 1 → c'.nreg kqA = c.nreg kqA)) := by
  unfold stopLab
  refine IRS.seq (K₁ := 5) (K₂ := 79) (ldAux_irs hI (by omega)) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4⟩
  have hK₁ := hK₀.fix hI₁
  have nL : ∀ q, LblR kqN kqL q → q ≠ kqX ∧ q ≠ kqV := fun q hq => by
    simp only [LblR, kqN, kqL, sw] at hq; refine ⟨?_, ?_⟩ <;> kqr
  have lb1 : lblOf c₁ kqN kqL = lblOf c kqN kqL := kqLblOf_eq fun q hq =>
    a3 q (nL q hq).1 (nL q hq).2
  have fr1 : ∀ q, ¬ KStR q → c₁.nreg q = c.nreg q := fun q hq =>
    a3 q (fun h => hq (Or.inr (Or.inl h))) (fun h => hq (Or.inr (Or.inr (Or.inl h))))
  have eN1 : c₁.nreg kqN = c.nreg kqN := a3 _ (by kqr) (by kqr)
  have eA1 : c₁.nreg kqA = c.nreg kqA := a3 _ (by kqr) (by kqr)
  refine kqIsOne_irs (K := 75) hI₁ hK₁ (fun h1 => ?_) (fun h1 => ?_)
  · rw [a2] at h1
    refine (anchL_irs hI₁ hK₀ (by omega) (by omega) hW4).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3, b4, b5⟩
    refine ⟨fun q hq => (b4 q hq).trans (fr1 q hq), by rw [b5, a4], b2, ?_, fun _ => b1,
      fun h => absurd h1 h⟩
    rw [b3, lb1, a1, a4]
    unfold stopLabs
    rw [ite_eq_left h1]
  · rw [a2] at h1
    refine ⟨fr1, a4, by omega, ?_, fun h => absurd h h1, fun _ => eA1⟩
    rw [lb1]
    unfold stopLabs
    rw [ite_eq_right h1, kqAddLs_nil]

end

end SweepEv

end Chazelle.Core
