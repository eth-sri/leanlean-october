module

public meta import Chazelle.Arithmetic

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
  rw [h N (Or.inl rfl)]
  apply List.map_congr_left
  ram_grind

theorem kqAddLs_nil (l : List ℕ) : addLs l [] = l := rfl

theorem kqAddLs_append (l a b : List ℕ) : addLs l (a ++ b) = addLs (addLs l a) b := by
  core_grind

section
variable (hI : IInv W c₀ c)
include hI
theorem addLabK_irs (hK : Consts c) (hN : c.nreg kqN ≤ 4) (hW : 4 ≤ W) :
    IRS P W c₀ (addLab kqN kqL kqV) c 30 (fun c' => c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addL (lblOf c kqN kqL) (c.nreg kqV) ∧
      (∀ q, ¬ LblR kqN kqL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) :=
  addLab_irs hI hK (iscr_sw' (by norm_num) (by norm_num))
    (fun i hi => iscr_sw (by omega_nf) (by omega_nf))
    (fun i hi => by omega_nf) (by kqr) (fun i hi => by omega_nf)
    (by omega_nf) hN hW

theorem anchHead_irs (hK1 : c.nreg K1 = 1) (hW : c.nreg kqX + 1 ≤ W) :
    IRS P W c₀ (block [.constN kqA 1, .addN kqX kqX K1, .loadN kqY kqX]) c 3 (fun c' =>
      c'.nreg kqA = 1 ∧ c'.nreg kqX = c.nreg kqX + 1 ∧ c'.nreg kqY = c.nmem (c.nreg kqX + 1) ∧
      (∀ q, q ≠ kqA → q ≠ kqX → q ≠ kqY → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, K1, kqX, Nat.reduceAdd] at hK1 hW
  refine (IRS.block _ hI ?_).mono le_rfl ?_
  all_goals (simp_all [okB, okI, regI, upd, kqX, kqA, kqY, K1, sw, IScr, regB] <;> omega_nf)


end

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
    ram_grind
  have lb1 : lblOf c₁ kqN kqL = lblOf c kqN kqL := kqLblOf_eq fun q hq =>
    a4 q (nL q hq).1 (nL q hq).2.1 (nL q hq).2.2.1
  have eN1 : c₁.nreg kqN = c.nreg kqN := a4 _ (by kqr) (by kqr) (by kqr)
  set m := c.nmem with hm
  set x := c.nreg kqX with hx
  by_cases h0 : c₁.nreg K0 < c₁.nreg kqY
  · rw [hK₁.1, a3] at h0
    refine IRS.mono (K := 66 + 2) (IRS.ifT (by ram_grind) ?_) (by norm_num)
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
      rw [d3 _ (by omega_nf), b3 _ (by kqr) (by kqr), a3]
    have eX3 : c₃.nreg kqX = x + 2 := by ram_grind
    have eA3 : c₃.nreg kqA = 1 := by
      rw [d3 _ (by omega_nf), b3 _ (by kqr) (by kqr), a1]
    have fr3 : ∀ q, ¬ KStR q → c₃.nreg q = c.nreg q := fun q hq => by
      ram_grind
    have mem3 : c₃.nmem = m := by ram_grind
    by_cases h1 : c₃.nreg K1 < c₃.nreg kqY
    · rw [hK₃.2.1, eY3] at h1
      refine IRS.mono (K := 32 + 2) (IRS.ifT (by ram_grind) ?_) le_rfl
        (fun _ h => h)
      refine IRS.seq (K₁ := 2) (K₂ := 30) (ldNext_irs (Or.inl rfl) hI₃ hK₃.2.1 (by omega)) ?_
      rintro c₄ hI₄ - - ⟨e1, e2, e3, e4⟩
      have lb4 : lblOf c₄ kqN kqL = lblOf c₃ kqN kqL := kqLblOf_eq fun q hq =>
        e3 q (nL q hq).2.1 (nL q hq).2.2.2
      have eN4 : c₄.nreg kqN = c₃.nreg kqN := e3 _ (by kqr) (by kqr)
      rw [mem3, eX3] at e2
      refine (addLabK_irs hI₄ (hK₀.fix hI₄) (by omega) hW4).mono le_rfl ?_
      rintro c' ⟨f1, f2, f3, f4⟩
      refine ⟨by rw [f3 _ (by omega_nf), e3 _ (by kqr) (by kqr), eA3], f1, ?_,
        fun q hq => ?_, by ram_grind⟩
      · grind [addLs, List.range_succ]
      · rw [f3 q (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inr h))))),
          e3 q (nA q hq).2.1 (fun h => hq (Or.inr (Or.inr (Or.inl h)))), fr3 q hq]
    · rw [hK₃.2.1, eY3] at h1
      refine IRS.mono (K := 0 + 2) (IRS.ifF (by ram_grind) (IRS.skip hI₃ rfl))
        (by norm_num) ?_
      grind [addLs]
  · rw [hK₁.1, a3] at h0
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by omega) (IRS.skip hI₁ rfl))
      (by norm_num) ?_
    grind [addLs]

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
    omega_nf
  have lb1 : lblOf c₁ kqN kqL = lblOf c kqN kqL := kqLblOf_eq fun q hq =>
    a3 q (nL q hq).1 (nL q hq).2
  have fr1 : ∀ q, ¬ KStR q → c₁.nreg q = c.nreg q := fun q hq =>
    a3 q (fun h => hq (Or.inr (Or.inl h))) (fun h => hq (Or.inr (Or.inr (Or.inl h))))
  have eN1 : c₁.nreg kqN = c.nreg kqN := a3 _ (by kqr) (by kqr)
  have eA1 : c₁.nreg kqA = c.nreg kqA := a3 _ (by kqr) (by kqr)
  refine kqIsOne_irs (K := 75) hI₁ hK₁ (fun h1 => ?_) (fun h1 => ?_)
  · rw [a2] at h1
    grind [Chazelle.Core.SweepEv.anchL_irs, stopLabs]
  simp_all [stopLabs, kqAddLs_nil] 

end

end SweepEv

end Chazelle.Core
