module

public import Chazelle.Core.SweepIoSpec2
public import Chazelle.Core.SweepIoCand1E

/-!
# The sweep RAM (WP-D), answers: pieces of the per-query pipeline

* `query_facts`: the class, height and location facts of a query point;
* `convL_val`, `convR_val`: the conversion of a position of the model of `C₁` / `C₂` to the walk
  of `C` with the stage-0 constants;
* `hitParam_le_of_onCB`, `winner_eq`: the winner of a complete accumulator is the first hit;
* `winQ`, `winQ_irs`: the winner converted to the walk of `C` (by its tag and the bits);
* `AEnv.ctxW`, `AEnv.ctxL`, `AEnv.ctxR`: the chain contexts at `sw 2`, `sw 20`, `sw 21`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem sideChain_cases (J : Merge.Junction) {i : ℕ} (hi : i ≤ 1) :
    (i = 0 ∧ sideChain J i = J.left) ∨ (i = 1 ∧ sideChain J i = J.right) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · left; exact ⟨rfl, by simp [sideChain]⟩
  · right; exact ⟨rfl, by simp [sideChain]⟩

theorem sideChain_P (J : Merge.Junction) (i : ℕ) : (sideChain J i).P = J.P := by
  unfold sideChain; split_ifs <;> rfl

theorem sideChain_radius (J : Merge.Junction) (i : ℕ) :
    (sideChain J i).radius = J.whole.radius := FuseMath.radius_of_P J (sideChain_P J i)

theorem sideChain_set (J : Merge.Junction) (i : ℕ) : (sideChain J i).set ⊆ J.whole.set := by
  unfold sideChain; split_ifs
  · exact J.left_set_subset
  · exact J.right_set_subset

theorem sideChain_top (J : Merge.Junction) (i : ℕ) : (sideChain J i).top.2 ≤ J.whole.top.2 := by
  unfold sideChain; split_ifs
  · exact J.left_top_le
  · exact J.right_top_le

/-- **The facts of a query point.** -/
theorem query_facts (J : Merge.Junction) {Q : Polygon} {i : ℕ} {q : ℕ × ℕ × ℕ}
    (hq : QueryOK J Q i q) :
    PosClass (sideChain J i) Q ⟨q.1, q.2.1⟩ ∧
    |((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2| < J.whole.radius ∧
    ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2 ≤ (sideChain J i).top.2 ∧
    ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2 ≤ J.whole.top.2 ∧
    ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩ ∈ J.whole.set ∨
      (|((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).1| = J.whole.radius ∧
        |((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2| < J.whole.radius)) := by
  obtain ⟨he, -, -, h0, h1, htop, hsec⟩ := hq
  have hσ := Sweep.dirOf_cases q.2.2
  have hsec' : sideLeft (chainModel (sideChain J i)).W q.1
      ((chainModel (sideChain J i)).param Q ⟨q.1, q.2.1⟩)
      (rayPt ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩) (dirOf q.2.2) 1) := by
    rw [show rayPt ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩) (dirOf q.2.2) 1 =
      (((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).1 + dirOf q.2.2,
        ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2) by
      unfold rayPt; rw [mul_one]]
    exact hsec
  have hy := query_abs (C := sideChain J i) (x := ⟨q.1, q.2.1⟩) he h0 h1 htop hσ hsec'
  have hR := sideChain_radius J i
  have hcls := posClass_of (C := sideChain J i) (x := ⟨q.1, q.2.1⟩) he h0 h1 hy (Or.inl htop)
  refine ⟨hcls, hR ▸ hy, htop, htop.trans (sideChain_top J i), ?_⟩
  rcases posClass_pt hcls h0 h1 hy with h | ⟨h, h'⟩
  · exact Or.inl (sideChain_set J i h)
  · exact Or.inr ⟨hR ▸ h, hR ▸ h'⟩

/-- **The conversion of a position of the model of `C₁`** with the stage-0 constants. -/
theorem convL_val {P : Polygon} {c : Config} {H : Host} {J : Merge.Junction}
    (hst : SweepEv.St0S P c H J) (hP : J.P.Simple) {Q : Polygon} {e h : ℕ}
    (hv : PosClass J.left Q ⟨e, h⟩) :
    convVal (c.nreg (sw 45)) (c.nreg (sw 45 + 1)) (c.nreg (sw 45 + 2)) (c.nreg (sw 45 + 4))
        (c.nreg (sw 33)) (c.nreg (sw 35)) e < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param Q ⟨convVal (c.nreg (sw 45)) (c.nreg (sw 45 + 1))
        (c.nreg (sw 45 + 2)) (c.nreg (sw 45 + 4)) (c.nreg (sw 33)) (c.nreg (sw 35)) e, h⟩ =
        (chainModel J.left).param Q ⟨e, h⟩ ∧
      (chainModel J.whole).pos Q ⟨convVal (c.nreg (sw 45)) (c.nreg (sw 45 + 1))
        (c.nreg (sw 45 + 2)) (c.nreg (sw 45 + 4)) (c.nreg (sw 33)) (c.nreg (sw 35)) e, h⟩ =
        (chainModel J.left).pos Q ⟨e, h⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, h33, -, h35, -⟩ := hst
  have e0 : c.nreg (sw 45) = 6 + tpos J.whole (J.m₁ + 2 * J.m₂) := by
    rw [show sw 45 = sw (45 + 0) from rfl, h45 0 (by norm_num)]; rfl
  have e1 : c.nreg (sw 45 + 1) = 6 + tpos J.left J.m₁ := by
    rw [show sw 45 + 1 = sw (45 + 1) from rfl, h45 1 (by norm_num)]; rfl
  have e2 : c.nreg (sw 45 + 2) = Sweep.lL1 J := by
    rw [show sw 45 + 2 = sw (45 + 2) from rfl, h45 2 (by norm_num)]; rfl
  have e4 : c.nreg (sw 45 + 4) = Sweep.lδ J := by
    rw [show sw 45 + 4 = sw (45 + 4) from rfl, h45 4 (by norm_num)]; rfl
  have en : c.nreg (sw 33) = (chainModel J.left).W.n := by rw [h33, cm_n]
  have en' : c.nreg (sw 35) = (chainModel J.whole).W.n := by rw [h35, cm_n]
  rw [e0, e1, e2, e4, en, en']
  exact conv_pos (sideConvL J hP) Q hv

/-- **The conversion of a position of the model of `C₂`** with the stage-0 constants. -/
theorem convR_val {P : Polygon} {c : Config} {H : Host} {J : Merge.Junction}
    (hst : SweepEv.St0S P c H J) (hP : J.P.Simple) {Q : Polygon} {e h : ℕ}
    (hv : PosClass J.right Q ⟨e, h⟩) :
    convVal (c.nreg (sw 40)) (c.nreg (sw 40 + 1)) (c.nreg (sw 40 + 2)) (c.nreg (sw 40 + 4))
        (c.nreg (sw 34)) (c.nreg (sw 35)) e < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param Q ⟨convVal (c.nreg (sw 40)) (c.nreg (sw 40 + 1))
        (c.nreg (sw 40 + 2)) (c.nreg (sw 40 + 4)) (c.nreg (sw 34)) (c.nreg (sw 35)) e, h⟩ =
        (chainModel J.right).param Q ⟨e, h⟩ ∧
      (chainModel J.whole).pos Q ⟨convVal (c.nreg (sw 40)) (c.nreg (sw 40 + 1))
        (c.nreg (sw 40 + 2)) (c.nreg (sw 40 + 4)) (c.nreg (sw 34)) (c.nreg (sw 35)) e, h⟩ =
        (chainModel J.right).pos Q ⟨e, h⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, h35, -⟩ := hst
  have e0 : c.nreg (sw 40) = 6 + tpos J.whole J.m₁ := by
    rw [show sw 40 = sw (40 + 0) from rfl, h40 0 (by norm_num)]; rfl
  have e1 : c.nreg (sw 40 + 1) = 6 + tpos J.right 0 := by
    rw [show sw 40 + 1 = sw (40 + 1) from rfl, h40 1 (by norm_num)]; rfl
  have e2 : c.nreg (sw 40 + 2) = Sweep.rL1 J := by
    rw [show sw 40 + 2 = sw (40 + 2) from rfl, h40 2 (by norm_num)]; rfl
  have e4 : c.nreg (sw 40 + 4) = Sweep.rδ J := by
    rw [show sw 40 + 4 = sw (40 + 4) from rfl, h40 4 (by norm_num)]; rfl
  have en : c.nreg (sw 34) = (chainModel J.right).W.n := by rw [h34, cm_n]
  have en' : c.nreg (sw 35) = (chainModel J.whole).W.n := by rw [h35, cm_n]
  rw [e0, e1, e2, e4, en, en']
  exact conv_pos (sideConvR J hP) Q hv

/-- A candidate on the chain or the box is not before the first hit. -/
theorem hitParam_le_of_onCB (C : Chain) {z : Point} {σ τ : ℝ} (hτ : 0 < τ)
    (h : OnCB C (rayPt z σ τ)) : C.hitParam z σ ≤ τ := by
  refine csInf_le (C.hitSet_bddBelow z σ) ⟨hτ, fun hd => ?_⟩
  obtain ⟨hb, hno⟩ := hd
  rcases h with h | h | h
  · exact hno (Or.inl h)
  · exact absurd h (ne_of_lt hb.1)
  · exact absurd h (ne_of_lt hb.2)

/-- **The winner of the accumulator is the first hit.** -/
theorem winner_eq {P : Polygon} {A : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {J : Merge.Junction}
    {z : Point} {σ : ℝ} {L : Set ℝ} {c : Config} (hacc : AccOK P A Mod R₀ z σ L c)
    (hgood : ∀ τ ∈ L, 0 < τ ∧ OnCB J.whole (rayPt z σ τ)) (hT : J.whole.hitParam z σ ∈ L) :
    c.nreg A = 1 ∧ c.nreg (A + 3) ≤ 2 ∧
      ProperPos (chainModel (Mod (c.nreg (A + 3)))) (Qof P) P.n ⟨c.nreg (A + 1), c.nreg (A + 2)⟩ ∧
      c.nreg (A + 1) < (chainModel (Mod (c.nreg (A + 3)))).W.n ∧
      (chainModel (Mod (c.nreg (A + 3)))).pos (Qof P) ⟨c.nreg (A + 1), c.nreg (A + 2)⟩ =
        rayPt z σ (J.whole.hitParam z σ) := by
  obtain ⟨hle, h0, h1⟩ := hacc
  have hA : c.nreg A = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · have := h0 h; rw [this] at hT; exact absurd hT (Set.notMem_empty _)
    · exact h
  obtain ⟨τ, hτ, hmin, ht, hpp, he, hpos, -⟩ := h1 hA
  have e : τ = J.whole.hitParam z σ :=
    le_antisymm (hmin _ hT) (hitParam_le_of_onCB J.whole (hgood τ hτ).1 (hgood τ hτ).2)
  rw [e] at hpos
  exact ⟨hA, ht, hpp, he, hpos⟩

/-! ## The winner in the walk of `C` -/

/-- Copy the winner's edge. -/
def cpW : Stmt := .instr (.copyN yE (accA + 1))

/-- **The winner, converted to the walk of `C`** (by its tag and the bits). -/
def winQ : Stmt :=
  .seq (.ifLtN (accA + 3) K1
      (.ifLtN bL K1 cpW (convS (sw 45) (sw 33) (accA + 1) yE))
      (.ifLtN (accA + 3) K2
        (.ifLtN bR K1 cpW (convS (sw 40) (sw 34) (accA + 1) yE))
        cpW))
    (.instr (.copyN yH (accA + 2)))

/-- The converted edge of the winner. -/
def winVal (c : Config) : ℕ :=
  if c.nreg (accA + 3) = 0 ∧ c.nreg bL = 1 then
    convVal (c.nreg (sw 45)) (c.nreg (sw 45 + 1)) (c.nreg (sw 45 + 2)) (c.nreg (sw 45 + 4))
      (c.nreg (sw 33)) (c.nreg (sw 35)) (c.nreg (accA + 1))
  else if c.nreg (accA + 3) = 1 ∧ c.nreg bR = 1 then
    convVal (c.nreg (sw 40)) (c.nreg (sw 40 + 1)) (c.nreg (sw 40 + 2)) (c.nreg (sw 40 + 4))
      (c.nreg (sw 34)) (c.nreg (sw 35)) (c.nreg (accA + 1))
  else c.nreg (accA + 1)

set_option maxHeartbeats 4000000 in
theorem winQ_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hb : c.nreg bL ≤ 1 ∧ c.nreg bR ≤ 1)
    (hl : c.nreg (accA + 3) = 0 → c.nreg bL = 1 → c.nreg (accA + 1) < c.nreg (sw 33) ∧
      c.nreg (sw 45 + 1) < c.nreg (sw 33) ∧ c.nreg (sw 33) ≤ W ∧
      c.nreg (sw 45) < c.nreg (sw 35) ∧ c.nreg (sw 35) ≤ W)
    (hr : c.nreg (accA + 3) = 1 → c.nreg bR = 1 → c.nreg (accA + 1) < c.nreg (sw 34) ∧
      c.nreg (sw 40 + 1) < c.nreg (sw 34) ∧ c.nreg (sw 34) ≤ W ∧
      c.nreg (sw 40) < c.nreg (sw 35) ∧ c.nreg (sw 35) ≤ W) :
    IRS P W c₀ winQ c 30 (fun c' => c'.nreg yE = winVal c ∧ c'.nreg yH = c.nreg (accA + 2) ∧
      (∀ r, r ≠ yE → r ≠ yH → r ≠ cX → r ≠ cT → r ≠ cDd → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have k2 : c.nreg K2 = 2 := hKc.2.2.2.2.2.1
  have syE : IScr yE := iscr_sw (by unfold yE sw; norm_num) (by unfold yE sw; norm_num)
  have syH : IScr yH := iscr_sw (by unfold yH sw; norm_num) (by unfold yH sw; norm_num)
  have hyX : yE ≠ cX ∧ yE ≠ cT ∧ yE ≠ cDd := by unfold yE cX cT cDd sw; omega
  have hpe : accA + 1 ≠ cX ∧ accA + 1 ≠ cT ∧ accA + 1 ≠ cDd := by unfold accA cX cT cDd sw; omega
  -- the copy branch
  have cp : IRS P W c₀ cpW c 1 (fun c₁ => c₁.nreg yE = c.nreg (accA + 1) ∧
      (∀ r, r ≠ yE → r ≠ cX → r ≠ cT → r ≠ cDd → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    refine (IRS.instr1 (i := .copyN yE (accA + 1)) hI syE).mono le_rfl ?_
    rintro c' rfl
    refine ⟨?_, fun r h1 _ _ _ => ?_, rfl⟩
    · show upd c.nreg yE (c.nreg (accA + 1)) yE = _; rw [upd_same]
    · show upd c.nreg yE (c.nreg (accA + 1)) r = _; rw [upd_other _ _ _ h1]
  have st1 : IRS P W c₀ (.ifLtN (accA + 3) K1
      (.ifLtN bL K1 cpW (convS (sw 45) (sw 33) (accA + 1) yE))
      (.ifLtN (accA + 3) K2
        (.ifLtN bR K1 cpW (convS (sw 40) (sw 34) (accA + 1) yE))
        cpW)) c 28 (fun c₁ => c₁.nreg yE = winVal c ∧
      (∀ r, r ≠ yE → r ≠ cX → r ≠ cT → r ≠ cDd → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem) := by
    by_cases t0 : c.nreg (accA + 3) < c.nreg K1
    · have t0' : c.nreg (accA + 3) = 0 := by omega
      refine IRS.mono (K := 28) (IRS.ifT t0 ?_) le_rfl (fun _ h => h)
      by_cases b0 : c.nreg bL < c.nreg K1
      · refine (IRS.ifT b0 cp).mono (by norm_num) ?_
        rintro c₁ ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rw [h1]; unfold winVal; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · have b1 : c.nreg bL = 1 := by omega
        obtain ⟨a1, a2, a3, a4, a5⟩ := hl t0' b1
        refine (IRS.ifF b0 (convS_irs (Or.inr rfl) (Or.inl rfl) hpe ⟨syE, hyX⟩ hI hK a1 a2 a3
          a4 a5)).mono (by norm_num) ?_
        rintro c₁ ⟨h1, h2, h3⟩
        refine ⟨?_, fun r r1 r2 r3 r4 => h2 r (by
          unfold CvSet; rintro (h | h | h | h) <;> simp_all), h3⟩
        rw [h1]; unfold winVal; rw [ite_eq_left ⟨t0', b1⟩]
    · refine IRS.mono (K := 28) (IRS.ifF t0 ?_) le_rfl (fun _ h => h)
      by_cases t1 : c.nreg (accA + 3) < c.nreg K2
      · have t1' : c.nreg (accA + 3) = 1 := by omega
        refine IRS.mono (K := 26) (IRS.ifT t1 ?_) le_rfl (fun _ h => h)
        by_cases b0 : c.nreg bR < c.nreg K1
        · refine (IRS.ifT b0 cp).mono (by norm_num) ?_
          rintro c₁ ⟨h1, h2, h3⟩
          refine ⟨?_, h2, h3⟩
          rw [h1]; unfold winVal; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        · have b1 : c.nreg bR = 1 := by omega
          obtain ⟨a1, a2, a3, a4, a5⟩ := hr t1' b1
          refine (IRS.ifF b0 (convS_irs (Or.inl rfl) (Or.inr rfl) hpe ⟨syE, hyX⟩ hI hK a1 a2 a3
            a4 a5)).mono (by norm_num) ?_
          rintro c₁ ⟨h1, h2, h3⟩
          refine ⟨?_, fun r r1 r2 r3 r4 => h2 r (by
            unfold CvSet; rintro (h | h | h | h) <;> simp_all), h3⟩
          rw [h1]; unfold winVal; rw [ite_eq_right (by omega), ite_eq_left ⟨t1', b1⟩]
      · refine (IRS.ifF t1 cp).mono (by norm_num) ?_
        rintro c₁ ⟨h1, h2, h3⟩
        refine ⟨?_, h2, h3⟩
        rw [h1]; unfold winVal; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  refine (IRS.seq (K₂ := 1) st1 ?_).mono (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨h1, h2, h3⟩
  refine (IRS.instr1 (i := .copyN yH (accA + 2)) hI₁ syH).mono le_rfl ?_
  rintro c' rfl
  refine ⟨?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, h3⟩
  · show upd c₁.nreg yH (c₁.nreg (accA + 2)) yE = _
    rw [upd_other _ _ _ (by unfold yE yH sw; norm_num), h1]
  · show upd c₁.nreg yH (c₁.nreg (accA + 2)) yH = _
    rw [upd_same, h2 _ (by unfold yE accA sw; norm_num) (by unfold cX accA sw; norm_num)
      (by unfold cT accA sw; norm_num) (by unfold cDd accA sw; norm_num)]
  · show upd c₁.nreg yH (c₁.nreg (accA + 2)) r = _
    rw [upd_other _ _ _ r2, h2 r r1 r3 r4 r5]

/-! ## The chain contexts of the answer phase -/

end

end SweepIo

end Chazelle.Core
