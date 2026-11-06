module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoCand1P

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the branches

From the state `Mid` after the local hit in the model of `C₂`, the branches of the classes to the
output (`CandOut`, `CandFr`):

* `boxB_irs`: box wall (the local hit at the box twin in the model of `C₁` if `bL = 1`);
* `bruteB_irs`: brute force (`callSym` and `bruteS` if `bL = 1`), from `BruteBody`;
* `tab_irs`: a regular endpoint query, from `TabBody` (`TabStepSpec`);
* `shr_irs`: the shared vertex, from `ShrBody` (`ShrStepSpec`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

/-! ## The bodies of the contracts of the parts -/

/-- The body of `BruteSpec`. -/
def BruteBody (bruteS : Stmt → Stmt) (κB : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      SymPtIn c sO s → s.Lt P.n → s.eval (Qof P) = z → z ∉ J.left.set →
      |z.1| < J.whole.radius → |z.2| < J.whole.radius → z.2 ≤ J.left.top.2 → c.nreg bL = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ W →
      IRS P W c₀ (bruteS sh) c (κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.left (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            (FreeAt J.left z (dirOf (c.nreg qD)) →
              J.left.hitParam z (dirOf (c.nreg qD)) ∈ L')) ∧
          PartFr c c')

theorem bruteBody_of (h : BruteSpec) : ∃ bruteS κB, BruteBody bruteS κB := h

/-- The body of `TabStepSpec`. -/
def TabBody (tabB : Stmt) (κT : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ)
    (z : Point),
    AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
    c.nreg qJ < 2 * N₂.nChords → endOrigin J (Qof P) N₂ (c.nreg qJ) = z →
    endDir (c.nreg qJ) = dirOf (c.nreg qD) →
    z ∈ J.right.set → z ≠ J.shared → z ≠ J.right.top →
    AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
    c.nreg ALLOC + κT ≤ W →
    IRS P W c₀ tabB c κT
      (fun c' =>
        (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
            (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
          (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
          (J.whole.hitParam z (dirOf (c.nreg qD)) ∈ L' ∨
            J.whole.hitParam z (dirOf (c.nreg qD)) = J.right.hitParam z (dirOf (c.nreg qD)))) ∧
        CandFr c c')

theorem tabBody_of (h : TabStepSpec) : ∃ tabB κT, TabBody tabB κT := h

/-- The body of `ShrStepSpec`. -/
def ShrBody (shrB : Stmt → Stmt) (κS : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      1 ≤ c.nreg qH → c.nreg qH ≤ P.n → ((Qof P).vtx (c.nreg qH - 1)).2 = J.shared.2 →
      FreeAt J.whole J.shared (dirOf (c.nreg qD)) → c.nreg bL = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius J.shared
        (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + (κS + Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) ≤ W →
      IRS P W c₀ (shrB sh) c
        (κS + Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius J.shared
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.left (rayPt J.shared (dirOf (c.nreg qD)) τ))) ∧
            J.left.hitParam J.shared (dirOf (c.nreg qD)) ∈ L') ∧
          CandFr c c')

theorem shrBody_of (h : ShrStepSpec) : ∃ shrB κS, ShrBody shrB κS := h

/-! ## The branches -/

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}

/-- `bL = 1` from the run-time test. -/
theorem bL_one (hq : QState P J 1 z c) (hK : Consts c₂) (fr : CandFr c c₂)
    (hb : c₂.nreg K0 < c₂.nreg bL) : c.nreg bL = 1 := by
  have := hq.hbL.1; rw [hK.1, candFr_bL fr] at hb; omega

theorem bL_zero (hq : QState P J 1 z c) (hK : Consts c₂) (fr : CandFr c c₂)
    (hb : ¬ c₂.nreg K0 < c₂.nreg bL) : ¬ z.2 ≤ J.left.top.2 := fun h => by
  have := (hq.hbL.2).2 h; rw [hK.1, candFr_bL fr] at hb; omega

theorem modB_left {l r : ℕ} (h : l = 1) : ModB J l r 0 = J.left := ⊚ ModB, h

/-- **The box class.** -/
theorem boxB_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hbox : c.nreg qE = 1 ∨ c.nreg qE = 3)
    (hroom : c₂.nreg ALLOC + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (boxB sh) c₂ (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 2)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, -, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  have fr := hM.2.2.2
  have eE := candFr_qE fr
  have eH := candFr_qH fr
  have eD := candFr_qD fr
  have hK := hA.hK.fix hI₂
  unfold boxB
  refine IRS.ite (fun hb => ?_) (fun hb => ?_)
  · have hb1 := bL_one hq hK fr hb
    have h₁ : z.2 ≤ J.left.top.2 := (hq.hbL.2).1 hb1
    obtain ⟨hgL, hposL, hparL⟩ := lhGeo_boxL hbox hgeo (by rw [hzpos]; exact habs)
      (by rw [hzpos]; exact h₁)
    have h := lhsL_irs (e := qE) (t := 0) hsh hBs hXl hA (by unfold OutL qE sw; omega) hI₂
      (Mod := ModB J (c.nreg bL) (c.nreg bR)) (R₀ := J.whole.radius) (L := L) (z := z)
      (by rw [eE, cm_n]; rcases hbox with h | h <;> rw [h] <;> omega)
      (by rw [eE, eH]; unfold ProperPos; rw [hparL]; exact hpp)
      (Ρ eE, eH, hposL, hzpos)
      (by rw [show J.left.radius = J.right.radius from rfl]; exact habs)
      (Or.inl (by rw [eE]; exact hbox))
      (by rw [eD]; exact hM.1) (⊛) (modB_left hb1) rfl hroom
    refine h.mono le_rfl ?_
    rintro c' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
    rw [eD] at a' g' geo'
    rw [eE, eH] at geo'
    have hM' : Mid P J z c c' L' := mid_step hM a' s'
      (fun τ hτ => (g' τ hτ).imp_right (fun h => ⟨h.1, onCB_of_left J h.2⟩))
      (candFr_lhw fr' hA' hm')
    exact fin1 hq hM' (fun _ => geo' hgL)
  · have hb0 := bL_zero hq hK fr hb
    exact IRS.skip hI₂ (fin1 hq hM (fun h => absurd h hb0))

/-- **The brute-force class.** -/
theorem bruteB_irs {bruteS : Stmt → Stmt} {κB : ℕ} (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hnb : ¬ (c.nreg qE = 1 ∨ c.nreg qE = 3)) (hns : z ≠ J.shared)
    (hroom : c₂.nreg ALLOC + (16707 + κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1)) ≤ W) :
    IRS P W c₀ (bruteB bruteS sh) c₂
      (16707 + κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) + 2)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, hpc, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  obtain ⟨hzC, -, hcls⟩ := tour_set J.right (Qof P) hpc hnb hpp.1 hpp.2.1
  rw [hzpos] at hzC
  have fr := hM.2.2.2
  have eE := candFr_qE fr
  have eH := candFr_qH fr
  have eD := candFr_qD fr
  have hK := hA.hK.fix hI₂
  unfold bruteB
  refine IRS.ite (fun hb => ?_) (fun hb => ?_)
  · have hb1 := bL_one hq hK fr hb
    have h₁ : z.2 ≤ J.left.top.2 := (hq.hbL.2).1 hb1
    have hsym := callSym_irs (dsc := sw 21) (re := qE) (rh := qH) (o := sw 3230) hI₂
      (AEnv.ctxR hA hI₂) (by unfold qE qH sw; omega) (by unfold sw; omega)
      (by rw [eE]; exact hqE) (by rw [eE, eH]; exact hpp)
      (by rw [eE, eH, hzpos]; exact habs) (by rw [eE, eH]; exact hcls) (⋄)
    refine IRS.seq hsym ?_
    rintro c₃ hI₃ hA₃ hA₃' ⟨sp, hsp, hlt, hev, hfr3, hal3, hm3⟩
    have fr3 : CandFr c₂ c₃ := candFr_regs (S := fun r => sw 3230 ≤ r ∧ r ≤ sw 3233)
      (fun r h => by unfold Alw; unfold sw at h ⊢; omega)
      (fun r a b d => hfr3 r a (by unfold sw at b ⊢; omega) d) hal3 hm3
    have fr3' := candFr_trans fr fr3
    have eD3 := candFr_qD fr3'
    have eL3 := candFr_bL fr3'
    have eR3 := candFr_bR fr3'
    rw [eE, eH, hzpos] at hev
    have hacc3 : AccOK P accA (ModB J (c₃.nreg bL) (c₃.nreg bR)) J.whole.radius z
        (dirOf (c₃.nreg qD)) L c₃ := by
      Ξ eD3, eL3, eR3
      exact hM.1.transport (fun j hj => by
        rw [hfr3 _ (not_oracle_sw (by unfold accA sw; omega) (by unfold accA sw; omega))
          (by unfold accA sw; omega) (by unfold accA ALLOC sw; omega)])
    have hab := abs_lt_whole hzC
    have h := hBr sh Bs F X Ok hsh hBs hXl P W c₀ c₃ J H N₁ N₂ E L sp z hA hI₃
      (by rw [show sO = sw 3230 + 1 from rfl]; exact hsp) hlt hev (not_mem_left hA.hP hzC hns)
      hab.1 hab.2 h₁ (by rw [eL3]; exact hb1) hacc3 (⋄)
    refine h.mono le_rfl ?_
    rintro c' ⟨⟨L', a', s', g', geo'⟩, pf⟩
    rw [eD3, eL3, eR3] at a'
    rw [eD3] at g' geo'
    have hM' : Mid P J z c c' L' := mid_step hM a' s'
      (fun τ hτ => (g' τ hτ).imp_right (fun h => ⟨h.1, onCB_of_left J h.2⟩))
      (candFr_trans fr3 (candFr_part pf))
    exact fin1 hq hM' (fun _ => geo' (freeAt_left_of J h₁ hq.hfree))
  · have hb0 := bL_zero hq hK fr hb
    exact IRS.skip hI₂ (fin1 hq hM (fun h => absurd h hb0))

/-- **A regular endpoint query**: the table step. -/
theorem tab_irs {tabB : Stmt} {κT : ℕ} (hT : TabBody tabB κT)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hnb : ¬ (c.nreg qE = 1 ∨ c.nreg qE = 3))
    (hj : c.nreg qJ < 2 * N₂.nChords)
    (hend : (c.nreg qE, c.nreg qH, c.nreg qD) = (sweepEndQ N₂.chords).getD (c.nreg qJ) (0, 0, 0))
    (hns : z ≠ J.shared) (hnt : z ≠ J.right.top) (hroom : c₂.nreg ALLOC + κT ≤ W) :
    IRS P W c₀ tabB c₂ κT (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, hpc, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  obtain ⟨hzC, -, -⟩ := tour_set J.right (Qof P) hpc hnb hpp.1 hpp.2.1
  rw [hzpos] at hzC
  obtain ⟨ho, hd⟩ := endQ_facts hA.hNF₂ hj hend
  rw [hzpos] at ho
  have fr := hM.2.2.2
  have eJ := candFr_qJ fr
  have eD := candFr_qD fr
  have eL := candFr_bL fr
  have eR := candFr_bR fr
  have h := hT P W X Ok J H N₁ N₂ E c₀ c₂ L z hA hI₂ (by rw [eJ]; exact hj)
    (by rw [eJ]; exact ho.symm) (by rw [eJ, eD]; exact hd.symm) hzC hns hnt
    (by rw [eD, eL, eR]; exact hM.1) hroom
  refine h.mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', hh⟩, fr'⟩
  rw [eD, eL, eR] at a'
  rw [eD] at g' hh
  exact fin2 (mid_step hM a' s' g' fr') hh

/-- **The shared vertex.** -/
theorem shr_irs {shrB : Stmt → Stmt} {κS : ℕ} (hS : ShrBody shrB κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hzs : z = J.shared)
    (hroom : c₂.nreg ALLOC +
      (κS + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) ≤ W) :
    IRS P W c₀ (shrB sh) c₂ (κS + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, hpc, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  subst hzs
  have fr := hM.2.2.2
  have eH := candFr_qH fr
  have eD := candFr_qD fr
  have eL := candFr_bL fr
  have eR := candFr_bR fr
  have h₁ : J.shared.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set J.shared_mem_left
  have hb1 : c.nreg bL = 1 := (hq.hbL.2).2 h₁
  have h := hS sh Bs F X Ok hsh hBs hXl P W c₀ c₂ J H N₁ N₂ E L hA hI₂
    (by rw [eH]; exact h1H) (by rw [eH]; exact hHn) (by rw [eH]; exact hht)
    (by rw [eD]; exact hq.hfree) (by rw [eL]; exact hb1) (by rw [eD, eL, eR]; exact hM.1) hroom
  refine h.mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', hh⟩, fr'⟩
  rw [eD, eL, eR] at a'
  rw [eD] at g' hh
  have hM' : Mid P J J.shared c c' L' := mid_step hM a' s'
    (fun τ hτ => (g' τ hτ).imp_right (fun h => ⟨h.1, onCB_of_left J h.2⟩)) fr'
  exact fin1 hq hM' (fun _ => hh)

end Cand1

end

end SweepIo

end Chazelle.Core
