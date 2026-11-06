module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoCand1B

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, tour positions

The classification of a tour position (`tourB`): the copies and constants (`prepL`), the
normalised height code (`normS`), the top edge (`midB`), then the decision tree `genT` / `zeroT`
/ `topT` among the shared vertex, a regular endpoint query and a brute-force query.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}

theorem irs_ifEq' {a b : ℕ} {t e : Stmt} {K K' : ℕ} {Q : Config → Prop} (hK : K + 4 ≤ K')
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (ifEq a b t e) c K' Q :=
  (irs_ifEq ht he).mono hK (fun _ h => h)

theorem irs_ite' {a b : ℕ} {t e : Stmt} {K K' : ℕ} {Q : Config → Prop} (hK : K + 2 ≤ K')
    (ht : c.nreg a < c.nreg b → IRS P W c₀ t c K Q)
    (he : ¬ c.nreg a < c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c K' Q :=
  (IRS.ite ht he).mono hK (fun _ h => h)

/-- `Mid` survives a step writing only `sw 4800 … 4999` (and the oracle bands). -/
theorem mid_keep {c₃ : Config} (hM : Mid P J z c c₂ L)
    (h : ∀ r, bandOf r ∉ oracleBands → (r < sw 4800 ∨ sw 4999 < r) → r ≠ ALLOC →
      c₃.nreg r = c₂.nreg r)
    (ha : c₂.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ a, a < c₂.nreg ALLOC → c₃.nmem a = c₂.nmem a) :
    Mid P J z c c₃ L := by
  refine mid_step hM (hM.1.transport (fun j hj => h _
    (not_oracle_sw (by unfold accA sw; omega) (by unfold accA sw; omega))
    (by unfold accA sw; omega) (by unfold accA ALLOC sw; omega))) subset_rfl
    (fun τ hτ => Or.inl hτ) ?_
  exact candFr_regs (S := fun r => sw 4800 ≤ r ∧ r ≤ sw 4999)
    (fun r h => by unfold Alw; unfold sw at h ⊢; omega)
    (fun r a b d => h r a (by unfold sw at b ⊢; omega) d) ha hm

/-- The budget of the decision tree (the leaves). -/
def kD (κT κS LK KB : ℕ) : ℕ := 16749 + κT + κS + LK + KB

section Tree

variable {tabB : Stmt} {shrB bruteS : Stmt → Stmt} {κT κS κB KB : ℕ}

/-- The common hypotheses of the decision tree at the state `c₂`. -/
structure TreeH (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c c₂ : Config) (z : Point)
    (L : Set ℝ) (F : ℕ → ℕ) (κB KB : ℕ) : Prop where
  hA : AEnv P W X Ok J H N₁ N₂ E c₀
  hq : QState P J 1 z c
  hend : c.nreg qJ < 2 * N₂.nChords →
    (c.nreg qE, c.nreg qH, c.nreg qD) = (sweepEndQ N₂.chords).getD (c.nreg qJ) (0, 0, 0)
  hKB : BruteQ J N₂ (c.nreg qJ) z →
    κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ KB
  hI₂ : IInv W c₀ c₂
  hM : Mid P J z c c₂ L
  hnb : ¬ (c.nreg qE = 1 ∨ c.nreg qE = 3)
  vE : c₂.nreg qE = c.nreg qE
  vy : c₂.nreg y34 = 2 * J.m₂ + 6
  vk : c₂.nreg k2 = N₂.nChords
  vj : c₂.nreg jx = c.nreg qJ - N₂.nChords
  vt : c₂.nreg tgt = 6 + midT J.right
  v41 : c₂.nreg (sw 41) = cstR J 1
  hK : Consts c₂

variable (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
  (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)

/-- The position facts of a tour query. -/
theorem tree_pos (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) :
    (chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z ∧
      c.nreg qE < (chainModel J.right).W.n ∧
      0 ≤ (chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ∧
      (chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ < 1 := by
  obtain ⟨hzpos, hqE, hpp, -⟩ := q1_facts h.hq
  exact ⟨hzpos, hqE, hpp.1, hpp.2.1⟩

include hT in
theorem leaf_tab (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (hj : c.nreg qJ < 2 * N₂.nChords) (hns : z ≠ J.shared) (hnt : z ≠ J.right.top)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB ≤ W) :
    IRS P W c₀ tabB c₂ (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') :=
  (tab_irs hT h.hA h.hq h.hI₂ h.hM h.hnb hj (h.hend hj) hns hnt
    (by unfold kD at hroom; omega)).mono (by unfold kD; omega) (fun _ h => h)

include hS hsh hBs hXl in
theorem leaf_shr (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) (hzs : z = J.shared)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB ≤ W) :
    IRS P W c₀ (shrB sh) c₂
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') :=
  (shr_irs hS hsh hBs hXl h.hA h.hq h.hI₂ h.hM hzs
    (by unfold kD at hroom; omega)).mono (by unfold kD; omega) (fun _ h => h)

include hBr hsh hBs hXl in
theorem leaf_brute (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (hbq : BruteQ J N₂ (c.nreg qJ) z) (hns : z ≠ J.shared)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB ≤ W) :
    IRS P W c₀ (bruteB bruteS sh) c₂
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  have hk := h.hKB hbq
  exact (bruteB_irs hBr hsh hBs hXl h.hA h.hq h.hI₂ h.hM h.hnb hns
    (by unfold kD at hroom; omega)).mono (by unfold kD; omega) (fun _ h => h)

include hT hBr hsh hBs hXl in
/-- **A vertex position other than the shared vertex.** -/
theorem topT_irs (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) (hns : z ≠ J.shared)
    (h0 : (chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = 0)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB ≤ W) :
    IRS P W c₀ (topT tabB bruteS sh) c₂
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB + 14)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hx, hp0, hp1⟩ := tree_pos h
  have htop := top_iffR h.hA.hP (Qof P) hx hp0 hp1
  rw [hzpos] at htop
  dsimp only at htop
  have k6 := h.hK.2.2.1
  set KK := kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB with hKK
  unfold topT
  refine irs_ite' (K := KK + 12) (⋄) (fun hj => ?_) (fun hj => ?_)
  · rw [h.vj, h.vk] at hj
    have hj' : c.nreg qJ < 2 * N₂.nChords := ⋄
    refine irs_ifEq' (K := KK + 8) (⋄) (fun e => ?_) (fun e => ?_)
    · rw [h.vE, k6] at e
      exact (leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ⟨h0, Or.inl e⟩)) hns hroom).mono
        (⋄) (fun _ h => h)
    · refine irs_ifEq' (K := KK + 4) (⋄) (fun e' => ?_) (fun e' => ?_)
      · rw [h.vE, h.vy] at e'
        have e1 : c.nreg qE + 1 = 2 * J.m₂ + 7 := ⋄
        exact (leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ⟨h0, Or.inr (Or.inl e1)⟩))
          hns hroom).mono (⋄) (fun _ h => h)
      · refine irs_ifEq' (K := KK) le_rfl (fun e'' => ?_) (fun e'' => ?_)
        · rw [h.vE, h.vt] at e''
          exact leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ⟨h0, Or.inr (Or.inr e'')⟩)) hns
            hroom
        · rw [h.vE, k6] at e
          rw [h.vE, h.vy] at e'
          rw [h.vE, h.vt] at e''
          have hnt : z ≠ J.right.top := fun hz => by
            rcases (htop.1 hz).2 with a | a | a
            · exact e a
            · exact e' (⋄)
            · exact e'' a
          exact leaf_tab hT h hj' hns hnt hroom
  · rw [h.vj, h.vk] at hj
    exact (leaf_brute hBr hsh hBs hXl h (Or.inl (⋄)) hns hroom).mono (⋄)
      (fun _ h => h)

include hT hS hBr hsh hBs hXl in
/-- **The decision tree** of a tour position. -/
theorem dec_irs (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (vH : c₂.nreg tH = nhgt (chainModel J.right) (Qof P) ⟨c.nreg qE, c.nreg qH⟩)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB ≤ W) :
    IRS P W c₀ (.ifLtN K0 tH (genT tabB bruteS sh) (zeroT tabB shrB bruteS sh)) c₂
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB + 28)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hx, hp0, hp1⟩ := tree_pos h
  have hsh' := shared_iffR h.hA.hP (Qof P) hx hp0 hp1
  rw [hzpos] at hsh'
  dsimp only at hsh'
  set KK := kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB with hKK
  have k0 := h.hK.1
  have k6 := h.hK.2.2.1
  have hz0 := nhgt_eq_zero_iff (chainModel J.right) (Qof P) ⟨c.nreg qE, c.nreg qH⟩
  refine irs_ite' (K := KK + 26) (⋄) (fun hp => ?_) (fun hp => ?_)
  · -- parameter positive
    rw [k0, vH] at hp
    have hne : (chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ≠ 0 :=
      fun e => by rw [hz0.2 e] at hp; exact lt_irrefl _ hp
    have hns : z ≠ J.shared := fun e => hne (hsh'.1 e).1
    have hnt : z ≠ J.right.top := fun e => by
      have := (top_iffR h.hA.hP (Qof P) hx hp0 hp1).1 (by rw [hzpos]; exact e)
      exact hne this.1
    unfold genT
    refine irs_ite' (K := KK) (⋄) (fun hj => ?_) (fun hj => ?_)
    · rw [h.vj, h.vk] at hj
      exact leaf_tab hT h (⋄) hns hnt hroom
    · rw [h.vj, h.vk] at hj
      exact leaf_brute hBr hsh hBs hXl h (Or.inl (⋄)) hns hroom
  · -- parameter zero
    rw [k0, vH] at hp
    have h0 : (chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = 0 :=
      hz0.1 (⋄)
    unfold zeroT
    refine irs_ifEq' (K := KK + 22) (⋄) (fun e => ?_) (fun e => ?_)
    · rw [h.vE, h.v41] at e
      exact (leaf_shr hS hsh hBs hXl h (hsh'.2 ⟨h0, Or.inl e⟩) hroom).mono (⋄)
        (fun _ h => h)
    · rw [h.vE, h.v41] at e
      refine irs_ifEq' (K := KK + 18) (⋄) (fun e' => ?_) (fun e' => ?_)
      · rw [h.vE, h.vy] at e'
        refine irs_ifEq' (K := KK + 14) (⋄) (fun e'' => ?_) (fun e'' => ?_)
        · rw [h.v41, k6] at e''
          have e1 : c.nreg qE + 1 = 2 * J.m₂ + 7 := ⋄
          exact (leaf_shr hS hsh hBs hXl h (hsh'.2 ⟨h0, Or.inr ⟨e1, e''⟩⟩) hroom).mono
            (⋄) (fun _ h => h)
        · rw [h.v41, k6] at e''
          have hns : z ≠ J.shared := fun hz => by
            rcases (hsh'.1 hz).2 with a | ⟨-, a⟩
            · exact e a
            · exact e'' a
          exact topT_irs hT hBr hsh hBs hXl h hns h0 hroom
      · rw [h.vE, h.vy] at e'
        have hns : z ≠ J.shared := fun hz => by
          rcases (hsh'.1 hz).2 with a | ⟨a, -⟩
          · exact e a
          · exact e' (⋄)
        exact (topT_irs hT hBr hsh hBs hXl h hns h0 hroom).mono (⋄) (fun _ h => h)

end Tree

end Cand1

end

end SweepIo

end Chazelle.Core
