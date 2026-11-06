module

public import Chazelle.Core.OracleRamNode

/-!
# Lemma 3.6 (WP-H), RAM part 6: the scan of the nodes of `D*`

`dstarS` scans the nodes `DL[i]`, `i < nD` (the list of the nodes of `D*` built by the
preprocessing), with `nodeScanS`.  Loop counter `120100`, scratch `120101`.  Main result:
`dstarS_exec`: the best hit is updated with the points `nodePts` of all listed nodes, at cost
`dstarCost` (the sum of the costs of the listed nodes, plus constants).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- One node of the list. -/
def dstarBody : Stmt :=
  .seq (block [.addN 120101 120034 120100, .loadN 120090 120101])
    (.seq nodeScanS (.instr (.addN 120100 120100 120011)))

/-- **The scan of the nodes of `D*`.** -/
def dstarS : Stmt := .seq (.instr (.constN 120100 0)) (.whileLtN 120100 120035 dstarBody)

/-- The registers written by `dstarS`. -/
def BD (r : ℕ) : Bool := BN r || decide (r = 120090) || decide (120100 ≤ r ∧ r ≤ 120101)

theorem BD_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BD r = false := by
  simp only [BD, BN, BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- The cost of the listed nodes from the `i`-th on. -/
def dstarCostFrom (m : ℕ → ℕ) (V : QV) (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i V.nD, (nodeCost m V (m (V.DL + t)) + 6)

/-- **The cost of the scan of `D*`.** -/
def dstarCost (m : ℕ → ℕ) (V : QV) : ℕ := dstarCostFrom m V 0 + 4

/-- The points of the listed nodes before the `i`-th. -/
def dstarPts (m : ℕ → ℕ) (V : QV) (C : Chain) (i : ℕ) : Set Point :=
  {x | ∃ t, t < i ∧ x ∈ nodePts m V C (m (V.DL + t))}

/-- **The invariant of the loop of `dstarS`.** -/
structure DInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  i_le : c.nreg 120100 ≤ V.nD
  hit : Sweep.FirstHitOpt (S ∪ dstarPts c₀.nmem V C (c.nreg 120100)) z (sgnOf V.σb)
    (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))
  fr : FrameB BD c₀ c

theorem dstarBody_inv {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point}
    (hm : QMem V c₀.nmem W) (hDL : V.DL + V.nD ≤ W) {c : Config} (h : DInv P W C V z c₀ S c)
    (ht : c.nreg 120100 < c.nreg 120035) :
    ∃ c' k, Exec P W dstarBody c c' k ∧ DInv P W C V z c₀ S c' ∧
      dstarCostFrom c₀.nmem V (c'.nreg 120100) + k + 2 ≤ dstarCostFrom c₀.nmem V (c.nreg 120100) := by
  set i := c.nreg 120100
  have hin : i < V.nD := by rwa [h.q.nD] at ht
  have hmem : c.nmem = c₀.nmem := h.fr.2.2.1
  -- 1. read the node
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 120101 120034 120100, .loadN 120090 120101]) c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 120090 = c₀.nmem (V.DL + i) ∧ (∀ r, r ≠ 120101 → r ≠ 120090 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hw := h.wb
    exec_block
    · rw [h.q.DL]; omega
    · refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [h.q.DL, hmem]
      · config_simp; upd_solve
  obtain ⟨x90, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have hq₁ : QConst P V c₁ := h.q.congr fun r h1 h2 => r₁ r (by omega) (by omega)
  have hb₁ : BestOK P.n V.s V.m c₁ := by
    unfold BestOK
    rw [r₁ 120050 (by decide) (by decide), r₁ 120051 (by decide) (by decide),
      r₁ 120052 (by decide) (by decide)]
    exact h.b
  have hbo₁ : bestOf c₁ = bestOf c := by
    unfold bestOf; rw [r₁ 120050 (by decide) (by decide), r₁ 120052 (by decide) (by decide)]
  have hm₁ : c₁.nmem = c₀.nmem := m₁.trans hmem
  -- 2. scan it
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := nodeScan_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    (by rwa [hm₁]) (S := S ∪ dstarPts c₀.nmem V C i) (by rw [hbo₁]; exact h.hit)
  rw [x90, hm₁] at hk₂ hit₂
  have R₂ : ∀ r, BN r = false → c₂.nreg r = c₁.nreg r := f₂.1
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ BN_const
  -- 3. next
  have x100 : c₂.nreg 120100 = i := (R₂ _ (by decide)).trans (r₁ _ (by decide) (by decide))
  have hW1 : i + 1 ≤ W := by have := h.wb.1 120035; rw [h.q.nD] at this; omega
  obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec (P := P) e₂.wb_right 120100 120100 120011
    (by rwa [x100, hq₂.one])
  rw [x100, hq₂.one] at v₃
  have ex : Exec P W dstarBody c c₃ (k₁ + (k₂ + 1)) := .seq e₁ (.seq e₂ e₃)
  have fb := exec_frameB ex (B := BD) (by decide)
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, hq₂.congr fun r h1 h2 => r₃ r (by omega), ?_, by omega, ?_,
    h.fr.trans fb⟩, ?_⟩
  · unfold BestOK
    rwa [r₃ 120050 (by decide), r₃ 120051 (by decide), r₃ 120052 (by decide)]
  · have hbo : bestOf c₃ = bestOf c₂ := by
      unfold bestOf; rw [r₃ 120050 (by decide), r₃ 120052 (by decide)]
    rw [hbo, v₃]
    have e : dstarPts c₀.nmem V C (i + 1) =
        dstarPts c₀.nmem V C i ∪ nodePts c₀.nmem V C (c₀.nmem (V.DL + i)) := by
      ext x
      simp only [dstarPts, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨t, ht, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | rfl
        · exact Or.inl ⟨t, h', hx⟩
        · exact Or.inr hx
      · rintro (⟨t, ht, hx⟩ | hx)
        · exact ⟨t, by omega, hx⟩
        · exact ⟨i, by omega, hx⟩
    rwa [e, ← Set.union_assoc]
  · rw [v₃]
    unfold dstarCostFrom
    rw [Finset.sum_eq_sum_Ico_succ_bot hin]
    omega

/-- **The scan of the nodes of `D*`.** -/
theorem dstarS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) (hDL : V.DL + V.nD ≤ W)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))) :
    ∃ c' k, Exec P W dstarS c c' k ∧ k ≤ dstarCost c.nmem V ∧ FrameB BD c c' ∧
      BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ dstarPts c.nmem V C V.nD) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120100 0 (by omega)
  have I₀ : DInv P W C V z c S c₁ := by
    refine ⟨e₁.wb_right, hq.congr fun r h1 h2 => r₁ r (by omega), ?_, by rw [v₁]; omega, ?_, ?_⟩
    · unfold BestOK
      rwa [r₁ 120050 (by decide), r₁ 120051 (by decide), r₁ 120052 (by decide)]
    · have hbo : bestOf c₁ = bestOf c := by
        unfold bestOf; rw [r₁ 120050 (by decide), r₁ 120052 (by decide)]
      rw [hbo, v₁]
      have : dstarPts c.nmem V C 0 = ∅ := by ext x; simp [dstarPts]
      rwa [this, Set.union_empty]
    · exact FrameB.mono (exec_frameB e₁ (B := fun r => decide (r = 120100)) (by decide))
        fun r hr => by
          simp only [decide_eq_true_eq] at hr
          simp only [BD, Bool.or_eq_true, decide_eq_true_eq]; omega
  obtain ⟨c₂, k₂, e₂, I₂, hex, hk₂⟩ := Exec.whileLtN_potential (a := 120100) (b := 120035)
    (DInv P W C V z c S) (fun d => dstarCostFrom c.nmem V (d.nreg 120100)) (fun _ h => h.wb)
    (fun d hd ht => dstarBody_inv (P := P) hG hW hs hm hDL hd ht) I₀
  have hi2 : c₂.nreg 120100 = V.nD := by
    have := I₂.i_le; rw [I₂.q.nD] at hex; omega
  refine ⟨c₂, _, .seq e₁ e₂, ?_, I₂.fr, I₂.b, by rw [← hi2]; exact I₂.hit⟩
  rw [v₁] at hk₂
  unfold dstarCost; omega

end

end OracleR

end Chazelle.Core
