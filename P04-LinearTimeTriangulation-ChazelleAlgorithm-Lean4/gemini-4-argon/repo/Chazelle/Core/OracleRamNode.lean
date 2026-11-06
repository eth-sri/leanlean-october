module

public import Chazelle.Core.OracleRamArc

/-!
# Lemma 3.6 (WP-H), RAM part 5: the scan of one node

`nodeScanS` scans the node `v` (register `120090`, a spine position of the normal form; nodes
`v ≥ A` are padding and scan nothing): it reads the arc `j₀ = seq[v]`, its region `r`, the
number `na` and the start `ls` of the arc list of `r`, and runs `arcScan` on the arcs
`list[ls + t]`, `t < na`.

The memory quantities are named by functions of the memory (`arcSe`, `nodeNa`, …); `nodePts` is
the set of points scanned for a node.  `QMem` collects the facts about the memory that keep the
scan in range.  Main result: `nodeScan_exec` (cost `nodeCost` + a constant).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## Memory quantities -/

section Mem
variable (m : ℕ → ℕ) (V : QV)

/-- The start edge of arc record `j`. -/
def arcSe (j : ℕ) : ℕ := m (V.AB + 5 * j + 1)
/-- The end edge of arc record `j`. -/
def arcEe (j : ℕ) : ℕ := m (V.AB + 5 * j + 3)
/-- The spine position of arc record `j`. -/
def arcPos (j : ℕ) : ℕ := m (V.POS + j)
/-- The number of scanned walk edges of arc record `j`, minus one. -/
def arcLenM (j : ℕ) : ℕ := lenOf V.A (2 * V.m + 7) (arcSe m V j) (arcEe m V j) (arcPos m V j)
/-- The arc record of node `v`. -/
def nodeArc0 (v : ℕ) : ℕ := m (V.SB + v)
/-- The region of node `v`. -/
def nodeReg (v : ℕ) : ℕ := m (V.AB + 5 * nodeArc0 m V v)
/-- The number of arcs of the region of node `v`. -/
def nodeNa (v : ℕ) : ℕ := m (V.RB + 5 * nodeReg m V v)
/-- The start of the arc list of the region of node `v`. -/
def nodeLs (v : ℕ) : ℕ := m (V.RB + 5 * nodeReg m V v + 1)
/-- The `t`-th arc record of the region of node `v`. -/
def nodeArc (v t : ℕ) : ℕ := m (V.LB + nodeLs m V v + t)

/-- The points scanned for arc record `j`. -/
def arcPts (C : Chain) (j : ℕ) : Set Point :=
  scanned C (2 * V.m + 7) (arcSe m V j) (arcLenM m V j + 1)

/-- **The points scanned for node `v`.** -/
def nodePts (C : Chain) (v : ℕ) : Set Point :=
  {x | v < V.A ∧ ∃ t, t < nodeNa m V v ∧ x ∈ arcPts m V C (nodeArc m V v t)}

/-- The cost of the arcs of node `v` from the `t`-th on. -/
def nodeCostFrom (v t : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico t (nodeNa m V v), (1132 * (arcLenM m V (nodeArc m V v i) + 1) + 40)

/-- **The cost of the scan of node `v`.** -/
def nodeCost (v : ℕ) : ℕ := if v < V.A then nodeCostFrom m V v 0 + 40 else 40

end Mem

/-- **The memory facts** that keep the scans in range (word bound `W`). -/
structure QMem (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  A_le : V.A ≤ W
  arc : ∀ j, j < V.A → arcSe m V j < 2 * V.m + 7 ∧ arcEe m V j < 2 * V.m + 7 ∧
    arcPos m V j < V.A ∧ V.AB + 5 * j + 3 ≤ W ∧ V.POS + j ≤ W
  node : ∀ v, v < V.A → V.SB + v ≤ W ∧ nodeArc0 m V v < V.A ∧
    V.RB + 5 * nodeReg m V v + 1 ≤ W ∧ V.LB + nodeLs m V v ≤ W ∧
    ∀ t, t < nodeNa m V v → nodeArc m V v t < V.A ∧ V.LB + nodeLs m V v + t ≤ W

/-! ## The program -/

/-- `rd := rb + 5 · rs`. -/
def t5 (rd rs rb : ℕ) : Stmt := block [.addN rd rs rs, .addN rd rd rd, .addN rd rd rs, .addN rd rd rb]

/-- Read the region of node `v` and its arc list. -/
def nodeHead : Stmt :=
  .seq (block [.addN 120091 120046 120090, .loadN 120092 120091])
    (.seq (t5 120093 120092 120044) (.seq (.instr (.loadN 120094 120093))
      (.seq (t5 120095 120094 120045) (block [.loadN 120096 120095, .addN 120095 120095 120011,
        .loadN 120097 120095, .addN 120097 120097 120047, .constN 120098 0]))))

/-- One arc of the region. -/
def nodeBody : Stmt :=
  .seq (block [.addN 120099 120097 120098, .loadN 120080 120099])
    (.seq arcScan (.instr (.addN 120098 120098 120011)))

/-- **The scan of node `v`** (register `120090`). -/
def nodeScanS : Stmt :=
  .ifLtN 120090 120030 (.seq nodeHead (.whileLtN 120098 120096 nodeBody)) .skip

/-- The registers written by `nodeScanS`. -/
def BN (r : ℕ) : Bool := BA r || decide (r = 120080) || decide (120091 ≤ r ∧ r ≤ 120099)

theorem BN_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BN r = false := by
  simp only [BN, BA, BW, BE, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-! ## Execution -/

theorem t5_exec {P : Polygon} {W : ℕ} {rd rs rb : ℕ} (h1 : rd ≠ rs) (h2 : rd ≠ rb) (c : Config)
    (hw : WordsBounded W c) (h : c.nreg rb + 5 * c.nreg rs ≤ W) :
    ∃ c', Exec P W (t5 rd rs rb) c c' 4 ∧ c'.nreg rd = c.nreg rb + 5 * c.nreg rs ∧
      (∀ r, r ≠ rd → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold t5
  obtain ⟨c', k, ex, hk, hq⟩ : ∃ c' k, Exec P W (block [.addN rd rs rs, .addN rd rd rd,
      .addN rd rd rs, .addN rd rd rb]) c c' k ∧ k = 4 ∧ (c'.nreg rd = c.nreg rb + 5 * c.nreg rs ∧
        (∀ r, r ≠ rd → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
    exec_block
    · omega
    · config_simp; omega
    · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
    · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> omega)
    · refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;>
          first | omega)
      · config_simp; upd_solve
  subst hk
  exact ⟨c', ex, hq⟩

/-- **The invariant of the loop of `nodeScanS`.** -/
structure NInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (v : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  rv : c.nreg 120090 = v
  na : c.nreg 120096 = nodeNa c₀.nmem V v
  ls : c.nreg 120097 = V.LB + nodeLs c₀.nmem V v
  t_le : c.nreg 120098 ≤ nodeNa c₀.nmem V v
  hit : Sweep.FirstHitOpt (S ∪ {x | ∃ t, t < c.nreg 120098 ∧
      x ∈ arcPts c₀.nmem V C (nodeArc c₀.nmem V v t)}) z (sgnOf V.σb)
    (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))
  fr : FrameB BN c₀ c

theorem nodeCostFrom_succ (m : ℕ → ℕ) (V : QV) {v t : ℕ} (ht : t < nodeNa m V v) :
    nodeCostFrom m V v t = (1132 * (arcLenM m V (nodeArc m V v t) + 1) + 40) +
      nodeCostFrom m V v (t + 1) := by
  unfold nodeCostFrom
  rw [Finset.sum_eq_sum_Ico_succ_bot ht]

theorem nodeBody_inv {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain}
    {V : QV} {z : Point} (hs : SemOK P C V z) {c₀ : Config} {S : Set Point} {v : ℕ}
    (hvA : v < V.A) (hm : QMem V c₀.nmem W) {c : Config} (h : NInv P W C V z c₀ S v c)
    (ht : c.nreg 120098 < c.nreg 120096) :
    ∃ c' k, Exec P W nodeBody c c' k ∧ NInv P W C V z c₀ S v c' ∧
      nodeCostFrom c₀.nmem V v (c'.nreg 120098) + k + 2 ≤
        nodeCostFrom c₀.nmem V v (c.nreg 120098) := by
  set t := c.nreg 120098
  have htn : t < nodeNa c₀.nmem V v := by rwa [h.na] at ht
  have hmem : c.nmem = c₀.nmem := h.fr.2.2.1
  obtain ⟨hSB, hj0, hRB, hLB, hlist⟩ := hm.node v hvA
  obtain ⟨hjA, hLBt⟩ := hlist t htn
  set j := nodeArc c₀.nmem V v t
  obtain ⟨hsen, heen, hpA, haddr, hpos⟩ := hm.arc j hjA
  -- 1. read the arc
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 120099 120097 120098, .loadN 120080 120099]) c c₁ k₁ ∧ k₁ = 2 ∧
      (c₁.nreg 120080 = j ∧ (∀ r, r ≠ 120099 → r ≠ 120080 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hw := h.wb
    exec_block
    · rwa [h.ls]
    · refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [h.ls, hmem]; rfl
      · config_simp; upd_solve
  obtain ⟨x80, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
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
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := arcScan_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    (se := arcSe c₀.nmem V j) (ee := arcEe c₀.nmem V j) (p := arcPos c₀.nmem V j)
    (by rw [x80, hm₁]; rfl) (by rw [x80, hm₁]; rfl) (by rw [x80, hm₁]; rfl) hsen heen hpA
    (by rwa [x80]) (by rwa [x80])
    (S := S ∪ {x | ∃ t', t' < t ∧ x ∈ arcPts c₀.nmem V C (nodeArc c₀.nmem V v t')})
    (by rw [hbo₁]; exact h.hit)
  have R₂ : ∀ r, BA r = false → c₂.nreg r = c₁.nreg r := f₂.1
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ BA_const
  -- 3. next
  have x98 : c₂.nreg 120098 = t := (R₂ _ (by decide)).trans (r₁ _ (by decide) (by decide))
  have hW98 : t + 1 ≤ W := by
    have := h.wb.1 120096; rw [h.na] at this; omega
  obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec (P := P) e₂.wb_right 120098 120098 120011
    (by rwa [x98, hq₂.one])
  rw [x98, hq₂.one] at v₃
  have R₃ : ∀ r, BA r = false → r ≠ 120099 → r ≠ 120080 → r ≠ 120098 → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => (r₃ r h4).trans ((R₂ r h1).trans (r₁ r h2 h3))
  have ex : Exec P W nodeBody c c₃ (k₁ + (k₂ + 1)) := .seq e₁ (.seq e₂ e₃)
  have fb := exec_frameB ex (B := BN) (by decide)
  refine ⟨c₃, _, ex, ⟨e₃.wb_right, hq₂.congr fun r h1 h2 => r₃ r (by omega), ?_, ?_, ?_, ?_,
    ?_, ?_, h.fr.trans fb⟩, ?_⟩
  · unfold BestOK
    rwa [r₃ 120050 (by decide), r₃ 120051 (by decide), r₃ 120052 (by decide)]
  · rw [R₃ _ (by decide) (by decide) (by decide) (by decide)]; exact h.rv
  · rw [R₃ _ (by decide) (by decide) (by decide) (by decide)]; exact h.na
  · rw [R₃ _ (by decide) (by decide) (by decide) (by decide)]; exact h.ls
  · rw [v₃]; omega
  · have hbo : bestOf c₃ = bestOf c₂ := by
      unfold bestOf; rw [r₃ 120050 (by decide), r₃ 120052 (by decide)]
    rw [hbo, v₃]
    have e : {x | ∃ t', t' < t + 1 ∧ x ∈ arcPts c₀.nmem V C (nodeArc c₀.nmem V v t')} =
        {x | ∃ t', t' < t ∧ x ∈ arcPts c₀.nmem V C (nodeArc c₀.nmem V v t')} ∪
          arcPts c₀.nmem V C j := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨t', ht', hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
        · exact Or.inl ⟨t', h', hx⟩
        · exact Or.inr hx
      · rintro (⟨t', ht', hx⟩ | hx)
        · exact ⟨t', by omega, hx⟩
        · exact ⟨t, by omega, hx⟩
    rwa [e, ← Set.union_assoc]
  · rw [v₃, nodeCostFrom_succ c₀.nmem V htn]
    have e : arcLenM c₀.nmem V (nodeArc c₀.nmem V v t) = lenOf V.A (2 * V.m + 7)
        (arcSe c₀.nmem V j) (arcEe c₀.nmem V j) (arcPos c₀.nmem V j) := rfl
    rw [e]
    omega

/-- **The scan of node `v`** (register `120090`). -/
theorem nodeScan_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) {S : Set Point}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))) :
    ∃ c' k, Exec P W nodeScanS c c' k ∧ k ≤ nodeCost c.nmem V (c.nreg 120090) ∧
      FrameB BN c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ nodePts c.nmem V C (c.nreg 120090)) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  set v := c.nreg 120090
  by_cases hvA : v < V.A
  swap
  · refine ⟨c, _, .ifLtN_false (by rwa [hq.A]) (.skip hw), by
      unfold nodeCost; rw [ite_eq_right hvA]; omega,
      FrameB.refl _ _, hb, ?_⟩
    have e : nodePts c.nmem V C v = ∅ := by
      ext x; simp only [nodePts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hvA h.1
    rwa [e, Set.union_empty]
  obtain ⟨hSB, hj0, hRB, hLB, hlist⟩ := hm.node v hvA
  obtain ⟨-, -, -, haddr0, -⟩ := hm.arc _ hj0
  -- 1. the head
  obtain ⟨c₁, e₁, v₁⟩ : ∃ c₁, Exec P W (block [.addN 120091 120046 120090, .loadN 120092 120091])
      c c₁ 2 ∧ (c₁.nreg 120092 = nodeArc0 c.nmem V v ∧
        (∀ r, r ≠ 120091 → r ≠ 120092 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    obtain ⟨c₁, k, e, hk, hq'⟩ : ∃ c₁ k, Exec P W (block [.addN 120091 120046 120090,
        .loadN 120092 120091]) c c₁ k ∧ k = 2 ∧ (c₁.nreg 120092 = nodeArc0 c.nmem V v ∧
        (∀ r, r ≠ 120091 → r ≠ 120092 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
      exec_block
      · rwa [hq.SB]
      · refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hq.SB]; rfl
        · config_simp; upd_solve
    subst hk; exact ⟨c₁, e, hq'⟩
  obtain ⟨x92, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  obtain ⟨c₂, e₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := t5_exec (P := P) (rd := 120093) (rs := 120092)
    (rb := 120044) (by decide) (by decide) c₁ e₁.wb_right (by
      rw [x92, r₁ _ (by decide) (by decide), hq.AB]; omega)
  rw [x92, r₁ _ (by decide) (by decide), hq.AB] at v₂
  have e₃ := Exec.loadN e₂.wb_right 120094 120093 (P := P)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 120094 (c₂.nmem (c₂.nreg 120093)) } with hc₃
  have x94 : c₃.nreg 120094 = nodeReg c.nmem V v := by
    rw [hc₃]; config_simp; rw [v₂, m₂, m₁]; rfl
  have r₃ : ∀ r, r ≠ 120094 → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [hc₃]; config_simp; upd_solve
  obtain ⟨c₄, e₄, v₄, r₄, m₄, rr₄, rm₄, o₄⟩ := t5_exec (P := P) (rd := 120095) (rs := 120094)
    (rb := 120045) (by decide) (by decide) c₃ e₃.wb_right (by
      rw [x94, r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide), hq.RB]; omega)
  rw [x94, r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide), hq.RB] at v₄
  have m₄' : c₄.nmem = c.nmem := by rw [m₄]; show c₂.nmem = c.nmem; rw [m₂, m₁]
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (block [.loadN 120096 120095,
      .addN 120095 120095 120011, .loadN 120097 120095, .addN 120097 120097 120047,
      .constN 120098 0]) c₄ c₅ k₅ ∧ k₅ = 5 ∧
      (c₅.nreg 120096 = nodeNa c.nmem V v ∧ c₅.nreg 120097 = V.LB + nodeLs c.nmem V v ∧
        c₅.nreg 120098 = 0 ∧
        (∀ r, r ≠ 120095 → r ≠ 120096 → r ≠ 120097 → r ≠ 120098 → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have hq4 : c₄.nreg 120011 = 1 := by
      rw [r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide),
        hq.one]
    have hq47 : c₄.nreg 120047 = V.LB := by
      rw [r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), r₁ _ (by decide) (by decide),
        hq.LB]
    have w₄ := e₄.wb_right
    exec_block
    · config_simp; rw [v₄, hq4]; omega
    · config_simp; rw [v₄, hq4, hq47, m₄']
      have : nodeLs c.nmem V v = c.nmem (V.RB + 5 * nodeReg c.nmem V v + 1) := rfl
      rw [← this]; omega
    · omega
    · refine ⟨rfl, ?_, ?_, by config_simp, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [v₄, m₄']; rfl
      · config_simp; rw [v₄, hq4, hq47, m₄', Nat.add_comm]; rfl
      · config_simp; upd_solve
  obtain ⟨x96, x97, x98, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  -- the frame of the head
  have exh : Exec P W nodeHead c c₅ (2 + (4 + (1 + (4 + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have fh := exec_frameB exh (B := fun r => decide (120091 ≤ r ∧ r ≤ 120098)) (by decide)
  have R₅ : ∀ r, (r < 120091 ∨ 120098 < r) → c₅.nreg r = c.nreg r := fun r hr =>
    fh.1 r (by simp only [decide_eq_false_iff_not, not_and, not_le]; omega)
  have I₀ : NInv P W C V z c S v c₅ := by
    refine ⟨e₅.wb_right, hq.congr fun r h1 h2 => R₅ r (by omega), ?_, R₅ _ (by omega), x96, x97,
      by rw [x98]; omega, ?_, FrameB.mono fh fun r hr => ?_⟩
    · unfold BestOK
      rwa [R₅ 120050 (by omega), R₅ 120051 (by omega), R₅ 120052 (by omega)]
    · have hbo : bestOf c₅ = bestOf c := by
        unfold bestOf; rw [R₅ 120050 (by omega), R₅ 120052 (by omega)]
      rw [hbo, x98]
      have : {x | ∃ t, t < 0 ∧ x ∈ arcPts c.nmem V C (nodeArc c.nmem V v t)} = ∅ := by
        ext x; simp
      rwa [this, Set.union_empty]
    · simp only [decide_eq_true_eq] at hr
      simp only [BN, Bool.or_eq_true, decide_eq_true_eq]; omega
  -- 2. the loop
  obtain ⟨c₆, k₆, e₆, I₆, hex, hk₆⟩ := Exec.whileLtN_potential (a := 120098) (b := 120096)
    (NInv P W C V z c S v) (fun d => nodeCostFrom c.nmem V v (d.nreg 120098)) (fun _ h => h.wb)
    (fun d hd ht => nodeBody_inv (P := P) hG hW hs hvA hm hd ht) I₀
  have ht6 : c₆.nreg 120098 = nodeNa c.nmem V v := by
    have := I₆.t_le; rw [I₆.na] at hex; omega
  refine ⟨c₆, _, .ifLtN_true (by rwa [hq.A]) (.seq exh e₆), ?_, I₆.fr, I₆.b, ?_⟩
  · rw [x98] at hk₆
    unfold nodeCost; rw [ite_eq_left hvA]; omega
  · have e : nodePts c.nmem V C v =
        {x | ∃ t, t < c₆.nreg 120098 ∧ x ∈ arcPts c.nmem V C (nodeArc c.nmem V v t)} := by
      ext x
      simp only [nodePts, Set.mem_ofPred_eq, ht6]
      exact ⟨fun h => h.2, fun h => ⟨hvA, h⟩⟩
    rw [e]; exact I₆.hit

end

end OracleR

end Chazelle.Core
