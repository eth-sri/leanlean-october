module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleRamList

/-!
# Lemma 3.6 (WP-H), RAM part 7: the scan of a cluster

`clusS` scans the cluster of the node `c` (register `120110`): all nodes `u < μ` with the label
of `c`.  The preprocessing stores the nodes sorted by label (`ORD`) and the position of each node
in that order (`RK`); the nodes with the label `l` of `c` form a block of `ORD` around `RK[c]`:
the program walks left from `RK[c]` to the start of the block, then scans the block with
`nodeScanS`.

Registers `120110 … 120118`.  Main result: `clusS_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## The order of the nodes by label -/

section Ord
variable (m : ℕ → ℕ) (V : QV)

/-- The label of node `u`. -/
def lab (u : ℕ) : ℕ := m (V.LAB + u)

/-- The node at position `i` of the order. -/
def ordAt (i : ℕ) : ℕ := m (V.ORD + i)

/-- The position of node `u` in the order. -/
def rkOf (u : ℕ) : ℕ := m (V.RK + u)

end Ord

/-- **The order by label in memory.** -/
structure OrdOK (m : ℕ → ℕ) (V : QV) (W : ℕ) : Prop where
  μ_le : V.μ ≤ W
  lt : ∀ i, i < V.μ → ordAt m V i < V.μ
  inj : ∀ i j, i < V.μ → j < V.μ → ordAt m V i = ordAt m V j → i = j
  rk : ∀ u, u < V.μ → rkOf m V u < V.μ ∧ ordAt m V (rkOf m V u) = u
  sorted : ∀ i j, i ≤ j → j < V.μ → lab m V (ordAt m V i) ≤ lab m V (ordAt m V j)
  ORD_le : V.ORD + V.μ ≤ W
  RK_le : V.RK + V.μ ≤ W
  LAB_le : V.LAB + V.μ ≤ W

section
variable (m : ℕ → ℕ) (V : QV)
include m V
/-- The points of the nodes with label `l`. -/
def clusPts (C : Chain) (l : ℕ) : Set Point :=
  {x | ∃ u, u < V.μ ∧ lab m V u = l ∧ x ∈ nodePts m V C u}

/-- The number of nodes with label `l`. -/
noncomputable def clusSize (l : ℕ) : ℕ :=
  ((Finset.range V.μ).filter fun u => lab m V u = l).card

/-! ## The program -/


end

/-- Read the label and the position of `c`. -/
def clusHead : Stmt := block [.addN 120111 120033 120110, .loadN 120112 120111,
  .addN 120111 120037 120110, .loadN 120113 120111, .constN 120114 1]

/-- One step left: move to `i - 1` if its node has the label, else stop. -/
def leftBody : Stmt :=
  .ifLtN 120012 120113
    (.seq (block [.subN 120115 120113 120011, .addN 120116 120036 120115, .loadN 120117 120116,
        .addN 120116 120033 120117, .loadN 120118 120116])
      (ifEq 120118 120112 (.instr (.copyN 120113 120115)) (.instr (.constN 120114 0))))
    (.instr (.constN 120114 0))

/-- One step right: scan the node at `i` if it has the label, else stop. -/
def fwdBody : Stmt :=
  .ifLtN 120113 120049
    (.seq (block [.addN 120116 120036 120113, .loadN 120090 120116, .addN 120116 120033 120090,
        .loadN 120118 120116])
      (ifEq 120118 120112 (.seq nodeScanS (.instr (.addN 120113 120113 120011)))
        (.instr (.constN 120114 0))))
    (.instr (.constN 120114 0))

/-- **The scan of the cluster of node `c`** (register `120110`). -/
def clusS : Stmt :=
  .seq clusHead (.seq (.whileLtN 120012 120114 leftBody)
    (.seq (.instr (.constN 120114 1)) (.whileLtN 120012 120114 fwdBody)))

/-- The registers written by `clusS`. -/
def BC (r : ℕ) : Bool := BN r || decide (r = 120090) || decide (120111 ≤ r ∧ r ≤ 120118)

theorem BC_const (r : ℕ) (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BC r = false := by
  core_grind

/-! ## The block of a label -/

section Block
variable {m : ℕ → ℕ} {V : QV} {W : ℕ}

section
variable (hO : OrdOK m V W)
include hO
/-- Left of the start of the block, the labels are different. -/
theorem lab_ne_left {lo l : ℕ} (hlo : lo < V.μ) (hl : lab m V (ordAt m V lo) = l)
    (hstop : lo = 0 ∨ lab m V (ordAt m V (lo - 1)) ≠ l) {j : ℕ} (hj : j < lo) :
    lab m V (ordAt m V j) ≠ l := by
  rcases hstop with h | h
  · omega
  · have h1 := hO.sorted (lo - 1) lo (by omega) hlo
    have h2 := hO.sorted j (lo - 1) (by omega) (by omega)
    omega

/-- Right of the end of the block, the labels are different. -/
theorem lab_ne_right {j' hi l : ℕ} (hj' : j' < hi)
    (hl : lab m V (ordAt m V j') = l) (hstop : hi = V.μ ∨ lab m V (ordAt m V hi) ≠ l) {j : ℕ}
    (hj : hi ≤ j) (hjμ : j < V.μ) : lab m V (ordAt m V j) ≠ l := by
  rcases hstop with h | h
  · omega
  · have h1 := hO.sorted j' hi (by omega) (by omega)
    have h2 := hO.sorted hi j hj hjμ
    omega


end

section
variable (m : ℕ → ℕ) (V : QV) (l i : ℕ)
include m V l i
/-- The number of positions with label `l` from `i` on. -/
noncomputable def cntFrom : ℕ :=
  ((Finset.Ico i V.μ).filter fun j => lab m V (ordAt m V j) = l).card

/-- The number of positions with label `l` before `i`. -/
noncomputable def cntBelow : ℕ :=
  ((Finset.range i).filter fun j => lab m V (ordAt m V j) = l).card


end

theorem cntFrom_succ {l i : ℕ} (hi : i < V.μ) (hl : lab m V (ordAt m V i) = l) :
    cntFrom m V l i = cntFrom m V l (i + 1) + 1 := by
  unfold cntFrom
  have e : (Finset.Ico i V.μ).filter (fun j => lab m V (ordAt m V j) = l) =
      insert i ((Finset.Ico (i + 1) V.μ).filter fun j => lab m V (ordAt m V j) = l) := by
    grind
  simp_all

theorem cntBelow_pred {l i : ℕ} (hi : 0 < i) (hl : lab m V (ordAt m V (i - 1)) = l) :
    cntBelow m V l i = cntBelow m V l (i - 1) + 1 := by
  unfold cntBelow
  have e : Finset.range i = insert (i - 1) (Finset.range (i - 1)) := by
    grind
  simp_all [Finset.filter_insert]

/-- The positions with label `l` correspond to the nodes with label `l`. -/
theorem card_positions (hO : OrdOK m V W) (l : ℕ) :
    ((Finset.range V.μ).filter fun j => lab m V (ordAt m V j) = l).card = clusSize m V l := by
  unfold clusSize
  rw [← Finset.card_image_of_injOn (f := ordAt m V) (s := (Finset.range V.μ).filter _)
    (fun i hi j hj h => hO.inj i j (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) h)]
  congr 1
  ext u
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  all_goals ram_grind

theorem cntFrom_le (l i : ℕ) : cntFrom m V l i ≤
    ((Finset.range V.μ).filter fun j => lab m V (ordAt m V j) = l).card := by
  unfold cntFrom
  apply Finset.card_le_card
  grind

theorem cntBelow_le (l i : ℕ) (hi : i ≤ V.μ) : cntBelow m V l i ≤
    ((Finset.range V.μ).filter fun j => lab m V (ordAt m V j) = l).card := by
  unfold cntBelow
  apply Finset.card_le_card
  grind

end Block

/-! ## The left walk -/

/-- **The invariant of the left walk.** -/
structure LInv (P : Polygon) (W : ℕ) (V : QV) (c₀ : Config) (l r0 : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  fr : FrameB (fun r => decide (120113 ≤ r ∧ r ≤ 120118)) c₀ c
  rl : c.nreg 120112 = l
  f_le : c.nreg 120114 ≤ 1
  i_le : c.nreg 120113 ≤ r0
  blk : ∀ j, c.nreg 120113 ≤ j → j ≤ r0 → lab c₀.nmem V (ordAt c₀.nmem V j) = l
  stop : c.nreg 120114 = 0 → c.nreg 120113 = 0 ∨
    lab c₀.nmem V (ordAt c₀.nmem V (c.nreg 120113 - 1)) ≠ l

theorem leftBody_inv {P : Polygon} {W : ℕ} {V : QV} {c₀ : Config} {l r0 : ℕ}
    (hq : QConst P V c₀) (hO : OrdOK c₀.nmem V W) (hr0 : r0 < V.μ) {c : Config}
    (h : LInv P W V c₀ l r0 c) (ht : c.nreg 120012 < c.nreg 120114) :
    ∃ c' k, Exec P W leftBody c c' k ∧ LInv P W V c₀ l r0 c' ∧
      13 * (cntBelow c₀.nmem V l (c'.nreg 120113) + c'.nreg 120114) + k + 2 ≤
        13 * (cntBelow c₀.nmem V l (c.nreg 120113) + c.nreg 120114) := by
  have hq' : QConst P V c := hq.frame h.fr fun r h1 h2 => by
    grind
  have hmem : c.nmem = c₀.nmem := h.fr.2.2.1
  have hf1 : c.nreg 120114 = 1 := by ram_grind
  have hw := h.wb
  
  by_cases hi0 : 0 < (c.nreg 120113)
  swap
  · -- at the left end
    obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120114 0 (by omega)
    refine ⟨c₁, _, .ifLtN_false (by omega) e₁, ⟨e₁.wb_right, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (FrameB.mono (exec_frameB e₁ (B := fun r => decide (r = 120114))
        (by decide)) fun r hr => by simp_all)
    · rw [r₁ _ (by decide)]; exact h.rl
    · omega
    all_goals (grind [Chazelle.Core.OracleR.LInv.i_le, Chazelle.Core.OracleR.LInv.blk])
  have hir : (c.nreg 120113) ≤ r0 := h.i_le
  have hu : ordAt c₀.nmem V ((c.nreg 120113) - 1) < V.μ := hO.lt _ (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 120115 120113 120011,
      .addN 120116 120036 120115, .loadN 120117 120116, .addN 120116 120033 120117,
      .loadN 120118 120116]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 120115 = (c.nreg 120113) - 1 ∧ c₁.nreg 120118 = lab c₀.nmem V (ordAt c₀.nmem V ((c.nreg 120113) - 1)) ∧
        (∀ r, r < 120115 ∨ 120118 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hORD := hO.ORD_le
    have hLAB := hO.LAB_le
    exec_block
    · config_simp; rw [hq'.ORD, hq'.one]; omega
    · config_simp; rw [hq'.ORD, hq'.one, hq'.LAB, hmem]
      ram_grind
    · refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hq'.one]
      · config_simp; rw [hq'.ORD, hq'.one, hq'.LAB, hmem]; rfl
      · config_simp; upd_solve
  obtain ⟨x115, x118, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have w₁ := e₁.wb_right
  have fr₁ : FrameB (fun r => decide (120113 ≤ r ∧ r ≤ 120118)) c c₁ :=
    FrameB.mono (exec_frameB e₁ (B := fun r => decide (120115 ≤ r ∧ r ≤ 120118)) (by decide))
      fun r hr => by grind
  by_cases heq : lab c₀.nmem V (ordAt c₀.nmem V ((c.nreg 120113) - 1)) = l
  · -- move left
    have hq12 : c₁.nreg 120118 = c₁.nreg 120112 := by
      rw [x118, r₁ _ (by omega), h.rl, heq]
    obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec (P := P) w₁ 120113 120115
    rw [x115] at v₂
    refine ⟨c₂, _, .ifLtN_true (by omega) (.seq e₁ (ifEq_eq_exec hq12 e₂)),
      ⟨e₂.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (fr₁.trans (FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 120113))
        (by decide)) fun r hr => by simp_all))
    · simp_all
    · simp_all
    · omega
    · grind [Chazelle.Core.OracleR.LInv.blk]
    all_goals (grind [Chazelle.Core.OracleR.cntBelow_pred])
  · -- stop
    have hq12 : c₁.nreg 120118 ≠ c₁.nreg 120112 := by
      rw [x118, r₁ _ (by omega), h.rl]; exact heq
    obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) w₁ 120114 0 (by omega)
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120113 120115)) hq12 e₂
    refine ⟨c₂, _, .ifLtN_true (by omega) (.seq e₁ ex'),
      ⟨e₂.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact h.fr.trans (fr₁.trans (FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 120114))
        (by decide)) fun r hr => by simp_all))
    · rw [r₂ _ (by decide), r₁ _ (by omega)]; exact h.rl
    · omega
    · simp_all
    all_goals (grind [Chazelle.Core.OracleR.LInv.blk])

/-! ## The forward walk -/

/-- **The invariant of the forward walk.** -/
structure FInv (P : Polygon) (W : ℕ) (C : Chain) (V : QV) (z : Point) (c₀ : Config)
    (S : Set Point) (l lo : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  q : QConst P V c
  b : BestOK P.n V.s V.m c
  fr : FrameB BC c₀ c
  rl : c.nreg 120112 = l
  f_le : c.nreg 120114 ≤ 1
  lo_le : lo ≤ c.nreg 120113
  i_le : c.nreg 120113 ≤ V.μ
  blk : ∀ j, lo ≤ j → j < c.nreg 120113 → lab c₀.nmem V (ordAt c₀.nmem V j) = l
  stop : c.nreg 120114 = 0 → c.nreg 120113 = V.μ ∨
    lab c₀.nmem V (ordAt c₀.nmem V (c.nreg 120113)) ≠ l
  hit : Sweep.FirstHitOpt (S ∪ {x | ∃ j, lo ≤ j ∧ j < c.nreg 120113 ∧
      x ∈ nodePts c₀.nmem V C (ordAt c₀.nmem V j)}) z (sgnOf V.σb)
    (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))

section
variable {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z)
include hG hW hs
theorem fwdBody_inv {c₀ : Config} {S : Set Point}
    {l lo NC : ℕ} (hm : QMem V c₀.nmem W) (hO : OrdOK c₀.nmem V W)
    (hNC : ∀ u, u < V.μ → nodeCost c₀.nmem V u ≤ NC) {c : Config}
    (h : FInv P W C V z c₀ S l lo c) (ht : c.nreg 120012 < c.nreg 120114) :
    ∃ c' k, Exec P W fwdBody c c' k ∧ FInv P W C V z c₀ S l lo c' ∧
      (NC + 60) * cntFrom c₀.nmem V l (c'.nreg 120113) + 60 * c'.nreg 120114 + k + 2 ≤
        (NC + 60) * cntFrom c₀.nmem V l (c.nreg 120113) + 60 * c.nreg 120114 := by
  have hmem : c.nmem = c₀.nmem := h.fr.2.2.1
  have hf1 : c.nreg 120114 = 1 := by ram_grind
  have hw := h.wb
  have fconst : ∀ (c₂ : Config) (e₂ : Exec P W (.instr (.constN 120114 0)) c c₂ 1),
      FrameB BC c c₂ := fun c₂ e₂ => FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 120114))
        (by decide)) fun r hr => by
          simp_all [decide_eq_true_eq, BC, Bool.or_eq_true]
  by_cases hiμ : c.nreg 120113 < V.μ
  swap
  · obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120114 0 (by omega)
    have f₁ := fconst c₁ e₁
    refine ⟨c₁, _, .ifLtN_false (by rw [h.q.μ]; exact hiμ) e₁, ⟨e₁.wb_right, h.q.frame f₁ BC_const,
      ?_, h.fr.trans f₁, by ram_grind, by omega,
      by ram_grind, by ram_grind,
      by ram_grind, fun _ => by
        ram_grind, ?_⟩, ?_⟩
    · unfold BestOK
      rw [r₁ 120050 (by decide), r₁ 120051 (by decide), r₁ 120052 (by decide)]; exact h.b
    · have hbo : bestOf c₁ = bestOf c := by
        simp_all [bestOf]
      rw [hbo, r₁ _ (by decide)]; exact h.hit
    simp_all
  have hu : ordAt c₀.nmem V (c.nreg 120113) < V.μ := hO.lt _ hiμ
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 120116 120036 120113,
      .loadN 120090 120116, .addN 120116 120033 120090, .loadN 120118 120116]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 120090 = ordAt c₀.nmem V (c.nreg 120113) ∧
        c₁.nreg 120118 = lab c₀.nmem V (ordAt c₀.nmem V (c.nreg 120113)) ∧
        (∀ r, r ≠ 120090 → r ≠ 120116 → r ≠ 120118 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hORD := hO.ORD_le
    have hLAB := hO.LAB_le
    exec_block
    · rw [h.q.ORD]; omega
    · config_simp; rw [h.q.ORD, h.q.LAB, hmem]
      ram_grind
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [h.q.ORD, hmem]; rfl
      · config_simp; rw [h.q.ORD, h.q.LAB, hmem]; rfl
      simp_all
  obtain ⟨x90, x118, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have w₁ := e₁.wb_right
  have fr₁ : FrameB BC c c₁ :=
    FrameB.mono (exec_frameB e₁ (B := fun r => decide (r = 120090) || decide (r = 120116) ||
      decide (r = 120118)) (by decide)) fun r hr => by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
  have hq₁ : QConst P V c₁ := h.q.frame fr₁ BC_const
  have hbo₁ : bestOf c₁ = bestOf c := by
    core_grind
  have hb₁ : BestOK P.n V.s V.m c₁ := by
    unfold BestOK
    rw [r₁ 120050 (by decide) (by decide) (by decide), r₁ 120051 (by decide) (by decide)
      (by decide), r₁ 120052 (by decide) (by decide) (by decide)]; exact h.b
  by_cases heq : lab c₀.nmem V (ordAt c₀.nmem V (c.nreg 120113)) = l
  · have hq12 : c₁.nreg 120118 = c₁.nreg 120112 := by
      rw [x118, r₁ _ (by decide) (by decide) (by decide), h.rl, heq]
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := nodeScan_exec (P := P) hG hW hs c₁ w₁ hq₁ hb₁
      (by simp_all)
      (S := S ∪ {x | ∃ j, lo ≤ j ∧ j < (c.nreg 120113) ∧ x ∈ nodePts c₀.nmem V C (ordAt c₀.nmem V j)})
      (by rw [hbo₁]; exact h.hit)
    rw [x90, m₁, hmem] at hk₂ hit₂
    have hq₂ : QConst P V c₂ := hq₁.frame f₂ BN_const
    have x113 : c₂.nreg 120113 = (c.nreg 120113) :=
      (f₂.1 _ (by decide)).trans (r₁ _ (by decide) (by decide) (by decide))
    obtain ⟨c₃, e₃, v₃, r₃, m₃⟩ := add_exec (P := P) e₂.wb_right 120113 120113 120011
      (by rw [x113, hq₂.one]; have := hO.μ_le; omega)
    rw [x113, hq₂.one] at v₃
    have f₂' : FrameB BC c₁ c₂ := FrameB.mono f₂ fun r hr => by
      simp only [BC, hr, Bool.true_or]
    have f₃ : FrameB BC c₂ c₃ := FrameB.mono (exec_frameB e₃ (B := fun r => decide (r = 120113))
      (by decide)) fun r hr => by
        simp only [decide_eq_true_eq] at hr
        simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
    have ex : Exec P W (.seq nodeScanS (.instr (.addN 120113 120113 120011))) c₁ c₃ (k₂ + 1) :=
      .seq e₂ e₃
    refine ⟨c₃, _, .ifLtN_true (by rw [h.q.μ]; exact hiμ) (.seq e₁ (ifEq_eq_exec hq12 ex)),
      ⟨e₃.wb_right, hq₂.frame f₃ BC_const, ?_, h.fr.trans (fr₁.trans (f₂'.trans f₃)), ?_, ?_,
        by rw [v₃]; have := h.lo_le; omega, by omega, ?_, ?_, ?_⟩, ?_⟩
    · grind [BestOK]
    · rw [r₃ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide) (by decide)]
      exact h.rl
    · rw [r₃ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide) (by decide)]
      exact h.f_le
    · intro j hj hji
      rw [v₃] at hji
      rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h' | rfl
      · exact h.blk j hj h'
      · exact heq
    · intro hf
      rw [r₃ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide) (by decide)] at hf
      omega
    · have hbo : bestOf c₃ = bestOf c₂ := by
        core_grind
      rw [hbo, v₃]
      have e : {x | ∃ j, lo ≤ j ∧ j < (c.nreg 120113) + 1 ∧ x ∈ nodePts c₀.nmem V C (ordAt c₀.nmem V j)} =
          {x | ∃ j, lo ≤ j ∧ j < (c.nreg 120113) ∧ x ∈ nodePts c₀.nmem V C (ordAt c₀.nmem V j)} ∪
            nodePts c₀.nmem V C (ordAt c₀.nmem V (c.nreg 120113)) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · grind
        · rintro (⟨j, h1, h2, hx⟩ | hx)
          · grind
          · exact ⟨(c.nreg 120113), h.lo_le, by omega, hx⟩
      grind
    · have hk2' : k₂ ≤ NC := hk₂.trans (hNC _ hu)
      rw [v₃, r₃ _ (by decide), f₂.1 _ (by decide), r₁ _ (by decide) (by decide) (by decide),
        hf1, cntFrom_succ hiμ heq, Nat.mul_add, Nat.mul_one]
      omega
  · have hq12 : c₁.nreg 120118 ≠ c₁.nreg 120112 := by
      rw [x118, r₁ _ (by decide) (by decide) (by decide), h.rl]; exact heq
    obtain ⟨c₂, e₂, v₂, r₂⟩ := const_exec (P := P) w₁ 120114 0 (by omega)
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec
      (S := .seq nodeScanS (.instr (.addN 120113 120113 120011))) hq12 e₂
    have f₂ : FrameB BC c₁ c₂ := FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 120114))
      (by decide)) fun r hr => by
        simp only [decide_eq_true_eq] at hr
        simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
    have R : ∀ r, r ≠ 120114 → r ≠ 120090 → r ≠ 120116 → r ≠ 120118 → c₂.nreg r = c.nreg r :=
      fun r h1 h2 h3 h4 => (r₂ r h1).trans (r₁ r h2 h3 h4)
    refine ⟨c₂, _, .ifLtN_true (by rw [h.q.μ]; exact hiμ) (.seq e₁ ex'),
      ⟨e₂.wb_right, hq₁.frame f₂ BC_const, ?_, h.fr.trans (fr₁.trans f₂),
        by rw [R _ (by decide) (by decide) (by decide) (by decide)]; exact h.rl, by omega,
        by rw [R _ (by decide) (by decide) (by decide) (by decide)]; exact h.lo_le,
        by grind,
        by rw [R _ (by decide) (by decide) (by decide) (by decide)]; exact h.blk,
        fun _ => by grind,
        ?_⟩, ?_⟩
    · grind [BestOK]
    · have hbo : bestOf c₂ = bestOf c := by
        core_grind
      rw [hbo, R _ (by decide) (by decide) (by decide) (by decide)]; exact h.hit
    grind

/-! ## The scan of a cluster -/

/-- **The scan of the cluster of node `c`** (register `120110`). -/
theorem clusS_exec (c : Config) (hw : WordsBounded W c)
    (hq : QConst P V c) (hb : BestOK P.n V.s V.m c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    (hcμ : c.nreg 120110 < V.μ) {NC : ℕ} (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    {S : Set Point}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))) :
    ∃ c' k, Exec P W clusS c c' k ∧
      k ≤ (clusSize c.nmem V (lab c.nmem V (c.nreg 120110)) + 2) * (NC + 80) ∧
      FrameB BC c c' ∧ BestOK P.n V.s V.m c' ∧
      Sweep.FirstHitOpt (S ∪ clusPts c.nmem V C (lab c.nmem V (c.nreg 120110))) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  obtain ⟨u₀, hu₀⟩ : ∃ u, c.nreg 120110 = u := ⟨_, rfl⟩
  rw [hu₀] at hcμ ⊢
  obtain ⟨l, hl⟩ : ∃ l, lab c.nmem V u₀ = l := ⟨_, rfl⟩
  rw [hl]
  obtain ⟨hr0μ, hr0u⟩ := hO.rk u₀ hcμ
  obtain ⟨r0, hr0⟩ : ∃ r, rkOf c.nmem V u₀ = r := ⟨_, rfl⟩
  rw [hr0] at hr0μ hr0u
  have hLAB := hO.LAB_le
  have hRK := hO.RK_le
  -- 1. the head
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W clusHead c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 120112 = l ∧ c₁.nreg 120113 = r0 ∧ c₁.nreg 120114 = 1 ∧
        (∀ r, r < 120111 ∨ 120114 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold clusHead
    exec_block
    · rw [hq.LAB, hu₀]; omega
    · config_simp; rw [hq.RK, hu₀]; omega
    · omega
    · refine ⟨rfl, ?_, ?_, by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hq.LAB, hu₀]; exact hl
      · config_simp; rw [hq.RK, hu₀]; exact hr0
      · config_simp; upd_solve
  obtain ⟨x112, x113, x114, r₁, m₁, rr₁, rm₁, o₁⟩ := v₁
  have fr₁ : FrameB (fun r => decide (120111 ≤ r ∧ r ≤ 120114)) c c₁ :=
    exec_frameB e₁ (by decide)
  have hq₁ : QConst P V c₁ := hq.frame fr₁ fun r h1 h2 => by
    grind
  -- 2. the left walk
  have L₀ : LInv P W V c₁ l r0 c₁ := by
    refine ⟨e₁.wb_right, FrameB.refl _ _, x112, by omega, by omega, fun j h1 h2 => ?_,
      fun h => by omega⟩
    grind
  obtain ⟨c₂, k₂, e₂, L₂, hex₂, hk₂⟩ := Exec.whileLtN_potential (a := 120012) (b := 120114)
    (LInv P W V c₁ l r0) (fun d => 13 * (cntBelow c₁.nmem V l (d.nreg 120113) + d.nreg 120114))
    (fun _ h => h.wb)
    (fun d hd ht => leftBody_inv (P := P) hq₁ (by simp_all) hr0μ hd ht) L₀
  have hq₂ : QConst P V c₂ := hq₁.frame L₂.fr fun r h1 h2 => by
    grind
  have hf2 : c₂.nreg 120114 = 0 := by rw [hq₂.zero] at hex₂; omega
  obtain ⟨lo, hlo⟩ : ∃ lo, c₂.nreg 120113 = lo := ⟨_, rfl⟩
  have hlo_r0 : lo ≤ r0 := by rw [← hlo]; exact L₂.i_le
  have hloμ : lo < V.μ := by omega
  have hstop := L₂.stop hf2
  rw [hlo] at hstop
  -- 3. the forward walk
  obtain ⟨c₃, e₃, v₃, r₃⟩ := const_exec (P := P) L₂.wb 120114 1 (by omega)
  have fr₃ : FrameB (fun r => decide (r = 120114)) c₂ c₃ := exec_frameB e₃ (by decide)
  have mm : c₃.nmem = c.nmem := by rw [fr₃.2.2.1, L₂.fr.2.2.1, m₁]
  have R₃ : ∀ r, (r < 120111 ∨ 120118 < r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [r₃ r (by omega), L₂.fr.1 r (by grind),
      r₁ r (by omega)]
  have x3 : c₃.nreg 120113 = lo := by grind
  have F₀ : FInv P W C V z c₃ S l lo c₃ := by
    refine ⟨e₃.wb_right, hq₂.frame fr₃ fun r h1 h2 => by grind,
      ?_, FrameB.refl _ _, ?_, by rw [v₃], by rw [x3], by omega,
      fun j h1 h2 => by omega, fun h => by omega, ?_⟩
    · grind [BestOK]
    · rw [r₃ _ (by decide), L₂.fr.1 _ (by decide), x112]
    · have hbo : bestOf c₃ = bestOf c := by
        core_grind
      rw [hbo, x3]
      have : {x | ∃ j, lo ≤ j ∧ j < lo ∧ x ∈ nodePts c₃.nmem V C (ordAt c₃.nmem V j)} = ∅ := by
        grind
      grind [Set.union_empty]
  obtain ⟨c₄, k₄, e₄, F₄, hex₄, hk₄⟩ := Exec.whileLtN_potential (a := 120012) (b := 120114)
    (FInv P W C V z c₃ S l lo)
    (fun d => (NC + 60) * cntFrom c₃.nmem V l (d.nreg 120113) + 60 * d.nreg 120114)
    (fun _ h => h.wb)
    (fun d hd ht => fwdBody_inv (P := P) hG hW hs (by grind) (by grind)
      (fun u hu => by grind) hd ht) F₀
  have hf4 : c₄.nreg 120114 = 0 := by rw [F₄.q.zero] at hex₄; omega
  obtain ⟨hi, hhi⟩ : ∃ hi, c₄.nreg 120113 = hi := ⟨_, rfl⟩
  have hstop4 := F₄.stop hf4
  rw [hhi] at hstop4
  have hlo4 : lo ≤ hi := by rw [← hhi]; exact F₄.lo_le
  have hhiμ : hi ≤ V.μ := by rw [← hhi]; exact F₄.i_le
  -- the block is `[lo, hi)`
  have m13 : c₁.nmem = c₃.nmem := by rw [m₁, mm]
  have hO3 : OrdOK c₃.nmem V W := by grind
  rw [← mm]
  have hblkL : ∀ j, lo ≤ j → j ≤ r0 → lab c₃.nmem V (ordAt c₃.nmem V j) = l := by
    intro j h1 h2; rw [← m13]; exact L₂.blk j (by omega) h2
  have hr0hi : r0 < hi := by
    grind
  have hstop' : lo = 0 ∨ lab c₃.nmem V (ordAt c₃.nmem V (lo - 1)) ≠ l := by
    grind
  have hmemb : ∀ j, j < V.μ → (lab c₃.nmem V (ordAt c₃.nmem V j) = l ↔ lo ≤ j ∧ j < hi) := by
    intro j hj
    constructor
    · intro hjl
      refine ⟨?_, ?_⟩
      · by_contra hc; push Not at hc
        exact lab_ne_left hO3 hloμ (hblkL lo le_rfl hlo_r0) hstop' hc hjl
      · by_contra hc; push Not at hc
        exact lab_ne_right hO3 hr0hi (hblkL r0 hlo_r0 le_rfl) hstop4 hc hj hjl
    · rintro ⟨h1, h2⟩; exact F₄.blk j h1 (by omega)
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_, F₄.b, ?_⟩
  · -- the cost
    have hcs := card_positions hO3 l
    have hc1 : cntBelow c₁.nmem V l r0 ≤ clusSize c₃.nmem V l := by
      rw [← hcs, m13]; exact cntBelow_le l r0 hr0μ.le
    have hc2 : cntFrom c₃.nmem V l lo ≤ clusSize c₃.nmem V l := by
      rw [← hcs]; exact cntFrom_le l lo
    rw [x113, x114] at hk₂
    rw [x3, v₃] at hk₄
    have h1 : (NC + 60) * cntFrom c₃.nmem V l lo ≤ (NC + 60) * clusSize c₃.nmem V l :=
      Nat.mul_le_mul_left _ hc2
    grind
  · have f₂' : FrameB BC c₁ c₂ := FrameB.mono L₂.fr fun r hr => by
      simp only [decide_eq_true_eq] at hr
      simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
    have f₁' : FrameB BC c c₁ := FrameB.mono fr₁ fun r hr => by
      simp only [decide_eq_true_eq] at hr
      simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
    have f₃' : FrameB BC c₂ c₃ := FrameB.mono fr₃ fun r hr => by
      simp only [decide_eq_true_eq] at hr
      simp only [BC, Bool.or_eq_true, decide_eq_true_eq]; omega
    exact f₁'.trans (f₂'.trans (f₃'.trans F₄.fr))
  · have e : clusPts c₃.nmem V C l =
        {x | ∃ j, lo ≤ j ∧ j < c₄.nreg 120113 ∧ x ∈ nodePts c₃.nmem V C (ordAt c₃.nmem V j)} := by
      rw [hhi]
      ext x
      simp only [clusPts, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, hu, hul, hx⟩
        obtain ⟨hru, hru'⟩ := hO3.rk u hu
        grind
      · rintro ⟨j, h1, h2, hx⟩
        have hjμ : j < V.μ := by omega
        exact ⟨ordAt c₃.nmem V j, hO3.lt j hjμ, (hmemb j hjμ).2 ⟨h1, h2⟩, hx⟩
    rw [e]; exact F₄.hit


end

end

end OracleR

end Chazelle.Core
